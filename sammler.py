#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Zeitreihen-Sammler, Version 2.

Holt Listen von den konfigurierten Quellen, verdichtet sie je Schlüssel und Variante zu einer
Zeile und legt jeden neuen Stand als verschlüsselte Datei ab. Alle Adressen, Feldnamen und
Zugangsdaten kommen aus der Umgebung; in diesem Skript steht nichts davon.

Aufruf:
  python3 sammler.py           stündlicher Lauf (holt neue Stände und wartet auf den nächsten, wenn er bald kommt)
  python3 sammler.py woche     Wochenlauf: Wörterbuch zusammenfassen, Wochenarchiv, Ringpuffer

Umgebung:
  FM_ID, FM_GEHEIM   Zugangsdaten für das Token (nur stündlicher Lauf)
  FM_SCHLUESSEL      Datenschlüssel (32 Byte, Base64)
  FM_KONFIG          Einstellungen als JSON
  GH_TOKEN, REPO     nur Wochenlauf: Zugriff auf das eigene Projekt
"""
import base64
import datetime as dt
import gzip
import hashlib
import io
import json
import lzma
import math
import os
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile
from email.utils import parsedate_to_datetime

from cryptography.hazmat.primitives.ciphers.aead import AESGCM

VERSION = "0.1.1"
KENNUNG = b"FMD1"
SPALTEN = ["item", "variante", "min", "markt", "s100", "s1000", "menge", "angebote", "neu", "neu_menge", "kurz"]
STAFFEL = ["s10000", "st5", "st10", "st25"]
UMFORMUNG = {"item": "delta", "markt": "minus_min", "s100": "minus_min", "s1000": "minus_min", "s10000": "minus_min"}
ZIEL = os.environ.get("FM_ZIEL", "d")
VORDNER = os.environ.get("FM_VORDNER", "v")
GH_API = os.environ.get("FM_GH_API", "https://api.github.com")
GH_HOCH = os.environ.get("FM_GH_UPLOAD", "https://uploads.github.com")


def sag(text):
    print(text, flush=True)


def utc_jetzt():
    return dt.datetime.now(dt.timezone.utc)


# ---------------------------------------------------------------- Abruf
class Antwort:
    def __init__(self, status, kopf, roh, fehler=""):
        self.status, self.kopf, self.roh, self.fehler = status, kopf, roh, fehler

    def json(self):
        try:
            return json.loads(self.roh.decode("utf-8"))
        except Exception:
            return None


def hole(url, params=None, kopf=None, methode="GET", daten=None, versuche=3, timeout=180):
    if params:
        url += ("&" if "?" in url else "?") + urllib.parse.urlencode(params)
    h = {"Accept-Encoding": "gzip", "User-Agent": "sammler/" + VERSION}
    h.update(kopf or {})
    letzter = ""
    for v in range(versuche):
        req = urllib.request.Request(url, data=daten, method=methode, headers=h)
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                status, hk, roh = r.status, r.headers, r.read()
        except urllib.error.HTTPError as e:
            status, hk, roh = e.code, e.headers, e.read()
        except Exception as e:
            letzter = type(e).__name__
            time.sleep(3 * (v + 1))
            continue
        if status in (429, 500, 502, 503, 504) and v < versuche - 1:
            time.sleep(5 * (v + 1))
            continue
        k = {a.lower(): b for a, b in hk.items()}
        if k.get("content-encoding", "").lower() == "gzip" and roh:
            try:
                roh = gzip.decompress(roh)
            except Exception:
                return Antwort(0, k, b"", "Antwort nicht lesbar")
        return Antwort(status, k, roh)
    return Antwort(0, {}, b"", letzter or "keine Antwort")


def hole_token(konfig, kennung, geheim):
    auth = base64.b64encode(f"{kennung}:{geheim}".encode()).decode()
    r = hole(konfig["token_url"], None, {"Authorization": "Basic " + auth, "Content-Type": "application/x-www-form-urlencoded"}, "POST", b"grant_type=client_credentials")
    tok = (r.json() or {}).get("access_token") if r.status == 200 else None
    if not tok:
        raise SystemExit(f"Kein Token erhalten (Status {r.status}).")
    return tok


# ---------------------------------------------------------------- Verschlüsselung
def verschluessele(daten, schluessel):
    nonce = os.urandom(12)
    return KENNUNG + nonce + AESGCM(schluessel).encrypt(nonce, daten, KENNUNG)


def entschluessele(roh, schluessel):
    if roh[:4] != KENNUNG:
        raise ValueError("Unbekanntes Dateiformat")
    return AESGCM(schluessel).decrypt(roh[4:16], roh[16:], KENNUNG)


def lies_schluessel(text):
    try:
        s = base64.urlsafe_b64decode(text.strip() + "=" * (-len(text.strip()) % 4))
    except Exception:
        s = b""
    if len(s) != 32:
        raise SystemExit("FM_SCHLUESSEL fehlt oder hat nicht die erwartete Länge.")
    return s


def schreibe_json_verschluesselt(pfad, obj, schluessel):
    roh = lzma.compress(json.dumps(obj, separators=(",", ":"), sort_keys=True).encode("utf-8"), preset=9)
    os.makedirs(os.path.dirname(pfad) or ".", exist_ok=True)
    with open(pfad + ".teil", "wb") as f:
        f.write(verschluessele(roh, schluessel))
    os.replace(pfad + ".teil", pfad)


def lies_json_verschluesselt(pfad, schluessel):
    with open(pfad, "rb") as f:
        return json.loads(lzma.decompress(entschluessele(f.read(), schluessel)).decode("utf-8"))


# ---------------------------------------------------------------- Varianten-Wörterbuch
class Woerterbuch:
    """Feste Nummer je (Schlüssel, Variante). Basis-Datei plus kleine Nachträge je Lauf.

    Basis:    v/basis.bin   {"v":1, "i": {"<schluessel>": {"<variante>": nr, ...}}}
    Nachtrag: v/n-<zeit>.bin {"v":1, "n": [[schluessel, nr, variante], ...]}
    """

    def __init__(self, ordner, schluessel):
        self.ordner, self.schluessel = ordner, schluessel
        self.items, self.neu, self.nachtraege = {}, [], []
        basis = os.path.join(ordner, "basis.bin")
        if os.path.isfile(basis):
            for iid, d in lies_json_verschluesselt(basis, schluessel)["i"].items():
                self.items[int(iid)] = dict(d)
        if os.path.isdir(ordner):
            for n in sorted(os.listdir(ordner)):
                if n.startswith("n-") and n.endswith(".bin"):
                    self.nachtraege.append(os.path.join(ordner, n))
                    for iid, nr, var in lies_json_verschluesselt(os.path.join(ordner, n), schluessel)["n"]:
                        self.items.setdefault(int(iid), {}).setdefault(var, int(nr))

    def nummer(self, iid, var):
        if not var:
            return 0
        d = self.items.get(iid)
        if d is None:
            d = self.items[iid] = {}
        nr = d.get(var)
        if nr is None:
            nr = d[var] = max(d.values(), default=0) + 1
            self.neu.append([iid, nr, var])
        return nr

    def anzahl(self):
        return sum(len(d) for d in self.items.values())

    def speichere_nachtrag(self, zeit):
        if not self.neu:
            return 0
        pfad = os.path.join(self.ordner, f"n-{zeit.strftime('%Y%m%d%H%M%S')}.bin")
        schreibe_json_verschluesselt(pfad, {"v": 1, "n": self.neu}, self.schluessel)
        anz = len(self.neu)
        self.neu = []
        return anz

    def zusammenfassen(self):
        schreibe_json_verschluesselt(os.path.join(self.ordner, "basis.bin"),
                                     {"v": 1, "i": {str(k): v for k, v in self.items.items()}}, self.schluessel)
        for p in self.nachtraege:
            os.remove(p)
        anz = len(self.nachtraege)
        self.nachtraege = []
        return anz


def varianten_text(it, vk):
    """Beschreibt die Variante eines Eintrags als kurzen Text; leer = keine Variante."""
    if not isinstance(it, dict) or not vk:
        return ""
    liste = it.get(vk.get("liste", ""))
    a = ".".join(str(x) for x in sorted(x for x in liste if isinstance(x, int) and not isinstance(x, bool))) if isinstance(liste, list) else ""
    b = ""
    paare = it.get(vk.get("paare", ""))
    if isinstance(paare, list):
        arten, fa, fw = set(vk.get("paar_arten", [])), vk.get("paar_art", "type"), vk.get("paar_wert", "value")
        p = sorted((x.get(fa), x.get(fw)) for x in paare if isinstance(x, dict) and x.get(fa) in arten)
        b = ".".join(f"{t}:{w}" for t, w in p)
    z = [it.get(f) for f in vk.get("zusatz", [])]
    c = ".".join("" if x is None else str(x) for x in z) if any(x is not None for x in z) else ""
    return f"{a}|{b}|{c}" if (a or b or c) else ""


# ---------------------------------------------------------------- Verdichten
class FormFehler(Exception):
    pass


def liste_aus(doc, felder):
    if not isinstance(doc, dict):
        raise FormFehler("Antwort ist kein Objekt")
    eintraege = doc.get(felder["liste"])
    if eintraege is None:
        return []
    if not isinstance(eintraege, list):
        raise FormFehler("Liste hat eine unerwartete Form")
    return eintraege


def schnitt(angebote, stueck, grenze=None):
    rest, kosten, genommen = stueck, 0.0, 0
    for preis, menge in angebote:
        if grenze is not None and preis > grenze:
            break
        k = min(rest, menge)
        kosten += k * preis
        genommen += k
        rest -= k
        if rest <= 0:
            break
    return kosten / genommen


def verdichte(eintraege, felder, vk, wb, max_nr_alt=None, staffel=False):
    """Fasst Einträge je (item, variante) zusammen. Rückgabe: (spalten, statistik).

    min = günstigster Stückpreis; markt = Schnitt der günstigsten 15 % aller Stücke;
    s100/s1000/s10000 = Schnitt der ersten 100/1.000/10.000 Stücke ohne Angebote über dem 3-fachen Mindestpreis;
    st5/st10/st25 = Stücke bis 5/10/25 % über dem Mindestpreis; neu = Einträge mit höherer Nummer als
    beim vorigen Stand (-1 beim ersten Stand); kurz = Einträge mit der kürzesten Restlaufzeit.
    """
    f_item, f_id = felder["item"], felder["item_id"]
    f_menge, f_stk, f_ges, f_lz, f_nr = felder["menge"], felder["stueckpreis"], felder["gesamtpreis"], felder["laufzeit"], felder["nr"]
    kurz_wert = felder.get("kurz_wert", "SHORT")
    gruppen = {}
    stat = {"eintraege": 0, "ohne_preis": 0, "fehlerhaft": 0, "max_nr": max_nr_alt or 0}
    for e in eintraege:
        stat["eintraege"] += 1
        if not isinstance(e, dict):
            stat["fehlerhaft"] += 1
            continue
        it = e.get(f_item)
        iid = it.get(f_id) if isinstance(it, dict) else it
        menge = e.get(f_menge)
        if not isinstance(iid, int) or isinstance(iid, bool) or not isinstance(menge, int) or menge < 1:
            stat["fehlerhaft"] += 1
            continue
        if e.get(f_stk):
            preis = e[f_stk]
        elif e.get(f_ges):
            preis = e[f_ges] / menge
        else:
            stat["ohne_preis"] += 1
            continue
        if not isinstance(preis, (int, float)) or preis <= 0:
            stat["fehlerhaft"] += 1
            continue
        variante = wb.nummer(iid, varianten_text(it, vk)) if vk else 0
        nr = e.get(f_nr)
        nr = nr if isinstance(nr, int) else 0
        if nr > stat["max_nr"]:
            stat["max_nr"] = nr
        g = gruppen.get((iid, variante))
        if g is None:
            g = gruppen[(iid, variante)] = [[], 0, 0, 0]
        g[0].append((preis, menge))
        if max_nr_alt is not None and nr > max_nr_alt:
            g[1] += 1
            g[2] += menge
        if e.get(f_lz) == kurz_wert:
            g[3] += 1
    namen = SPALTEN + (STAFFEL if staffel else [])
    sp = {n: [] for n in namen}
    for (iid, variante), (angebote, neu, neu_menge, kurz) in sorted(gruppen.items()):
        angebote.sort()
        gesamt = sum(m for _, m in angebote)
        mini = angebote[0][0]
        werte = [iid, variante, int(round(mini)), int(round(schnitt(angebote, max(1, math.ceil(0.15 * gesamt))))),
                 int(round(schnitt(angebote, 100, 3 * mini))), int(round(schnitt(angebote, 1000, 3 * mini))),
                 gesamt, len(angebote), neu if max_nr_alt is not None else -1, neu_menge if max_nr_alt is not None else -1, kurz]
        if staffel:
            werte += [int(round(schnitt(angebote, 10000, 3 * mini)))] + [sum(m for p, m in angebote if p <= mini * f) for f in (1.05, 1.10, 1.25)]
        for n, w in zip(namen, werte):
            sp[n].append(w)
    stat["zeilen"] = len(sp["item"])
    return sp, stat


# ---------------------------------------------------------------- Ablage
# Dateiaufbau (vor dem Verschlüsseln, LZMA-gepackt):
#   4 Byte Länge des Kopfes, Kopf als JSON, danach je Spalte ein Block ganzer Zahlen (Zickzack-Varint).
#   Kopf: {"v":2, "n":Zeilen, "spalten":[[Name, Umformung, Bytes], ...], weitere Angaben zum Stand}
def varint(werte):
    aus = bytearray()
    for v in werte:
        v = (v << 1) ^ (v >> 63)
        while v > 0x7F:
            aus.append((v & 0x7F) | 0x80)
            v >>= 7
        aus.append(v)
    return bytes(aus)


def packe(spalten, meta):
    mini = spalten["min"]
    bloecke, kopf_spalten = [], []
    for name, werte in spalten.items():
        art = UMFORMUNG.get(name, "")
        if art == "delta":
            werte = [w - v for w, v in zip(werte, [0] + werte[:-1])]
        elif art == "minus_min":
            werte = [w - m for w, m in zip(werte, mini)]
        block = varint(werte)
        bloecke.append(block)
        kopf_spalten.append([name, art, len(block)])
    kopf = dict(meta)
    kopf.update({"v": 2, "n": len(mini), "spalten": kopf_spalten})
    kb = json.dumps(kopf, separators=(",", ":"), sort_keys=True).encode("utf-8")
    return lzma.compress(len(kb).to_bytes(4, "little") + kb + b"".join(bloecke), preset=9 | lzma.PRESET_EXTREME)


def stand_zeit(kopf):
    lm = kopf.get("last-modified")
    if not lm:
        return None, None
    try:
        return lm, parsedate_to_datetime(lm).astimezone(dt.timezone.utc)
    except Exception:
        return lm, None


def pfad_fuer(zeit, k):
    return os.path.join(ZIEL, zeit.strftime("%Y-%m"), zeit.strftime("%d"), f"{zeit.strftime('%H%M')}-{k}.bin")


# ---------------------------------------------------------------- Stündlicher Lauf
def eine_quelle(q, konfig, kopf, alt, wb, schluessel, jetzt):
    """Rückgabe: ("neu"|"gleich"|"stoerung", info, neuer_zustand_oder_None)."""
    k, felder = q["k"], konfig["felder"]
    bedingt = dict(kopf)
    if alt.get("lm"):
        bedingt["If-Modified-Since"] = alt["lm"]
    r = hole(konfig["basis"] + q["p"], konfig.get("parameter"), bedingt)
    if r.status == 304:
        return "gleich", "", None
    if r.status != 200:
        if r.status in (0, 429, 500, 502, 503, 504):
            return "stoerung", f"Status {r.status} {r.fehler}".strip(), None
        raise FormFehler(f"Status {r.status}")
    lm, zeit = stand_zeit(r.kopf)
    if lm and lm == alt.get("lm"):
        return "gleich", "", None
    eintraege = liste_aus(r.json(), felder)
    vor = len(wb.neu)
    spalten, stat = verdichte(eintraege, felder, konfig.get("variante") if q.get("var", 1) else None, wb, alt.get("max_nr"), bool(q.get("staffel")))
    if stat["eintraege"] and stat["fehlerhaft"] > 0.02 * stat["eintraege"]:
        del wb.neu[vor:]
        raise FormFehler(f"{stat['fehlerhaft']} von {stat['eintraege']} Einträgen haben eine unerwartete Form")
    if not stat["zeilen"] and (alt.get("zeilen") or 0) > 0:
        del wb.neu[vor:]
        raise FormFehler("leere Antwort, obwohl der vorige Stand Daten hatte")
    pruef = hashlib.sha256(repr(sorted(spalten.items())).encode()).hexdigest()[:16]
    if lm is None and pruef == alt.get("pruef"):
        return "gleich", "", None
    zeit = zeit or jetzt
    pfad = pfad_fuer(zeit, k)
    meta = {"q": k, "stand": zeit.strftime("%Y-%m-%dT%H:%M:%SZ"), "abruf": utc_jetzt().strftime("%Y-%m-%dT%H:%M:%SZ"),
            "eintraege": stat["eintraege"], "ohne_preis": stat["ohne_preis"], "erster": int(alt.get("max_nr") is None)}
    if os.path.exists(pfad):
        info = f"Stand {zeit.strftime('%d.%m. %H:%M')} liegt schon vor"
    else:
        roh = verschluessele(packe(spalten, meta), schluessel)
        os.makedirs(os.path.dirname(pfad), exist_ok=True)
        with open(pfad, "wb") as f:
            f.write(roh)
        info = f"neuer Stand {zeit.strftime('%d.%m. %H:%M')} UTC, {stat['eintraege']} Einträge, {stat['zeilen']} Zeilen, {len(roh) / 1024:.0f} KB"
    zustand = {"lm": lm, "max_nr": stat["max_nr"], "zeilen": stat["zeilen"], "pruef": pruef, "stand": meta["stand"]}
    return "neu", info, zustand


def lade_konfig():
    try:
        konfig = json.loads(os.environ.get("FM_KONFIG", ""))
        assert isinstance(konfig["quellen"], list) and konfig["felder"]
        return konfig
    except Exception:
        raise SystemExit("FM_KONFIG fehlt oder ist kein gültiges JSON.")


def stand_von(z):
    try:
        return dt.datetime.strptime(z["stand"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc)
    except Exception:
        return None


def lauf():
    """Holt sofort alle neuen Stände. Kommt der nächste Stand innerhalb von vorlauf_min Minuten,
    wartet der Lauf auch auf ihn. So entstehen keine Lücken, auch wenn GitHub die Läufe
    unregelmäßig und nur etwa stündlich startet."""
    kennung, geheim = os.environ.get("FM_ID", "").strip(), os.environ.get("FM_GEHEIM", "").strip()
    if not kennung or not geheim:
        raise SystemExit("FM_ID oder FM_GEHEIM fehlt.")
    schluessel = lies_schluessel(os.environ.get("FM_SCHLUESSEL", ""))
    konfig = lade_konfig()
    standdatei = os.path.join(VORDNER, "stand.json")
    try:
        with open(standdatei, encoding="utf-8") as f:
            stand = json.loads(f.read())
    except Exception:
        stand = {}
    takt = float(konfig.get("takt_s", 120))
    intervall = dt.timedelta(minutes=float(konfig.get("intervall_min", 60)))
    vorlauf = dt.timedelta(minutes=float(konfig.get("vorlauf_min", 50)))
    nachlauf = dt.timedelta(minutes=float(konfig.get("nachlauf_min", 15)))
    hart = time.time() + float(konfig.get("max_min", 70)) * 60
    kopf = {"Authorization": "Bearer " + hole_token(konfig, kennung, geheim)}
    wb = Woerterbuch(VORDNER, schluessel)
    quellen = {q["k"]: q for q in konfig["quellen"]}
    gesperrt, stoerungen = set(), {}
    zaehler = {"neu": 0, "fehler": 0}

    def runde(auswahl):
        neu = 0
        for k in auswahl:
            if k in gesperrt:
                continue
            try:
                ergebnis, info, zustand = eine_quelle(quellen[k], konfig, kopf, stand.get(k) or {}, wb, schluessel, utc_jetzt())
            except FormFehler as e:
                zaehler["fehler"] += 1
                gesperrt.add(k)
                sag(f"Quelle {k}: FEHLER - {e}")
                continue
            except Exception as e:                               # nichts Unerwartetes darf Zugangsdaten ins Protokoll bringen
                zaehler["fehler"] += 1
                gesperrt.add(k)
                sag(f"Quelle {k}: FEHLER - {type(e).__name__}")
                continue
            if ergebnis == "neu":
                neu += 1
                stand[k] = zustand
                sag(f"Quelle {k}: {info}")
            elif ergebnis == "stoerung":
                stoerungen[k] = stoerungen.get(k, 0) + 1
                if stoerungen[k] >= 3:
                    zaehler["fehler"] += 1
                    gesperrt.add(k)
                    sag(f"Quelle {k}: FEHLER - dreimal gestört ({info})")
        if neu:
            zaehler["neu"] += neu
            sichern()
        return neu

    def sichern():                                               # nach jeder Runde mit neuen Ständen, falls der Lauf abbricht
        wb.speichere_nachtrag(utc_jetzt())
        os.makedirs(VORDNER, exist_ok=True)
        with open(standdatei + ".teil", "w", encoding="utf-8") as f:
            f.write(json.dumps(stand, indent=1, sort_keys=True))
        os.replace(standdatei + ".teil", standdatei)

    # 1. sofort: alles holen, was gerade neu ist
    n = runde(list(quellen))
    sag(f"Sofort: {n} neue Stände von {len(quellen)} Quellen.")

    # 2. nächsten Stand abwarten, wenn er bald kommt
    zeiten = [t for t in (stand_von(stand.get(k) or {}) for k in quellen) if t]
    if zeiten:
        jetzt = utc_jetzt()
        ziel = max(zeiten) + intervall
        while ziel < jetzt - nachlauf:                           # Quelle hat Stände ausgelassen
            ziel += intervall
        if ziel - jetzt > vorlauf:
            sag(f"Nächster Stand gegen {ziel.strftime('%H:%M')} UTC, in {(ziel - jetzt).total_seconds() / 60:.0f} Minuten - das übernimmt der nächste Lauf.")
        else:
            warte = (ziel - jetzt).total_seconds() - 60
            sag(f"Warte auf den Stand gegen {ziel.strftime('%H:%M')} UTC (Nachfrage alle {takt:.0f} s) ...")
            if warte > 0:
                time.sleep(min(warte, max(0, hart - time.time())))
            schwelle = ziel - intervall / 2
            while True:
                offen = [k for k in quellen if k not in gesperrt and not ((stand_von(stand.get(k) or {}) or ziel - intervall) >= schwelle)]
                if not offen:
                    break
                runde(offen)
                offen = [k for k in quellen if k not in gesperrt and not ((stand_von(stand.get(k) or {}) or ziel - intervall) >= schwelle)]
                if not offen or utc_jetzt() > ziel + nachlauf or time.time() + takt > hart:
                    for k in offen:
                        sag(f"Quelle {k}: Stand gegen {ziel.strftime('%H:%M')} UTC kam nicht in diesem Lauf")
                    break
                time.sleep(takt)
    if wb.neu:
        sichern()
    sag(f"Fertig: {zaehler['neu']} neue Stände, {zaehler['fehler']} Fehler, Varianten gesamt {wb.anzahl()}.")
    return 1 if zaehler["fehler"] else 0


# ---------------------------------------------------------------- Wochenlauf
def gh(methode, url, token, daten=None, art="application/json"):
    kopf = {"Authorization": "Bearer " + token, "Accept": "application/vnd.github+json", "X-GitHub-Api-Version": "2022-11-28"}
    if daten is not None:
        kopf["Content-Type"] = art
        if art == "application/json":
            daten = json.dumps(daten).encode()
    r = hole(url, None, kopf, methode, daten, timeout=600)
    return r.status, r.json()


def git(*args, eingabe=None):
    r = subprocess.run(["git", *args], input=eingabe, capture_output=True)
    if r.returncode != 0:
        raise RuntimeError(f"git {args[0]} fehlgeschlagen: {r.stderr.decode(errors='replace')[-300:]}")
    return r.stdout.decode().strip()


def alle_releases(repo, token):
    aus, seite = {}, 1
    while True:
        st, d = gh("GET", f"{GH_API}/repos/{repo}/releases?per_page=100&page={seite}", token)
        if st != 200 or not isinstance(d, list):
            raise RuntimeError(f"Archivliste nicht lesbar (Status {st})")
        for rel in d:
            aus[rel["tag_name"]] = {"id": rel["id"], "assets": {a["name"]: a.get("size") for a in rel.get("assets", [])},
                                    "upload_url": rel.get("upload_url", "")}
        if len(d) < 100:
            return aus
        seite += 1


def stand_dateien():
    """Alle Stand-Dateien: Liste (pfad, datum, quelle)."""
    aus = []
    for wurzel, _, dateien in os.walk(ZIEL):
        for n in dateien:
            if not n.endswith(".bin") or "-" not in n:
                continue
            teile = os.path.relpath(os.path.join(wurzel, n), ZIEL).replace("\\", "/").split("/")
            try:
                datum = dt.datetime.strptime(teile[0] + "-" + teile[1], "%Y-%m-%d").date()
            except Exception:
                continue
            aus.append((os.path.join(wurzel, n), datum, n[:-4].split("-", 1)[1]))
    return sorted(aus)


def woche():
    schluessel = lies_schluessel(os.environ.get("FM_SCHLUESSEL", ""))
    konfig = lade_konfig()
    token, repo = os.environ.get("GH_TOKEN", ""), os.environ.get("REPO", "")
    if not token or repo.count("/") != 1:
        raise SystemExit("GH_TOKEN oder REPO fehlt.")
    ring = int(konfig.get("ring_tage", 14))
    heute = utc_jetzt().date()
    geaendert = False

    # 1. Wörterbuch zusammenfassen
    wb = Woerterbuch(VORDNER, schluessel)
    if wb.nachtraege:
        n = wb.zusammenfassen()
        geaendert = True
        sag(f"Wörterbuch: {n} Nachträge zusammengefasst, {wb.anzahl()} Varianten.")

    # 2. Wochenarchiv: jede abgeschlossene Woche als eigene Veröffentlichung, je Quelle eine Zip-Datei "<quelle>-<anzahl>.zip"
    dateien = stand_dateien()
    wochen = {}
    for pfad, datum, k in dateien:
        j, w, _ = datum.isocalendar()
        wochen.setdefault(f"w{j}-{w:02d}", {}).setdefault(k, []).append((pfad, datum))
    releases = alle_releases(repo, token)
    gesichert = set()
    anker_da = False
    for tag in sorted(wochen):
        j, w = int(tag[1:5]), int(tag[6:])
        if dt.date.fromisocalendar(j, w, 7) >= heute:
            continue                                             # Woche noch nicht abgeschlossen
        soll = {f"{k}-{len(v)}.zip": (k, v) for k, v in wochen[tag].items()}
        rel = releases.get(tag)

        def gedeckt(name):
            """Gesichert, wenn ein Archiv dieser Quelle mit mindestens so vielen Ständen vorliegt
            (nach dem Ringpuffer liegen im Projekt evtl. nur noch Teile einer Woche)."""
            if not rel:
                return False
            k, n = name[:-4].rsplit("-", 1)
            return any(a[:-4].rsplit("-", 1)[0] == k and a[:-4].rsplit("-", 1)[1].isdigit() and int(a[:-4].rsplit("-", 1)[1]) >= int(n)
                       for a in rel["assets"] if a.endswith(".zip") and "-" in a)

        fehlt = [n for n in soll if not gedeckt(n)]
        if fehlt:
            if not anker_da:
                anker_sicherstellen()
                anker_da = True
            if not rel:
                st, d = gh("POST", f"{GH_API}/repos/{repo}/releases", token,
                           {"tag_name": tag, "name": tag, "target_commitish": "anker", "body": "", "draft": False, "prerelease": False})
                if st != 201:
                    sag(f"Archiv {tag}: FEHLER beim Anlegen (Status {st})")
                    continue
                rel = releases[tag] = {"id": d["id"], "assets": {}, "upload_url": d.get("upload_url", "")}
            for name in fehlt:
                k, liste = soll[name]
                puffer = io.BytesIO()
                with zipfile.ZipFile(puffer, "w", zipfile.ZIP_STORED) as z:
                    for pfad, _ in liste:
                        z.write(pfad, os.path.relpath(pfad, ZIEL).replace("\\", "/"))
                inhalt = puffer.getvalue()
                st, d = gh("POST", f"{GH_HOCH}/repos/{repo}/releases/{rel['id']}/assets?name={urllib.parse.quote(name)}", token,
                           inhalt, "application/zip")
                if st == 201 and isinstance(d, dict) and d.get("size") == len(inhalt):
                    rel["assets"][name] = len(inhalt)
                else:
                    sag(f"Archiv {tag}: FEHLER beim Hochladen von {name} (Status {st})")
            sag(f"Archiv {tag}: {sum(1 for n in soll if gedeckt(n))} von {len(soll)} Dateien gesichert.")
        if rel and all(gedeckt(n) for n in soll):
            gesichert.add(tag)

    # 3. Ringpuffer: nur gesicherte Stände älter als ring Tage entfernen
    grenze = heute - dt.timedelta(days=ring)
    weg = 0
    for pfad, datum, _ in dateien:
        j, w, _ = datum.isocalendar()
        if datum < grenze and f"w{j}-{w:02d}" in gesichert:
            os.remove(pfad)
            weg += 1
    for wurzel, unter, rest in sorted(os.walk(ZIEL, topdown=False)):
        if wurzel != ZIEL and not os.listdir(wurzel):
            os.rmdir(wurzel)
    if weg:
        geaendert = True
        sag(f"Ringpuffer: {weg} Stände älter als {ring} Tage entfernt (sie liegen im Wochenarchiv).")

    # 4. Verlauf durch einen frischen Stand ersetzen, damit das Projekt klein bleibt
    if geaendert:
        zweig = git("rev-parse", "--abbrev-ref", "HEAD")
        git("checkout", "-q", "--orphan", "frisch")
        git("add", "-A")
        git("-c", "user.name=github-actions[bot]", "-c", "user.email=41898282+github-actions[bot]@users.noreply.github.com",
            "commit", "-q", "-m", "stand")
        git("push", "-q", "-f", "origin", f"HEAD:refs/heads/{zweig}")
        sag("Verlauf ersetzt.")
    else:
        sag("Nichts zu tun.")
    return 0


def anker_sicherstellen():
    """Leerer Zweig 'anker', an dem die Archiv-Markierungen hängen (hält keine alten Daten fest)."""
    if git("ls-remote", "--heads", "origin", "anker"):
        return
    leer = git("hash-object", "-t", "tree", "-w", "--stdin", eingabe=b"")
    c = git("-c", "user.name=github-actions[bot]", "-c", "user.email=41898282+github-actions[bot]@users.noreply.github.com",
            "commit-tree", leer, "-m", "anker")
    git("push", "-q", "origin", f"{c}:refs/heads/anker")


if __name__ == "__main__":
    sys.exit(woche() if sys.argv[1:2] == ["woche"] else lauf())
