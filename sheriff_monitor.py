#!/usr/bin/env python3
"""NJ sheriff-sale monitor.

Every new listing is looked up in the NJ tax-parcel database (MOD-IV) to learn what it really is, then filtered:

  * Essex/Bergen/Passaic/Hudson/Union: 4+ unit, apartments (4C), commercial (4A, incl. storage), industrial (4B), vacant land
  * Morris/Sussex: lakefront on Lake Mohawk / Lake Hopatcong
  * DROPPED if the SalesWeb status history shows WRIT EXPIRED, Bankruptcy or Adjourned Plaintiff
  * DROPPED if the upset price is not at least $50,000 below the estimated value
    (estimate = tax assessment / NJ Chapter 123 average ratio)
  * Anything listed in ignore.txt is skipped

Email rules: ONLY when a new qualifying property appears, at most once per day. Problems are shown on the dashboard, never emailed.
Env vars (GitHub secrets): GMAIL_USER, GMAIL_APP_PASSWORD, NOTIFY_TO
"""
import datetime, hashlib, html, json, math, os, re, smtplib, sys, time
from collections import Counter
from email.message import EmailMessage
from pathlib import Path
from urllib.parse import quote, urljoin

import requests
from bs4 import BeautifulSoup

HERE = Path(__file__).parent
STATE_FILE = HERE / "seen.json"
DATA_FILE = HERE / "docs" / "data.json"      # feeds the dashboard (docs/index.html)
IGNORE_FILE = HERE / "ignore.txt"
SCHEMA = 3                                    # bump to force a clean re-scan under new rules

MIN_DISCOUNT = 50_000          # upset must be at least this far BELOW estimated value
EMAIL_MIN_HOURS = 20           # property emails: at most about once a day
PROBLEM_EMAIL_DAYS = 7         # problem emails: at most weekly
GEOCODE_CAP = 40               # max address geocodes per run (fallback lookups)
EXCLUDE_STATUS_RE = re.compile(r"writ\s+expired|bankruptcy|adjourned\s+plaintiff", re.I)

CIVIL = "https://salesweb.civilview.com/Sales/SalesSearch?countyId={}"
PARCEL_URLS = [
    "https://services2.arcgis.com/XVOqAjTOJ5P6ngMu/arcgis/rest/services/Parcels_Composite_NJ_WM/FeatureServer/0/query",  # hosted, fast
    "https://maps.nj.gov/arcgis/rest/services/Framework/Cadastral/MapServer/0/query",                                  # state, slow fallback
]
OVERPASS_URLS = ["https://overpass-api.de/api/interpreter", "https://overpass.kumi.systems/api/interpreter",
                 "https://lz4.overpass-api.de/api/interpreter"]
RATIO_URL = "https://www.nj.gov/njbonds/treasury/taxation/pdf/lpt/chap123/{}CH123.pdf"

GLOBAL_DEADLINE = time.time() + float(os.getenv("TIME_BUDGET_MIN", "40")) * 60
DEADLINE = GLOBAL_DEADLINE     # per-county slice, set in main()
HEADERS = {"User-Agent": "Mozilla/5.0 (sheriff-sale-monitor; personal use)"}

SOURCES = [
    {"county": "Essex",   "type": "civilview", "url": CIVIL.format(2),  "rules": "investment"},
    {"county": "Bergen",  "type": "civilview", "url": CIVIL.format(7),  "rules": "investment"},
    {"county": "Passaic", "type": "civilview", "url": CIVIL.format(17), "rules": "investment"},
    {"county": "Hudson",  "type": "civilview", "url": CIVIL.format(10), "rules": "investment"},
    {"county": "Union",   "type": "civilview", "url": CIVIL.format(15), "rules": "investment"},
    {"county": "Morris",  "type": "civilview", "url": CIVIL.format(9),  "rules": "lake"},
    {"county": "Sussex",  "type": "sussex", "url": "https://www.sussexcountysheriff.com/foreclosure-listings", "rules": "lake"},
]
LAKES = {   # bbox = south, west, north, east (limits the OpenStreetMap query)
    "Lake Mohawk":    {"towns": ["sparta"], "bbox": (40.99, -74.70, 41.08, -74.55)},
    "Lake Hopatcong": {"towns": ["hopatcong", "byram", "jefferson", "mount arlington", "mt arlington",
                                 "mt. arlington", "roxbury", "landing"], "bbox": (40.88, -74.75, 41.02, -74.58)},
}
LAKEFRONT_M, NEAR_M = 20, 60                 # parcel boundary to shoreline
POINT_LAKEFRONT_M, POINT_NEAR_M = 40, 120    # looser when only an address point is available

CLASS_NAMES = {"1": "Vacant land", "2": "Residential (1-4 family)", "3A": "Farm (regular)", "3B": "Farm (qualified)",
               "4A": "Commercial", "4B": "Industrial", "4C": "Apartment (5+ units)"}
NUM = {"four": 4, "five": 5, "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10}
ABBR = {"STREET": "ST", "AVENUE": "AVE", "ROAD": "RD", "DRIVE": "DR", "BOULEVARD": "BLVD", "LANE": "LN",
        "PLACE": "PL", "COURT": "CT", "TERRACE": "TER", "TRAIL": "TRL", "PARKWAY": "PKWY", "HIGHWAY": "HWY",
        "TURNPIKE": "TPKE", "CIRCLE": "CIR", "NORTH": "N", "SOUTH": "S", "EAST": "E", "WEST": "W",
        "MOUNT": "MT", "SAINT": "ST"}
ORD = {"FIRST": "1ST", "SECOND": "2ND", "THIRD": "3RD", "FOURTH": "4TH", "FIFTH": "5TH", "SIXTH": "6TH",
       "SEVENTH": "7TH", "EIGHTH": "8TH", "NINTH": "9TH", "TENTH": "10TH", "ELEVENTH": "11TH", "TWELFTH": "12TH",
       "THIRTEENTH": "13TH", "FOURTEENTH": "14TH", "FIFTEENTH": "15TH", "SIXTEENTH": "16TH",
       "SEVENTEENTH": "17TH", "EIGHTEENTH": "18TH", "NINETEENTH": "19TH", "TWENTIETH": "20TH"}
DIRS = {"N", "S", "E", "W"}
STORAGE_RE = re.compile(r"self[\s-]?storage|mini[\s-]?storage|storage\s+(?:facilit|unit|building|center|warehouse|co\b|corp|llc|inc)|\bstorage\b", re.I)
COUNTIES = ["Atlantic", "Bergen", "Burlington", "Camden", "Cape May", "Cumberland", "Essex", "Gloucester", "Hudson",
            "Hunterdon", "Mercer", "Middlesex", "Monmouth", "Morris", "Ocean", "Passaic", "Salem", "Somerset",
            "Sussex", "Union", "Warren"]

def out_of_time():
    return time.time() > DEADLINE

def get(url, **kw):
    r = requests.get(url, headers=HEADERS, timeout=25, **kw)
    r.raise_for_status()
    return r

def now_utc():
    return datetime.datetime.now(datetime.timezone.utc)

# ---------------- state ----------------
def load_state():
    try:
        d = json.loads(STATE_FILE.read_text())
    except Exception:
        return set(), {"schema": SCHEMA}, True
    if d.get("schema") != SCHEMA:          # old format: re-scan everything once under the new rules
        return set(), {"schema": SCHEMA}, True
    return set(d.get("seen", [])), {k: v for k, v in d.items() if k != "seen"}, False

def save_state(seen, meta):
    STATE_FILE.write_text(json.dumps({"seen": sorted(seen), **meta}, indent=1))

def load_data(fresh):
    if not fresh:
        try:
            return json.loads(DATA_FILE.read_text())
        except Exception:
            pass
    return {"items": []}

def load_ignore():
    try:
        return [l.strip().lower() for l in IGNORE_FILE.read_text().splitlines() if l.strip() and not l.startswith("#")]
    except Exception:
        return []

# ---------------- address parsing / parcel lookup ----------------
def norm(s):
    toks = re.sub(r"[^A-Z0-9 ]", " ", s.upper()).split()
    return [ABBR.get(t, t) for t in toks]

def mun_key(s):
    s = re.sub(r"[^A-Z ]", " ", s.upper().replace("-", " "))
    s = re.sub(r"\b(BORO|BOROUGH|TWP|TOWNSHIP|CITY|TOWN|VILLAGE|OF|THE)\b", " ", s)
    return " ".join(s.split())

def parse_address(addr):
    """-> list of (house numbers, street tokens). Handles ranges (548-550), 30-07, AKA, UNIT, ordinal words."""
    out = []
    for seg in re.split(r"\bA/K/A\b|\bAKA\b|\bALSO KNOWN AS\b|\bMAILING ADDRESS\b", (addr or "").upper()):
        seg = re.split(r"\b(?:UNIT|APT|APARTMENT|SUITE|STE|BUILDING|BLDG)\b|#|,", seg)[0].strip()
        m = re.match(r"(\d+)(?:\s*-\s*(\d+))?\s+(.*)", seg)
        if not m:
            continue
        nums = [n for n in (m.group(1), m.group(2)) if n]
        toks = [ABBR.get(t, t) for t in re.sub(r"[^A-Z0-9 ]", " ", m.group(3)).split()]
        out.append((nums, [ORD.get(t, t) for t in toks]))
    return out

def tok_match(a, b):
    return a == b or (len(a) >= 3 and len(b) >= 3 and (a.startswith(b) or b.startswith(a)))

def arcgis(params):
    p = {"f": "json", "outFields": "*", "outSR": 4326}
    p.update(params)
    last = None
    for url in PARCEL_URLS:
        text = ""
        try:
            r = requests.get(url, params=p, headers=HEADERS, timeout=25)
            text = r.text[:150].replace("\n", " ")
            j = r.json()
            if "error" in j:
                raise RuntimeError(str(j["error"])[:200])
            return j.get("features", [])
        except Exception as e:
            last = f"{type(e).__name__}: {e} | response: {text!r}"
            print(f"  parcel service failed ({url.split('/')[2]}): {last}", flush=True)
    raise RuntimeError(f"all parcel services failed: {last}")

def _first_num(f):
    m = re.match(r"\s*(\d+)", f["attributes"].get("PROP_LOC") or "")
    return m.group(1) if m else None

def best_parcel(feats, toks, upper_blob):
    if not feats:
        return None
    blob_key = mun_key(upper_blob)
    def score(f):
        a = f["attributes"]
        loc = norm(a.get("PROP_LOC") or "")
        s = sum(1 for t in toks[:3] if any(tok_match(t, x) for x in loc[1:]))
        mk = mun_key(a.get("MUN_NAME") or "")
        hit = bool(mk) and mk in blob_key
        return s + (3 if hit else 0) + (len(mk) / 100 if hit else 0), s, hit, mk
    ranked = sorted(feats, key=lambda f: score(f)[0], reverse=True)
    top = score(ranked[0])
    if len({score(f)[3] for f in ranked if score(f)[0] == top[0]}) > 1:
        return None                                  # same street in several towns, can't tell which
    if not (top[2] or (top[1] >= 2 and len({score(f)[3] for f in ranked}) == 1)):
        return None                                  # town doesn't match and street evidence is weak
    f = ranked[0]
    return {"attrs": f["attributes"], "rings": (f.get("geometry") or {}).get("rings")}

_geo_used = 0

def lookup_parcel(county, addr, blob, want_geometry=False, point=None):
    """Find the tax parcel for a listing. Returns {'attrs':..., 'rings':...} or None."""
    global _geo_used
    ub = (blob or "").upper()
    geom = "true" if want_geometry else "false"
    cty = county.upper().replace("'", "")
    for nums, toks in parse_address(addr):
        key = next((t for t in toks if t not in DIRS and len(t) > 1 and t != "ST"), toks[0] if toks else None)
        if not key:
            continue
        key = key.replace("'", "")
        where = f"COUNTY LIKE '{cty}%' AND PROP_LOC LIKE '{nums[0]}%' AND PROP_LOC LIKE '%{key}%'"
        feats = arcgis({"where": where, "returnGeometry": geom})
        if not feats:
            feats = arcgis({"where": where.replace("COUNTY", "UPPER(COUNTY)").replace("PROP_LOC", "UPPER(PROP_LOC)"),
                            "returnGeometry": geom})
        time.sleep(0.1)
        pick = best_parcel([f for f in feats if _first_num(f) in nums], toks, ub)
        if pick:
            return pick
    if point is None and addr and _geo_used < GEOCODE_CAP:     # last resort: geocode, then parcel under the point
        _geo_used += 1
        point = geocode(addr.split("A/K/A")[0].split("AKA")[0], "")
    if point:
        feats = arcgis({"geometry": f"{point[1]},{point[0]}", "geometryType": "esriGeometryPoint", "inSR": 4326,
                        "spatialRel": "esriSpatialRelIntersects", "returnGeometry": geom})
        if feats:
            return {"attrs": feats[0]["attributes"], "rings": (feats[0].get("geometry") or {}).get("rings")}
    return None

def geocode(address, city):
    full = f"{address}, {city}, NJ" if city else address
    try:
        r = requests.get("https://nominatim.openstreetmap.org/search",
                         params={"q": full, "format": "json", "limit": 1, "countrycodes": "us"},
                         headers=HEADERS, timeout=30).json()
        time.sleep(1.1)
        if r:
            return float(r[0]["lat"]), float(r[0]["lon"])
    except Exception as e:
        print(f"  nominatim failed: {e}", file=sys.stderr)
    try:
        r = requests.get("https://geocoding.geo.census.gov/geocoder/locations/onelineaddress",
                         params={"address": full, "benchmark": "Public_AR_Current", "format": "json"},
                         headers=HEADERS, timeout=30).json()
        m = r["result"]["addressMatches"]
        if m:
            return m[0]["coordinates"]["y"], m[0]["coordinates"]["x"]
    except Exception as e:
        print(f"  census geocoder failed: {e}", file=sys.stderr)
    return None

# ---------------- amounts, value estimate, exclusions ----------------
def money(text, labels):
    for lab in labels:
        m = re.search(lab + r"[^$\d:]{0,30}:?\s*\$?\s*([\d,]+(?:\.\d{1,2})?)", text, re.I)
        if m:
            try:
                return float(m.group(1).replace(",", ""))
            except ValueError:
                pass
    return None

def status_exclusion(text):
    """Reason string if the status history shows WRIT EXPIRED / Bankruptcy / Adjourned Plaintiff."""
    i = text.lower().find("status history")
    m = EXCLUDE_STATUS_RE.search(text[i:] if i >= 0 else text)
    return m.group(0).upper() if m else None

_ratios = None
CODE_COUNTY = {"01": "ATLANTIC", "02": "BERGEN", "03": "BURLINGTON", "04": "CAMDEN", "05": "CAPE MAY", "06": "CUMBERLAND",
               "07": "ESSEX", "08": "GLOUCESTER", "09": "HUDSON", "10": "HUNTERDON", "11": "MERCER", "12": "MIDDLESEX",
               "13": "MONMOUTH", "14": "MORRIS", "15": "OCEAN", "16": "PASSAIC", "17": "SALEM", "18": "SOMERSET",
               "19": "SUSSEX", "20": "UNION", "21": "WARREN"}
RATIO_ROW = re.compile(r"(?<!\d)(\d{2})(\d{2})\s+([A-Z][A-Z .'&-]*?)\**\s+(\d{1,3}\.\d{2})\s+(\d{1,3}\.\d{2})\s+(\d{1,3}\.\d{2})(?!\d)")

def parse_ratios(text):
    """Rows look like '2019 UNION TWP 8.89 7.56 10.22' (first two digits = county code)."""
    out = {}
    for m in RATIO_ROW.finditer(text):
        county = CODE_COUNTY.get(m.group(1))
        if county:
            out[(county, mun_key(m.group(3)))] = min(float(m.group(4)) / 100, 1.0)   # ratios over 100% count as 100%
    return out

def load_ratios():
    """NJ Chapter 123 average ratios (assessed / true value) by county + municipality."""
    global _ratios
    if _ratios is not None:
        return _ratios
    _ratios = {}
    try:
        import io
        from pypdf import PdfReader
        for yr in (now_utc().year + 1, now_utc().year, now_utc().year - 1):
            try:
                r = requests.get(RATIO_URL.format(yr), headers=HEADERS, timeout=60)
                if r.status_code != 200:
                    continue
                text = "\n".join((p.extract_text() or "") for p in PdfReader(io.BytesIO(r.content)).pages)
            except Exception:
                continue
            found = parse_ratios(text)
            if len(found) > 100:
                _ratios = found
                print(f"  loaded {len(found)} municipal ratios from the {yr} Chapter 123 table", flush=True)
                break
            print(f"  {yr} ratio table found but only {len(found)} rows parsed", flush=True)
    except Exception as e:
        print(f"  ratio table unavailable: {e}", flush=True)
    return _ratios

def find_ratio(ratios, county, mun_name):
    mk = mun_key(mun_name)
    if (county, mk) in ratios:
        return ratios[(county, mk)]
    import difflib
    keys = [k for (c, k) in ratios if c == county]
    close = difflib.get_close_matches(mk, keys, n=1, cutoff=0.85)      # e.g. HASBROUCK HEIGHTS vs HASBROUCK HGHTS
    return ratios[(county, close[0])] if close else None

def est_value(attrs, county):
    """(value, note) -- tax assessment divided by the state's average ratio for that town."""
    def num(k):
        try:
            return float(attrs.get(k) or 0)
        except (TypeError, ValueError):
            return 0.0
    assessed = (num("LAND_VAL") + num("IMPRVT_VAL") + num("IMPRV_VAL")) or num("NET_VALUE")
    if not assessed:
        return None, "no assessment on record"
    ratios = load_ratios()
    c = (attrs.get("COUNTY") or county).upper().replace("COUNTY", "").strip()
    r = find_ratio(ratios, c, attrs.get("MUN_NAME") or "")
    if not r:
        return None, f"no state ratio found for {attrs.get('MUN_NAME')}"
    return assessed / r, f"assessed ${assessed:,.0f} / {r * 100:.1f}% state ratio"

def is_ignored(l, ignore):
    blob = (l.get("address", "") + " " + l.get("link", "")).lower()
    return any(x in blob for x in ignore)

# ---------------- investment classification (from tax record) ----------------
def units_from_text(t):
    best = 0
    for m in re.finditer(r"\b(\d{1,3}|four|five|six|seven|eight|nine|ten)[\s-]*(?:units?|family|fam|apartments?|apts?)\b", t.lower()):
        best = max(best, NUM.get(m.group(1)) or int(m.group(1)))
    if re.search(r"\b4fam|\b4-fam", t.lower()):
        best = max(best, 4)
    return best

def classify_investment(l, county):
    """Returns (tags, details_text, verified). Stores the tax record in l['attrs']."""
    parcel = lookup_parcel(county, l.get("address", ""), l["text"])
    if not parcel:
        return [], "", False
    a = parcel["attrs"]
    l["attrs"] = a
    if not globals().get("_fields_logged"):
        globals()["_fields_logged"] = True
        print(f"  parcel fields: {sorted(a.keys())}", flush=True)
    cls = (a.get("PROP_CLASS") or "").strip().upper()
    desc = " ".join(str(a.get(k) or "") for k in ("BLDG_DESC", "LAND_DESC", "BLDG_CLASS", "FAC_NAME", "OWNER_NAME"))
    tags = []
    if cls == "4C":
        tags.append("APARTMENT 5+ units (tax class 4C)")
    elif cls == "4A":
        tags.append("COMMERCIAL (tax class 4A)")
    elif cls == "4B":
        tags.append("INDUSTRIAL (tax class 4B)")
    elif cls == "1":
        tags.append("VACANT LAND (tax class 1)")
    elif cls == "2":
        n = units_from_text(desc)          # tax record description; the sheriff description is checked in main()
        if n >= 4:
            tags.append(f"4+ UNIT residential ({n} units per tax record)")
    if cls in ("4A", "4B") and STORAGE_RE.search(desc + " " + l["text"]):
        tags.append("storage facility")
    if not tags and STORAGE_RE.search(desc):
        tags.append("storage facility (check classification)")
    details = (f"Tax record: class {cls} {CLASS_NAMES.get(cls, '')} | {a.get('PROP_LOC', '')}, {a.get('MUN_NAME', '')} | "
               f"owner {a.get('OWNER_NAME') or '?'} | bldg {a.get('BLDG_DESC', '')} | land {a.get('LAND_DESC', '')} | "
               f"{(a.get('CALC_ACRE') or 0):.2f} ac | built {a.get('YR_CONSTR') or '?'}")
    return tags, details, True

# ---------------- lake detection ----------------
_lake_cache = {}

def lake_segments(name):
    if name in _lake_cache:
        if _lake_cache[name] is None:
            raise RuntimeError(f"{name} shoreline unavailable (OpenStreetMap servers unreachable this run)")
        return _lake_cache[name]
    s, w, n, e = LAKES[name]["bbox"]
    q = (f'[out:json][timeout:90];(way["natural"="water"]["name"="{name}"]({s},{w},{n},{e});'
         f'relation["natural"="water"]["name"="{name}"]({s},{w},{n},{e}););out geom;')
    data, last = None, None
    for attempt in range(2):
        for url in OVERPASS_URLS:
            try:
                data = requests.post(url, data={"data": q}, headers=HEADERS, timeout=100).json()
                break
            except Exception as ex:
                last = ex
                print(f"  overpass {url.split('/')[2]} failed: {type(ex).__name__}", flush=True)
        if data is not None:
            break
        time.sleep(20)                       # servers are sometimes busy; wait and try the round again
    if data is None:
        _lake_cache[name] = None
        raise RuntimeError(f"{name} shoreline unavailable: {last}")
    rings = []
    for el in data.get("elements", []):
        if el["type"] == "way" and "geometry" in el:
            rings.append(el["geometry"])
        for m in el.get("members", []):
            if m.get("geometry"):
                rings.append(m["geometry"])
    segs = []
    for ring in rings:
        pts = [(p["lat"], p["lon"]) for p in ring]
        segs += list(zip(pts, pts[1:]))
    if not segs:
        _lake_cache[name] = None
        raise RuntimeError(f"{name} shoreline not found in OpenStreetMap")
    _lake_cache[name] = segs
    return segs

def _pt_seg(px, py, ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    L2 = dx * dx + dy * dy
    t = 0 if L2 == 0 else max(0, min(1, ((px - ax) * dx + (py - ay) * dy) / L2))
    return math.hypot(px - (ax + t * dx), py - (ay + t * dy))

def _inside(x, y, ring):
    ins = False
    for (x1, y1), (x2, y2) in zip(ring, ring[1:]):
        if (y1 > y) != (y2 > y) and x < (x2 - x1) * (y - y1) / (y2 - y1) + x1:
            ins = not ins
    return ins

def parcel_to_shore_m(rings, segs):
    """Min distance (m) between a parcel polygon (lon/lat rings) and the shoreline; 0 if they overlap."""
    lons = [p[0] for r in rings for p in r]
    lats = [p[1] for r in rings for p in r]
    lat0, lon0 = sum(lats) / len(lats), sum(lons) / len(lons)
    ky, kx = 110540.0, 111320.0 * math.cos(math.radians(lat0))
    pad = 0.004
    near = [(((a[1] - lon0) * kx, (a[0] - lat0) * ky), ((b[1] - lon0) * kx, (b[0] - lat0) * ky))
            for a, b in segs
            if min(lat for lat in (a[0], b[0])) <= max(lats) + pad and max(a[0], b[0]) >= min(lats) - pad
            and min(a[1], b[1]) <= max(lons) + pad and max(a[1], b[1]) >= min(lons) - pad]
    if not near:
        return float("inf")
    loc_rings = [[((x - lon0) * kx, (y - lat0) * ky) for x, y in r] for r in rings]
    for (a, _b) in near[::5]:          # shoreline inside parcel => overlap
        if any(_inside(a[0], a[1], r) for r in loc_rings):
            return 0.0
    best = float("inf")
    for r in loc_rings:
        for (x1, y1), (x2, y2) in zip(r, r[1:]):
            n = max(1, int(math.hypot(x2 - x1, y2 - y1) // 3))
            for i in range(n + 1):
                px, py = x1 + (x2 - x1) * i / n, y1 + (y2 - y1) * i / n
                for (a, b) in near:
                    d = _pt_seg(px, py, a[0], a[1], b[0], b[1])
                    if d < best:
                        best = d
    return best

def point_to_shore_m(lat, lon, segs):
    ky, kx = 110540.0, 111320.0 * math.cos(math.radians(lat))
    return min(_pt_seg(0, 0, (a[1] - lon) * kx, (a[0] - lat) * ky, (b[1] - lon) * kx, (b[0] - lat) * ky) for a, b in segs)

def classify_lake(l, county):
    """Returns (tags, extra, verified)."""
    blob = (l["text"] + " " + l.get("city", "")).lower()
    city = (l.get("city") or "").lower()
    tags, extra, verified = [], "", True
    for lake, cfg in LAKES.items():
        in_town = (city in cfg["towns"]) if city else any(t in blob for t in cfg["towns"])
        if not in_town and lake.split()[-1].lower() not in blob:
            continue
        segs = lake_segments(lake)
        pt = None
        parcel = lookup_parcel(county, l.get("address", ""), blob, want_geometry=True)
        if not parcel or not parcel.get("rings"):
            pt = geocode(l.get("address", ""), l.get("city") or "")
            if pt:
                parcel = lookup_parcel(county, "", blob, want_geometry=True, point=pt) or parcel
        if parcel and parcel.get("rings"):
            d = parcel_to_shore_m(parcel["rings"], segs)
            a = parcel["attrs"]
            l["attrs"] = a
            extra = f"Tax record: {a.get('PROP_LOC')}, {a.get('MUN_NAME')} | class {a.get('PROP_CLASS')} | owner {a.get('OWNER_NAME') or '?'}"
            if d <= LAKEFRONT_M:
                tags.append(f"LIKELY LAKEFRONT on {lake} (parcel ~{d:.0f} m from shoreline)")
            elif d <= NEAR_M:
                tags.append(f"Near {lake} (parcel ~{d:.0f} m from shoreline) - verify if lakefront")
            if tags:
                ring = parcel["rings"][0]
                l["map"] = f"https://www.google.com/maps/search/?api=1&query={ring[0][1]},{ring[0][0]}"
        elif pt:
            d = point_to_shore_m(pt[0], pt[1], segs)
            if d <= POINT_LAKEFRONT_M:
                tags.append(f"LIKELY LAKEFRONT on {lake} (~{d:.0f} m, address point only - no tax parcel found)")
            elif d <= POINT_NEAR_M:
                tags.append(f"Near {lake} (~{d:.0f} m, address point only) - verify")
            if tags:
                l["map"] = f"https://www.google.com/maps/search/?api=1&query={pt[0]},{pt[1]}"
        elif in_town:
            tags.append(f"{lake} town listing - address could not be located, check manually")
            verified = False
    return tags, extra, verified

# ---------------- scrapers ----------------
SESSIONS = {}          # county -> (requests.Session, search page url)
HOME_MARK = "click the link below to search that county"
_samples_logged = 0

def case_no(cells):
    for c in cells:
        c = c.strip()
        if re.fullmatch(r"[A-Za-z]{1,3}-?\d[\d-]{4,}", c):
            return c.upper()
    return None

def scrape_civilview(src, seen):
    sess = requests.Session()
    sess.headers.update(HEADERS)
    r = sess.get(src["url"], timeout=25)
    r.raise_for_status()
    SESSIONS[src["county"]] = (sess, src["url"])        # detail pages only open inside this session
    soup = BeautifulSoup(r.text, "html.parser")
    out = []
    for tr in soup.select("tr"):
        a = tr.find("a", href=re.compile("SaleDetails", re.I))
        if not a:
            continue
        link = urljoin(src["url"], a["href"])
        cells = [td.get_text(" ", strip=True) for td in tr.find_all("td")]
        row = " | ".join(c for c in cells if c and c.lower() != "view details")
        case = case_no(cells)
        address = cells[-1] if cells else ""
        # NOTE: PropertyId in the link changes whenever the sheriff republishes, so it cannot identify a listing.
        # The Sheriff # (case number) is stable.
        key = case or hashlib.sha1((address + row[:60]).encode()).hexdigest()[:12]
        out.append({"id": f"{src['county']}:{key}", "county": src["county"], "summary": row, "text": row,
                    "link": link, "address": address, "city": "", "needs_detail": True, "case": case})
    if not out:
        raise RuntimeError("no listings parsed (site layout changed, or list is empty/blocked)")
    counts = Counter(o["id"] for o in out)              # same case listed for two properties: tell them apart
    for o in out:
        if counts[o["id"]] > 1:
            o["id"] += ":" + hashlib.sha1(o["address"].encode()).hexdigest()[:6]
    return out

def ensure_detail(l):
    """Open the 'View Details' page (inside the county session). Sets l['detail_ok']."""
    global _samples_logged
    if not l.pop("needs_detail", False):
        l.setdefault("detail_ok", True)
        return
    sess, search_url = SESSIONS.get(l.get("county"), (None, None))
    html_text = None
    try:
        for attempt in range(2):
            r = (sess or requests).get(l["link"], headers={"Referer": search_url or ""}, timeout=25)
            if HOME_MARK not in r.text.lower():
                html_text = r.text
                break
            if sess:
                sess.get(search_url, timeout=25)        # session expired: re-open the county list, then retry
            time.sleep(1)
    except Exception as e:
        print(f"  detail fetch failed {l['link']}: {e}", flush=True)
    time.sleep(0.3)
    if html_text is None:
        l["detail_ok"] = False
        return
    text = BeautifulSoup(html_text, "html.parser").get_text(" ", strip=True)
    l["text"] += " " + text
    l["detail_ok"] = True
    if _samples_logged < 2:                              # lets us see the real page layout in the log
        _samples_logged += 1
        print(f"  detail page sample: {text[:900]!r}", flush=True)

def scrape_sussex(src, seen):
    soup = BeautifulSoup(get(src["url"]).text, "html.parser")
    out = []
    for table in soup.find_all("table"):
        rows = table.find_all("tr")
        if not rows:
            continue
        header = [c.get_text(" ", strip=True).lower() for c in rows[0].find_all(["th", "td"])]
        if "address" not in header or "city" not in header:
            continue
        ia, ic = header.index("address"), header.index("city")
        for tr in rows[1:]:
            cells = tr.find_all("td")
            if len(cells) <= max(ia, ic):
                continue
            vals = [c.get_text(" ", strip=True) for c in cells]
            a = tr.find("a", href=True)
            pdf = urljoin(src["url"], a["href"]) if a else ""
            out.append({"id": f"Sussex:{vals[0]}", "summary": " | ".join(v for v in vals if v)[:300],
                        "text": " ".join(vals), "link": pdf or src["url"], "pdf": pdf,
                        "address": vals[ia], "city": vals[ic]})
    if not out:
        raise RuntimeError("Sussex table not found (page may be JavaScript-rendered or layout changed)")
    return out

def scrape(src, seen):
    if not src["url"]:
        raise RuntimeError("source URL not configured")
    return scrape_civilview(src, seen) if src["type"] == "civilview" else scrape_sussex(src, seen)

# ---------------- email ----------------
def money_s(x):
    return f"${x:,.0f}" if x is not None else "n/a"

def links_for(it):
    q = quote(it.get("address") or "")
    return {"Zillow": f"https://www.zillow.com/homes/{q}_rb/",
            "Redfin": f"https://www.redfin.com/search?q={q}",
            "Google": f"https://www.google.com/search?q={q}+for+sale"}

def build_email(items, unverified_count, dash_url):
    plain, h = [f"{len(items)} new sheriff-sale propert{'y' if len(items) == 1 else 'ies'}:\n"], []
    h.append(f"<h3>{len(items)} new sheriff-sale propert{'y' if len(items) == 1 else 'ies'}</h3>")
    for it in items:
        amt = []
        if it.get("upset") is not None:
            amt.append(("Upset*", it["upset"]))
        if it.get("judgment") is not None:
            amt.append(("Judgment", it["judgment"]))
        plain += [f"[{it['county']}] {'; '.join(it['tags'])}", f"  {it['address']}"]
        plain.append("  " + "  |  ".join(f"{k.upper()}: {money_s(v)}" for k, v in amt) if amt else "  Upset/judgment: not found on listing")
        if it.get("est_value"):
            plain.append(f"  Est. value ~{money_s(it['est_value'])} ({it.get('value_note', '')})")
        else:
            plain.append(f"  Est. value: unavailable ({it.get('value_note', '')}) - $50k rule not applied")
        plain += [f"  {it['link']}", f"  {it['details']}" if it.get("details") else "", "  Check if under contract: " +
                  " | ".join(f"{k}: {v}" for k, v in links_for(it).items())]
        if it.get("map"):
            plain.append(f"  Map: {it['map']}")
        plain.append("")
        e = html.escape
        block = [f"<p><b>[{e(it['county'])}]</b> {e('; '.join(it['tags']))}<br>{e(it['address'])}<br>"]
        block.append(" &nbsp;|&nbsp; ".join(f"<b>{k}: {money_s(v)}</b>" for k, v in amt) if amt else "Upset/judgment: not found on listing")
        if it.get("est_value"):
            block.append(f"<br>Est. value ~{money_s(it['est_value'])} <small>({e(it.get('value_note', ''))})</small>")
        else:
            block.append(f"<br><i>Est. value unavailable ({e(it.get('value_note', ''))}) - $50k rule not applied</i>")
        block.append(f"<br><a href=\"{e(it['link'])}\">Sheriff listing</a>")
        block.append(" &middot; " + " &middot; ".join(f"<a href=\"{e(v)}\">{k}</a>" for k, v in links_for(it).items()) + " <small>(check if under contract)</small>")
        if it.get("map"):
            block.append(f" &middot; <a href=\"{e(it['map'])}\">Map</a>")
        if it.get("details"):
            block.append(f"<br><small>{e(it['details'])}</small>")
        block.append("</p>")
        h.append("".join(block))
    if unverified_count:
        note = f"{unverified_count} other new listing(s) could not be classified from tax records; see the dashboard (Unverified filter)."
        plain.append(note)
        h.append(f"<p><i>{html.escape(note)}</i></p>")
    if dash_url:
        plain.append(f"Dashboard: {dash_url}")
        h.append(f"<p><a href=\"{html.escape(dash_url)}\">Open dashboard</a></p>")
    return "\n".join(plain), "".join(h)

def send(subject, body, html_body=None):
    user = os.environ["GMAIL_USER"].strip()
    pw = re.sub(r"[^A-Za-z0-9]", "", os.environ["GMAIL_APP_PASSWORD"])   # drops spaces/hidden characters from copy-paste
    print(f"  email login: user has @={'@' in user}, password length={len(pw)} (should be 16)", flush=True)
    msg = EmailMessage()
    msg["From"], msg["To"], msg["Subject"] = user, os.environ["NOTIFY_TO"].strip(), subject
    msg.set_content(body)
    if html_body:
        msg.add_alternative(f"<html><body>{html_body}</body></html>", subtype="html")
    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465, timeout=30) as s:
            s.login(user, pw)
            s.send_message(msg)
    except (smtplib.SMTPServerDisconnected, OSError):
        with smtplib.SMTP("smtp.gmail.com", 587, timeout=30) as s:   # fallback route
            s.starttls()
            s.login(user, pw)
            s.send_message(msg)

def write_dashboard(data, errors, excluded):
    now = now_utc().isoformat(timespec="minutes")
    data["items"].sort(key=lambda i: i["first_seen"], reverse=True)
    data["last_run"], data["last_errors"], data["excluded_last_run"] = now, errors, dict(excluded)
    DATA_FILE.parent.mkdir(exist_ok=True)
    DATA_FILE.write_text(json.dumps(data, indent=1))

def hours_since(iso):
    try:
        return (now_utc() - datetime.datetime.fromisoformat(iso)).total_seconds() / 3600
    except Exception:
        return 1e9

def main():
    global DEADLINE
    if "--test-email" in sys.argv:
        send("Sheriff monitor: test email", "If you can read this, email alerts work.")
        print("Test email sent.", flush=True)
        return
    seen, meta, fresh = load_state()
    data = load_data(fresh)
    ignore = load_ignore()
    errors, excluded = [], Counter()
    have = {i["id"] for i in data["items"]}
    baseline = set(meta.get("baseline", []))
    deferred = 0
    looked_up = failed = 0
    for idx, src in enumerate(SOURCES):
        left = len(SOURCES) - idx
        DEADLINE = min(GLOBAL_DEADLINE, time.time() + max(0, GLOBAL_DEADLINE - time.time()) / left)   # fair share per county
        print(f"Checking {src['county']}...", flush=True)
        try:
            listings = scrape(src, seen)
        except Exception as e:
            errors.append(f"{src['county']}: {e}")
            continue
        baselined = set(meta.get("baselined", []))
        if src["county"] not in baselined:            # first time we see this county: everything listed now is "old"
            baseline.update(l["id"] for l in listings)
            meta["baselined"] = sorted(baselined | {src["county"]})
            meta["baseline"] = sorted(baseline)
        new = [l for l in listings if l["id"] not in seen]
        t0 = time.time()
        print(f"  {len(listings)} listings, {len(new)} new", flush=True)
        for n, l in enumerate(new, 1):
            if out_of_time():
                print("  time budget reached - remaining listings will be checked next run", flush=True)
                break
            try:
                if is_ignored(l, ignore):
                    excluded["on ignore list"] += 1
                    seen.add(l["id"])
                    continue
                verified, details = True, ""
                if src["rules"] == "investment":
                    looked_up += 1
                    tags, details, verified = classify_investment(l, src["county"])
                    if verified and not tags and (l["attrs"].get("PROP_CLASS") or "").strip().upper() == "2" \
                            and not re.search(r"\b(UNIT|APT|APARTMENT)\b|#", l.get("address", "").upper()):
                        ensure_detail(l)               # 4-family buildings are class 2: read the sheriff's description
                        if not l.get("detail_ok", True):
                            deferred += 1
                            continue
                        n_units = units_from_text(l["text"])
                        if n_units >= 4:
                            tags = [f"4+ UNIT residential ({n_units} units per sheriff description)"]
                    if not verified and re.search(r"\b(UNIT|APT|APARTMENT)\b|#", l.get("address", "").upper()):
                        excluded["single condo unit (no tax record)"] += 1
                        seen.add(l["id"])
                        continue
                    if not verified:
                        failed += 1
                        print(f"  no tax record: {l.get('address', '')}", flush=True)
                        tags = ["Type unknown - no tax record found (check manually)"]
                else:
                    ensure_detail(l)
                    tags, details, verified = classify_lake(l, src["county"])
                if not tags:
                    seen.add(l["id"])
                    continue
                ensure_detail(l)                       # need the status history and amounts for anything we might list
                if not l.get("detail_ok", True):
                    deferred += 1                      # could not open the details page: retry next run, never list blind
                    continue
                reason = status_exclusion(l["text"])
                if reason:
                    excluded[reason.title()] += 1
                    seen.add(l["id"])
                    continue
                upset = money(l["text"], [r"upset"])
                judgment = money(l["text"], [r"approx\.?\s*judgment", r"judgment"])
                value, vnote = (est_value(l["attrs"], src["county"]) if l.get("attrs") else (None, "no tax record"))
                if upset is None and judgment is None and l.get("case") is not None and _samples_logged < 4:
                    globals()["_samples_logged"] += 1
                    print(f"  amounts not found; page text: {l['text'][-700:]!r}", flush=True)
                if not value and globals().get("_value_logged", 0) < 3:
                    globals()["_value_logged"] = globals().get("_value_logged", 0) + 1
                    print(f"  value unavailable for {l.get('address', '')}: {vnote}", flush=True)
                compare = upset if upset is not None else judgment
                if verified and value and compare is not None and value - compare < MIN_DISCOUNT:
                    excluded[f"upset within ${MIN_DISCOUNT:,} of value"] += 1
                    seen.add(l["id"])
                    continue
                if l["id"] not in have:
                    data["items"].append({
                        "id": l["id"], "county": src["county"], "tags": tags, "address": l.get("address", ""),
                        "summary": l["summary"], "link": l["link"], "details": details or "", "map": l.get("map", ""),
                        "upset": upset, "judgment": judgment, "est_value": value, "value_note": vnote,
                        "first_seen": now_utc().isoformat(timespec="minutes"), "emailed": l["id"] in baseline,
                        "verified": verified, "notified_unverified": l["id"] in baseline})
                seen.add(l["id"])
            except Exception as e:
                errors.append(f"{src['county']} {l.get('address', '')}: {e}")
                continue          # not marked seen -> retried next run
            if n % 25 == 0:
                print(f"  ...{n}/{len(new)} done", flush=True)
        print(f"  finished in {time.time() - t0:.0f}s", flush=True)
        save_state(seen, meta)

    if deferred:
        errors.append(f"Could not open the details page for {deferred} listing(s); they will be retried next run")
    if looked_up and failed / looked_up > 0.6:
        errors.append(f"Tax-record lookup failed for {failed} of {looked_up} new listings (address format or GIS service problem)")
    if len(errors) > 10:
        errors = errors[:10] + [f"...and {len(errors) - 10} more"]

    write_dashboard(data, errors, excluded)
    save_state(seen, meta)
    print(f"excluded={dict(excluded)} errors={errors}", flush=True)

    # ---- email rules: only new qualifying properties, at most about once a day ----
    pending = [i for i in data["items"] if i.get("verified") and not i.get("emailed", True)]
    unv = [i for i in data["items"] if not i.get("verified", True) and not i.get("notified_unverified", True)]
    repo = os.getenv("GITHUB_REPOSITORY", "")
    dash_url = f"https://{repo.split('/')[0]}.github.io/{repo.split('/')[1]}/" if "/" in repo else ""
    failed_send = False
    try:
        if pending and hours_since(meta.get("last_email", "")) >= EMAIL_MIN_HOURS:
            plain, html_body = build_email(pending, len(unv), dash_url)
            send(f"Sheriff Sales: {len(pending)} new propert{'y' if len(pending) == 1 else 'ies'}", plain, html_body)
            for i in pending:
                i["emailed"] = True
            for i in unv:
                i["notified_unverified"] = True
            meta["last_email"] = now_utc().isoformat(timespec="minutes")
            print(f"Email sent with {len(pending)} propert(ies).", flush=True)
        elif pending:
            print(f"{len(pending)} new propert(ies) waiting; last email was < {EMAIL_MIN_HOURS}h ago.", flush=True)
    except Exception as e:
        failed_send = True
        print(f"EMAIL FAILED: {type(e).__name__}: {e}", flush=True)
        print("Check GMAIL_USER (full address) / GMAIL_APP_PASSWORD / NOTIFY_TO secrets.", flush=True)
    write_dashboard(data, errors, excluded)
    save_state(seen, meta)
    if failed_send:
        sys.exit(1)

if __name__ == "__main__":
    main()
