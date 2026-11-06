#!/usr/bin/env python3
"""NJ sheriff-sale monitor: emails NEW listings that match your criteria.

The sheriff sites only publish an address, so every candidate is looked up in the NJ statewide
tax-parcel layer (NJOGIS / MOD-IV) to learn what it really is.

  1. Essex, Bergen, Passaic, Hudson, Union:
       tax class 4C apartments (5+ units), residential parcels that look like 4+ units, 4A commercial
       (incl. storage facilities), 4B industrial, class 1 vacant land
  2. Morris, Sussex: lakefront on Lake Mohawk or Lake Hopatcong
       (parcel boundary vs. the lake shoreline from OpenStreetMap)

Env vars (set as GitHub secrets): GMAIL_USER, GMAIL_APP_PASSWORD, NOTIFY_TO
"""
import datetime, json, math, os, re, smtplib, sys, time
from email.message import EmailMessage
from pathlib import Path
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup

STATE_FILE = Path(__file__).with_name("seen.json")
DATA_FILE = Path(__file__).with_name("docs") / "data.json"   # feeds the dashboard (docs/index.html)
CIVIL = "https://salesweb.civilview.com/Sales/SalesSearch?countyId={}"
PARCELS = "https://maps.nj.gov/arcgis/rest/services/Framework/Cadastral/MapServer/0/query"
OVERPASS = "https://overpass-api.de/api/interpreter"
DEADLINE = time.time() + float(os.getenv("TIME_BUDGET_MIN", "30")) * 60   # stop cleanly, save progress, resume next run
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

# Lakes to watch and the municipalities that touch them
LAKES = {
    "Lake Mohawk":    {"towns": ["sparta"]},
    "Lake Hopatcong": {"towns": ["hopatcong", "byram", "jefferson", "mount arlington", "mt arlington",
                                 "mt. arlington", "roxbury", "landing"]},
}
LAKEFRONT_M = 20   # parcel boundary within this many meters of the shoreline -> lakefront
NEAR_M = 60        # within this -> "near the lake, verify"
POINT_LAKEFRONT_M, POINT_NEAR_M = 40, 120   # looser limits when only a geocoded point is available

CLASS_NAMES = {"1": "Vacant land", "2": "Residential (1-4 family)", "3A": "Farm (regular)", "3B": "Farm (qualified)",
               "4A": "Commercial", "4B": "Industrial", "4C": "Apartment (5+ units)"}
NUM = {"four": 4, "five": 5, "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10}
ABBR = {"STREET": "ST", "AVENUE": "AVE", "ROAD": "RD", "DRIVE": "DR", "BOULEVARD": "BLVD", "LANE": "LN",
        "PLACE": "PL", "COURT": "CT", "TERRACE": "TER", "TRAIL": "TRL", "PARKWAY": "PKWY", "HIGHWAY": "HWY",
        "TURNPIKE": "TPKE", "CIRCLE": "CIR", "NORTH": "N", "SOUTH": "S", "EAST": "E", "WEST": "W",
        "MOUNT": "MT", "SAINT": "ST"}
STORAGE_RE = re.compile(r"self[\s-]?storage|mini[\s-]?storage|storage\s+(?:facilit|unit|building|center|warehouse|co\b|corp|llc|inc)|\bstorage\b", re.I)

def out_of_time():
    return time.time() > DEADLINE

def get(url, **kw):
    r = requests.get(url, headers=HEADERS, timeout=25, **kw)
    r.raise_for_status()
    return r

# ---------------- address parsing / parcel lookup ----------------
def norm(s):
    toks = re.sub(r"[^A-Z0-9 ]", " ", s.upper()).split()
    return [ABBR.get(t, t) for t in toks]

def parse_address(addr):
    """-> (house number, street tokens). Handles '12 Main Street, Newark, NJ 07102' and 'Unit/Apt' suffixes."""
    street = addr.split(",")[0]
    street = re.split(r"\b(?:UNIT|APT|APARTMENT|SUITE|STE|#)\b", street, flags=re.I)[0]
    toks = norm(street)
    if not toks:
        return None, []
    m = re.match(r"(\d+)", toks[0])
    if not m:
        return None, toks
    return m.group(1), toks[1:]

def tok_match(a, b):
    return a == b or (len(a) >= 3 and len(b) >= 3 and (a.startswith(b) or b.startswith(a)))

def arcgis(params):
    p = {"f": "json", "outFields": "*", "outSR": 4326}
    p.update(params)
    r = requests.get(PARCELS, params=p, headers=HEADERS, timeout=30)
    r.raise_for_status()
    j = r.json()
    if "error" in j:
        raise RuntimeError(j["error"])
    return j.get("features", [])

def lookup_parcel(county, addr, blob, want_geometry=False, point=None):
    """Find the tax parcel for a listing. Returns {'attrs':..., 'rings':...} or None."""
    house, street = parse_address(addr or "")
    feats = []
    if house and street:
        w = (f"UPPER(COUNTY) LIKE '{county.upper()}%' AND UPPER(PROP_LOC) LIKE "
             f"'{house} {street[0].replace(chr(39), '')}%'")
        feats = arcgis({"where": w, "returnGeometry": "true" if want_geometry else "false"})
        time.sleep(0.3)
    if feats:
        upper_blob = blob.upper()
        def score(f):
            loc = norm(f["attributes"].get("PROP_LOC") or "")
            s = sum(1 for t in street if any(tok_match(t, x) for x in loc[1:]))
            mun = (f["attributes"].get("MUN_NAME") or "").upper()
            mun_core = re.sub(r"\b(TOWNSHIP|TWP|BOROUGH|CITY|TOWN|VILLAGE)\b", "", mun).strip()
            return s + (3 if mun_core and mun_core in upper_blob else 0)
        feats.sort(key=score, reverse=True)
        muns = {f["attributes"].get("MUN_NAME") for f in feats}
        best = feats[0]
        if len(muns) == 1 or score(best) > score(feats[1] if len(feats) > 1 else best) or len(feats) == 1:
            return {"attrs": best["attributes"], "rings": (best.get("geometry") or {}).get("rings")}
    if point:  # fallback: parcel containing the geocoded point
        feats = arcgis({"geometry": f"{point[1]},{point[0]}", "geometryType": "esriGeometryPoint", "inSR": 4326,
                        "spatialRel": "esriSpatialRelIntersects", "returnGeometry": "true" if want_geometry else "false"})
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

# ---------------- investment classification (from tax record) ----------------
def units_from_text(t):
    best = 0
    for m in re.finditer(r"\b(\d{1,3}|four|five|six|seven|eight|nine|ten)[\s-]*(?:units?|family|fam|apartments?|apts?)\b", t.lower()):
        best = max(best, NUM.get(m.group(1)) or int(m.group(1)))
    if re.search(r"\b4fam|\b4-fam", t.lower()):
        best = max(best, 4)
    return best

def classify_investment(l, county):
    """Returns (tags, details_text, verified)."""
    parcel = lookup_parcel(county, l.get("address", ""), l["text"])
    if not parcel:
        return [], "", False
    a = parcel["attrs"]
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
        n = max(units_from_text(desc), units_from_text(l["text"]))
        dw = a.get("DWELL") or 0
        if n >= 4:
            tags.append(f"4+ UNIT residential ({n} units per record/description)")
        elif isinstance(dw, (int, float)) and dw >= 4:
            tags.append(f"POSSIBLE 4+ unit residential (tax record dwelling count {dw} - verify)")
    if cls in ("4A", "4B", "2") and STORAGE_RE.search(desc + " " + l["text"]) and cls != "2":
        tags.append("storage facility")
    if not tags and STORAGE_RE.search(desc):
        tags.append("storage facility (check classification)")
    details = (f"Tax record: class {cls} {CLASS_NAMES.get(cls, '')} | {a.get('PROP_LOC', '')}, {a.get('MUN_NAME', '')} | "
               f"owner {a.get('OWNER_NAME', '')} | bldg {a.get('BLDG_DESC', '')} | land {a.get('LAND_DESC', '')} | "
               f"{(a.get('CALC_ACRE') or 0):.2f} ac | built {a.get('YR_CONSTR') or '?'} | assessed ${a.get('NET_VALUE') or 0:,}")
    return tags, details, True

# ---------------- lake detection ----------------
_lake_cache = {}

def lake_segments(name):
    if name in _lake_cache:
        return _lake_cache[name]
    q = (f'[out:json][timeout:90];(way["natural"="water"]["name"="{name}"];'
         f'relation["natural"="water"]["name"="{name}"];);out geom;')
    data = requests.post(OVERPASS, data={"data": q}, headers=HEADERS, timeout=120).json()
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
    blob = (l["text"] + " " + l.get("city", "")).lower()
    city = (l.get("city") or "").lower()
    tags, extra = [], ""
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
            extra = f"Tax record: {a.get('PROP_LOC')}, {a.get('MUN_NAME')} | class {a.get('PROP_CLASS')} | owner {a.get('OWNER_NAME') or '?'} | assessed ${a.get('NET_VALUE') or 0:,}"
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
    return tags, extra

# ---------------- scrapers ----------------
def scrape_civilview(src, seen):
    soup = BeautifulSoup(get(src["url"]).text, "html.parser")
    out = []
    for table in soup.find_all("table"):
        head = [c.get_text(" ", strip=True).lower() for c in (table.find("tr") or table).find_all(["th", "td"])]
        ia = next((i for i, h in enumerate(head) if "address" in h), -1)
        for tr in table.find_all("tr"):
            a = tr.find("a", href=re.compile("SaleDetails", re.I))
            if not a:
                continue
            link = urljoin(src["url"], a["href"])
            lid = f"{src['county']}:{link}"
            cells = [td.get_text(" ", strip=True) for td in tr.find_all("td")]
            row = " | ".join(cells)
            entry = {"id": lid, "summary": row, "text": row, "link": link,
                     "address": cells[ia] if 0 <= ia < len(cells) else (cells[-1] if cells else ""), "city": ""}
            entry["needs_detail"] = True
            out.append(entry)
    if not out:
        raise RuntimeError("no listings parsed (site layout changed, or list is empty/blocked)")
    return out

def ensure_detail(l):
    """Fetch the CivilView detail page only for listings we are about to classify."""
    if l.pop("needs_detail", False):
        try:
            l["text"] += " " + BeautifulSoup(get(l["link"]).text, "html.parser").get_text(" ", strip=True)
        except Exception as e:
            print(f"  detail fetch failed {l['link']}: {e}", flush=True)
        time.sleep(0.5)

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
def send(subject, body):
    user, pw = os.environ["GMAIL_USER"], os.environ["GMAIL_APP_PASSWORD"]
    msg = EmailMessage()
    msg["From"], msg["To"], msg["Subject"] = user, os.environ["NOTIFY_TO"], subject
    msg.set_content(body)
    with smtplib.SMTP_SSL("smtp.gmail.com", 465) as s:
        s.login(user, pw)
        s.send_message(msg)

def write_dashboard(matches, unverified, errors):
    """Append this run's matches to docs/data.json, which the dashboard page reads."""
    now = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="minutes")
    try:
        data = json.loads(DATA_FILE.read_text())
    except Exception:
        data = {"items": []}
    have = {i["id"] for i in data["items"]}
    for county, tags, l in matches:
        if l["id"] in have:
            continue
        data["items"].append({"id": l["id"], "county": county, "tags": tags, "summary": l["summary"],
                              "link": l["link"], "details": l.get("details", ""), "map": l.get("map", ""),
                              "address": l.get("address", ""), "first_seen": now, "verified": True})
    for county, l in unverified:
        if l["id"] not in have:
            data["items"].append({"id": l["id"], "county": county, "tags": ["No tax record found - check manually"],
                                  "summary": l["summary"], "link": l["link"], "details": "", "map": "",
                                  "address": l.get("address", ""), "first_seen": now, "verified": False})
    data["items"].sort(key=lambda i: i["first_seen"], reverse=True)
    data["last_run"] = now
    data["last_errors"] = errors
    DATA_FILE.parent.mkdir(exist_ok=True)
    DATA_FILE.write_text(json.dumps(data, indent=1))

def main():
    seen = set(json.loads(STATE_FILE.read_text())["seen"]) if STATE_FILE.exists() else set()
    first_run = not STATE_FILE.exists()
    matches, unverified, errors = [], [], []
    looked_up = failed = 0
    for src in SOURCES:
        print(f"Checking {src['county']}...", flush=True)
        try:
            listings = scrape(src, seen)
        except Exception as e:
            errors.append(f"{src['county']}: {e}")
            continue
        new = [l for l in listings if l["id"] not in seen]
        print(f"  {len(listings)} listings, {len(new)} new", flush=True)
        for n, l in enumerate(new, 1):
            if out_of_time():
                print("  time budget reached - remaining listings will be checked next run", flush=True)
                break
            try:
                ensure_detail(l)
                if src["rules"] == "investment":
                    looked_up += 1
                    tags, details, ok = classify_investment(l, src["county"])
                    if not ok:
                        failed += 1
                        unverified.append((src["county"], l))
                else:
                    tags, details = classify_lake(l, src["county"])
            except Exception as e:
                errors.append(f"{src['county']} {l.get('address', '')}: {e}")
                continue          # not marked seen -> retried next run
            l["details"] = details
            if tags:
                matches.append((src["county"], tags, l))
            seen.add(l["id"])
            if n % 25 == 0:
                print(f"  ...{n}/{len(new)} done", flush=True)
        STATE_FILE.write_text(json.dumps({"seen": sorted(seen)}, indent=1))

    # if most tax lookups failed, the lookup itself is broken: report that instead of flooding you
    if looked_up and failed / looked_up > 0.4:
        errors.append(f"Tax-record lookup failed for {failed} of {looked_up} new listings (address format or state GIS service problem)")
        for _c, _l in unverified:
            seen.discard(_l["id"])      # retry these next run
        unverified = []

    if len(errors) > 10:
        errors = errors[:10] + [f"...and {len(errors) - 10} more"]
    if matches or unverified:
        lines = []
        if matches:
            lines.append(f"{len(matches)} new sheriff-sale match(es):\n")
            for county, tags, l in matches:
                lines += [f"[{county}] {'; '.join(tags)}", f"  {l['summary']}", f"  {l['link']}"]
                if l.get("details"):
                    lines.append(f"  {l['details']}")
                if l.get("map"):
                    lines.append(f"  Map (switch to satellite): {l['map']}")
                lines.append("")
        if unverified:
            lines.append("Could not find a tax record for these (check manually):")
            lines += [f"  [{c}] {l['address']}  {l['link']}" for c, l in unverified]
            lines.append("")
        if errors:
            lines += ["Problems this run:"] + errors
        send(f"Sheriff Sale Alert: {len(matches)} match(es)" + (f", {len(unverified)} unverified" if unverified else ""),
             "\n".join(lines))
    elif errors and not first_run:
        key = "errors:" + "|".join(errors)
        if key not in seen:
            send("Sheriff monitor: problem", "\n".join(errors))
            seen.add(key)

    write_dashboard(matches, unverified, errors)
    STATE_FILE.write_text(json.dumps({"seen": sorted(seen)}, indent=1))
    print(f"matches={len(matches)} unverified={len(unverified)} errors={errors}")

if __name__ == "__main__":
    main()
