#!/usr/bin/env python3
"""
youthwater_tender_scanner.py

Youth Water (Y.H2O) Tender Intelligence Scanner
Aptiv Consulting -- built for Youth Water (bottled water / hospitality supplier)

Scans the South African national eTenders portal for open tenders matching Youth
Water's service offering (bottled water supply, catering, hospitality, events),
scores them for strategic fit, and emails an HTML digest of Strong/Possible matches.

Architecture mirrors Aptiv's own aptiv_tender_scanner.py:
- JSON API only, no HTML scraping / bs4
- MD5-hash dedupe cache (id|title|number) committed back to the repo each run
- SMTP over SSL (port 465), not STARTTLS
- Runs 3x/day via GitHub Actions cron

CHANGE LOG
----------
2026-07-15 v1.0 Initial build for Youth Water. Forked from Aptiv's scanner
                architecture. Category allowlist rebuilt from scratch (does NOT
                reuse Aptiv's professional-services allowlist -- see section 5
                of the build spec). Score weights reweighted 35/25/20/20 (vs
                Aptiv's 40/30/20/10) per Neal's call: B-BBEE/youth-ownership is
                Youth Water's primary competitive edge, not a secondary bonus.
                Feasibility rebuilt as a multi-province coverage model (Western
                Cape / Eastern Cape / Gauteng) instead of Aptiv's single
                HOME_PROVINCE model, since Youth Water delivers physical goods
                across three provinces with no single stated HQ.
2026-07-16 v1.1 Fix: fetch_tenders() was issuing a single API call capped at
                length=300 with no pagination loop, silently dropping every
                tender past the first page. Verified live on 2026-07-16 against
                Aptiv's own scanner run in the same window: the portal returned
                1,865 total advertised tenders, of which Youth Water's scanner
                was only ever seeing the first 300 (~16%). Replaced with the
                same paginated fetch loop Aptiv's scanner uses (500-record
                pages, looping until recordsTotal is exhausted), so the two
                scanners now have identical fetch coverage of the portal --
                only scoring/category logic differs, per the 2026-07-15 design
                decision above. No other behavior changed.
2026-07-25 v1.2 Tightened scope per Neal's diagnosis: the scanner was surfacing
                municipal/rural bulk-water and pipeline-style water
                infrastructure tenders instead of genuine event bottled/tanker
                water work -- i.e. right commodity (water), wrong tender type.
                Added (a) a set of unambiguous water-infrastructure/civil-works
                terms to the existing hard EXCLUSIONS list (pipeline, water
                infrastructure, reticulation, water supply scheme, drought
                relief, communal standpipe, yard connection, rehabilitation/
                refurbishment of water) -- these never describe an events
                contract, so a blanket exclusion is safe; and (b) a new
                context-aware exclusion, is_bulk_infrastructure(), for the
                genuinely ambiguous terms ("water tanker", "bulk water
                supply", "potable water supply", "water carting") that
                describe BOTH large-event tanker delivery AND municipal
                drought-relief/rural household water-carting -- this only
                excludes when that language co-occurs with a municipal/
                rural-scale signal (ward, village, household, municipality,
                informal settlement, etc.), so a genuine event/festival/
                wedding/conference water-tanker tender still passes untouched.
                No change to the category allowlist, service-match keyword
                corpus, or scoring weights -- this is an additive exclusion
                gate only, applied before scoring.

OPEN ITEMS (see build spec section 10 -- confirm before treating output as final):
- Youth Water's physical base/warehouse location is not stated in the source
docs; FEASIBILITY_PROVINCE_POINTS below treats all three coverage provinces
equally rather than weighting Western Cape higher for track record.
- Category allowlist (section 5) is built from the live eTenders Advanced
Search filter list as of 2026-07-15 -- re-verify periodically, categories on
government portals do get renamed/added.
- MUNICIPAL_SCALE_SIGNALS (added 2026-07-25) is a first pass at "this reads as
municipal/rural scale" -- monitor the next few digests for false
exclusions (a genuine large event tender that happens to mention a
municipality by name as the venue location) and false admits (municipal
tenders that don't use any of these exact words) and refine the list.
"""

import hashlib
import json
import logging
import os
import re
import smtplib
import ssl
import sys
import time
from datetime import datetime, timedelta
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from urllib.parse import quote

import requests

# ---------------------------------------------------------------------------
# CONFIG
# ---------------------------------------------------------------------------

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)],
)
log = logging.getLogger("youthwater_tender_scanner")

TENDER_API_URL = "https://www.etenders.gov.za/Home/PaginatedTenderOpportunities"
TENDER_PORTAL_URL = "https://www.etenders.gov.za/Home/opportunities?id=1"
DOWNLOAD_BASE_URL = "https://www.etenders.gov.za/home/Download/"

SEEN_CACHE_FILE = "seen_tenders.json"
CACHE_RETENTION_DAYS = 30

GMAIL_ADDRESS = os.environ.get("GMAIL_ADDRESS", "")
GMAIL_APP_PASSWORD = os.environ.get("GMAIL_APP_PASSWORD", "").replace(" ", "")

RECIPIENTS = [
    "nealtitus4823@gmail.com",
    "keisha.ash@krosworx.co.za",
    "liam.dalton@inkrow.co.za",
    "keisha@youthwater.co.za",
    "oliver.bailey@krosworx.co.za",
    "prayleen.bailey1@gmail.com",
]

# --- Scoring thresholds & weights -------------------------------------------
# Reweighted from Aptiv's 40/30/20/10 per Neal's decision (2026-07-15): B-BBEE
# Level 1 + 100% Youth Black Female ownership is Youth Water's primary pitch in
# public procurement, not an incidental bonus -- Consortium Advantage carries
# more weight here than it does in Aptiv's own scanner.
THRESHOLD_STRONG = 55
THRESHOLD_POSSIBLE = 25

SCORE_WEIGHTS = {
    "service_match": 35,
    "strategic_fit": 25,
    "feasibility": 20,
    "consortium_advantage": 20,
}

# --- Category hard filter ----------------------------------------------------
# Pulled directly from the live eTenders Advanced Search category filter list
# (fetched 2026-07-15). Deliberately NOT a copy of Aptiv's allowlist -- Aptiv's
# EXCLUSIONS list excludes catering/water/general-supplies categories on
# purpose (irrelevant to a professional-services firm); those are exactly
# Youth Water's core categories, so this is a fresh allowlist built for a
# bottled-water/hospitality goods supplier.
CATEGORY_ALLOWLIST = {
    "Food and beverage service activities",
    "Supplies: General",
    "Supplies: Perishable Provisions",
    "Accommodation",
    "Travel agency, tour operator, reservation service and related activities",
    "Arts, entertainment and recreation",
    "Creative, arts and entertainment activities",
}

# Safety net: even if a tender's category isn't in the allowlist above (portal
# miscategorisation happens -- e.g. a catering RFQ filed under "Services:
# General"), still pull it in if the description hits one of these anchors.
SERVICE_MATCH_OVERRIDE_KEYWORDS = [
    "bottled water",
    "drinking water supply",
    "catering services",
    "hospitality supplier",
]

# --- Keyword corpus -----------------------------------------------------------
# Rescaled from the draft corpus (originally built against a 40pt Service Match
# ceiling) to the new 35pt ceiling: multiplier 35/40 = 0.875, rounded, capped at 35.
SERVICE_MATCH_KEYWORDS = {
    # Anchor keywords -- near-instant full Service Match score
    "bottled water": 35,
    "drinking water supply": 35,
    "supply and delivery of water": 35,
    # Strong, close-to-core
    "still water": 31,
    "sparkling water": 31,
    "catering services": 26,
    "beverage supply": 26,
    "hospitality supplier": 26,
    # Adjacent / partial credit
    "event water supply": 19,
    "conference refreshments": 18,
    "food and beverage": 16,
    "consumables supply": 13,
    "guest amenities": 13,
    "hospitality services": 13,
    # Events-context adjacency (from EXTRA_KEYWORDS in the build spec) --
    # weaker signal on their own, but stack with anchors on real tenders
    "conference": 7,
    "corporate event": 7,
    "gala dinner": 7,
    "golf day": 7,
    "wedding": 6,
    "festival": 6,
    "wine estate": 6,
    "boardroom": 5,
    "guest rooms": 5,
    "hotel supplies": 7,
    "function catering": 8,
}

# Each match adds STRATEGIC_FIT_POINTS_PER_MATCH, capped at the category weight
# (25). 3+ matches maxes it out -- these tenders are usually explicit about
# preferential-procurement / SMME set-aside language when it applies at all.
STRATEGIC_FIT_KEYWORDS = [
    "youth empowerment",
    "youth development",
    "enterprise development",
    "sme support",
    "b-bbee",
    "preferential procurement",
    "socio-economic development",
    "women-owned",
    "black-owned",
    "designated group",
    "skills development",
    "eco-friendly packaging",
    "sustainability",
    "recyclable packaging",
    "green procurement",
]
STRATEGIC_FIT_POINTS_PER_MATCH = 9

# --- Feasibility: multi-province coverage model (Section K: INFERRED) -------
# Aptiv's scanner uses a single HOME_PROVINCE model (Gauteng) because it
# delivers remotely. Youth Water delivers physical goods across four cities in
# three provinces with no stated single HQ, so feasibility here is scored by
# whether the tender's province falls in Youth Water's coverage footprint --
# NOT weighted toward Western Cape's stronger track record (Franschhoek,
# Stellenbosch) over Gauteng's, pending Neal's confirmation of a physical
# base/warehouse. Revisit this if that changes.
COVERAGE_PROVINCES = {"Western Cape", "Eastern Cape", "Gauteng"}

FEASIBILITY_PROVINCE_POINTS = {
    "covered": 10,
    "other": 5,
    "unknown": 3,
}
FEASIBILITY_TIMELINE_POINTS = {"tight": 4, "moderate": 7, "ample": 10}
FEASIBILITY_TIMELINE_TIGHT_DAYS = 7
FEASIBILITY_TIMELINE_MODERATE_DAYS = 21

# --- Consortium / B-BBEE signal -----------------------------------------------
CONSORTIUM_SIGNALS = [
    "bbbee",
    "b-bbee",
    "bee",
    "sme",
    "small business",
    "joint venture",
    "consortium",
    "designated group",
    "youth",
    "women-owned",
]
CONSORTIUM_POINTS_PER_MATCH = 7

# --- Hard exclusions (keyword-level, applied regardless of category) --------
EXCLUSIONS = [
    "construction",
    "civil works",
    "road construction",
    "building renovation",
    "software development",
    "information technology",
    "network infrastructure",
    "cybersecurity",
    "legal services",
    "auditing services",
    "engineering consulting",
    "electrical installation",
    "security guarding",
    "fleet management",
    "recruitment services",
    "water treatment",
    "sanitation",
    "borehole",
    "waste management",
    "refuse",
    "paving",
    "fencing",
    "landscaping",
    # --- 2026-07-25 addition (v1.2) ------------------------------------------
    # Unambiguous water-infrastructure/civil-works terms. These never describe
    # an events bottled/tanker-water contract, so a blanket exclusion is safe
    # here -- unlike the tanker/bulk-water terms below, which need context
    # (see BULK_WATER_SIGNALS / is_bulk_infrastructure()).
    "pipeline",
    "water infrastructure",
    "reticulation",
    "rehabilitation of water",
    "refurbishment of water",
    "water supply scheme",
    "drought relief",
    "communal standpipe",
    "yard connection",
]

# --- Context-aware exclusion: municipal/rural bulk & tanker water -----------
# "water tanker(s)" / "bulk water supply" / "potable water supply" language
# legitimately describes BOTH (a) a large open-air event needing tanker-
# delivered water, and (b) a municipal drought-relief or rural household
# water-carting contract -- eTenders' one-line descriptions read almost
# identically for either. A blanket keyword exclusion would also kill genuine
# event-tanker tenders (exactly the kind Youth Water wants). So this only
# fires when bulk/tanker language co-occurs with a municipal/rural-scale
# signal; a standalone "water tanker" next to "conference"/"wedding"/
# "festival"/etc. still passes through normally. Added 2026-07-25 (v1.2) per
# Neal's diagnosis: scanner was pulling in municipal/pipeline-style water
# tenders instead of event bottled/tanker water.
BULK_WATER_SIGNALS = [
    "water tanker",
    "water tankers",
    "water tankering",
    "bulk water supply",
    "bulk water",
    "potable water supply",
    "water carting",
]

MUNICIPAL_SCALE_SIGNALS = [
    "ward",
    "village",
    "villages",
    "rural",
    "household",
    "households",
    "informal settlement",
    "municipality",
    "municipal",
    "community water",
    "district municipality",
    "local municipality",
]

# ---------------------------------------------------------------------------
# FETCH
# ---------------------------------------------------------------------------

def fetch_tenders():
    """Pull ALL currently-advertised tenders from the eTenders JSON API.

    v1.1 fix: paginates in batches of 500 until the portal's own recordsTotal
    is exhausted -- mirrors Aptiv's fetch_all_tenders() exactly. The original
    v1.0 version issued a single request with length=300 and no loop, which
    silently truncated results to the first 300 records returned by the
    portal (verified live on 2026-07-16: the portal had 1,865 total
    advertised tenders at the time, so v1.0 was only ever seeing ~16% of the
    open tenders on any given run).
    """
    log.info("Fetching tenders from eTenders API...")
    session = requests.Session()
    all_tenders = []
    page_size = 500
    start = 0
    draw = 1

    while True:
        params = {
            "draw": draw,
            "start": start,
            "length": page_size,
            "search[value]": "",
            "search[regex]": "false",
            "order[0][column]": 4,  # date_Published
            "order[0][dir]": "desc",
            "status": 1,  # Advertised/Open
            "_": int(time.time() * 1000),
        }
        try:
            resp = session.get(TENDER_API_URL, params=params, timeout=45)
            resp.raise_for_status()
            payload = resp.json()
        except Exception as e:
            log.warning(f"Fetch error at start={start}: {e}")
            break

        records = payload.get("data", [])
        total = payload.get("recordsTotal", 0)
        all_tenders.extend(records)

        if start + page_size >= total:
            break
        start += page_size
        draw += 1
        time.sleep(0.5)

    # Client-side sort as a safety net -- resilient to DataTables column-index
    # changes even though we also pass order[] params server-side above.
    all_tenders.sort(key=lambda t: t.get("date_Published") or "", reverse=True)
    log.info(f"Fetched {len(all_tenders)} tenders")
    return all_tenders

# ---------------------------------------------------------------------------
# DEDUPE CACHE
# ---------------------------------------------------------------------------

def tender_hash(tender):
    """MD5 hash of id|title|number -- same dedupe key pattern as Aptiv's scanner."""
    key = f"{tender.get('id')}|{tender.get('description')}|{tender.get('tender_No')}"
    return hashlib.md5(key.encode("utf-8")).hexdigest()

def load_seen_cache():
    if not os.path.exists(SEEN_CACHE_FILE):
        return {}
    try:
        with open(SEEN_CACHE_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except (json.JSONDecodeError, OSError) as e:
        log.warning(f"Could not read {SEEN_CACHE_FILE} ({e}); starting fresh")
        return {}

def prune_seen_cache(cache):
    """Drop entries older than CACHE_RETENTION_DAYS to keep the cache file small."""
    cutoff = datetime.utcnow() - timedelta(days=CACHE_RETENTION_DAYS)
    pruned = {}
    for h, seen_at in cache.items():
        try:
            if datetime.fromisoformat(seen_at) >= cutoff:
                pruned[h] = seen_at
        except ValueError:
            continue
    return pruned

def save_seen_cache(cache):
    with open(SEEN_CACHE_FILE, "w", encoding="utf-8") as f:
        json.dump(cache, f, indent=2, sort_keys=True)

# ---------------------------------------------------------------------------
# SCORING
# ---------------------------------------------------------------------------

def _contains_any(haystack, needles):
    return [n for n in needles if n in haystack]

def is_excluded(text):
    return any(term in text for term in EXCLUSIONS)

def is_bulk_infrastructure(text):
    """True if bulk/tanker water language co-occurs with municipal/rural-scale
    context -- i.e. this reads as a water-relief/infrastructure contract, not
    an events tanker-rental job. See BULK_WATER_SIGNALS / MUNICIPAL_SCALE_
    SIGNALS comment above (added 2026-07-25, v1.2). Precision-first: only
    fires on the combination, not either list alone, so a genuine large-event
    water-tanker tender (no ward/household/municipal-scale language) still
    passes through to scoring."""
    return bool(_contains_any(text, BULK_WATER_SIGNALS)) and bool(
        _contains_any(text, MUNICIPAL_SCALE_SIGNALS)
    )

def passes_category_filter(tender, text):
    category = (tender.get("category") or "").strip()
    if category in CATEGORY_ALLOWLIST:
        return True
    return any(kw in text for kw in SERVICE_MATCH_OVERRIDE_KEYWORDS)

def score_service_match(text):
    matched = [(kw, pts) for kw, pts in SERVICE_MATCH_KEYWORDS.items() if kw in text]
    if not matched:
        return 0, []
    score = min(SCORE_WEIGHTS["service_match"], max(pts for _, pts in matched))
    return score, [kw for kw, _ in matched]

def score_strategic_fit(text):
    matched = _contains_any(text, STRATEGIC_FIT_KEYWORDS)
    score = min(SCORE_WEIGHTS["strategic_fit"], len(matched) * STRATEGIC_FIT_POINTS_PER_MATCH)
    return score, matched

def score_feasibility(tender):
    province = (tender.get("province") or "").strip()
    if not province:
        bucket = "unknown"
    elif province in COVERAGE_PROVINCES:
        bucket = "covered"
    else:
        bucket = "other"
    province_pts = FEASIBILITY_PROVINCE_POINTS[bucket]

    days_left = None
    closing_raw = tender.get("closing_Date")
    if closing_raw:
        try:
            closing_dt = datetime.fromisoformat(closing_raw)
            days_left = (closing_dt - datetime.utcnow()).days
        except ValueError:
            pass

    if days_left is None:
        timeline_pts = FEASIBILITY_TIMELINE_POINTS["moderate"]
        timeline_bucket = "unknown"
    elif days_left <= FEASIBILITY_TIMELINE_TIGHT_DAYS:
        timeline_pts = FEASIBILITY_TIMELINE_POINTS["tight"]
        timeline_bucket = "tight"
    elif days_left <= FEASIBILITY_TIMELINE_MODERATE_DAYS:
        timeline_pts = FEASIBILITY_TIMELINE_POINTS["moderate"]
        timeline_bucket = "moderate"
    else:
        timeline_pts = FEASIBILITY_TIMELINE_POINTS["ample"]
        timeline_bucket = "ample"

    score = min(SCORE_WEIGHTS["feasibility"], province_pts + timeline_pts)
    return score, {"province_bucket": bucket, "timeline_bucket": timeline_bucket, "days_left": days_left}

def score_consortium(text):
    matched = _contains_any(text, CONSORTIUM_SIGNALS)
    score = min(SCORE_WEIGHTS["consortium_advantage"], len(matched) * CONSORTIUM_POINTS_PER_MATCH)
    return score, matched

def score_tender(tender):
    description = (tender.get("description") or "")
    category = (tender.get("category") or "")
    text = f"{description} {category}".lower()

    if is_excluded(text):
        return None
    if is_bulk_infrastructure(text):
        return None
    if not passes_category_filter(tender, text):
        return None

    service_score, service_hits = score_service_match(text)
    strategic_score, strategic_hits = score_strategic_fit(text)
    feasibility_score, feasibility_detail = score_feasibility(tender)
    consortium_score, consortium_hits = score_consortium(text)

    total = service_score + strategic_score + feasibility_score + consortium_score

    if total < THRESHOLD_POSSIBLE:
        return None

    tier = "Strong Fit" if total >= THRESHOLD_STRONG else "Possible Fit"

    return {
        "tender": tender,
        "total_score": total,
        "tier": tier,
        "breakdown": {
            "service_match": {"score": service_score, "hits": service_hits},
            "strategic_fit": {"score": strategic_score, "hits": strategic_hits},
            "feasibility": {"score": feasibility_score, "detail": feasibility_detail},
            "consortium_advantage": {"score": consortium_score, "hits": consortium_hits},
        },
    }

# ---------------------------------------------------------------------------
# EMAIL
# ---------------------------------------------------------------------------

CARD_TEMPLATE = """
<div style="border:1px solid #ddd;border-left:6px solid {border_color};border-radius:6px;
padding:16px;margin-bottom:14px;font-family:Arial,Helvetica,sans-serif;">
<div style="font-size:12px;font-weight:bold;color:{border_color};text-transform:uppercase;
letter-spacing:0.5px;margin-bottom:6px;">{tier} &middot; {score}/100</div>
<div style="font-size:15px;font-weight:bold;color:#1a1a1a;margin-bottom:6px;">{description}</div>
<div style="font-size:13px;color:#555;margin-bottom:8px;">
<strong>Tender No:</strong> {tender_no} &nbsp;|&nbsp;
<strong>Organ of State:</strong> {organ} &nbsp;|&nbsp;
<strong>Province:</strong> {province}<br/>
<strong>Category:</strong> {category} &nbsp;|&nbsp;
<strong>Closing:</strong> {closing} &nbsp;|&nbsp;
<strong>Published:</strong> {published}
</div>
<div style="font-size:12px;color:#777;">
Service match: {service_hits} &nbsp;|&nbsp; Strategic fit: {strategic_hits} &nbsp;|&nbsp;
Consortium signals: {consortium_hits}
</div>
<div style="margin-top:10px;">
<a href="{portal_url}" style="font-size:13px;color:#0b5fff;text-decoration:none;">
{link_text} &rarr;</a>
</div>
</div>
"""

def _fmt_hits(hits):
    return ", ".join(hits) if hits else "none"

def document_url(tender):
    """Build a genuine per-tender document link from the API's own
    supportDocument GUID + extension, falling back to the portal listing
    page when no document is attached to the tender.

    Note (carried over from Aptiv's own scanner, verified independently):
    this direct download link works reliably when fetched programmatically,
    but the portal has shown intermittent 503s on a cold top-level browser
    navigation to it (likely bot/hotlink protection) -- not something we can
    fix from this script. The listing-page fallback below is the guaranteed
    path when either no document exists or the link itself misbehaves.
    """
    docs = tender.get("supportDocument") or []
    if not docs:
        return TENDER_PORTAL_URL, False
    doc = docs[0]
    doc_id = doc.get("supportDocumentID")
    ext = doc.get("extension") or ""
    filename = doc.get("fileName") or "tender_document"
    if not doc_id:
        return TENDER_PORTAL_URL, False
    blob_name = f"{doc_id}{ext}"
    url = f"{DOWNLOAD_BASE_URL}?blobName={quote(blob_name)}&downloadedFileName={quote(filename)}"
    return url, True

def build_card(result):
    tender = result["tender"]
    border_color = "#1a7f37" if result["tier"] == "Strong Fit" else "#b8860b"
    link_url, has_doc = document_url(tender)
    link_text = "View tender document" if has_doc else "View on eTenders portal (search this tender)"
    return CARD_TEMPLATE.format(
        border_color=border_color,
        tier=result["tier"],
        score=result["total_score"],
        description=(tender.get("description") or "").strip()[:220],
        tender_no=tender.get("tender_No") or "N/A",
        organ=tender.get("organ_of_State") or "N/A",
        province=tender.get("province") or "Not stated",
        category=tender.get("category") or "N/A",
        closing=tender.get("closing_Date") or "N/A",
        published=tender.get("date_Published") or "N/A",
        service_hits=_fmt_hits(result["breakdown"]["service_match"]["hits"]),
        strategic_hits=_fmt_hits(result["breakdown"]["strategic_fit"]["hits"]),
        consortium_hits=_fmt_hits(result["breakdown"]["consortium_advantage"]["hits"]),
        portal_url=link_url,
        link_text=link_text,
    )

def build_email_html(strong, possible, run_date):
    strong_cards = "".join(build_card(r) for r in strong) or "<p>None today.</p>"
    possible_cards = "".join(build_card(r) for r in possible) or "<p>None today.</p>"
    return f"""
<html>
<body style="background:#f4f4f4;padding:20px;font-family:Arial,Helvetica,sans-serif;">
<div style="max-width:680px;margin:0 auto;background:#fff;padding:24px;border-radius:8px;">
<h2 style="color:#1a1a1a;margin-bottom:4px;">Youth Water Tender Intelligence</h2>
<p style="color:#777;margin-top:0;">{run_date} &middot; {len(strong)} Strong, {len(possible)} Possible</p>
<h3 style="color:#1a7f37;">Strong Fit ({len(strong)})</h3>
{strong_cards}
<h3 style="color:#b8860b;">Possible Fit ({len(possible)})</h3>
{possible_cards}
<p style="font-size:11px;color:#999;margin-top:24px;">
Automated scan of the eTenders national portal. Scoring weights: Service Match 35,
Strategic Fit 25, Feasibility 20, Consortium Advantage 20. Thresholds: Strong &ge; 55,
Possible &ge; 25.
</p>
</div>
</body>
</html>
"""

def send_email(subject, html_body):
    if not GMAIL_ADDRESS or not GMAIL_APP_PASSWORD:
        log.error("GMAIL_ADDRESS / GMAIL_APP_PASSWORD not set -- skipping send")
        return False

    msg = MIMEMultipart("alternative")
    msg["Subject"] = subject
    msg["From"] = GMAIL_ADDRESS
    msg["To"] = ", ".join(RECIPIENTS)
    msg.attach(MIMEText(html_body, "html"))

    context = ssl.create_default_context()
    try:
        with smtplib.SMTP_SSL("smtp.gmail.com", 465, context=context) as server:
            server.login(GMAIL_ADDRESS, GMAIL_APP_PASSWORD)
            server.sendmail(GMAIL_ADDRESS, RECIPIENTS, msg.as_string())
        log.info(f"Email sent to {len(RECIPIENTS)} recipients")
        return True
    except smtplib.SMTPException as e:
        log.error(f"Failed to send email: {e}")
        return False

# ---------------------------------------------------------------------------
# MAIN
# ---------------------------------------------------------------------------

def main():
    tenders = fetch_tenders()
    cache = prune_seen_cache(load_seen_cache())

    strong, possible = [], []
    pending_hashes = []  # relevant tenders -- only marked seen after a successful send

    for tender in tenders:
        h = tender_hash(tender)
        if h in cache:
            continue

        result = score_tender(tender)

        if result is None:
            # Irrelevant/excluded tenders are safe to cache immediately -- this
            # only avoids re-scoring cost and never affects email delivery.
            cache[h] = datetime.utcnow().isoformat()
            continue

        pending_hashes.append(h)
        if result["tier"] == "Strong Fit":
            strong.append(result)
        else:
            possible.append(result)

    strong.sort(key=lambda r: r["total_score"], reverse=True)
    possible.sort(key=lambda r: r["total_score"], reverse=True)

    new_count = len(pending_hashes)
    log.info(f"Filtered: {new_count} new & relevant ({len(strong)} strong, {len(possible)} possible)")

    if new_count == 0:
        save_seen_cache(cache)
        log.info("No new relevant tenders -- skipping email")
        return

    run_date = datetime.utcnow().strftime("%Y-%m-%d")
    subject = f"Youth Water Tender Intelligence -- {run_date} | {len(strong)} Strong, {len(possible)} Possible"
    html = build_email_html(strong, possible, run_date)
    sent = send_email(subject, html)

    if sent:
        now = datetime.utcnow().isoformat()
        for h in pending_hashes:
            cache[h] = now
    else:
        log.warning(
            "Email send failed -- relevant tenders NOT marked as seen; "
            "they will be retried on the next run instead of being lost."
        )

    save_seen_cache(cache)

if __name__ == "__main__":
    main()
