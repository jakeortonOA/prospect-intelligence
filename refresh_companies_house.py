#!/usr/bin/env python3
from __future__ import annotations

import argparse
import io
import json
import os
import re
import time
import zipfile
from datetime import datetime, timezone, date
from pathlib import Path
from urllib.parse import urljoin

import requests
from lxml import etree

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
PROS = DATA / "prospects.json"
PROSJS = DATA / "prospects.js"
STATUS = DATA / "feed_status.json"
STATUSJS = DATA / "feed_status.js"
PROCESSED = DATA / "processed_feeds.json"

INDEX_URL = "https://download.companieshouse.gov.uk/en_accountsdata.html"
PROFILE_URL = "https://api.company-information.service.gov.uk/company/{company_number}"
PSC_URL = "https://api.company-information.service.gov.uk/company/{company_number}/persons-with-significant-control"
OFFICERS_URL = "https://api.company-information.service.gov.uk/company/{company_number}/officers"
API_REQUEST_DELAY = 0.55
FILE_RE = re.compile(r'href=["\']([^"\']*Accounts_Bulk_Data-(\d{4}-\d{2}-\d{2})\.zip)["\']', re.I)
COMPANY_RE = re.compile(r'_((?:SC|NI|OC|SO|LP|SL|FC|NF|NL|IP|SP|RS)?[A-Z0-9]{5,8})_(\d{8})(?:\.|_)', re.I)

RETENTION_DAYS = 30
PROFILE_REFRESH_DAYS = 30

# Cheap pre-API exclusions, only to avoid wasting enrichment calls on obvious mismatches.
NAME_ACTIVITY_EXCLUDE = [
    "accountant", "accountancy", "bookkeeping", "tax adviser", "tax advisor",
    "financial adviser", "financial advisor", "wealth management", "insurance broker",
    "solicitor", "law firm", "car dealer", "used car", "motor dealer", "motor retail",
    "restaurant", "cafe", "public house", "hotel", "nursery", "childcare",
    "residential care", "nursing care", "charity", "membership organisation",
    "membership organization", "property investment", "property letting",
    "investment holding",
]

# Oldfield sector mapping from current Companies House SIC codes.
# We deliberately keep Business services narrower than the entire professional-services universe.
BUSINESS_SERVICE_CODES = {
    # Software / IT / data
    "62011","62012","62020","62030","62090","63110","63120","63990",
    # Management / technical consultancy
    "70210","70229","71121","71122","71200","72110","72190",
    # Marketing / design / specialist technical
    "73110","73120","74100","74901","74909",
    # Security / facilities / cleaning
    "80100","80200","80300","81100","81210","81221","81222","81229","81291","81299",
    # Office / business support
    "82110","82190","82200","82301","82302","82920","82990",
}

def jread(path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return default

def lname(tag):
    return str(tag).split("}")[-1].split(":")[-1]

def text(el):
    try:
        return " ".join("".join(el.itertext()).split())
    except Exception:
        return ""

def number(value):
    if value is None:
        return None
    s = str(value).replace(",", "").replace("£", "").strip()
    if s in {"", "-"}:
        return None
    negative = s.startswith("(") and s.endswith(")")
    s = s.strip("()")
    try:
        value = float(s)
        return -value if negative else value
    except Exception:
        return None

def growth(previous, current):
    if previous is None or current is None or previous == 0:
        return None
    return (current - previous) / abs(previous) * 100

def score(g, steps):
    if g is None or g <= 0:
        return 0
    out = 0
    for threshold, value in steps:
        if g >= threshold:
            out = value
    return out

def momentum(emp_growth, na_growth, re_growth):
    return min(
        100,
        score(emp_growth, [(5,8),(20,18),(50,30),(100,40)])
        + score(na_growth, [(5,7),(20,16),(50,27),(100,35)])
        + score(re_growth, [(5,5),(20,11),(50,18),(100,25)])
    )

def company_no(filename):
    match = COMPANY_RE.search(filename)
    return match.group(1).upper() if match else None

def company_number_is_england_wales(company_number):
    n = (company_number or "").upper()
    return not n.startswith(("SC", "NI", "SO", "SL"))

def obvious_text_exclusion(company, activity):
    combined = f"{company or ''} {activity or ''}".lower()
    return next((term for term in NAME_ACTIVITY_EXCLUDE if term in combined), None)

def oldfield_sector_from_sic(sic_codes):
    cleaned = [str(x).zfill(5) for x in (sic_codes or []) if str(x).isdigit()]
    for sic in cleaned:
        n = int(sic)
        if 10000 <= n <= 33999:
            return "Manufacturing"
    for sic in cleaned:
        n = int(sic)
        if 41000 <= n <= 43999:
            return "Construction"
    for sic in cleaned:
        n = int(sic)
        if 46000 <= n <= 46999:
            return "Wholesale"
    if any(sic in BUSINESS_SERVICE_CODES for sic in cleaned):
        return "Business services"
    return None

def format_address(address):
    if not address:
        return None
    ordered = [
        address.get("premises"),
        address.get("address_line_1"),
        address.get("address_line_2"),
        address.get("locality"),
        address.get("region"),
        address.get("postal_code"),
        address.get("country"),
    ]
    parts = []
    for value in ordered:
        v = str(value or "").strip()
        if v and v not in parts:
            parts.append(v)
    return ", ".join(parts) or None

def profile_location(address):
    if not address:
        return None
    locality = str(address.get("locality") or "").strip()
    region = str(address.get("region") or "").strip()
    if locality and region and locality.lower() != region.lower():
        return f"{locality}, {region}"
    return locality or region or str(address.get("country") or "").strip() or None

def profile_is_england_wales(profile, company_number):
    address = profile.get("registered_office_address") or {}
    country = str(address.get("country") or "").strip().lower()
    if country in {"scotland", "northern ireland"}:
        return False
    if country in {"england", "wales", "united kingdom", "great britain", "not specified", ""}:
        return company_number_is_england_wales(company_number)
    return company_number_is_england_wales(company_number)

def parse_doc(raw, filename):
    root = etree.fromstring(raw, parser=etree.XMLParser(recover=True, huge_tree=True))

    contexts = {}
    for el in root.iter():
        if lname(el.tag) == "context":
            dates, members = [], []
            for child in el.iter():
                ln = lname(child.tag)
                if ln in {"instant", "endDate"}:
                    dates.append((ln, (child.text or "").strip()))
                if ln in {"explicitMember", "typedMember"}:
                    members.append(text(child))
            contexts[el.get("id")] = {"dates": dates, "members": members}

    facts = []
    for el in root.iter():
        if lname(el.tag) in {"nonFraction", "nonNumeric"}:
            facts.append((el.get("name") or "", el.get("contextRef") or "", text(el)))

    def vals(names):
        wanted = {x.lower() for x in names}
        out = []
        for name, context_ref, value in facts:
            if name.split(":")[-1].lower() not in wanted:
                continue
            fact_date = None
            for _, d in contexts.get(context_ref, {}).get("dates", []):
                if d:
                    fact_date = d
            out.append((fact_date, context_ref, value))
        return out

    def two(names, predicate=None):
        arr = []
        for fact_date, context_ref, value in vals(names):
            if predicate and not predicate(context_ref, contexts.get(context_ref, {})):
                continue
            numeric = number(value)
            if numeric is not None and fact_date:
                arr.append((fact_date, numeric))
        dedup = {d: v for d, v in arr}
        ordered = sorted(dedup.items(), reverse=True)
        return (
            ordered[1][1] if len(ordered) > 1 else None,
            ordered[0][1] if ordered else None,
        )

    cn = company_no(filename)
    names = [x[2] for x in vals(["EntityCurrentLegalOrRegisteredName"]) if x[2]]
    company = names[0] if names else cn or "Unknown company"

    emp_prev, emp_cur = two(["AverageNumberEmployeesDuringPeriod", "AverageNumberOfEmployeesDuringPeriod"])
    na_prev, na_cur = two(["NetAssetsLiabilities"])
    re_prev, re_cur = two(
        ["Equity", "RetainedEarningsAccumulatedLosses"],
        lambda c, z: "retained" in c.lower() or any("retained" in m.lower() for m in z.get("members", []))
    )

    directors = []
    for _, _, value in vals(["NameEntityOfficer", "DirectorName"]):
        if value and value not in directors:
            directors.append(value)

    activities = [x[2] for x in vals(["DescriptionPrincipalActivities", "PrincipalActivity"]) if x[2]]
    activity = activities[0] if activities else None

    dates = [d for c in contexts.values() for _, d in c.get("dates", []) if d]
    period_end = max(dates) if dates else None

    emp_growth = growth(emp_prev, emp_cur)
    na_growth = growth(na_prev, na_cur)
    re_growth = growth(re_prev, re_cur)
    momentum_score = momentum(emp_growth, na_growth, re_growth)

    scale = (
        (emp_cur is not None and emp_cur >= 10)
        or (na_cur is not None and na_cur >= 500000)
    )

    return {
        "company": company,
        "company_number": cn,
        "period_end": period_end,
        "directors": directors,
        "director_count": len(directors),
        "emp_prev": emp_prev,
        "emp_cur": emp_cur,
        "emp_growth_pct": emp_growth,
        "na_prev": na_prev,
        "na_cur": na_cur,
        "na_growth_pct": na_growth,
        "re_prev": re_prev,
        "re_cur": re_cur,
        "re_growth_pct": re_growth,
        "momentum_score": momentum_score,
        "confidence": "High" if re_cur is not None else "Medium",
        "signal": "Strong momentum" if momentum_score >= 60 else "Momentum detected" if momentum_score >= 20 else "Low momentum",
        "principal_activity": activity,
        "scale_fit": "£1m+ likely proxy" if scale else "Scale not evidenced",
        "scale_fit_bool": scale,
        "research_priority": momentum_score,
    }

def financial_prescreen(row):
    if not row.get("company_number"):
        return False, "Missing company number"
    if not company_number_is_england_wales(row["company_number"]):
        return False, "Outside England & Wales"
    if obvious_text_exclusion(row.get("company"), row.get("principal_activity")):
        return False, "Obvious activity exclusion"
    if not row.get("scale_fit_bool"):
        return False, "Insufficient current scale evidence"
    if (row.get("momentum_score") or 0) < 25:
        return False, "Insufficient momentum"
    return True, "Financial pre-screen passed"

def iter_docs(zf, info):
    raw = zf.read(info.filename)
    low = info.filename.lower()

    if low.endswith((".html", ".htm", ".xml", ".xhtml")):
        yield raw, info.filename
        return

    if low.endswith(".zip"):
        try:
            with zipfile.ZipFile(io.BytesIO(raw)) as nested:
                for nested_info in nested.infolist():
                    if not nested_info.is_dir() and nested_info.filename.lower().endswith((".html", ".htm", ".xml", ".xhtml")):
                        yield nested.read(nested_info.filename), f"{info.filename}/{nested_info.filename}"
        except zipfile.BadZipFile:
            return

def process_daily_zip(path, source_date):
    parsed_rows = []
    parsed_documents = 0
    parse_failures = 0

    with zipfile.ZipFile(path) as zf:
        for info in zf.infolist():
            if info.is_dir():
                continue
            for raw, name in iter_docs(zf, info):
                try:
                    row = parse_doc(raw, name)
                    if row.get("company_number"):
                        row["source_feed_date"] = source_date
                        parsed_rows.append(row)
                        parsed_documents += 1
                except Exception:
                    parse_failures += 1

    unique = {}
    for row in parsed_rows:
        key = row["company_number"]
        if key not in unique or row["research_priority"] > unique[key]["research_priority"]:
            unique[key] = row

    unique_rows = list(unique.values())
    prescreen = []
    for row in unique_rows:
        ok, reason = financial_prescreen(row)
        row["pre_screen_reason"] = reason
        if ok:
            prescreen.append(row)

    return unique_rows, prescreen, {
        "filings": parsed_documents,
        "unique_companies": len(unique_rows),
        "parse_failures": parse_failures,
        "financial_prescreen_candidates": len(prescreen),
    }

def discover(session):
    response = session.get(INDEX_URL, timeout=60)
    response.raise_for_status()

    files, seen = [], set()
    for href, source_date in FILE_RE.findall(response.text):
        filename = f"Accounts_Bulk_Data-{source_date}.zip"
        if filename in seen:
            continue
        seen.add(filename)
        files.append({"name": filename, "date": source_date, "url": urljoin(INDEX_URL, href)})
    return sorted(files, key=lambda x: x["date"])

def download(session, url, destination):
    partial = destination.with_suffix(".zip.part")
    with session.get(url, stream=True, timeout=(30, 300)) as response:
        response.raise_for_status()
        with partial.open("wb") as f:
            for chunk in response.iter_content(1024 * 1024):
                if chunk:
                    f.write(chunk)

    if not zipfile.is_zipfile(partial):
        partial.unlink(missing_ok=True)
        raise RuntimeError("Companies House response was not a valid ZIP file.")

    partial.replace(destination)

def fetch_company_endpoint(session, url, api_key, params=None, not_found=None):
    for attempt in range(6):
        response = session.get(url, auth=(api_key, ""), params=params, timeout=30)
        time.sleep(API_REQUEST_DELAY)
        if response.status_code == 200:
            return response.json()
        if response.status_code == 404:
            return not_found
        if response.status_code == 429:
            # Stay conservative with the public API rate limit rather than repeatedly hammering it.
            time.sleep(15 * (attempt + 1))
            continue
        if response.status_code >= 500:
            time.sleep(3 * (attempt + 1))
            continue
        response.raise_for_status()
    raise RuntimeError(f"Companies House API request repeatedly failed: {url}")

def fetch_company_profile(session, company_number, api_key):
    return fetch_company_endpoint(
        session,
        PROFILE_URL.format(company_number=company_number),
        api_key,
        not_found=None,
    )

def fetch_company_psc(session, company_number, api_key):
    return fetch_company_endpoint(
        session,
        PSC_URL.format(company_number=company_number),
        api_key,
        params={"items_per_page": 100},
        not_found={"items": []},
    ) or {"items": []}

def fetch_company_officers(session, company_number, api_key):
    return fetch_company_endpoint(
        session,
        OFFICERS_URL.format(company_number=company_number),
        api_key,
        params={"items_per_page": 100},
        not_found={"items": []},
    ) or {"items": []}

def year_end_from_profile(profile):
    accounts = (profile or {}).get("accounts") or {}
    ard = accounts.get("accounting_reference_date") or {}
    day = ard.get("day")
    month = ard.get("month")
    try:
        day = int(day) if day is not None else None
        month = int(month) if month is not None else None
    except Exception:
        day, month = None, None
    if not month or month < 1 or month > 12:
        return None, None, None
    month_names = [
        None, "January", "February", "March", "April", "May", "June",
        "July", "August", "September", "October", "November", "December"
    ]
    label = f"{day} {month_names[month]}" if day else month_names[month]
    return day, month, label

def person_name_tokens(name):
    cleaned = re.sub(r"[^a-z0-9 ]+", " ", str(name or "").lower())
    stop = {"mr", "mrs", "miss", "ms", "dr", "sir", "dame", "prof", "professor"}
    return [x for x in cleaned.split() if x and x not in stop]

def names_match(a, b):
    aa, bb = person_name_tokens(a), person_name_tokens(b)
    if not aa or not bb:
        return False
    sa, sb = set(aa), set(bb)
    if sa == sb:
        return True
    overlap = sa & sb
    return len(overlap) >= 2 and (aa[-1] in sb or bb[-1] in sa)

def control_strength(natures):
    score = 0
    for nature in natures or []:
        n = str(nature).lower()
        if "75-to-100-percent" in n:
            score = max(score, 100)
        elif "50-to-75-percent" in n:
            score = max(score, 90)
        elif "25-to-50-percent" in n:
            score = max(score, 70)
        elif "appoint-and-remove-directors" in n:
            score = max(score, 85)
        elif "significant-influence-or-control" in n:
            score = max(score, 60)
        else:
            score = max(score, 40)
    return score

def friendly_control(natures):
    labels = []
    for nature in natures or []:
        n = str(nature).lower()
        label = None
        if "ownership-of-shares-75-to-100-percent" in n:
            label = "Shares: 75-100%"
        elif "ownership-of-shares-50-to-75-percent" in n:
            label = "Shares: 50-75%"
        elif "ownership-of-shares-25-to-50-percent" in n:
            label = "Shares: 25-50%"
        elif "voting-rights-75-to-100-percent" in n:
            label = "Voting rights: 75-100%"
        elif "voting-rights-50-to-75-percent" in n:
            label = "Voting rights: 50-75%"
        elif "voting-rights-25-to-50-percent" in n:
            label = "Voting rights: 25-50%"
        elif "appoint-and-remove-directors" in n:
            label = "Can appoint/remove directors"
        elif "significant-influence-or-control" in n:
            label = "Significant influence/control"
        if label and label not in labels:
            labels.append(label)
    return labels

def simplify_psc(payload):
    out = []
    for item in (payload or {}).get("items") or []:
        if item.get("ceased_on"):
            continue
        kind = str(item.get("kind") or "")
        name = item.get("name")
        if not name:
            elements = item.get("name_elements") or {}
            name = " ".join(
                str(elements.get(k) or "").strip()
                for k in ("forename", "middle_name", "surname")
                if str(elements.get(k) or "").strip()
            ) or None
        if not name:
            continue
        natures = item.get("natures_of_control") or []
        out.append({
            "name": name,
            "kind": kind,
            "is_individual": "individual" in kind,
            "natures_of_control": natures,
            "control_summary": friendly_control(natures),
            "control_score": control_strength(natures),
            "notified_on": item.get("notified_on"),
        })
    return sorted(out, key=lambda x: (-x.get("control_score", 0), x.get("name", "")))

def simplify_directors(payload):
    out = []
    for item in (payload or {}).get("items") or []:
        if item.get("resigned_on"):
            continue
        role = str(item.get("officer_role") or "").lower()
        if role not in {"director", "corporate-director"}:
            continue
        name = item.get("name")
        if not name:
            continue
        out.append({
            "name": name,
            "role": role,
            "is_individual": role == "director",
            "appointed_on": item.get("appointed_on"),
        })
    return sorted(out, key=lambda x: (x.get("appointed_on") or "9999-99-99", x.get("name", "")))

def choose_primary_contact(controllers, directors):
    individual_directors = [d for d in directors if d.get("is_individual")]
    candidates = []
    for controller in controllers:
        if not controller.get("is_individual"):
            continue
        matched = next((d for d in individual_directors if names_match(controller.get("name"), d.get("name"))), None)
        contact_score = int(controller.get("control_score") or 0) + (25 if matched else 0)
        candidates.append((contact_score, controller, matched))

    if candidates:
        _, controller, matched = max(candidates, key=lambda x: x[0])
        summary = controller.get("control_summary") or []
        both = matched is not None
        confidence = "High" if both or (controller.get("control_score") or 0) >= 90 else "Medium"
        return {
            "name": controller.get("name"),
            "role": "PSC + active director" if both else "Person with significant control",
            "confidence": confidence,
            "is_psc": True,
            "is_director": both,
            "control_summary": summary,
            "basis": (
                "Individual PSC also appears on the current active-director list."
                if both else
                "Highest-control individual PSC on the current Companies House record."
            ),
        }

    if individual_directors:
        director = individual_directors[0]
        corporate_controller = next((c for c in controllers if not c.get("is_individual")), None)
        return {
            "name": director.get("name"),
            "role": "Active director",
            "confidence": "Low",
            "is_psc": False,
            "is_director": True,
            "control_summary": [],
            "basis": (
                f"No individual PSC identified; control is recorded against {corporate_controller.get('name')}. "
                "Using an active director as the best available contact proxy."
                if corporate_controller else
                "No individual PSC identified; using the longest-standing active director as a contact proxy."
            ),
        }
    return None

def apply_control_data(row, psc_payload, officers_payload):
    controllers = simplify_psc(psc_payload)
    directors = simplify_directors(officers_payload)
    contact = choose_primary_contact(controllers, directors)
    row["controllers"] = controllers
    row["active_directors"] = directors
    row["primary_contact"] = contact
    row["primary_contact_name"] = contact.get("name") if contact else None
    row["primary_contact_role"] = contact.get("role") if contact else None
    row["primary_contact_confidence"] = contact.get("confidence") if contact else None
    row["primary_contact_basis"] = contact.get("basis") if contact else None
    row["primary_contact_checked_at_utc"] = datetime.now(timezone.utc).isoformat()
    row["ownership_source"] = "Companies House PSC + officer APIs"
    return row

def apply_current_profile(row, profile):
    if not profile:
        row["company_status"] = "not found"
        row["profile_sector"] = None
        row["sic_codes"] = []
        row["integrity_flags"] = ["Current Companies House profile not found"]
        row["profile_enriched_at_utc"] = datetime.now(timezone.utc).isoformat()
        return row

    address = profile.get("registered_office_address") or {}
    row["company"] = profile.get("company_name") or row.get("company")
    row["company_status"] = profile.get("company_status")
    row["company_type"] = profile.get("type")
    row["date_of_creation"] = profile.get("date_of_creation")
    row["sic_codes"] = profile.get("sic_codes") or []
    row["profile_sector"] = oldfield_sector_from_sic(row["sic_codes"])
    row["registered_office"] = format_address(address)
    row["location"] = profile_location(address)
    row["postcode"] = address.get("postal_code")
    row["registered_office_country"] = address.get("country")
    row["previous_company_names"] = profile.get("previous_company_names") or []
    year_end_day, year_end_month, year_end_label = year_end_from_profile(profile)
    row["year_end_day"] = year_end_day
    row["year_end_month"] = year_end_month
    row["year_end_label"] = year_end_label
    row["profile_enriched_at_utc"] = datetime.now(timezone.utc).isoformat()
    row["profile_source"] = "Companies House company profile API"

    flags = []
    if profile.get("registered_office_is_in_dispute"):
        flags.append("Registered office is in dispute")
    if profile.get("undeliverable_registered_office_address"):
        flags.append("Registered office marked undeliverable")
    row["integrity_flags"] = flags
    return row

def profile_eligibility(row):
    if row.get("company_status") != "active":
        return False, f"Company status is {row.get('company_status') or 'unknown'}"
    if not company_number_is_england_wales(row.get("company_number")):
        return False, "Outside England & Wales"
    country = str(row.get("registered_office_country") or "").lower()
    if country in {"scotland", "northern ireland"}:
        return False, "Registered office outside England & Wales"
    if not row.get("profile_sector"):
        return False, "Current SIC codes are outside Oldfield target sectors"
    if row.get("integrity_flags"):
        return False, "Current Companies House profile has an address integrity flag"
    return True, f"{row['profile_sector']} confirmed from current Companies House SIC code(s)"

def needs_profile_refresh(row, today_date):
    if (
        not row.get("profile_enriched_at_utc")
        or not row.get("sic_codes")
        or not row.get("registered_office")
        or "year_end_month" not in row
    ):
        return True
    try:
        enriched = datetime.fromisoformat(row["profile_enriched_at_utc"].replace("Z", "+00:00")).date()
        return (today_date - enriched).days >= PROFILE_REFRESH_DAYS
    except Exception:
        return True

def needs_control_refresh(row, today_date):
    if "controllers" not in row or "active_directors" not in row or not row.get("primary_contact_checked_at_utc"):
        return True
    try:
        enriched = datetime.fromisoformat(row["primary_contact_checked_at_utc"].replace("Z", "+00:00")).date()
        return (today_date - enriched).days >= PROFILE_REFRESH_DAYS
    except Exception:
        return True

def days_between(older, newer):
    try:
        return (date.fromisoformat(newer) - date.fromisoformat(older)).days
    except Exception:
        return 0

def archive_stale(master, latest_feed_date):
    archived = 0
    for row in master.values():
        last_triggered = row.get("last_triggered_feed_date") or row.get("source_feed_date")
        if not last_triggered:
            continue
        age = days_between(last_triggered, latest_feed_date)
        if age > RETENTION_DAYS and row.get("candidate_state") != "archived":
            row["candidate_state"] = "archived"
            row["archived_reason"] = f"No fresh qualifying trigger for {age} days"
            archived += 1
    return archived

def merge_financial_refresh(fresh, old):
    if not old:
        return fresh
    for key in [
        "location", "postcode", "registered_office", "profile_sector", "company_status",
        "company_type", "date_of_creation", "sic_codes", "previous_company_names",
        "year_end_day", "year_end_month", "year_end_label",
        "profile_enriched_at_utc", "profile_source", "registered_office_country",
        "integrity_flags", "controllers", "active_directors", "primary_contact",
        "primary_contact_name", "primary_contact_role", "primary_contact_confidence",
        "primary_contact_basis", "primary_contact_checked_at_utc", "ownership_source"
    ]:
        if key in old and old.get(key) not in (None, "", [], {}):
            fresh[key] = old[key]
    return fresh

def enrich_existing_master(master, session, api_key):
    changed = 0
    archived = 0
    today_date = datetime.now(timezone.utc).date()

    for company_number, row in list(master.items()):
        profile_due = needs_profile_refresh(row, today_date)
        control_due = needs_control_refresh(row, today_date)
        if not profile_due and not control_due:
            continue

        before = json.dumps(row, sort_keys=True, default=str)
        if profile_due:
            profile = fetch_company_profile(session, company_number, api_key)
            apply_current_profile(row, profile)

        eligible, reason = profile_eligibility(row)
        row["gate_reason"] = reason
        row["gate_basis"] = "current_company_profile"

        if eligible:
            if control_due:
                psc_payload = fetch_company_psc(session, company_number, api_key)
                officers_payload = fetch_company_officers(session, company_number, api_key)
                apply_control_data(row, psc_payload, officers_payload)
            row["gate_status"] = "research"
            # Re-open only automatic archived records caused by missing/old profile data.
            if (row.get("archived_reason") or "").startswith(("Current Companies House", "Company status", "Registered office", "Current SIC")):
                row["candidate_state"] = "active"
                row["archived_reason"] = None
        else:
            row["latest_screen_pass"] = False
            if row.get("candidate_state") != "archived":
                row["candidate_state"] = "archived"
                row["archived_reason"] = reason
                archived += 1

        after = json.dumps(row, sort_keys=True, default=str)
        if before != after:
            changed += 1

    return changed, archived

def write(master_rows, status, processed):
    ordered = sorted(
        master_rows,
        key=lambda x: (
            x.get("candidate_state") == "archived",
            -(x.get("research_priority") or 0),
            -(x.get("momentum_score") or 0),
            x.get("company", "").lower(),
        )
    )

    PROS.write_text(json.dumps(ordered, indent=2, ensure_ascii=False), encoding="utf-8")
    PROSJS.write_text("window.OLD_FIELD_PROSPECT_DATA = " + json.dumps(ordered, ensure_ascii=False) + ";\n", encoding="utf-8")
    STATUS.write_text(json.dumps(status, indent=2), encoding="utf-8")
    STATUSJS.write_text("window.OLD_FIELD_FEED_STATUS = " + json.dumps(status) + ";\n", encoding="utf-8")
    PROCESSED.write_text(json.dumps(processed, indent=2), encoding="utf-8")

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--local-zip")
    parser.add_argument("--source-date")
    args = parser.parse_args()

    api_key = os.environ.get("COMPANIES_HOUSE_API_KEY", "").strip()
    if not api_key:
        raise SystemExit(
            "COMPANIES_HOUSE_API_KEY is required. Add it as a GitHub Actions repository secret "
            "so current SIC, status and registered-office data can be enriched before prospects are retained."
        )

    existing = jread(PROS, [])
    status = jread(STATUS, {})
    processed = jread(PROCESSED, [])

    processed_dates = {x.get("date") for x in processed if x.get("date")}
    latest_processed = max(processed_dates) if processed_dates else status.get("latest_processed_date")

    session = requests.Session()
    session.headers["User-Agent"] = "OldfieldAdvisoryProspectIntelligence/3.1"

    master = {p["company_number"]: p for p in existing if p.get("company_number")}

    if args.local_zip:
        if not args.source_date:
            raise SystemExit("--source-date required with --local-zip")
        queue = [{
            "name": Path(args.local_zip).name,
            "date": args.source_date,
            "url": None,
            "local": Path(args.local_zip),
        }]
    else:
        files = discover(session)
        queue = [
            f for f in files
            if f["date"] not in processed_dates
            and (latest_processed is None or f["date"] > latest_processed)
        ]
        if latest_processed is None and queue:
            queue = [queue[-1]]

    tmp = ROOT / ".tmp_downloads"
    tmp.mkdir(exist_ok=True)

    total_new = 0
    total_refreshed = 0
    total_archived_by_profile = 0
    latest_item = None
    latest_summary = None

    for item in queue:
        latest_item = item
        path = item.get("local") or tmp / item["name"]

        if not item.get("local"):
            print("Downloading", item["name"])
            download(session, item["url"], path)

        print("Processing", item["name"])
        all_rows, prescreen_rows, summary = process_daily_zip(path, item["date"])
        latest_summary = summary

        all_by_company = {r["company_number"]: r for r in all_rows}
        for company_number, old in master.items():
            if company_number in all_by_company:
                old["last_filing_seen_date"] = item["date"]

        new_candidates = 0
        refreshed_candidates = 0
        sector_rejected = 0
        inactive_rejected = 0
        integrity_rejected = 0

        for fresh in prescreen_rows:
            company_number = fresh["company_number"]
            old = master.get(company_number)
            fresh = merge_financial_refresh(fresh, old)

            profile = fetch_company_profile(session, company_number, api_key)
            apply_current_profile(fresh, profile)
            eligible, reason = profile_eligibility(fresh)

            if not eligible:
                if "status" in reason.lower():
                    inactive_rejected += 1
                elif "integrity" in reason.lower():
                    integrity_rejected += 1
                else:
                    sector_rejected += 1
                # Existing prospects are retained as archive/history rather than deleted.
                if old:
                    old.update(fresh)
                    old["candidate_state"] = "archived"
                    old["archived_reason"] = reason
                    old["gate_status"] = "research"
                    old["gate_reason"] = reason
                    old["latest_screen_pass"] = False
                    master[company_number] = old
                continue

            psc_payload = fetch_company_psc(session, company_number, api_key)
            officers_payload = fetch_company_officers(session, company_number, api_key)
            apply_control_data(fresh, psc_payload, officers_payload)

            fresh["first_seen_feed_date"] = old.get("first_seen_feed_date") if old else item["date"]
            fresh["last_triggered_feed_date"] = item["date"]
            fresh["last_filing_seen_date"] = item["date"]
            fresh["trigger_count"] = int(old.get("trigger_count") or 0) + 1 if old else 1
            fresh["candidate_state"] = "active"
            fresh["archived_reason"] = None
            fresh["latest_screen_pass"] = True
            fresh["gate_status"] = "research"
            fresh["gate_reason"] = reason
            fresh["gate_basis"] = "current_company_profile"
            fresh["research_priority"] = (fresh.get("momentum_score") or 0) + 10

            if old:
                refreshed_candidates += 1
            else:
                new_candidates += 1

            master[company_number] = fresh

        newly_archived = archive_stale(master, item["date"])

        entry = {
            "date": item["date"],
            "file": item["name"],
            **summary,
            "new_candidates": new_candidates,
            "refreshed_candidates": refreshed_candidates,
            "sector_or_geo_rejected_after_profile": sector_rejected,
            "inactive_rejected_after_profile": inactive_rejected,
            "integrity_rejected_after_profile": integrity_rejected,
            "newly_archived": newly_archived,
            "status": "processed",
            "processed_at_utc": datetime.now(timezone.utc).isoformat(),
        }
        processed.append(entry)
        processed_dates.add(item["date"])

        total_new += new_candidates
        total_refreshed += refreshed_candidates
        total_archived_by_profile += sector_rejected + inactive_rejected + integrity_rejected

        if not item.get("local"):
            path.unlink(missing_ok=True)

        print(json.dumps(entry, indent=2))

    # Backfill or refresh current profile fields for the existing retained master,
    # even when there is no newer daily ZIP. This is what fixes the current live 75.
    backfilled, backfill_archived = enrich_existing_master(master, session, api_key)

    active_total = sum(1 for p in master.values() if p.get("candidate_state") != "archived")
    archived_total = sum(1 for p in master.values() if p.get("candidate_state") == "archived")

    if latest_item and latest_summary:
        status.update({
            "latest_processed_date": latest_item["date"],
            "latest_processed_file": latest_item["name"],
            "latest_source_filings": latest_summary["filings"],
            "latest_unique_companies": latest_summary["unique_companies"],
            "latest_screened_candidates": latest_summary["financial_prescreen_candidates"],
            "latest_candidates_total": total_new + total_refreshed,
            "latest_research_candidates": total_new + total_refreshed,
            "latest_new_candidates": total_new,
            "latest_refreshed_candidates": total_refreshed,
            "latest_discarded_after_screen": max(
                0,
                latest_summary["unique_companies"] - latest_summary["financial_prescreen_candidates"]
            ),
        })

    status.update({
        "automation_enabled": True,
        "source_name": "Companies House daily accounts + current company profile API",
        "source_index_url": INDEX_URL,
        "profile_enrichment_enabled": True,
        "profile_backfilled_or_refreshed": backfilled,
        "profile_archived_after_enrichment": backfill_archived + total_archived_by_profile,
        "retained_master_total": len(master),
        "active_candidate_total": active_total,
        "archived_candidate_total": archived_total,
        "retention_rule_days": RETENTION_DAYS,
        "processed_files": processed[-30:],
        "last_run_result": (
            f"Feed refresh complete. {total_new} new prospects, {total_refreshed} refreshed. "
            f"{backfilled} existing records had Companies House identity / ownership data backfilled or refreshed. "
            "Location, status, sector and accounting year end come from the current company profile; "
            "principal-contact suggestions come from current PSC and officer records."
        ),
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
    })

    write(list(master.values()), status, processed)

    if not queue:
        print("No newer daily ZIP. Current-profile enrichment/backfill still completed.")

    return 0

if __name__ == "__main__":
    raise SystemExit(main())
