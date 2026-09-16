#!/usr/bin/env python3
from __future__ import annotations

import argparse
import io
import json
import re
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
FILE_RE = re.compile(r'href=["\']([^"\']*Accounts_Bulk_Data-(\d{4}-\d{2}-\d{2})\.zip)["\']', re.I)
COMPANY_RE = re.compile(r'_((?:SC|NI|OC|SO|LP|SL|FC|NF|NL|IP|SP|RS)?[A-Z0-9]{5,8})_(\d{8})(?:\.|_)', re.I)

RETENTION_DAYS = 30

EXCLUDE = [
    "accountant","accountancy","bookkeeping","tax adviser","tax advisor",
    "financial adviser","financial advisor","wealth management","insurance broker",
    "solicitor","law firm","car dealer","used car","motor dealer","motor retail",
    "restaurant","cafe","public house","hotel","nursery","childcare",
    "residential care","nursing care","charity","membership organisation",
    "membership organization","property investment","property letting",
    "investment holding"
]

SECTORS = {
    "Construction": [
        "construction","contractor","building contractor","civil engineering",
        "roofing","plumbing","electrical installation","groundworks","fit out","interiors"
    ],
    "Wholesale": [
        "wholesale","wholesaler","distribution","distributor",
        "trade supplier","merchant","importer"
    ],
    "Manufacturing": [
        "manufactur","engineering","fabricat","machining","industrial equipment","factory"
    ],
    "Business services": [
        "business services","managed services","it services","software services",
        "commercial cleaning","facilities management","b2b marketing",
        "digital agency","logistics services"
    ]
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

def classify(company, activity):
    combined = f"{company or ''} {activity or ''}".lower()
    for term in EXCLUDE:
        if term in combined:
            return "Excluded", term
    for sector, terms in SECTORS.items():
        if any(term in combined for term in terms):
            return sector, None
    return "Other / unknown", None

def england_wales(company_number):
    n = (company_number or "").upper()
    return not n.startswith(("SC", "NI", "SO", "SL"))

def company_no(filename):
    match = COMPANY_RE.search(filename)
    return match.group(1).upper() if match else None

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
            ordered[0][1] if ordered else None
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

    sector, hard_exclusion = classify(company, activity)
    ew_fit = england_wales(cn)

    scale = (
        (emp_cur is not None and emp_cur >= 10)
        or (na_cur is not None and na_cur >= 500000)
    )
    strong_scale = (
        (emp_cur is not None and emp_cur >= 20)
        or (na_cur is not None and na_cur >= 1000000)
    )

    if not ew_fit:
        gate_status, gate_reason, gate_basis = "auto_excluded", "Outside England & Wales", "geography"
    elif hard_exclusion:
        gate_status, gate_reason, gate_basis = "auto_excluded", f"Automatic exclusion matched: {hard_exclusion}", "hard_exclusion"
    elif not scale:
        gate_status, gate_reason, gate_basis = "hold", "Insufficient current scale evidence", "scale"
    elif sector != "Other / unknown" and momentum_score >= 25:
        gate_status, gate_reason, gate_basis = "research", f"{sector} + scale evidence + momentum", "target_sector"
    elif sector == "Other / unknown" and strong_scale and momentum_score >= 85:
        gate_status, gate_reason, gate_basis = "research", "Exceptional momentum and scale; sector needs manual confirmation", "unknown_sector"
    else:
        gate_status, gate_reason, gate_basis = "hold", "Insufficient sector or momentum evidence for morning research", "screen"

    return {
        "company": company,
        "company_number": cn,
        "period_end": period_end,
        "location": "Location needs confirmation",
        "postcode": None,
        "registered_office": None,
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
        "profile_sector": sector if sector != "Excluded" else "Other / unknown",
        "principal_activity": activity,
        "ew_fit": ew_fit,
        "scale_fit": "£1m+ likely proxy" if scale else "Scale not evidenced",
        "scale_fit_bool": scale,
        "owner_managed_proxy": bool(directors) and len(directors) <= 3,
        "gate_status": gate_status,
        "gate_reason": gate_reason,
        "gate_basis": gate_basis,
        "research_priority": momentum_score + (5 if sector in SECTORS else 0),
    }

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
    retained = [r for r in unique_rows if r.get("gate_status") == "research"]

    return unique_rows, retained, {
        "filings": parsed_documents,
        "unique_companies": len(unique_rows),
        "parse_failures": parse_failures,
        "screened_candidates": len(retained),
        "research_candidates": len(retained),
        "discarded_after_screen": max(0, len(unique_rows) - len(retained)),
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

def merge_enrichment(fresh, old):
    if not old:
        return fresh
    for key in ["location", "postcode", "registered_office", "profile_sector", "principal_activity", "directors"]:
        if (not fresh.get(key) or fresh.get(key) in {"Location needs confirmation", "Other / unknown"}) and old.get(key):
            fresh[key] = old[key]
    return fresh

def write(master_rows, status, processed):
    ordered = sorted(
        master_rows,
        key=lambda x: (
            x.get("candidate_state") == "archived",
            -(x.get("research_priority") or 0),
            -(x.get("momentum_score") or 0),
            x.get("company", "").lower()
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

    existing = jread(PROS, [])
    status = jread(STATUS, {})
    processed = jread(PROCESSED, [])

    processed_dates = {x.get("date") for x in processed if x.get("date")}
    latest_processed = max(processed_dates) if processed_dates else status.get("latest_processed_date")

    session = requests.Session()
    session.headers["User-Agent"] = "OldfieldAdvisoryProspectIntelligence/2.0 public bulk-data refresh"

    if args.local_zip:
        if not args.source_date:
            raise SystemExit("--source-date required with --local-zip")
        queue = [{"name": Path(args.local_zip).name, "date": args.source_date, "url": None, "local": Path(args.local_zip)}]
    else:
        files = discover(session)
        queue = [
            f for f in files
            if f["date"] not in processed_dates
            and (latest_processed is None or f["date"] > latest_processed)
        ]
        if latest_processed is None and queue:
            queue = [queue[-1]]

    if not queue:
        print("No newer Companies House daily ZIP is available.")
        return 0

    master = {p["company_number"]: p for p in existing if p.get("company_number")}
    tmp = ROOT / ".tmp_downloads"
    tmp.mkdir(exist_ok=True)

    for item in queue:
        if item["date"] in processed_dates:
            continue

        path = item.get("local") or tmp / item["name"]
        if not item.get("local"):
            print("Downloading", item["name"])
            download(session, item["url"], path)

        print("Processing", item["name"])
        all_rows, qualifying_rows, summary = process_daily_zip(path, item["date"])

        all_by_company = {r["company_number"]: r for r in all_rows}
        for company_number, old in master.items():
            if company_number in all_by_company:
                old["last_filing_seen_date"] = item["date"]
                old["latest_screen_pass"] = all_by_company[company_number].get("gate_status") == "research"

        new_candidates = 0
        refreshed_candidates = 0

        for fresh in qualifying_rows:
            company_number = fresh["company_number"]
            old = master.get(company_number)

            fresh = merge_enrichment(fresh, old)
            fresh["first_seen_feed_date"] = old.get("first_seen_feed_date") if old else item["date"]
            fresh["last_triggered_feed_date"] = item["date"]
            fresh["last_filing_seen_date"] = item["date"]
            fresh["trigger_count"] = int(old.get("trigger_count") or 0) + 1 if old else 1
            fresh["candidate_state"] = "active"
            fresh["archived_reason"] = None
            fresh["latest_screen_pass"] = True

            if old:
                refreshed_candidates += 1
            else:
                new_candidates += 1

            master[company_number] = fresh

        newly_archived = archive_stale(master, item["date"])
        active_total = sum(1 for p in master.values() if p.get("candidate_state") != "archived")
        archived_total = sum(1 for p in master.values() if p.get("candidate_state") == "archived")

        entry = {
            "date": item["date"],
            "file": item["name"],
            **summary,
            "new_candidates": new_candidates,
            "refreshed_candidates": refreshed_candidates,
            "newly_archived": newly_archived,
            "retained_master_total": len(master),
            "active_candidate_total": active_total,
            "archived_candidate_total": archived_total,
            "status": "processed",
            "processed_at_utc": datetime.now(timezone.utc).isoformat(),
        }
        processed.append(entry)
        processed_dates.add(item["date"])

        status.update({
            "automation_enabled": True,
            "source_name": "Companies House Free Accounts Data Product",
            "source_index_url": INDEX_URL,
            "latest_processed_date": item["date"],
            "latest_processed_file": item["name"],
            "latest_source_filings": summary["filings"],
            "latest_unique_companies": summary["unique_companies"],
            "latest_screened_candidates": summary["screened_candidates"],
            "latest_candidates_total": summary["research_candidates"],
            "latest_research_candidates": summary["research_candidates"],
            "latest_new_candidates": new_candidates,
            "latest_refreshed_candidates": refreshed_candidates,
            "latest_discarded_after_screen": summary["discarded_after_screen"],
            "latest_newly_archived": newly_archived,
            "retained_master_total": len(master),
            "active_candidate_total": active_total,
            "archived_candidate_total": archived_total,
            "retention_rule_days": RETENTION_DAYS,
            "processed_files": processed[-30:],
            "last_run_result": (
                f"Processed {item['name']}: {summary['filings']:,} filing documents, "
                f"{new_candidates} new prospect candidates, {refreshed_candidates} refreshed, "
                f"{summary['discarded_after_screen']:,} discarded after the automatic screen. "
                "Raw filing records were not retained."
            ),
            "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        })

        write(list(master.values()), status, processed)

        if not item.get("local"):
            path.unlink(missing_ok=True)

        print(json.dumps(entry, indent=2))

    return 0

if __name__ == "__main__":
    raise SystemExit(main())
