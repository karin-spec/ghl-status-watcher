#!/usr/bin/env python3
"""
GHL Status -> Slack watcher.

Polls the official GoHighLevel status page (Better Stack powered) and posts a
formatted, Claude-summarized message to Slack for every genuinely new incident
or incident update.

Official sources used (no scraping):
  - https://status.gohighlevel.com/feed.rss    (primary event stream)
  - https://status.gohighlevel.com/index.json  (structured enrichment)

Design rules:
  - HighLevel's text is the source of truth. Claude summarizes only.
  - Anything Claude infers is printed under an explicit "AI assessment" label.
  - Deduplication is aggressive: GUID + content hash + near-duplicate check.
  - Failures never cause duplicate posts: state is only advanced after a
    successful Slack delivery.

Usage:
  python3 ghl_watcher.py              # normal run
  python3 ghl_watcher.py --dry-run    # print what would be posted, post nothing
  python3 ghl_watcher.py --test-slack # post one test message to Slack
  python3 ghl_watcher.py --demo       # post one example of each message format
  python3 ghl_watcher.py --seed       # mark everything current as seen, post nothing
"""

import argparse
import difflib
import hashlib
import html as html_mod
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import parsedate_to_datetime

# --------------------------------------------------------------------------
# Configuration (all overridable with environment variables)
# --------------------------------------------------------------------------

STATUS_BASE = os.environ.get("STATUS_PAGE_URL", "https://status.gohighlevel.com").rstrip("/")
RSS_URL = f"{STATUS_BASE}/feed.rss"
JSON_URL = f"{STATUS_BASE}/index.json"

SLACK_WEBHOOK_URL = os.environ.get("SLACK_WEBHOOK_URL", "").strip()
ANTHROPIC_API_KEY = os.environ.get("ANTHROPIC_API_KEY", "").strip()
ANTHROPIC_MODEL = os.environ.get("ANTHROPIC_MODEL", "claude-sonnet-5").strip()

STATE_FILE = os.environ.get("STATE_FILE", "state.json")

# Ignore anything published more than this many hours ago. Stops a flood if the
# watcher was switched off for a week and then switched back on.
LOOKBACK_HOURS = int(os.environ.get("LOOKBACK_HOURS", "72"))

# Hard cap on Slack posts per run. Anything above this is marked as seen and
# skipped, with one summary line posted instead.
MAX_POSTS_PER_RUN = int(os.environ.get("MAX_POSTS_PER_RUN", "10"))

# Two update bodies this similar (0-1) are treated as the same update.
NEAR_DUPLICATE_RATIO = float(os.environ.get("NEAR_DUPLICATE_RATIO", "0.97"))

# Post a Slack warning after this many consecutive failed polls.
FAILURE_ALERT_AFTER = int(os.environ.get("FAILURE_ALERT_AFTER", "3"))

HTTP_TIMEOUT = int(os.environ.get("HTTP_TIMEOUT", "25"))
USER_AGENT = "ghl-status-watcher/1.0 (+internal ops automation)"

STATE_VERSION = 1
MAX_SEEN_KEYS = 800
MAX_BODIES_PER_INCIDENT = 40


def log(msg):
    print(f"[{datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%S')}Z] {msg}", flush=True)


# --------------------------------------------------------------------------
# HTTP helpers (stdlib only, with retries)
# --------------------------------------------------------------------------

def http_get(url, retries=3, backoff=3):
    last_err = None
    for attempt in range(1, retries + 1):
        try:
            req = urllib.request.Request(url, headers={
                "User-Agent": USER_AGENT,
                "Accept": "*/*",
                "Cache-Control": "no-cache",
            })
            with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as resp:
                return resp.read()
        except Exception as e:  # noqa: BLE001 - we want to retry on anything
            last_err = e
            log(f"  GET {url} failed (attempt {attempt}/{retries}): {e}")
            if attempt < retries:
                time.sleep(backoff * attempt)
    raise last_err


def http_post_json(url, payload, extra_headers=None, retries=3, backoff=3):
    body = json.dumps(payload).encode("utf-8")
    headers = {"Content-Type": "application/json", "User-Agent": USER_AGENT}
    if extra_headers:
        headers.update(extra_headers)
    last_err = None
    for attempt in range(1, retries + 1):
        try:
            req = urllib.request.Request(url, data=body, headers=headers, method="POST")
            with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT) as resp:
                return resp.status, resp.read().decode("utf-8", "replace")
        except urllib.error.HTTPError as e:
            detail = e.read().decode("utf-8", "replace")[:500]
            last_err = RuntimeError(f"HTTP {e.code}: {detail}")
            log(f"  POST {url} failed (attempt {attempt}/{retries}): {last_err}")
            # 4xx other than 429 will not fix themselves - stop early.
            if 400 <= e.code < 500 and e.code != 429:
                raise last_err
        except Exception as e:  # noqa: BLE001
            last_err = e
            log(f"  POST {url} failed (attempt {attempt}/{retries}): {e}")
        if attempt < retries:
            time.sleep(backoff * attempt)
    raise last_err


# --------------------------------------------------------------------------
# Text helpers
# --------------------------------------------------------------------------

TAG_RE = re.compile(r"<[^>]+>")
LINK_RE = re.compile(r'<a\s[^>]*href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', re.I | re.S)
WS_RE = re.compile(r"[ \t]+")
MULTINL_RE = re.compile(r"\n{3,}")


def html_to_text(raw, slack_links=True):
    """Turn the HTML body from the feed into readable text."""
    if not raw:
        return ""
    text = raw

    # Pull links out first and park them behind placeholders, otherwise the
    # tag stripper below would eat Slack's own <url|label> syntax.
    parked = []

    def park(match):
        href = html_mod.unescape(match.group(1)).strip()
        label = html_mod.unescape(TAG_RE.sub("", match.group(2))).strip() or href
        parked.append(f"<{href}|{label}>" if slack_links else f"{label} ({href})")
        return f"\x00LINK{len(parked) - 1}\x00"

    text = LINK_RE.sub(park, text)
    text = re.sub(r"<br\s*/?>", "\n", text, flags=re.I)
    text = re.sub(r"</(p|div|li|h[1-6])>", "\n", text, flags=re.I)
    text = re.sub(r"<li[^>]*>", "\n• ", text, flags=re.I)
    text = TAG_RE.sub("", text)
    text = html_mod.unescape(text)
    for idx, replacement in enumerate(parked):
        text = text.replace(f"\x00LINK{idx}\x00", replacement)
    text = WS_RE.sub(" ", text)
    text = MULTINL_RE.sub("\n\n", text)
    return text.strip()


def normalize(text):
    """Aggressive normalization used for duplicate detection only."""
    t = html_to_text(text, slack_links=False).lower()
    t = re.sub(r"https?://\S+", " ", t)
    t = re.sub(r"[^a-z0-9 ]+", " ", t)
    t = re.sub(r"\s+", " ", t)
    return t.strip()


def truncate(text, limit):
    if text is None:
        return ""
    text = str(text)
    return text if len(text) <= limit else text[: limit - 1].rstrip() + "…"


# --------------------------------------------------------------------------
# Source 1: the official RSS feed (primary event stream)
# --------------------------------------------------------------------------

def _tag(el, name):
    for child in el:
        if child.tag.lower().endswith(name):
            return child
    return None


def _text(el, name):
    child = _tag(el, name)
    return (child.text or "").strip() if child is not None and child.text else ""


def parse_rss(raw_bytes):
    """Parse Better Stack RSS 2.0 into a normalized list of events."""
    root = ET.fromstring(raw_bytes)
    channel = root.find("channel")
    if channel is None:
        channel = root
    items = []
    for node in channel.iter():
        if not node.tag.lower().endswith("item") and not node.tag.lower().endswith("entry"):
            continue
        title = _text(node, "title")
        link = _text(node, "link")
        if not link:
            link_el = _tag(node, "link")
            if link_el is not None:
                link = link_el.attrib.get("href", "")
        body_raw = _text(node, "description") or _text(node, "summary") or _text(node, "content")
        guid = _text(node, "guid") or _text(node, "id") or link
        pub_raw = _text(node, "pubdate") or _text(node, "published") or _text(node, "updated")
        published = None
        if pub_raw:
            try:
                published = parsedate_to_datetime(pub_raw)
            except Exception:  # noqa: BLE001
                try:
                    published = datetime.fromisoformat(pub_raw.replace("Z", "+00:00"))
                except Exception:  # noqa: BLE001
                    published = None
        if published is not None and published.tzinfo is None:
            published = published.replace(tzinfo=timezone.utc)

        incident_id = ""
        m = re.search(r"/incident/(\d+)", link or guid or "")
        if m:
            incident_id = m.group(1)
        elif link:
            incident_id = link.rstrip("/").split("/")[-1]

        items.append({
            "guid": guid,
            "title": title,
            "body_html": body_raw,
            "body_text": html_to_text(body_raw),
            "body_plain": html_to_text(body_raw, slack_links=False),
            "link": link or STATUS_BASE,
            "incident_id": incident_id,
            "published": published or datetime.now(timezone.utc),
        })
    return items


# --------------------------------------------------------------------------
# Source 2: the official JSON API (structured enrichment)
# --------------------------------------------------------------------------

def fetch_enrichment():
    """
    Pull /index.json and return a lookup keyed by status report id.

    This is best-effort. If it fails, the watcher still works from RSS alone -
    it just has fewer official fields to show.
    """
    try:
        raw = http_get(JSON_URL, retries=2)
        doc = json.loads(raw)
    except Exception as e:  # noqa: BLE001
        log(f"  enrichment unavailable ({e}) - continuing with RSS only")
        return {}, None

    included = doc.get("included") or []
    page_state = ((doc.get("data") or {}).get("attributes") or {}).get("aggregate_state")

    resources = {}
    reports = {}
    for obj in included:
        otype = obj.get("type")
        attrs = obj.get("attributes") or {}
        if otype == "status_page_resource":
            resources[str(obj.get("id"))] = attrs.get("public_name") or ""
        elif otype == "status_report":
            reports[str(obj.get("id"))] = {
                "title": attrs.get("title") or "",
                "report_type": attrs.get("report_type") or "",
                "starts_at": attrs.get("starts_at"),
                "ends_at": attrs.get("ends_at"),
                "aggregate_state": attrs.get("aggregate_state") or "",
                "affected_resources": attrs.get("affected_resources") or [],
            }

    for rid, rep in reports.items():
        names = []
        for ar in rep["affected_resources"]:
            name = resources.get(str(ar.get("status_page_resource_id")), "")
            state = ar.get("status") or ""
            if name:
                names.append(f"{name} ({state})" if state else name)
        rep["affected_names"] = names
    return reports, page_state


def classify_official(item, report):
    """
    Decide which Slack template to use, using official structured data first.
    Returns one of: new_incident | update | resolved | maintenance
    """
    title_body = f"{item['title']} {item['body_plain']}".lower()

    is_maintenance = False
    is_resolved = False

    if report:
        rtype = (report.get("report_type") or "").lower()
        if rtype == "maintenance":
            is_maintenance = True
        if report.get("ends_at"):
            is_resolved = True
        if (report.get("aggregate_state") or "").lower() == "maintenance":
            is_maintenance = True

    # Text fallbacks for signals the JSON API does not expose (e.g. once a
    # report has scrolled out of the active list).
    if not is_maintenance and re.search(r"\b(scheduled|planned)\s+maintenance\b|\bmaintenance window\b", title_body):
        is_maintenance = True
    if re.search(r"\bmaintenance (has been )?completed\b", title_body):
        is_maintenance, is_resolved = True, True
    if re.search(r"\b(resolved|has been resolved|is now resolved|fully restored|back to normal|recovered)\b", title_body):
        is_resolved = True

    if is_maintenance:
        return "maintenance"
    if is_resolved:
        return "resolved"
    return "update"  # caller upgrades to new_incident when it is the first update


# --------------------------------------------------------------------------
# Claude analysis
# --------------------------------------------------------------------------

SYSTEM_PROMPT = """You summarize official status-page updates from HighLevel (GoHighLevel) for an internal Slack channel.

HARD RULES — these override everything else:
1. HighLevel's text is the only source of truth. Never add technical facts, causes, timelines, component names, numbers, or impact that are not in the provided text.
2. If HighLevel did not state something, return null for that field. Do not guess and do not fill gaps.
3. Never soften or exaggerate severity relative to what HighLevel wrote.
4. Anything that is your own inference goes ONLY in "ai_assessment" and must read as an inference, not a fact. Leave it null unless it genuinely helps a team decide what to do.
5. Preserve any concrete instructions, workarounds, or steps HighLevel gave. Do not drop them from the summary.

Reply with a single JSON object and nothing else. No markdown, no code fences.

Schema:
{
  "phase": "investigating" | "identified" | "monitoring" | "update" | "resolved" | "maintenance_scheduled" | "maintenance_in_progress" | "maintenance_completed" | "unclear",
  "summary": "2-4 sentences in plain English, faithful to the original meaning. Keep any workaround steps.",
  "affected_area_stated": "the service/component HighLevel named, or null",
  "impact_stated": "the user-facing impact HighLevel explicitly described, or null",
  "action_for_users_stated": "what HighLevel told users to do, or null",
  "timing_stated": "any date/time/window HighLevel stated, or null",
  "ai_assessment": "one short sentence of your own inference, or null",
  "severity": "low" | "medium" | "high" | "unknown"
}"""


def analyze_with_claude(item, report, template):
    """Ask Claude for a faithful summary. Returns (analysis_dict, ai_used_bool)."""
    fallback = {
        "phase": "unclear",
        "summary": truncate(item["body_text"], 1200) or "(no message body published)",
        "affected_area_stated": None,
        "impact_stated": None,
        "action_for_users_stated": None,
        "timing_stated": None,
        "ai_assessment": None,
        "severity": "unknown",
    }

    if not ANTHROPIC_API_KEY:
        log("  ANTHROPIC_API_KEY not set - posting HighLevel's text verbatim")
        return fallback, False

    official_block = {
        "incident_title": item["title"],
        "update_text": item["body_plain"],
        "published_at_utc": item["published"].astimezone(timezone.utc).isoformat(),
        "status_page_url": item["link"],
        "detected_template": template,
    }
    if report:
        official_block["official_report_type"] = report.get("report_type")
        official_block["official_aggregate_state"] = report.get("aggregate_state")
        official_block["official_affected_components"] = report.get("affected_names")
        official_block["official_ends_at"] = report.get("ends_at")

    user_msg = (
        "Here is the official HighLevel status update. Summarize it per the rules.\n\n"
        + json.dumps(official_block, indent=2, default=str)
    )

    payload = {
        "model": ANTHROPIC_MODEL,
        "max_tokens": 1200,
        "system": SYSTEM_PROMPT,
        "messages": [{"role": "user", "content": user_msg}],
    }

    try:
        status, body = http_post_json(
            "https://api.anthropic.com/v1/messages",
            payload,
            extra_headers={
                "x-api-key": ANTHROPIC_API_KEY,
                "anthropic-version": "2023-06-01",
            },
            retries=3,
        )
        data = json.loads(body)
        # Response content is a list of blocks; take text blocks only.
        text = "".join(
            blk.get("text", "")
            for blk in data.get("content", [])
            if blk.get("type") == "text"
        ).strip()
        text = re.sub(r"^```(?:json)?|```$", "", text.strip(), flags=re.M).strip()
        start, end = text.find("{"), text.rfind("}")
        if start == -1 or end == -1:
            raise ValueError(f"no JSON object in model reply: {text[:200]}")
        parsed = json.loads(text[start : end + 1])
        for key in fallback:
            parsed.setdefault(key, fallback[key])
        if not parsed.get("summary"):
            parsed["summary"] = fallback["summary"]
        return parsed, True
    except Exception as e:  # noqa: BLE001
        log(f"  Claude analysis failed ({e}) - falling back to HighLevel's raw text")
        return fallback, False


# --------------------------------------------------------------------------
# Slack message construction
# --------------------------------------------------------------------------

PHASE_LABEL = {
    "investigating": "Investigating",
    "identified": "Identified",
    "monitoring": "Monitoring",
    "update": "Update posted",
    "resolved": "Resolved",
    "maintenance_scheduled": "Scheduled",
    "maintenance_in_progress": "In progress",
    "maintenance_completed": "Completed",
    "unclear": "See official status page",
}

STATE_LABEL = {
    "downtime": "Outage",
    "degraded": "Degraded performance",
    "maintenance": "Maintenance",
    "operational": "Operational",
}


def _section(text):
    return {"type": "section", "text": {"type": "mrkdwn", "text": truncate(text, 2900)}}


def build_message(item, report, analysis, template, ai_used):
    title = item["title"] or "(untitled incident)"
    url = item["link"]
    phase = analysis.get("phase") or "unclear"

    # Status line: prefer official structured state, fall back to the phase.
    official_state = ""
    if report:
        if report.get("ends_at"):
            official_state = "Resolved"
        else:
            official_state = STATE_LABEL.get((report.get("aggregate_state") or "").lower(), "")
    phase_label = PHASE_LABEL.get(phase, "See official status page")
    if template == "resolved":
        status_line = "Resolved"
    elif phase == "unclear":
        status_line = official_state or "Ongoing — see official status page"
    elif official_state and official_state.lower() != phase_label.lower():
        status_line = f"{official_state} — {phase_label}"
    else:
        status_line = official_state or phase_label

    affected = ""
    if report and report.get("affected_names"):
        affected = ", ".join(report["affected_names"])
    elif analysis.get("affected_area_stated"):
        affected = analysis["affected_area_stated"]

    headers = {
        "new_incident": "🚨 *GHL STATUS — INVESTIGATING*",
        "update": "⚠️ *GHL STATUS UPDATE*",
        "resolved": "✅ *GHL STATUS — RESOLVED*",
        "maintenance": "🔧 *GHL MAINTENANCE*",
    }
    if template == "new_incident" and phase in ("identified", "monitoring"):
        headers["new_incident"] = f"🚨 *GHL STATUS — {PHASE_LABEL[phase].upper()}*"

    blocks = [_section(headers[template])]

    if template == "maintenance":
        blocks.append(_section(f"*Maintenance:*\n{title}"))
        when = analysis.get("timing_stated")
        if not when and report:
            when = _format_window(report.get("starts_at"), report.get("ends_at"))
        if when:
            blocks.append(_section(f"*Date/time:*\n{when}"))
        blocks.append(_section(f"*What HighLevel says:*\n{analysis['summary']}"))
        if analysis.get("impact_stated"):
            blocks.append(_section(f"*Expected impact:*\n{analysis['impact_stated']}"))
    elif template == "resolved":
        blocks.append(_section(f"*Issue:*\n{title}"))
        blocks.append(_section("*Status:*\nResolved"))
        if affected:
            blocks.append(_section(f"*Affected area:*\n{affected}"))
        blocks.append(_section(f"*Resolution:*\n{analysis['summary']}"))
    elif template == "new_incident":
        blocks.append(_section(f"*Issue:*\n{title}"))
        blocks.append(_section(f"*Status:*\n{status_line}"))
        if affected:
            blocks.append(_section(f"*Affected area:*\n{affected}"))
        blocks.append(_section(f"*What HighLevel says:*\n{analysis['summary']}"))
        if analysis.get("impact_stated"):
            blocks.append(_section(f"*Impact:*\n{analysis['impact_stated']}"))
    else:  # update
        blocks.append(_section(f"*Issue:*\n{title}"))
        blocks.append(_section(f"*Status:*\n{status_line}"))
        if affected:
            blocks.append(_section(f"*Affected area:*\n{affected}"))
        blocks.append(_section(f"*Latest update from HighLevel:*\n{analysis['summary']}"))
        if analysis.get("impact_stated"):
            blocks.append(_section(f"*Impact:*\n{analysis['impact_stated']}"))

    if analysis.get("action_for_users_stated"):
        blocks.append(_section(f"*What HighLevel asks users to do:*\n{analysis['action_for_users_stated']}"))

    if ai_used and analysis.get("ai_assessment"):
        blocks.append(_section(f"_*AI assessment:* {analysis['ai_assessment']}_"))

    blocks.append(_section(f"🔗 *Official status:*\n<{url}|{url}>"))

    published = item["published"].astimezone(timezone.utc).strftime("%d %b %Y, %H:%M UTC")
    footer = f"Published by HighLevel {published}"
    if not ai_used:
        footer += " · AI summary unavailable, showing HighLevel's text as published"
    blocks.append({"type": "context", "elements": [{"type": "mrkdwn", "text": footer}]})
    blocks.append({"type": "divider"})

    plain_header = re.sub(r"[*_]", "", headers[template])
    return {
        "text": f"{plain_header}: {truncate(title, 120)}",
        "blocks": blocks,
    }


def _format_window(starts_at, ends_at):
    def fmt(v):
        if not v:
            return None
        try:
            return datetime.fromisoformat(str(v).replace("Z", "+00:00")).astimezone(
                timezone.utc
            ).strftime("%d %b %Y, %H:%M UTC")
        except Exception:  # noqa: BLE001
            return str(v)
    a, b = fmt(starts_at), fmt(ends_at)
    if a and b:
        return f"{a} → {b}"
    return a or b or None


def post_to_slack(payload, dry_run=False):
    if dry_run:
        log("  DRY RUN - would post:")
        for blk in payload["blocks"]:
            if blk["type"] == "section":
                print("    | " + blk["text"]["text"].replace("\n", "\n    | "))
            elif blk["type"] == "context":
                print("    | " + blk["elements"][0]["text"])
        return True
    if not SLACK_WEBHOOK_URL:
        raise RuntimeError("SLACK_WEBHOOK_URL is not set")
    status, body = http_post_json(SLACK_WEBHOOK_URL, payload, retries=3)
    if body.strip() != "ok":
        raise RuntimeError(f"Slack returned {status}: {body[:300]}")
    return True


def post_plain(text, dry_run=False):
    return post_to_slack({"text": text, "blocks": [_section(text)]}, dry_run=dry_run)


# --------------------------------------------------------------------------
# State
# --------------------------------------------------------------------------

def load_state():
    if not os.path.exists(STATE_FILE):
        return {"version": STATE_VERSION, "initialized": False, "seen": [],
                "bodies": {}, "consecutive_failures": 0, "failure_alerted": False,
                "last_success": None}
    try:
        with open(STATE_FILE, "r", encoding="utf-8") as fh:
            state = json.load(fh)
    except Exception as e:  # noqa: BLE001
        log(f"state file unreadable ({e}); treating as first run to avoid duplicate posts")
        return {"version": STATE_VERSION, "initialized": False, "seen": [],
                "bodies": {}, "consecutive_failures": 0, "failure_alerted": False,
                "last_success": None}
    state.setdefault("version", STATE_VERSION)
    state.setdefault("initialized", bool(state.get("seen")))
    state.setdefault("seen", [])
    state.setdefault("bodies", {})
    state.setdefault("consecutive_failures", 0)
    state.setdefault("failure_alerted", False)
    state.setdefault("last_success", None)
    return state


def save_state(state):
    state["seen"] = state["seen"][-MAX_SEEN_KEYS:]
    for incident_id in list(state["bodies"].keys()):
        state["bodies"][incident_id] = state["bodies"][incident_id][-MAX_BODIES_PER_INCIDENT:]
    if len(state["bodies"]) > 200:
        for incident_id in list(state["bodies"].keys())[:-200]:
            del state["bodies"][incident_id]
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(state, fh, indent=2, sort_keys=True)
        fh.write("\n")
    os.replace(tmp, STATE_FILE)


def content_key(item):
    raw = f"{item['incident_id']}|{normalize(item['body_html'])}"
    return "c:" + hashlib.sha256(raw.encode("utf-8")).hexdigest()[:32]


def is_duplicate(item, state):
    seen = set(state["seen"])
    if f"g:{item['guid']}" in seen:
        return True, "same feed GUID"
    if content_key(item) in seen:
        return True, "identical update text"
    norm = normalize(item["body_html"])
    if not norm:
        return True, "empty update body"
    for previous in state["bodies"].get(item["incident_id"], []):
        ratio = difflib.SequenceMatcher(None, norm, previous).ratio()
        if ratio >= NEAR_DUPLICATE_RATIO:
            return True, f"near-identical to a previous update ({ratio:.2%})"
    return False, ""


def mark_seen(item, state):
    state["seen"].append(f"g:{item['guid']}")
    state["seen"].append(content_key(item))
    state["bodies"].setdefault(item["incident_id"], []).append(normalize(item["body_html"]))


# --------------------------------------------------------------------------
# Demo / test payloads
# --------------------------------------------------------------------------

DEMO_ITEMS = [
    ("new_incident", "Workflows delayed for some sub-accounts",
     "We are investigating reports of delayed workflow execution affecting a subset of "
     "sub-accounts. Contacts are entering workflows but actions are firing late. "
     "We will share an update within 30 minutes."),
    ("update", "Workflows delayed for some sub-accounts",
     "We have identified the cause as a backlog in our queue processing layer and are "
     "scaling additional workers. Delays of up to 15 minutes may continue while the "
     "backlog drains. No data has been lost."),
    ("resolved", "Workflows delayed for some sub-accounts",
     "The backlog has fully cleared and workflow execution has returned to normal "
     "latency for all sub-accounts. We will publish a summary in the coming days."),
    ("maintenance", "Scheduled database maintenance — LC Phone",
     "We will be performing scheduled maintenance on LC Phone infrastructure on "
     "12 March 2026 between 02:00 and 04:00 UTC. Outbound calling may be briefly "
     "unavailable for up to 5 minutes during the window."),
]


def run_demo(dry_run):
    log("Posting one example of each message format …")
    for template, title, body in DEMO_ITEMS:
        item = {
            "guid": "demo", "title": title, "body_html": body,
            "body_text": body, "body_plain": body,
            "link": f"{STATUS_BASE}/incident/000000", "incident_id": "000000",
            "published": datetime.now(timezone.utc),
        }
        analysis, ai_used = analyze_with_claude(item, None, template)
        post_to_slack(build_message(item, None, analysis, template, ai_used), dry_run=dry_run)
        log(f"  posted demo: {template}")
        time.sleep(1)
    log("Demo complete.")


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description="GoHighLevel status -> Slack watcher")
    ap.add_argument("--dry-run", action="store_true", help="print instead of posting to Slack")
    ap.add_argument("--seed", action="store_true", help="mark everything current as seen, post nothing")
    ap.add_argument("--test-slack", action="store_true", help="post a single test message and exit")
    ap.add_argument("--demo", action="store_true", help="post one example of each message format")
    args = ap.parse_args()

    if args.test_slack:
        post_plain(
            "✅ *GHL status watcher connected.* This channel will receive automatic "
            f"updates from <{STATUS_BASE}|the official HighLevel status page>.",
            dry_run=args.dry_run,
        )
        log("Test message sent.")
        return 0

    if args.demo:
        run_demo(args.dry_run)
        return 0

    state = load_state()

    # ---- fetch the official feed -----------------------------------------
    try:
        items = parse_rss(http_get(RSS_URL))
        log(f"Fetched {len(items)} items from {RSS_URL}")
    except Exception as e:  # noqa: BLE001
        state["consecutive_failures"] += 1
        log(f"Could not read the status feed: {e} "
            f"(consecutive failures: {state['consecutive_failures']})")
        if (state["consecutive_failures"] >= FAILURE_ALERT_AFTER
                and not state["failure_alerted"] and not args.dry_run):
            try:
                post_plain(
                    "⚠️ *GHL status watcher cannot reach the status feed.*\n"
                    f"It has failed {state['consecutive_failures']} times in a row. "
                    f"Automatic updates are paused until it recovers — check "
                    f"<{STATUS_BASE}|the status page> manually in the meantime.",
                )
                state["failure_alerted"] = True
            except Exception as se:  # noqa: BLE001
                log(f"  could not send failure alert: {se}")
        save_state(state)
        return 0  # exit 0 so the scheduler keeps running

    if state["consecutive_failures"] and state.get("failure_alerted") and not args.dry_run:
        try:
            post_plain("✅ *GHL status watcher is back online* and reading the official feed again.")
        except Exception:  # noqa: BLE001
            pass
    state["consecutive_failures"] = 0
    state["failure_alerted"] = False
    # Date only, on purpose: this keeps state.json byte-identical between runs
    # on quiet days, so the scheduler commits at most one heartbeat per day.
    state["last_success"] = datetime.now(timezone.utc).strftime("%Y-%m-%d")

    reports, _page_state = fetch_enrichment()

    # ---- first run: adopt current state without posting -------------------
    if not state["initialized"] or args.seed:
        for item in items:
            mark_seen(item, state)
        state["initialized"] = True
        save_state(state)
        log(f"Seeded {len(items)} existing items as already-seen. No Slack messages sent.")
        if not args.seed and not args.dry_run:
            try:
                post_plain(
                    "✅ *GHL status watcher is live.* From now on, new incidents, updates "
                    "and resolutions from "
                    f"<{STATUS_BASE}|the official HighLevel status page> will appear here "
                    "automatically. Existing items were not re-posted."
                )
            except Exception as e:  # noqa: BLE001
                log(f"  startup message failed: {e}")
        return 0

    # ---- select genuinely new items --------------------------------------
    cutoff = datetime.now(timezone.utc) - timedelta(hours=LOOKBACK_HOURS)
    candidates = []
    for item in items:
        dup, reason = is_duplicate(item, state)
        if dup:
            log(f"  skip [{truncate(item['title'], 50)}] — {reason}")
            continue
        if item["published"] < cutoff:
            log(f"  skip [{truncate(item['title'], 50)}] — older than {LOOKBACK_HOURS}h, marking seen")
            mark_seen(item, state)
            continue
        candidates.append(item)

    candidates.sort(key=lambda i: i["published"])

    if not candidates:
        save_state(state)
        log("No new updates. Nothing posted.")
        return 0

    overflow = []
    if len(candidates) > MAX_POSTS_PER_RUN:
        overflow = candidates[MAX_POSTS_PER_RUN:]
        candidates = candidates[:MAX_POSTS_PER_RUN]

    log(f"{len(candidates)} new update(s) to post.")

    posted = 0
    for item in candidates:
        report = reports.get(item["incident_id"])
        if not report:
            for rep in reports.values():
                if rep.get("title") and rep["title"].strip().lower() == item["title"].strip().lower():
                    report = rep
                    break

        template = classify_official(item, report)
        if template == "update":
            known = state["bodies"].get(item["incident_id"])
            if not known:
                template = "new_incident"

        analysis, ai_used = analyze_with_claude(item, report, template)
        message = build_message(item, report, analysis, template, ai_used)

        try:
            post_to_slack(message, dry_run=args.dry_run)
        except Exception as e:  # noqa: BLE001
            # Do NOT mark as seen - it will be retried on the next run.
            log(f"  Slack post failed for [{truncate(item['title'], 50)}]: {e}")
            log("  leaving it unseen so the next run retries it. Stopping here to keep order.")
            break

        mark_seen(item, state)
        save_state(state)  # persist after every successful post
        posted += 1
        log(f"  posted [{template}] {truncate(item['title'], 60)}")
        time.sleep(1)  # be polite to Slack

    if overflow:
        for item in overflow:
            mark_seen(item, state)
        try:
            post_plain(
                f"ℹ️ *{len(overflow)} further HighLevel status update(s)* were published in the "
                f"same window and were not posted individually to avoid flooding this channel. "
                f"See <{STATUS_BASE}|the official status page> for the full list."
            , dry_run=args.dry_run)
        except Exception as e:  # noqa: BLE001
            log(f"  overflow notice failed: {e}")

    save_state(state)
    log(f"Done. {posted} message(s) posted.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)
