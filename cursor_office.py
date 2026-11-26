#!/usr/bin/env python3
"""
cursor_office.py - A tiny Game Boy-style "office" that visualizes your AI agents.

Each little person in the office is a chat/agent that was active in the last 24 hours,
read from the local transcript files on this machine. BOTH tools are shown together:

  * Cursor agents      (~/.cursor/projects/*/agent-transcripts/)
  * Claude Code agents (~/.claude/projects/*/)

Hover any worker to see which tool it belongs to (teal = Cursor, coral = Claude Code),
along with its live token/spend/model, its task, and the last instruction you sent it.

  * WORKING agents sit at a desk and type on their computer.
  * WAITING agents (finished a turn and waiting for your reply) hang out in the
    kitchen, make coffee and grab a snack.

Click a person to open an overlay with their task, latest thinking/response and the
last tool they used. From there you can open that chat's transcript file in Cursor or
copy the session id (to find it under "Previous Chats" in Cursor).

------------------------------------------------------------------------------------
HOW TO RUN  (no dependencies, just Python 3.8+)

    python3 cursor_office.py

Then open the URL it prints (default http://127.0.0.1:8787). It auto-opens a browser.

By default it shows agents from ALL your Cursor + Claude Code projects/roots on this
machine (each worker is tagged with its project). You can scope it to a single root, or
hide a whole source, if you prefer.

Useful flags:
    python3 cursor_office.py --hours 48        # widen the activity window
    python3 cursor_office.py --port 9000       # change port
    python3 cursor_office.py --project my-app  # only this root/project (substring match)
    python3 cursor_office.py --list-projects   # list roots with active sessions, then exit
    python3 cursor_office.py --no-cursor       # hide Cursor agents (Claude Code only)
    python3 cursor_office.py --no-claude       # hide Claude Code agents (Cursor only)
    python3 cursor_office.py --demo            # add fake workers so the office is lively
    python3 cursor_office.py --demo-working 12 # TEST HOOK: N synthetic WORKING agents
                                               #   (implies --demo) -- verifies desk scaling
    python3 cursor_office.py --holiday halloween   # force a holiday theme (demo/verify):
                                               #   halloween|christmas|hanukkah|thanksgiving|newyear|none
    python3 cursor_office.py --date 2026-12-24 # pretend it's this date when auto-theming
    python3 cursor_office.py --no-open         # don't auto-open the browser

The office also AUTO-THEMES around holidays: from 7 days before through 3 days after
Halloween, Thanksgiving (US), Hanukkah, Christmas and New Year's, the live scene shows
that holiday's decorations. Overlapping windows (e.g. Christmas + New Year's) layer both.

------------------------------------------------------------------------------------
SHARING WITH YOUR TEAM

This is a single self-contained file. Drop it in a GitHub gist (or send the file) and
your teammates just run `python3 cursor_office.py`. It reads *their own* local Cursor
data from ~/.cursor/projects/*/agent-transcripts/ and Claude Code data from
~/.claude/projects/* -- nothing is uploaded anywhere and the server only listens on
localhost.
"""

import argparse
import hashlib
import json
import logging
import os
import re
import sqlite3
import sys
import threading
import time
import unicodedata
import webbrowser
from datetime import date, datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import quote, unquote, urlparse

logger = logging.getLogger(__name__)

# --------------------------------------------------------------------------------------
# Transcript discovery + parsing
# --------------------------------------------------------------------------------------

CURSOR_PROJECTS_DIR = os.path.expanduser("~/.cursor/projects")
# Claude Code stores one .jsonl per chat under ~/.claude/projects/<encoded-cwd>/,
# with any Task subagents in a sibling <session-uuid>/subagents/*.jsonl -- the same
# shape as Cursor, so both sources feed the SAME office (each worker is tagged with
# its `source` so the UI can tell a Cursor agent from a Claude Code agent).
CLAUDE_PROJECTS_DIR = os.path.expanduser("~/.claude/projects")

# Cursor's own display name for a chat (the title shown in the sidebar) is NOT stored
# in the .jsonl transcript -- it lives in Cursor's global SQLite state DB, under the
# cursorDiskKV table at key "composerData:<uuid>", whose JSON value carries a "name"
# field (e.g. "PR review for Tomer"). The <uuid> is exactly the transcript's filename
# uuid. We read that so each office worker is labelled with the real session name
# instead of the first line of its opening prompt. The DB is large and concurrently
# written by Cursor, so we open it READ-ONLY and cache per-uuid with a short TTL rather
# than touching it on every poll. Any failure falls back silently to the old behaviour.
CURSOR_GLOBAL_DB = os.path.expanduser(
    "~/Library/Application Support/Cursor/User/globalStorage/state.vscdb"
)
_SESSION_NAME_CACHE = {}          # uuid -> (name_or_"", fetched_at)
_SESSION_NAME_LOCK = threading.Lock()
_SESSION_NAME_TTL = 30            # seconds a resolved (or missing) name is trusted


def cursor_session_name(uuid):
    """Return Cursor's own sidebar display name for a chat `uuid`, or "" if none.

    Looks up cursorDiskKV["composerData:<uuid>"].name in Cursor's global state DB,
    read-only, with a small per-uuid TTL cache so we don't reopen the (large) DB on
    every poll. Returns "" on any error / missing name so callers fall back cleanly.
    """
    now = time.time()
    with _SESSION_NAME_LOCK:
        hit = _SESSION_NAME_CACHE.get(uuid)
        if hit and (now - hit[1]) < _SESSION_NAME_TTL:
            return hit[0]
    name = ""
    try:
        if os.path.isfile(CURSOR_GLOBAL_DB):
            uri = "file:%s?mode=ro" % quote(CURSOR_GLOBAL_DB)
            conn = sqlite3.connect(uri, uri=True, timeout=0.5)
            try:
                cur = conn.execute(
                    "SELECT json_extract(value,'$.name') FROM cursorDiskKV WHERE key=?",
                    ("composerData:" + uuid,),
                )
                row = cur.fetchone()
                if row and isinstance(row[0], str):
                    name = row[0].strip()
            finally:
                conn.close()
    except Exception:
        name = ""   # fall back to the prompt-derived title
    with _SESSION_NAME_LOCK:
        _SESSION_NAME_CACHE[uuid] = (name, now)
    return name


# Cursor's sidebar spinner stays on while a chat's own turn runs OR while any of its
# (background) subagents has a run in flight -- even after the parent wrote turn_ended.
# The persisted marker for "run in flight" is composerData:<uuid>.unfinishedRunAt (on
# parents AND subagents): Cursor sets it to the run's start time (with status "aborted",
# so a crash reads as aborted) when a run starts and clears it (status -> "completed"/
# "none") when the run finishes. A crash leaves it set forever, so it is only trusted
# together with recent activity.
#
# A PARENT chat's .jsonl lags its turn: Cursor appends the turn's records when the turn
# ends (sometimes flushing the user prompt a few seconds in), and a brand-new chat has no
# transcript dir at all until its first turn ends. So for parents the transcript alone
# reads "turn ended" (or nothing) for the whole turn; unfinishedRunAt is the live signal.
_RUN_FLAG_CACHE = {}              # uuid -> (info dict | None no record, fetched_at)
_RUN_FLAG_LOCK = threading.Lock()
_RUN_FLAG_TTL = 5


def _open_cursor_db():
    uri = "file:%s?mode=ro" % quote(CURSOR_GLOBAL_DB)
    return sqlite3.connect(uri, uri=True, timeout=0.5)


def cursor_run_info(uuids):
    """Return {uuid: info|None} from composerData, where info is
    ``{"run_at": run start (epoch s) or 0.0 when idle, "status": str, "parent":
    parentComposerId or "", "name": str, "folder": workspace fsPath or "", "sub_ids": [subagent
    composer ids], "sub_type": subagentTypeName or ""}``. None = no record / DB unreadable, so
    callers fall back to transcript heuristics. Read-only, TTL-cached."""
    now = time.time()
    out, missing = {}, []
    with _RUN_FLAG_LOCK:
        for u in uuids:
            hit = _RUN_FLAG_CACHE.get(u)
            if hit and (now - hit[1]) < _RUN_FLAG_TTL:
                out[u] = hit[0]
            else:
                missing.append(u)
    if not missing:
        return out
    fetched = dict.fromkeys(missing)
    try:
        if os.path.isfile(CURSOR_GLOBAL_DB):
            conn = _open_cursor_db()
            try:
                keys = ["composerData:" + u for u in missing]
                cur = conn.execute(
                    "SELECT key, json_extract(value,'$.unfinishedRunAt'), json_extract(value,'$.status'),"
                    " json_extract(value,'$.subagentInfo.parentComposerId'),"
                    " json_extract(value,'$.name'),"
                    " json_extract(value,'$.workspaceIdentifier.uri.fsPath'),"
                    " json_extract(value,'$.subagentComposerIds'),"
                    " json_extract(value,'$.subagentInfo.subagentTypeName') FROM cursorDiskKV "
                    "WHERE key IN (%s)" % ",".join("?" * len(keys)), keys)
                for key, run_at, status, parent, name, folder, sub_ids, sub_type in cur.fetchall():
                    try:
                        sub_ids = json.loads(sub_ids) if isinstance(sub_ids, str) else []
                    except ValueError:
                        sub_ids = []
                    if run_at is None:
                        started = 0.0
                    elif isinstance(run_at, (int, float)) and run_at > 0:
                        started = run_at / 1000.0
                    else:
                        started = 1.0   # set but unparseable: in flight, start unknown
                    fetched[key[len("composerData:"):]] = {
                        "run_at": started,
                        "status": status if isinstance(status, str) else "",
                        "parent": parent if isinstance(parent, str) else "",
                        "name": name.strip() if isinstance(name, str) else "",
                        "folder": folder if isinstance(folder, str) else "",
                        "sub_ids": [s for s in sub_ids if isinstance(s, str) and _UUID_RE.match(s)]
                                   if isinstance(sub_ids, list) else [],
                        "sub_type": sub_type if isinstance(sub_type, str) else "",
                    }
            finally:
                conn.close()
    except Exception:
        logger.debug("composerData run-state lookup failed", exc_info=True)
        fetched = dict.fromkeys(missing)
    with _RUN_FLAG_LOCK:
        for u, v in fetched.items():
            _RUN_FLAG_CACHE[u] = (v, now)
    out.update(fetched)
    return out


def cursor_runs_in_flight(uuids):
    """Return {uuid: True|False|None} from composerData.unfinishedRunAt (None = no record /
    DB unreadable, so callers fall back to transcript heuristics)."""
    return {u: (None if info is None else bool(info["run_at"]))
            for u, info in cursor_run_info(uuids).items()}


def cursor_run_finished(uuid):
    """True when Cursor's own record says the chat's run is over (no unfinishedRunAt and
    status completed/none). Cursor sometimes flushes a turn's user prompt but never its
    closing records, leaving a transcript that reads "in progress" long after the turn."""
    info = cursor_run_info([uuid]).get(uuid)
    return bool(info) and not info["run_at"] and info["status"] in ("completed", "none")


# Which composers Cursor is writing to right now. cursorDiskKV is declared
# "key UNIQUE ON CONFLICT REPLACE", so every write re-inserts its row at a new, highest
# rowid: the rowid tail is a cheap recency index (a covering scan, values never read).
# A live turn writes bubbleId:<composer>:<bubble> rows as it streams.
_UUID_RE = re.compile(r"^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$")
_DB_TAIL_LOCK = threading.Lock()
_DB_TAIL = {"at": 0.0, "max_rowid": 0}
_DB_TAIL_SEEN = {}                # composer uuid -> (last write observed at | 0.0 unknown, added_at)
_DB_TAIL_ROWS = 3000
_DB_TAIL_TTL = 5


def cursor_recent_writers():
    """{composer uuid: wall time a DB write to it was last observed (0.0 = before this
    process started watching)}, kept for WORKING_STALE_CAP_SECONDS so a run sitting in one
    long tool call stays a candidate after its rows scroll out of the tail."""
    now = time.time()
    with _DB_TAIL_LOCK:
        if (now - _DB_TAIL["at"]) < _DB_TAIL_TTL:
            return {u: s for u, (s, _a) in _DB_TAIL_SEEN.items()}
        _DB_TAIL["at"] = now
        last_max = _DB_TAIL["max_rowid"]
    rows = []
    try:
        if os.path.isfile(CURSOR_GLOBAL_DB):
            conn = _open_cursor_db()
            try:
                rows = conn.execute(
                    "SELECT rowid, key FROM cursorDiskKV WHERE rowid > ? ORDER BY rowid DESC LIMIT ?",
                    (last_max, _DB_TAIL_ROWS)).fetchall()
            finally:
                conn.close()
    except Exception:
        logger.debug("cursorDiskKV tail scan failed", exc_info=True)
    seen_at = now if last_max else 0.0
    with _DB_TAIL_LOCK:
        for rowid, key in rows:
            parts = key.split(":", 2) if isinstance(key, str) else []
            if len(parts) < 2 or parts[0] == "agentKv" or not _UUID_RE.match(parts[1]):
                continue
            prev = _DB_TAIL_SEEN.get(parts[1])
            _DB_TAIL_SEEN[parts[1]] = (max(seen_at, prev[0] if prev else 0.0), prev[1] if prev else now)
        if rows:
            _DB_TAIL["max_rowid"] = max(_DB_TAIL["max_rowid"], rows[0][0])
        for u in [u for u, (s, a) in _DB_TAIL_SEEN.items()
                  if (now - max(s, a)) > WORKING_STALE_CAP_SECONDS]:
            del _DB_TAIL_SEEN[u]
        return {u: s for u, (s, _a) in _DB_TAIL_SEEN.items()}


def cursor_live_runs():
    """{uuid: latest activity time} for Cursor composers (parents or subagents) whose run is
    in flight per composerData.unfinishedRunAt and active within WORKING_STALE_CAP_SECONDS,
    plus {uuid: info} for each (see cursor_run_info)."""
    writers = cursor_recent_writers()
    if not writers:
        return {}, {}
    infos = cursor_run_info(list(writers))
    now = time.time()
    live, live_infos = {}, {}
    for u, info in infos.items():
        if not info or not info["run_at"]:
            continue
        last = max(info["run_at"], writers.get(u, 0.0))
        if (now - last) <= WORKING_STALE_CAP_SECONDS:
            live[u] = last
            live_infos[u] = info
    return live, live_infos


# "Waiting on you": a chat blocked on a question for the user. Two strengths:
#   * "form"    -- an unanswered multiple-choice form (Cursor's ask_question tool / Claude
#                  Code's AskUserQuestion). Overrides WORKING: the agent can't go on without you.
#   * "message" -- the turn ended and the last assistant message ends with a question.
#
# Cursor keeps the form as a tool-call bubble, cursorDiskKV["bubbleId:<composer>:<bubble>"]:
# toolFormerData.name == "ask_question", and toolFormerData.additionalData.status is
# "pending" until the user acts ("submitted" + a result once answered, "cancelled" with
# userDecision "rejected" when skipped). The chat's run is NOT in flight while the form waits
# (unfinishedRunAt cleared, status "completed") and a brand-new chat has no transcript yet,
# so this is the only signal. A form still streaming in an in-flight run reads
# toolFormerData.status "loading" with no additionalData.status.
# A pending bubble only counts while it is the chat's latest ask_question with no later user
# bubble (type 1): typing a reply in the chat instead of using the form leaves it "pending".
ASK_RECENT_SECONDS = 6 * 3600     # only chats in flight or ended this recently are checked
_ASK_BUBBLE_ROWS = 12             # newest bubble rows (by rowid = last write) inspected per chat
_ASK_CACHE = {}                   # uuid -> (write stamp, checked_at, form dict | None)
_ASK_LOCK = threading.Lock()
_ASK_TTL = 30
_ASK_PREVIEW_CHARS = 160


def _fingerprint(*parts):
    """Stable short hash used as question_id -- never the question text itself."""
    return hashlib.sha1("\x1f".join(str(p) for p in parts).encode("utf-8")).hexdigest()[:16]


def _iso_epoch(s):
    try:
        return datetime.strptime(s[:19], "%Y-%m-%dT%H:%M:%S").replace(tzinfo=timezone.utc).timestamp()
    except Exception:
        return 0.0


def _short_preview(s, n=_ASK_PREVIEW_CHARS):
    s = WS_RE.sub(" ", (s or "").replace("\n", " ")).strip()
    return s if len(s) <= n else s[: n - 1].rstrip() + "\u2026"


def _form_preview(params):
    """(preview, question_count) from an ask_question params JSON string."""
    try:
        p = json.loads(params) if isinstance(params, str) else (params or {})
    except Exception:
        return "", 0
    qs = [q for q in (p.get("questions") or []) if isinstance(q, dict)]
    first = next((q.get("prompt") or q.get("question") or "" for q in qs), "")
    head = (p.get("title") or "").strip()
    text = (head + ": " + first) if head and first else (head or first)
    return _short_preview(_clean_text(text)), len(qs)


def _pending_form_from_rows(uuid, rows, in_flight):
    """rows: [(bubble_id, type, createdAt, tool name, tool status, additionalData.status,
    params, toolCallId)] for a chat's newest bubbles. Returns the form dict or None."""
    asks = [r for r in rows if r[3] == "ask_question"]
    if not asks:
        return None
    ask = max(asks, key=lambda r: r[2] or "")
    bubble_id, _t, created, _n, status, ui_status, params, call_id = ask
    pending = ui_status == "pending" or (ui_status is None and status == "loading" and in_flight)
    if not pending:
        return None
    if any(r[1] == 1 and (r[2] or "") > (created or "") for r in rows):
        return None
    preview, count = _form_preview(params)
    return {"asking": "form", "asked_at": _iso_epoch(created or ""),
            "question_id": _fingerprint(uuid, bubble_id, call_id or ""),
            "question_preview": preview, "question_count": count}


def cursor_pending_forms(uuids, live_ids=()):
    """{uuid: form dict | None} for Cursor chats blocked on an unanswered ask_question form.

    One read-only connection per batch; each chat costs a covering-index range scan over its
    bubble keys plus value reads for its newest _ASK_BUBBLE_ROWS rows. A result is reused
    until the DB tail shows a new write to that chat (cursor_recent_writers) or _ASK_TTL
    passes, so a steady office re-reads almost nothing."""
    now = time.time()
    writers = cursor_recent_writers()
    live_ids = set(live_ids)
    out, todo = {}, []
    with _ASK_LOCK:
        for u in uuids:
            stamp = (writers.get(u), u in live_ids)
            hit = _ASK_CACHE.get(u)
            if hit and hit[0] == stamp and (now - hit[1]) < _ASK_TTL:
                out[u] = hit[2]
            else:
                todo.append((u, stamp))
    if not todo:
        return out
    fetched = {}
    t0 = time.time()
    try:
        if os.path.isfile(CURSOR_GLOBAL_DB):
            conn = _open_cursor_db()
            try:
                for u, stamp in todo:
                    lo, hi = "bubbleId:%s:" % u, "bubbleId:%s;" % u
                    ids = [r[0] for r in conn.execute(
                        "SELECT rowid FROM cursorDiskKV WHERE key >= ? AND key < ? "
                        "ORDER BY rowid DESC LIMIT ?", (lo, hi, _ASK_BUBBLE_ROWS))]
                    rows = []
                    if ids:
                        rows = conn.execute(
                            "SELECT substr(key, ?), json_extract(value,'$.type'),"
                            " json_extract(value,'$.createdAt'),"
                            " json_extract(value,'$.toolFormerData.name'),"
                            " json_extract(value,'$.toolFormerData.status'),"
                            " json_extract(value,'$.toolFormerData.additionalData.status'),"
                            " CASE WHEN json_extract(value,'$.toolFormerData.name')='ask_question'"
                            "  THEN json_extract(value,'$.toolFormerData.params') END,"
                            " json_extract(value,'$.toolFormerData.toolCallId')"
                            " FROM cursorDiskKV WHERE rowid IN (%s)" % ",".join("?" * len(ids)),
                            [len(lo) + 1] + ids).fetchall()
                    fetched[u] = (stamp, _pending_form_from_rows(u, rows, stamp[1]))
            finally:
                conn.close()
    except Exception:
        logger.debug("ask_question bubble lookup failed", exc_info=True)
    logger.debug("ask_question lookup: %d chats, %d pending, %d ms", len(todo),
                 sum(1 for _s, f in fetched.values() if f), int((time.time() - t0) * 1000))
    with _ASK_LOCK:
        for u, (stamp, form) in fetched.items():
            _ASK_CACHE[u] = (stamp, now, form)
        for u in [u for u, v in _ASK_CACHE.items() if (now - v[1]) > WORKING_STALE_CAP_SECONDS]:
            del _ASK_CACHE[u]
    for u, _stamp in todo:
        out[u] = fetched.get(u, (None, None))[1]
    return out


# "Listening": a chat subscribed to Slack / GitHub / Linear / Origin events through the
# cursor-subscriptions MCP tools. Cursor keeps no local registry (it is server-side), but
# every call and every delivered event is a bubble row, cursorDiskKV["bubbleId:<c>:<b>"]:
#   * toolFormerData.name "mcp-cursor-subscriptions-<tool>"; params JSON .tools[0].parameters
#     (a JSON string of the call args); result JSON .result -> .content[0].text (JSON) =
#     {subscriptionId, expiresAt, subscription{source,type,scope,repo,pullNumber,branch,
#     channelId,...}, subscriptionMetadata{channelName,...}} or {error}. unsubscribe ->
#     {closed}; list_subscriptions -> {subscriptions:[{subscriptionId, subscriptionArgs,
#     subscriptionMetadata, expiresAt, ...}]}, the authoritative set at that moment.
#   * a delivered event is a user bubble with eventNotification{source, action, headline,
#     url, detail}. Slack headlines read "<sender> in #<channel>"; `detail` is message text
#     and is never read.
# Active = subscribed, not expired, not unsubscribed, not auto-closed (a PR merged/closed
# without keepWatchingAfterClose; default-branch CI after its first result), replayed in
# bubble order from the latest list_subscriptions snapshot. Only chats whose transcript
# shows a real cursor-subscriptions call are looked up; each keeps a rowid high-water mark
# so a refresh only reads rows written since (rewrites get a new rowid). The first fill of
# a chat can read 100k+ bubbles, so it always runs on a background worker.
_LISTEN_CALL_RE = re.compile(rb'"namespace"\s*:\s*"cursor-subscriptions"')
_LISTEN_SCAN = {}                 # transcript path -> (bytes scanned, found)
_LISTEN_SCAN_LOCK = threading.Lock()
_LISTEN = {}                      # uuid -> {"hw", "recs", "ready", "checked", "stamp", "queued"}
_LISTEN_LOCK = threading.Lock()
_LISTEN_WAKE = threading.Condition(_LISTEN_LOCK)
_LISTEN_QUEUE = []
_LISTEN_WORKER = {"thread": None}
_LISTEN_TTL = 60                  # re-read a chat at least this often even without a seen write
_LISTEN_INLINE_BUDGET = 0.25      # seconds of incremental reads allowed inside one request
_LISTEN_MAX = 8
_LISTEN_PREFIX = "mcp-cursor-subscriptions-"

# CI on a repo's default branch is one-shot. Neither the subscribe result nor the CI/PR
# events carry the default branch, so it comes from a local clone of the repo: its origin
# remote in .git/config gives the repo, refs/remotes/origin/HEAD the default branch. Clones
# are found by a shallow walk of the home dir (up to _REPO_SCAN_DEPTH levels, never inside
# a repo), rebuilt on a background thread every _REPO_HEAD_TTL. The usual trunk names in
# _FALLBACK_DEFAULT_BRANCHES count too. Either way a CI subscription only drops once a
# result for that branch has arrived.
_FALLBACK_DEFAULT_BRANCHES = ("main", "master", "dev")
_REPO_SCAN_DEPTH = 3
_REPO_SCAN_SKIP = {"Library", "Applications", "Pictures", "Music", "Movies", "node_modules",
                   "venv", "env", "site-packages", "dist", "build"}
_REPO_HEAD_TTL = 600
_REPO_HEAD = {"map": {}, "at": 0.0, "building": False}
_REPO_HEAD_LOCK = threading.Lock()
_REMOTE_SLUG_RE = re.compile(r"[:/]([^/:\s]+)/([^/\s]+?)(?:\.git)?/?$")


def _git_common_dir(repo_dir):
    """The .git dir holding config + refs (a worktree's .git file points at its gitdir,
    whose commondir is the main repo's .git)."""
    g = os.path.join(repo_dir, ".git")
    if os.path.isdir(g):
        return g
    try:
        with open(g, "r", encoding="utf-8", errors="replace") as fh:
            gd = fh.read().split("gitdir:", 1)[1].strip()
    except (OSError, IndexError):
        return None
    gd = gd if os.path.isabs(gd) else os.path.normpath(os.path.join(repo_dir, gd))
    try:
        with open(os.path.join(gd, "commondir"), "r", encoding="utf-8") as fh:
            return os.path.normpath(os.path.join(gd, fh.read().strip()))
    except OSError:
        return gd


def _clone_default_branch(git_dir):
    """(owner/repo lowercased, default branch) for a clone's origin, or None."""
    url = None
    try:
        with open(os.path.join(git_dir, "config"), "r", encoding="utf-8", errors="replace") as fh:
            in_origin = False
            for line in fh:
                s = line.strip()
                if s.startswith("["):
                    in_origin = s.replace(" ", "") in ('[remote"origin"]',)
                elif in_origin and s.startswith("url"):
                    url = s.split("=", 1)[-1].strip()
                    break
        with open(os.path.join(git_dir, "refs", "remotes", "origin", "HEAD"), "r", encoding="utf-8") as fh:
            head = fh.read().strip()
    except OSError:
        return None
    m = _REMOTE_SLUG_RE.search(url or "")
    prefix = "ref: refs/remotes/origin/"
    if not m or not head.startswith(prefix):
        return None
    return ("%s/%s" % (m.group(1), m.group(2))).lower(), head[len(prefix):]


def _scan_default_branches():
    t0 = time.time()
    home = os.path.expanduser("~")
    votes, clones = {}, 0
    stack = [(home, 0)]
    while stack:
        d, depth = stack.pop()
        try:
            entries = os.listdir(d)
        except OSError:
            continue
        if ".git" in entries and d != home:
            clones += 1
            gd = _git_common_dir(d)
            got = _clone_default_branch(gd) if gd else None
            if got:
                votes.setdefault(got[0], {}).setdefault(got[1], 0)
                votes[got[0]][got[1]] += 1
            continue
        if depth >= _REPO_SCAN_DEPTH:
            continue
        for e in entries:
            if e.startswith(".") or e in _REPO_SCAN_SKIP:
                continue
            p = os.path.join(d, e)
            if os.path.isdir(p) and not os.path.islink(p):
                stack.append((p, depth + 1))
    heads = {slug: max(v.items(), key=lambda kv: kv[1])[0] for slug, v in votes.items()}
    with _REPO_HEAD_LOCK:
        _REPO_HEAD.update({"map": heads, "at": time.time(), "building": False})
    logger.debug("default-branch index: %d clones, %d repos, %d ms",
                 clones, len(heads), int((time.time() - t0) * 1000))


def repo_default_branches():
    """{owner/repo: default branch} from local clones; never blocks (a stale or missing
    index is rebuilt in the background and the last one is served meanwhile)."""
    with _REPO_HEAD_LOCK:
        stale = (time.time() - _REPO_HEAD["at"]) > _REPO_HEAD_TTL
        if stale and not _REPO_HEAD["building"]:
            _REPO_HEAD["building"] = True
            threading.Thread(target=_scan_default_branches, daemon=True, name="repo-heads").start()
        return _REPO_HEAD["map"]


def _is_default_branch(repo, branch, heads):
    """A clone's origin/HEAD is fixed at clone time and can lag a later default-branch
    change, so it adds to the trunk names rather than replacing them."""
    known = heads.get(_repo_slug(repo).lower()) if repo else None
    return bool(branch) and (branch == known or branch in _FALLBACK_DEFAULT_BRANCHES)


def _transcript_listens(path):
    """True once the transcript holds a real cursor-subscriptions tool call (tool catalogs
    echoed into prompts don't match). Scans only bytes appended since the last check."""
    try:
        size = os.path.getsize(path)
    except OSError:
        return False
    with _LISTEN_SCAN_LOCK:
        done, found = _LISTEN_SCAN.get(path, (0, False))
    if found and size >= done:
        return True
    if size < done:
        done = 0
    if size == done:
        return found
    start = max(0, done - 64)
    try:
        with open(path, "rb") as fh:
            fh.seek(start)
            found = bool(_LISTEN_CALL_RE.search(fh.read(size - start)))
    except OSError:
        return False
    with _LISTEN_SCAN_LOCK:
        _LISTEN_SCAN[path] = (size, found)
    return found


def _json_or_none(s):
    if not isinstance(s, str) or not s:
        return None
    try:
        return json.loads(s)
    except Exception:
        return None


def _listen_call_args(params):
    p = _json_or_none(params)
    tools = (p or {}).get("tools") if isinstance(p, dict) else None
    if not tools or not isinstance(tools[0], dict):
        return {}
    args = tools[0].get("parameters")
    args = _json_or_none(args) if isinstance(args, str) else args
    return args if isinstance(args, dict) else {}


def _listen_call_result(result):
    r = _json_or_none(result)
    inner = _json_or_none(r.get("result")) if isinstance(r, dict) else None
    try:
        text = inner["content"][0]["text"]
    except Exception:
        return None
    out = _json_or_none(text)
    return out if isinstance(out, dict) else None


_SLACK_HEADLINE_RE = re.compile(r"^(?P<who>.+?) in #(?P<chan>\S+)\s*$")
_SLACK_URL_RE = re.compile(r"/archives/(?P<chan>[A-Z0-9]+)/p(?P<ts>\d{10})(?P<frac>\d+)")
_GH_PR_URL_RE = re.compile(r"github\.com/([^/\s]+/[^/\s]+)/pull/(\d+)")
_CI_HEADLINE_RE = re.compile(r"^CI (?P<result>\w+) on (?P<branch>.+?)\s*$")


def _listen_record(tool_name, status, params, result, created, ev_source, ev_action,
                   ev_headline, ev_url):
    """Reduce one bubble row to the few fields the active-set replay needs. Slack headlines
    are cut down to the sender and channel name here, so nothing else is kept in memory."""
    at = _iso_epoch(created) if isinstance(created, str) else (
        created / 1000.0 if isinstance(created, (int, float)) else 0.0)
    if isinstance(tool_name, str) and tool_name.startswith(_LISTEN_PREFIX):
        if status != "completed":
            return None
        res = _listen_call_result(result)
        if not res or "error" in res:
            return None
        return {"at": at, "tool": tool_name[len(_LISTEN_PREFIX):],
                "args": _listen_call_args(params), "res": res}
    if not ev_source:
        return None
    rec = {"at": at, "event": ev_source, "action": ev_action or "", "url": ev_url or ""}
    if ev_source == "slack":
        m = _SLACK_HEADLINE_RE.match(ev_headline or "")
        if m:
            rec["who"], rec["chan_name"] = m.group("who").strip(), m.group("chan")
        u = _SLACK_URL_RE.search(ev_url or "")
        if u:
            rec["chan"] = u.group("chan")
            rec["ts"] = "%s.%s" % (u.group("ts"), u.group("frac"))
        tm = re.search(r"[?&]thread_ts=([0-9.]+)", ev_url or "")
        rec["thread"] = tm.group(1) if tm else rec.get("ts")
    elif ev_source == "github":
        c = _CI_HEADLINE_RE.match(ev_headline or "")
        if c:
            rec["ci_result"], rec["branch"] = c.group("result").lower(), c.group("branch")
    return rec


def _repo_slug(repo):
    parts = [p for p in re.sub(r"^[a-z]+://", "", str(repo or "")).split("/") if p]
    if parts and "." in parts[0] and len(parts) > 2:
        parts = parts[1:]
    if parts[:1] == ["codebase"]:
        parts = parts[1:]
    return "/".join(parts[:2])


def _listen_sub(sid, args, sub, meta, expires, tool):
    opts = args.get("options") if isinstance(args.get("options"), dict) else {}
    s = dict(args)
    s.update(opts)
    s.update(sub or {})
    s.update({"sid": sid, "meta": meta if isinstance(meta, dict) else {},
              "expires": _iso_epoch(expires) if isinstance(expires, str) else 0.0,
              "keep": bool(args.get("keepWatchingAfterClose")), "tool": tool or "",
              "last_event": 0.0, "senders": [], "chan_name": "", "url": "", "ci": ""})
    if not s.get("source"):
        s["source"] = ("slack" if "slack" in s["tool"] else "github" if "github" in s["tool"]
                       else "linear" if "linear" in s["tool"] else "origin" if "origin" in s["tool"] else "")
    return s


def _listen_event_matches(s, e):
    if e["event"] == "slack":
        if s.get("source") != "slack" or not e.get("chan") or s.get("channelId") != e["chan"]:
            return False
        ts = s.get("threadTs")
        return not ts or ts in (e.get("thread"), e.get("ts"))
    if e["event"] == "github" and s.get("source") == "github":
        if e.get("branch"):
            m = re.search(r"github\.com/([^/\s]+/[^/\s]+)/commit/", e.get("url", ""))
            same_repo = not (m and s.get("repo")) or _repo_slug(s["repo"]).lower() == m.group(1).lower()
            return s.get("type") == "ci" and s.get("branch") == e["branch"] and same_repo
        m = _GH_PR_URL_RE.search(e.get("url", ""))
        if not m or not s.get("repo") or _repo_slug(s["repo"]).lower() != m.group(1).lower():
            return False
        return s.get("scope") != "pr" or str(s.get("pullNumber")) == m.group(2)
    return False


def _listening_from_records(recs, now, heads=None):
    """Replay a chat's subscription calls + events (bubble order) into its active list.
    `heads` ({owner/repo: default branch}) is fetched only if a CI result needs it."""
    subs = {}
    for r in sorted(recs, key=lambda r: r["at"]):
        tool = r.get("tool")
        if tool:
            res, args = r["res"], r["args"]
            if tool.startswith("subscribe_") and res.get("subscriptionId"):
                sid = res["subscriptionId"]
                prev = subs.get(sid)
                subs[sid] = _listen_sub(sid, args, res.get("subscription"),
                                        res.get("subscriptionMetadata"), res.get("expiresAt"), tool)
                if prev:
                    for k in ("last_event", "senders", "chan_name", "url", "ci"):
                        subs[sid][k] = prev[k]
            elif tool == "unsubscribe" and res.get("closed", True):
                subs.pop(args.get("subscriptionId"), None)
            elif tool == "list_subscriptions" and isinstance(res.get("subscriptions"), list):
                snap = {}
                for it in res["subscriptions"]:
                    if not isinstance(it, dict) or not it.get("subscriptionId"):
                        continue
                    sid = it["subscriptionId"]
                    prev = subs.get(sid) or {}
                    sa = it.get("subscriptionArgs") if isinstance(it.get("subscriptionArgs"), dict) else {}
                    s = _listen_sub(sid, {}, sa, it.get("subscriptionMetadata"), it.get("expiresAt"),
                                    prev.get("tool", ""))
                    for k in ("keep", "threadTs", "channelNameContains", "last_event", "senders",
                              "chan_name", "url", "ci"):
                        if k in prev:
                            s[k] = prev[k]
                    snap[sid] = s
                subs = snap
            continue
        for sid, s in list(subs.items()):
            if not _listen_event_matches(s, r):
                continue
            s["last_event"] = max(s["last_event"], r["at"])
            if r.get("url"):
                s["url"] = r["url"]
            if r.get("who") and r["who"] not in s["senders"]:
                s["senders"].append(r["who"])
            if r.get("chan_name"):
                s["chan_name"] = r["chan_name"]
            if r.get("ci_result"):
                s["ci"] = r["ci_result"]
                if heads is None:
                    heads = repo_default_branches()
                if _is_default_branch(s.get("repo"), s.get("branch"), heads):
                    del subs[sid]
            elif (r["event"] == "github" and r["action"] in ("merged", "closed")
                  and s.get("scope") == "pr" and not s["keep"]):
                del subs[sid]
    out = [_listen_entry(s) for s in subs.values() if not s["expires"] or s["expires"] > now]
    out.sort(key=lambda e: (-(e["last_event_at"] or 0), e["kind"], e["label"]))
    return out[:_LISTEN_MAX]


def _listen_entry(s):
    kind, scope = s.get("source") or "github", s.get("scope") or ""
    repo = _repo_slug(s.get("repo")) if s.get("repo") else ""
    detail, url = "", s.get("url") or ""
    if kind == "slack":
        chan = s["meta"].get("channelName") or s.get("chan_name")
        chan = ("#" + chan.lstrip("#")) if chan else ("channel " + str(s.get("channelId") or "?"))
        if s.get("tool") == "subscribe_slack_new_channels" or s.get("type") == "channel_created":
            sub, label = "new_channels", "new Slack channels"
            if s.get("channelNameContains"):
                label += " matching \u201c%s\u201d" % s["channelNameContains"]
        elif s.get("threadTs"):
            sub, label = "thread", "thread in " + chan
        else:
            sub, label = "channel", chan
        who = s["senders"]
        detail = (", ".join(who[:3]) + (" +%d" % (len(who) - 3) if len(who) > 3 else "")) if who else ""
    elif kind in ("github", "origin"):
        if s.get("type") == "ci" or "ci" in s.get("tool", ""):
            sub, label = "ci", "CI on " + str(s.get("branch") or "?")
            detail = repo + (" \u00b7 last: " + s["ci"] if s["ci"] else "")
        elif scope == "pr" or s.get("pullNumber") or s.get("prUrl"):
            num = s.get("pullNumber")
            if not num and s.get("prUrl"):
                m = re.search(r"/pull/(\d+)", s["prUrl"])
                num = m.group(1) if m else "?"
                repo = repo or _repo_slug(s["prUrl"].split("/pull/")[0])
            sub, label = "pr", "PR #%s %s" % (num, repo)
            if kind == "github" and not url and repo:
                url = "https://github.com/%s/pull/%s" % (repo, num)
        elif scope == "author":
            sub, label = "author", "PRs by %s in %s" % (s.get("author") or "?", repo)
        else:
            sub, label = "repo", "PRs in " + repo
    else:
        sub = scope or "issue"
        ref = s.get("issueId") or s.get("teamId") or s.get("projectId") or ""
        label = "Linear " + ("comments on " if "comment" in s.get("tool", "") else "") + (
            ("team " if sub == "team" else "project " if sub == "project" else "") + str(ref))
    return {"kind": kind, "sub": sub, "label": label.strip(), "detail": detail, "url": url,
            "expires_at": s["expires"] or None, "last_event_at": s["last_event"] or None}


_LISTEN_SQL = (
    "SELECT rowid, substr(key, ?), json_extract(value,'$.createdAt'),"
    " json_extract(value,'$.toolFormerData.name'), json_extract(value,'$.toolFormerData.status'),"
    " json_extract(value,'$.toolFormerData.params'), json_extract(value,'$.toolFormerData.result'),"
    " json_extract(value,'$.eventNotification.source'), json_extract(value,'$.eventNotification.action'),"
    " json_extract(value,'$.eventNotification.headline'), json_extract(value,'$.eventNotification.url')"
    " FROM cursorDiskKV WHERE key >= ? AND key < ? AND rowid > ?"
    " AND (instr(value, 'mcp-cursor-subscriptions-') > 0 OR instr(value, '\"eventNotification\"') > 0)")


def _listen_read(conn, uuid, hw):
    """(new high-water mark, {bubble id: record | None}) for rows written after `hw`."""
    top = conn.execute("SELECT max(rowid) FROM cursorDiskKV").fetchone()[0] or 0
    lo, hi = "bubbleId:%s:" % uuid, "bubbleId:%s;" % uuid
    got = {}
    for row in conn.execute(_LISTEN_SQL, (len(lo) + 1, lo, hi, hw)):
        got[row[1]] = _listen_record(*row[3:7], row[2], *row[7:])
    return top, got


def _listen_apply(uuid, hw, got, stamp, now):
    with _LISTEN_LOCK:
        st = _LISTEN.setdefault(uuid, {"hw": 0, "recs": {}, "ready": False, "checked": 0.0,
                                       "stamp": None, "queued": False})
        st["recs"].update(got)
        for k in [k for k, v in st["recs"].items() if v is None]:
            del st["recs"][k]
        st.update({"hw": max(st["hw"], hw), "ready": True, "checked": now, "stamp": stamp})


def _listen_worker():
    while True:
        with _LISTEN_LOCK:
            while not _LISTEN_QUEUE:
                _LISTEN_WAKE.wait()
            uuid, stamp = _LISTEN_QUEUE.pop(0)
            hw = _LISTEN.get(uuid, {}).get("hw", 0)
        t0 = time.time()
        try:
            conn = _open_cursor_db()
            try:
                top, got = _listen_read(conn, uuid, hw)
            finally:
                conn.close()
            _listen_apply(uuid, top, got, stamp, time.time())
            logger.debug("listening fill %s: %d rows, %d ms", uuid, len(got), int((time.time() - t0) * 1000))
        except Exception:
            logger.debug("listening fill failed for %s", uuid, exc_info=True)
        with _LISTEN_LOCK:
            if uuid in _LISTEN:
                _LISTEN[uuid]["queued"] = False


def _listen_enqueue(uuid, stamp):
    """Caller holds _LISTEN_LOCK."""
    st = _LISTEN.setdefault(uuid, {"hw": 0, "recs": {}, "ready": False, "checked": 0.0,
                                   "stamp": None, "queued": False})
    if st["queued"]:
        return
    st["queued"] = True
    _LISTEN_QUEUE.append((uuid, stamp))
    if not _LISTEN_WORKER["thread"]:
        _LISTEN_WORKER["thread"] = threading.Thread(target=_listen_worker, daemon=True,
                                                    name="listening-fill")
        _LISTEN_WORKER["thread"].start()
    _LISTEN_WAKE.notify()


def cursor_listening(paths):
    """{uuid: [listening entry]} for Cursor chats ({uuid: transcript path}). Never blocks on
    a first fill: unready chats are queued for the worker and read [] until it finishes."""
    now = time.time()
    cands = [u for u, p in paths.items() if p and _transcript_listens(p)]
    out = {}
    if not cands or not os.path.isfile(CURSOR_GLOBAL_DB):
        return {u: [] for u in paths}
    writers = cursor_recent_writers()
    inline = []
    with _LISTEN_LOCK:
        for u in cands:
            st = _LISTEN.get(u)
            stamp = writers.get(u)
            if not st or not st["ready"]:
                _listen_enqueue(u, stamp)
            elif not st["queued"] and (st["stamp"] != stamp or (now - st["checked"]) >= _LISTEN_TTL):
                inline.append((u, st["hw"], stamp))
    if inline:
        t0 = time.time()
        try:
            conn = _open_cursor_db()
            try:
                for i, (u, hw, stamp) in enumerate(inline):
                    if time.time() - t0 > _LISTEN_INLINE_BUDGET:
                        with _LISTEN_LOCK:
                            for u2, _hw, s2 in inline[i:]:
                                _listen_enqueue(u2, s2)
                        break
                    top, got = _listen_read(conn, u, hw)
                    _listen_apply(u, top, got, stamp, time.time())
            finally:
                conn.close()
        except Exception:
            logger.debug("listening refresh failed", exc_info=True)
        logger.debug("listening refresh: %d chats, %d ms", len(inline), int((time.time() - t0) * 1000))
    with _LISTEN_LOCK:
        recs = {u: list(_LISTEN[u]["recs"].values()) for u in cands
                if u in _LISTEN and _LISTEN[u]["ready"]}
    for u in paths:
        out[u] = _listening_from_records(recs[u], now) if u in recs else []
    return out


_FENCE_RE = re.compile(r"^\s*(```|~~~)")
_TRAIL_MARKUP = set("*_~`'\")]}\u201d\u2019\u00bb")


def _ends_with_question(text):
    """The "message" heuristic: the last non-empty prose line (fenced code blocks dropped)
    ends with "?", ignoring trailing whitespace, markdown emphasis, closing quotes/brackets
    and emoji. Returns that line, or "" when it isn't a question."""
    lines, in_fence = [], False
    for ln in (text or "").split("\n"):
        if _FENCE_RE.match(ln):
            in_fence = not in_fence
            continue
        if not in_fence and ln.strip():
            lines.append(ln.strip())
    if not lines:
        return ""
    last = lines[-1]
    end = len(last)
    while end and (last[end - 1].isspace() or last[end - 1] in _TRAIL_MARKUP
                   or unicodedata.category(last[end - 1]) in ("So", "Sk", "Cf", "Mn", "Cs")):
        end -= 1
    return last if end and last[end - 1] in "?\uff1f" else ""


def _message_question(uuid, events, skip_injected=False):
    """{asking: "message", ...} when the transcript's last conversational event is an
    assistant message ending with a question, else None. question_id hashes the event's
    position + length, never its text."""
    for i in range(len(events) - 1, -1, -1):
        e = events[i]
        if e["kind"] == "turn_ended" or (skip_injected and e["kind"] == "user" and e.get("injected")):
            continue
        if e["kind"] != "assistant" or not e["text"] or e["tools"]:
            return None
        line = _ends_with_question(e["text"])
        if not line:
            return None
        return {"asking": "message", "question_id": _fingerprint(uuid, "msg", i, len(e["text"])),
                "question_preview": _short_preview(line), "question_count": 1}
    return None


_NO_ASK = {"asking": None, "asked_at": None, "question_id": None,
           "question_preview": "", "question_count": 0}


def _apply_ask(a, ask, fallback_at):
    """Copy the asking fields onto an agent dict (cleared when ask is None). A pending
    form overrides WORKING: the agent can't continue until the user answers."""
    a.update(_NO_ASK)
    if not ask:
        return
    a.update(ask)
    if not a.get("asked_at"):
        a["asked_at"] = fallback_at
    if ask["asking"] == "form":
        a["status"] = "waiting"
        a["self_active"] = False

# Office (working/desk) vs kitchen (waiting) is decided by TURN STATE, not raw
# write-recency: a session is "working" while its latest turn is still IN PROGRESS
# (a user/assistant message after the last `turn_ended`). This keeps a genuinely
# busy chat at its desk even through long quiet stretches mid-turn -- a slow tool
# call, a long generation, or simply while you read -- which a write-recency window
# got wrong (it kept dropping active chats to "idle" during those gaps). A chat
# whose latest turn has ENDED is waiting on you, so it walks to the kitchen, picked
# up on the next poll. Refinements layer on top:
#   * Live run (Cursor): the transcript lags the turn (see cursor_run_info), so a chat
#     whose composerData.unfinishedRunAt is set and that was active within
#     WORKING_STALE_CAP_SECONDS counts as mid-turn too -- including a brand-new chat that
#     has no transcript yet (shown via _untranscribed_cursor_agent). Conversely a
#     transcript left "in progress" by a lost closing flush is overridden once Cursor's
#     record says the run finished (cursor_run_finished).
#   * Multitask rollup: if the parent's turn has ended but a background SUBAGENT was
#     written within SUBAGENT_ACTIVE_SECONDS -- or (Cursor) its latest run is still
#     unfinished per its transcript and Cursor's composerData.unfinishedRunAt -- the
#     chat still counts as working (the Multitask Mode case, where the parent is idle
#     while a worker runs).
#   * Staleness cap: a turn that has been completely silent (chat AND subagents)
#     for longer than WORKING_STALE_CAP_SECONDS is treated as abandoned/crashed and
#     sent to the kitchen, so a half-finished turn can't sit at a desk forever.
SUBAGENT_ACTIVE_SECONDS = 120    # multitask subagent freshness window; --active-secs
# Backstop only: a turn still "in progress" but completely silent this long is
# treated as abandoned/crashed -> kitchen. Kept FAR out (2h) on purpose: the
# transcript .jsonl records only user/assistant messages, NOT tool calls, so a
# busy tool-heavy turn can legitimately write nothing for many minutes. A short
# cap (e.g. 15m) wrongly evicted those active turns to the kitchen, so turn state
# -- not mtime -- is the primary signal and this only catches genuinely dead ones.
WORKING_STALE_CAP_SECONDS = 7200
# A turn that owes the user a PLAIN reply (last event is a real user message, no tool pending)
# but has produced nothing for this long is stuck/abandoned -- e.g. an interrupted request the
# user never continued. A real agent starts replying within seconds, so this is safe to keep
# short WITHOUT evicting long single-tool turns (those are "mid-tool", not "reply", so exempt).
REPLY_STALE_SECONDS = 600

# --watch (dev hot-reload). START_TOKEN changes every time the process (re-)starts;
# the page polls /api/version and reloads itself when it sees a new token. Set from
# the pid + import time so a re-exec after a file change produces a fresh value.
START_TOKEN = str(os.getpid()) + "-" + str(int(os.stat(__file__).st_mtime))
WATCH_MODE = False

# Dynamic Workflow (the Workflow tool) tents. A workflow run's tent is shown while it
# is running, and lingers this long after its last write before it closes (a finished
# workflow's full summary always stays in the chat's detail panel).
SHOW_WORKFLOWS = True
WORKFLOW_FRESH_SECONDS = 300

# TEST HOOK: when > 0, the office is populated with exactly this many synthetic WORKING
# agents (implies --demo) so the dynamic desk scaling can be verified. Set by --demo-working.
DEMO_WORKING = 0

# ------------------------------------------------------------------------------------
# Holiday calendar -- the LIVE office auto-themes around holidays.
# A holiday "themes" the office from 7 days BEFORE through 3 days AFTER its date,
# inclusive (see holiday_active()). HOLIDAY_OVERRIDE / HOLIDAY_DATE force a theme or a
# reference date for demos (set from --holiday / --date).
HOLIDAY_OVERRIDE = None   # None -> use the real date; "none" -> force plain office; else a holiday name
HOLIDAY_DATE = None       # datetime.date to treat as "today" (None -> real date.today())
HOLIDAY_WINDOW_BEFORE = 7
HOLIDAY_WINDOW_AFTER = 3
# Hanukkah's first night follows the Hebrew (lunar) calendar, so there is no simple
# Gregorian formula -- hardcode a small lookup of first-night (first candle, at sundown)
# dates. APPROXIMATE: these were sanity-checked for 2025-2030 but should be re-verified
# and EXTENDED every few years (the table drifts out of range otherwise).
HANUKKAH_FIRST_NIGHT = {
    2025: (12, 14), 2026: (12, 4), 2027: (12, 24),
    2028: (12, 12), 2029: (12, 1), 2030: (12, 20),
}


def _thanksgiving_us(year):
    """US Thanksgiving = the 4th Thursday of November, computed per year."""
    first = date(year, 11, 1)
    first_thu = 1 + (3 - first.weekday()) % 7   # weekday(): Mon=0..Thu=3
    return date(year, 11, first_thu + 21)       # first Thursday + 3 weeks -> 4th Thursday


def _holiday_dates(year):
    """{name: date} of every supported holiday for a given year."""
    out = {
        "halloween": date(year, 10, 31),
        "thanksgiving": _thanksgiving_us(year),
        "christmas": date(year, 12, 25),
        "newyear": date(year, 1, 1),
    }
    hk = HANUKKAH_FIRST_NIGHT.get(year)
    if hk:
        out["hanukkah"] = date(year, hk[0], hk[1])
    return out


def holiday_active(today):
    """Return the holiday(s) whose [-7, +3] day window contains `today`, nearest-first.

    Overlap rule: windows can co-occur (Hanukkah and Christmas often do), so we return
    ALL active holidays rather than picking one. The frontend layers every theme's decor;
    the FIRST (nearest-dated) name is what drives the single ambient scene tint, so tints
    never fight. Neighbouring years are checked too, so a window near a year boundary works.
    """
    hits = []
    for yr in (today.year - 1, today.year, today.year + 1):
        for name, d in _holiday_dates(yr).items():
            start = d - timedelta(days=HOLIDAY_WINDOW_BEFORE)
            # Hanukkah is an 8-night festival, so its anchor date `d` is only the FIRST
            # night; the +3 tail must hang off the LAST (8th) night = first_night + 7 days
            # so the whole span stays themed. Other holidays keep the plain -7/+3 window.
            tail_anchor = d + timedelta(days=7) if name == "hanukkah" else d
            end = tail_anchor + timedelta(days=HOLIDAY_WINDOW_AFTER)
            if start <= today <= end:
                hits.append((abs((today - d).days), name))
    hits.sort()
    seen, out = set(), []
    for _dist, name in hits:
        if name not in seen:
            seen.add(name)
            out.append(name)
    return out


def current_holidays():
    """Active holiday names for the office right now, honouring --holiday / --date."""
    if HOLIDAY_OVERRIDE is not None:
        return [] if HOLIDAY_OVERRIDE == "none" else [HOLIDAY_OVERRIDE]
    return holiday_active(HOLIDAY_DATE or date.today())


def hanukkah_night(today):
    """Which night of Hanukkah (1..8) `today` falls on, or None if it is outside the
    eight-night span. Night 1 is the first candle-lighting at sundown on the first-night
    date (e.g. Dec 4, 2026); night 8 is seven days later. Neighbouring years are checked
    so a date near a year boundary still resolves."""
    for yr in (today.year - 1, today.year, today.year + 1):
        hk = HANUKKAH_FIRST_NIGHT.get(yr)
        if not hk:
            continue
        first = date(yr, hk[0], hk[1])
        delta = (today - first).days
        if 0 <= delta <= 7:
            return delta + 1
    return None


# When Hanukkah is forced (--holiday hanukkah) without an in-span --date, light this many
# candles so the demo/forced render looks festive rather than night-1 sparse.
HANUKKAH_DEMO_NIGHT = 5


def current_hanukkah_night():
    """Night (1..8) of Hanukkah the office should light right now, or None when Hanukkah
    is not the/an active theme. Honours --holiday / --date exactly like current_holidays():
    a real in-span --date uses the true night; a forced theme without an in-span date falls
    back to a representative lit count so forced/demo renders look good."""
    if HOLIDAY_OVERRIDE is not None:
        if HOLIDAY_OVERRIDE != "hanukkah":
            return None
        if HOLIDAY_DATE is not None:
            real = hanukkah_night(HOLIDAY_DATE)
            if real is not None:
                return real
        return HANUKKAH_DEMO_NIGHT
    today = HOLIDAY_DATE or date.today()
    if "hanukkah" not in holiday_active(today):
        return None
    # Auto-themed: the true night inside the eight-night span; otherwise the theme is in its
    # -7/+3 approach window (before the first candle) -> show night 1 as the opening night.
    return hanukkah_night(today) or 1
_WORKFLOW_SCRIPT_CACHE = {}     # script_path -> (mtime, meta_dict)
_WORKFLOW_IDENTITY_CACHE = {}   # uuid -> (parent_mtime, {runId: {name,summary,scriptPath}})
_WORKFLOW_JOURNAL_CACHE = {}    # run_dir -> ((mtime,size), {total,done,running_ids})

# rough per-1M-token pricing (USD) by model family, for a best-effort $ spend estimate.
_MODEL_PRICING = {  # (input, output); cache-read ~= 0.1x input, cache-write ~= 1.25x input
    "opus": (15.0, 75.0),
    "sonnet": (3.0, 15.0),
    "haiku": (0.80, 4.0),
}

TAG_RE = re.compile(r"<[^>]+>")
WS_RE = re.compile(r"[ \t]+")
# leading "Thursday, Jun 25, 2026, 1:26 PM (UTC+3)" style timestamp lines
TS_LINE_RE = re.compile(
    r"^(mon|tue|wed|thu|fri|sat|sun)[a-z]*,.*\(utc.*\)\s*$", re.IGNORECASE
)

# Deterministic fun names so each agent feels like an office worker.
FIRST_NAMES = [
    "Pip", "Willow", "Clover", "Bun", "Maple", "Sprout", "Waffle", "Biscuit",
    "Poppy", "Mochi", "Pebble", "Fern", "Cricket", "Marshmallow", "Pumpkin",
    "Honey", "Acorn", "Noodle", "Pickle", "Sunny", "Berry", "Tofu", "Dandelion",
    "Bramble", "Hazel", "Olive", "Tansy", "Muffin", "Peaches", "Juniper",
]
LAST_NAMES = [
    "Sunbeam", "Marshmallow", "Buttercup", "Honeydew", "Pumpkinpatch",
    "Snugglebee", "Cloudberry", "Dewdrop", "Meadowlight", "Gigglesworth",
    "Cottontail", "Brightbloom", "Mossypaws", "Tinkerwhisk", "Sugarplum",
    "Pebblebrook", "Willowwisp", "Honeycomb", "Berrybramble", "Twinkletoes",
    "Mapleshade", "Cuddleburrow", "Dapplewood", "Snickerdoodle", "Fernwhistle",
]


def _clean_text(s):
    if not s:
        return ""
    s = TAG_RE.sub(" ", s)
    s = s.replace("\\n", "\n")
    # collapse runs of spaces/tabs but keep newlines
    lines = [WS_RE.sub(" ", ln).strip() for ln in s.split("\n")]
    out = "\n".join(ln for ln in lines)
    out = re.sub(r"\n{3,}", "\n\n", out).strip()
    return out


def _strip_leading_timestamp(s):
    """Drop leading blank/timestamp lines so the real query shows up first."""
    lines = (s or "").split("\n")
    while lines and (not lines[0].strip() or TS_LINE_RE.match(lines[0].strip())):
        lines.pop(0)
    return "\n".join(lines).strip()


def _name_for(uuid):
    h = 0
    for ch in uuid:
        h = (h * 131 + ord(ch)) & 0xFFFFFFFF
    first = FIRST_NAMES[h % len(FIRST_NAMES)]
    last = LAST_NAMES[(h // len(FIRST_NAMES)) % len(LAST_NAMES)]
    return f"{first} {last}"


def _variant_for(uuid):
    h = 0
    for ch in uuid:
        h = (h * 31 + ord(ch)) & 0xFFFFFFFF
    return h % 6


def _pretty_project(folder):
    name = folder
    if name.startswith("Users-"):
        parts = name.split("-")
        # keep the last 2 meaningful segments, e.g. ...-my-app -> "my-app"
        if len(parts) >= 2:
            name = "-".join(parts[-2:])
    return name


def _tool_detail(name, inp):
    # Tolerant of both Cursor and Claude Code tool schemas (e.g. Cursor's Shell /
    # StrReplace / `path` vs Claude's Bash / Edit / `file_path`).
    if not isinstance(inp, dict):
        return name
    def first_line(v):
        return _clean_text(str(v)).split("\n")[0][:80]
    def basename_of(*keys):
        for k in keys:
            v = inp.get(k)
            if v:
                return os.path.basename(v) or v
        return ""
    if name in ("Shell", "Bash"):
        return first_line(inp.get("description") or inp.get("command") or "")
    if name in ("Read", "Write", "Delete", "StrReplace", "Edit", "MultiEdit", "NotebookEdit"):
        return basename_of("path", "file_path", "notebook_path")
    if name in ("Grep", "SemanticSearch"):
        return first_line(inp.get("pattern") or inp.get("query") or "")
    if name in ("Task",):
        return first_line(inp.get("description") or inp.get("prompt") or "")
    if name == "Glob":
        return first_line(inp.get("glob_pattern") or inp.get("pattern") or "")
    if name in ("TodoWrite",):
        return "updating task list"
    if name in ("WebSearch", "WebFetch"):
        return first_line(inp.get("search_term") or inp.get("query") or inp.get("url") or "")
    # fall back to first value
    for k in ("description", "explanation", "title"):
        if inp.get(k):
            return first_line(inp[k])
    return name


def _normalize_events(path):
    """Normalize a Cursor .jsonl transcript into the shared event shape.

    Returns ``(events, scheduled, scheduled_name)``. A session started by a
    scheduled task / automation opens with a ``<scheduled-task name="..."
    file="...">`` marker in its first user message (the same convention Claude
    Code uses). We detect it on the RAW text -- before ``_clean_text`` strips the
    tag -- so those agents can be shown as couriers, mirroring the Claude source.
    Ordinary interactive sessions return ``scheduled=False``.

    NOTE: Cursor's own scheduled sessions (Automations) currently run as cloud
    agents and do not write local transcripts, so this is dormant today; it lights
    up automatically if/when a scheduled Cursor run lands locally with the marker.
    """
    events = []
    scheduled = False
    scheduled_name = ""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except Exception:
                    continue
                if obj.get("type") == "turn_ended":
                    events.append({
                        "kind": "turn_ended",
                        "status": obj.get("status"),
                        "text": "",
                        "tools": [],
                    })
                    continue
                role = obj.get("role")
                if role not in ("user", "assistant"):
                    continue
                content = ((obj.get("message") or {}).get("content")) or []
                texts = []
                tools = []
                if isinstance(content, str):
                    texts.append(content)
                else:
                    for block in content:
                        if not isinstance(block, dict):
                            continue
                        btype = block.get("type")
                        if btype == "text" and block.get("text"):
                            texts.append(block["text"])
                        elif btype == "tool_use":
                            tools.append({
                                "name": block.get("name", "tool"),
                                "detail": _tool_detail(block.get("name", ""), block.get("input")),
                            })
                if role == "user" and not scheduled:
                    joined = "\n".join(texts)  # raw, before tags are stripped
                    if "<scheduled-task" in joined:
                        scheduled = True
                        m = re.search(r'name="([^"]+)"', joined)
                        if m:
                            scheduled_name = m.group(1)
                events.append({
                    "kind": role,
                    "text": _clean_text("\n\n".join(texts)),
                    "tools": tools,
                })
    except Exception:
        pass
    return events, scheduled, scheduled_name


def _turn_in_progress(events):
    """True if the session's latest turn has NOT ended yet.

    A Cursor turn is delimited by an explicit ``turn_ended`` marker. The agent is
    actively working when there is conversational activity (a user prompt, or the
    agent mid-response / mid-tool-use) AFTER the last ``turn_ended``. Once the agent
    finishes and ``turn_ended`` is written, the session is waiting on the user.

    This is far more reliable than guessing from file timestamps, because
    ``turn_ended`` is a definitive boundary rather than a recency heuristic.
    """
    last_end = -1
    last_msg = -1
    for i, e in enumerate(events):
        if e["kind"] == "turn_ended":
            last_end = i
        elif e["kind"] in ("user", "assistant"):
            last_msg = i
    return last_msg > last_end


def _active_sub_count(sub_files):
    """How many background subagents are *currently running* -- i.e. their transcript
    was written within the freshness window. The subagents/ dir also holds finished
    ones, so we count only recently-touched files (the UI shows a little helper per
    active subagent next to the working agent)."""
    if not sub_files:
        return 0
    now = time.time()
    return sum(1 for _, m in sub_files if (now - m) <= SUBAGENT_ACTIVE_SECONDS)


_ENDED_CACHE = {}  # transcript path -> (mtime, ends_with_turn_ended)
_ENDED_LOCK = threading.Lock()


def _transcript_ended(path, mtime):
    """True if a Cursor transcript's last record is ``turn_ended``. Cursor strips that
    trailing marker when a subagent is resumed and re-appends it when the run finishes,
    so a missing one means the latest run has not finished."""
    with _ENDED_LOCK:
        hit = _ENDED_CACHE.get(path)
        if hit and hit[0] == mtime:
            return hit[1]
    ended = True
    try:
        with open(path, "rb") as fh:
            fh.seek(0, 2)
            size = fh.tell()
            fh.seek(max(0, size - 65536))
            tail = fh.read().decode("utf-8", "replace")
        for line in reversed(tail.splitlines()):
            try:
                obj = json.loads(line)
            except Exception:
                continue
            ended = obj.get("type") == "turn_ended"
            break
    except Exception:
        ended = True
    with _ENDED_LOCK:
        _ENDED_CACHE[path] = (mtime, ended)
    return ended


def _running_sub_files(sub_files, cursor_subs=False):
    """The subagents that count as running: written within SUBAGENT_ACTIVE_SECONDS, or (Cursor
    only) whose latest run is unfinished -- no trailing ``turn_ended`` and Cursor's
    ``unfinishedRunAt`` flag not cleared -- and written within WORKING_STALE_CAP_SECONDS.
    The second rule catches a background subagent busy in one long tool call, which writes
    nothing for many minutes after the parent's own turn has ended."""
    if not sub_files:
        return []
    now = time.time()
    running, unfinished = [], []
    for path, m in sub_files:
        age = now - m
        if age <= SUBAGENT_ACTIVE_SECONDS:
            running.append((path, m))
        elif cursor_subs and age <= WORKING_STALE_CAP_SECONDS and not _transcript_ended(path, m):
            unfinished.append((path, m))
    if unfinished:
        ids = [os.path.splitext(os.path.basename(p))[0] for p, _ in unfinished]
        flags = cursor_runs_in_flight(ids)
        running.extend(pm for pm, u in zip(unfinished, ids) if flags.get(u) is not False)
    return running


def _first_user_text(path):
    """First user-message text from a transcript (works for either Cursor or Claude
    line format). Used to label a subagent when it has no metadata file."""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    o = json.loads(line)
                except Exception:
                    continue
                role = o.get("role") or ((o.get("message") or {}).get("role"))
                if role != "user":
                    continue
                c = (o.get("message") or {}).get("content")
                if c is None:
                    c = o.get("content")
                if isinstance(c, str):
                    return _clean_text(c)
                if isinstance(c, list):
                    for b in c:
                        if isinstance(b, dict) and b.get("type") == "text" and b.get("text"):
                            return _clean_text(b["text"])
    except Exception:
        pass
    return ""


def _sub_activity(path):
    """Read a subagent transcript ONCE (scanned from the end) and return four fields --
    (bubble_text, bubble_kind, last_tool, last_message):
      - bubble_text/bubble_kind drive the ephemeral dwarf bubble/chip: the newest assistant
        message's headline, tool winning within that message (kind 'tool'|'assistant'|'').
      - last_tool = "Name: detail" of the most-recent tool_use (may be an earlier message).
      - last_message = the most-recent assistant TEXT ([:360], + " ..." when longer).
    The last two mirror the desk hover-card's independent last_tool / last_message so a
    helper dwarf's tooltip can show BOTH what it last ran and what it last wrote. All ""
    when nothing is found."""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            lines = fh.readlines()
    except Exception:
        return ("", "", "", "")
    bub_txt, bub_kind, last_tool, last_message = "", "", "", ""
    for line in reversed(lines):
        line = line.strip()
        if not line or '"assistant"' not in line:   # cheap pre-filter
            continue
        try:
            o = json.loads(line)
        except Exception:
            continue
        role = o.get("role") or ((o.get("message") or {}).get("role"))
        if role != "assistant":
            continue
        c = (o.get("message") or {}).get("content")
        if c is None:
            c = o.get("content")
        m_tool_first, m_tool_last, m_text = "", "", ""
        if isinstance(c, str):
            m_text = _clean_text(c)
        elif isinstance(c, list):
            tools, parts = [], []
            for b in c:
                if not isinstance(b, dict):
                    continue
                bt = b.get("type")
                if bt == "tool_use":
                    tools.append(("%s: %s" % (b.get("name", "tool"),
                                  _tool_detail(b.get("name", ""), b.get("input")))).strip().rstrip(":"))
                elif bt == "text" and b.get("text"):
                    parts.append(b["text"])
            if tools:
                m_tool_first, m_tool_last = tools[0], tools[-1]
            m_text = _clean_text("\n".join(parts))
        # ephemeral bubble: newest content-bearing message, tool wins (first tool in the msg)
        if not bub_kind:
            if m_tool_first:
                bub_txt, bub_kind = m_tool_first, "tool"
            elif m_text:
                bub_txt, bub_kind = m_text, "assistant"
        # hover fields: most-recent tool and most-recent text, found INDEPENDENTLY
        if not last_tool and m_tool_last:
            last_tool = m_tool_last
        if not last_message and m_text:
            last_message = m_text[:360].rstrip() + (" ..." if len(m_text) > 360 else "")
        if bub_kind and last_tool and last_message:
            break
    return (bub_txt, bub_kind, last_tool, last_message)


# ---- helper (subagent) hover-card fields ------------------------------------------------
# A Cursor subagent's short title is the `description` its parent passed to the Task tool;
# Cursor stores it as the subagent's own composerData:<sub-uuid>.name (exact-key lookup, so
# it's cheap even on the huge state DB). Claude subagents carry it in <name>.meta.json.
_SUB_META_CACHE = {}              # sub uuid -> (name, created_epoch, fetched_at)
_SUB_META_LOCK = threading.Lock()
_SUB_META_MISS_TTL = 60           # a found name never changes; only re-check misses

_TS_PREFIX_RE = re.compile(
    r"^(?:(?:mon|tue|wed|thu|fri|sat|sun)[a-z]*\.?,?\s+)?"
    r"(?:[a-z]{3,9}\.?\s+\d{1,2},?\s+\d{4}|\d{4}-\d{2}-\d{2}|\d{1,2}/\d{1,2}/\d{2,4})"
    r"(?:[,\sT]+\d{1,2}:\d{2}(?::\d{2})?(?:\.\d+)?\s*(?:am|pm)?)?"
    r"\s*(?:\(?(?:utc|gmt)[^)\s]*\)?)?[\s,.:\-]*", re.IGNORECASE)
_WORK_IN_RE = re.compile(
    r"^you(?:'re| are)? work(?:ing)? in (?:the )?.{0,80}?\brepo(?:sitory)?\b"
    r"(?: at \S+)?(?:\s*\([^)]*\)?)?[\s.,:;]*", re.IGNORECASE)
_SYS_BLOCK_RE = re.compile(r"<(system[\w-]*|user_info|rules?)\b[^>]*>.*?</\1>", re.IGNORECASE | re.DOTALL)
_STEP_PREFIX_RE = re.compile(
    r"^(?:phase|step|part|stage|task)\s*\d+(?:\s*(?:of|/)\s*\d+)?\s*[:.)\-\u2013\u2014]+\s*", re.IGNORECASE)
_GENERIC_HEADINGS = {"context", "task", "background", "instructions", "goal", "goals", "overview",
                     "summary", "role", "your task", "objective", "constraints", "notes"}


def _cursor_sub_meta(sub_id):
    """(name, created_epoch) for a Cursor subagent from composerData:<sub_id>; ("", 0.0)
    when unknown. Exact-key read-only lookup, cached (found names permanently)."""
    now = time.time()
    with _SUB_META_LOCK:
        hit = _SUB_META_CACHE.get(sub_id)
        if hit and (hit[0] or (now - hit[2]) < _SUB_META_MISS_TTL):
            return hit[0], hit[1]
    name, created = "", 0.0
    try:
        if os.path.isfile(CURSOR_GLOBAL_DB):
            conn = _open_cursor_db()
            try:
                row = conn.execute(
                    "SELECT json_extract(value,'$.name'), json_extract(value,'$.createdAt')"
                    " FROM cursorDiskKV WHERE key=?", ("composerData:" + sub_id,)).fetchone()
            finally:
                conn.close()
            if row:
                name = row[0].strip() if isinstance(row[0], str) else ""
                created = row[1] / 1000.0 if isinstance(row[1], (int, float)) and row[1] > 0 else 0.0
    except Exception:
        logger.debug("subagent composerData lookup failed", exc_info=True)
    with _SUB_META_LOCK:
        if len(_SUB_META_CACHE) > 4000:
            _SUB_META_CACHE.clear()
        _SUB_META_CACHE[sub_id] = (name, created, now)
    return name, created


def _clean_helper_title(s, limit=40):
    """A short, human label from a subagent title or prompt: the first meaningful line with
    timestamps, "You work in the X repo at ..." preambles, <system...> blocks, "PHASE 1 OF 2:"
    prefixes and markdown stripped, truncated on a word boundary to ~`limit` chars."""
    s = _SYS_BLOCK_RE.sub(" ", str(s or ""))
    s = _clean_text(s)
    for raw in s.split("\n"):
        ln = raw.strip()
        heading = ln.startswith("#")
        for _ in range(4):
            prev = ln
            ln = re.sub(r"^(?:#{1,6}\s*|[-*+>]\s+|\d+[.)]\s+)", "", ln).strip()
            ln = _TS_PREFIX_RE.sub("", ln, count=1).strip() if _TS_PREFIX_RE.match(ln) else ln
            ln = _WORK_IN_RE.sub("", ln, count=1).strip()
            ln = _STEP_PREFIX_RE.sub("", ln, count=1).strip()
            if ln == prev:
                break
        ln = re.sub(r"\*\*|__|`|~~", "", ln)
        ln = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", ln).strip(" \t-:;,.")
        if not ln or not re.search(r"[A-Za-z]", ln):
            continue
        if (heading or ln.endswith(":")) and ln.rstrip(":").strip().lower() in _GENERIC_HEADINGS:
            continue
        if ln.lower() in ("new chat", "untitled", "new agent"):
            continue
        if len(ln) > limit:
            cut = ln[:limit + 1].rsplit(" ", 1)[0]
            ln = (cut if len(cut) >= limit * 0.6 else ln[:limit]).rstrip(" ,.;:-") + "\u2026"
        return ln[:1].upper() + ln[1:]
    return ""


_SHELL_DROP_SEGMENT = {"cd", "pushd", "popd", "export", "source", ".", "set", "unset", "fi", "done",
                       "true", ":", "echo"}
_SHELL_WRAPPERS = {"sudo", "env", "time", "nohup", "exec", "then", "do", "if", "else", "while", "command"}


def _cmd_words(cmd, cap=3):
    """The first word of each command in a shell line ("sleep 5; ls -la && cd x" -> sleep, ls),
    skipping cd/env/VAR=val noise. Only bare program names -- never arguments or paths."""
    words = []
    for seg in re.split(r"&&|\|\||[;|\n]|\$\(|`", str(cmd or "")):
        for tok in seg.strip().lstrip("({").split():
            tok = tok.strip("'\"")
            if not tok or re.match(r"^[A-Za-z_][A-Za-z0-9_]*=", tok) or tok.lower() in _SHELL_WRAPPERS:
                continue
            if tok.lower() in _SHELL_DROP_SEGMENT:
                break
            tok = os.path.basename(tok)
            if re.match(r"^[A-Za-z][A-Za-z0-9._+-]{0,15}$", tok) and tok not in words:
                words.append(tok)
            break
        if len(words) >= cap:
            break
    return words


def _tool_plain(name, inp):
    """One plain-English line (with an emoji) for a tool call, e.g. "✏️ editing sync.py"."""
    inp = inp if isinstance(inp, dict) else {}
    n = str(name or "")
    low = n.lower()
    def base(*keys):
        for k in keys:
            v = inp.get(k)
            if isinstance(v, str) and v.strip():
                return os.path.basename(v.strip().rstrip("/")) or v.strip()
        return ""
    if low in ("shell", "bash", "run_terminal_command_v2", "run_terminal_cmd", "powershell"):
        w = _cmd_words(inp.get("command"))
        return "\U0001F5A5\uFE0F running: " + ", ".join(w) if w else "\U0001F5A5\uFE0F running a shell command"
    if low in ("awaitshell", "await", "bashoutput", "killshell", "killbash"):
        return "\u23F3 waiting on a shell"
    if low in ("strreplace", "edit", "multiedit", "edit_file_v2", "edit_file", "search_replace",
               "notebookedit", "editnotebook", "apply_patch"):
        f = base("path", "file_path", "notebook_path", "target_file")
        return "\u270F\uFE0F editing " + f if f else "\u270F\uFE0F editing a file"
    if low in ("write", "write_file"):
        f = base("path", "file_path", "target_file")
        return "\U0001F4DD writing " + f if f else "\U0001F4DD writing a file"
    if low in ("read", "read_file_v2", "read_file"):
        f = base("path", "file_path", "target_file")
        return "\U0001F4D6 reading " + f if f else "\U0001F4D6 reading a file"
    if low in ("delete", "delete_file"):
        f = base("path", "file_path", "target_file")
        return "\U0001F5D1\uFE0F deleting " + f if f else "\U0001F5D1\uFE0F deleting a file"
    if low in ("grep", "glob", "semanticsearch", "ripgrep_raw_search", "glob_file_search",
               "codebase_search", "grep_search", "file_search", "ls", "list_dir"):
        return "\U0001F50D searching the code"
    if low in ("webfetch", "web_fetch", "fetch"):
        return "\U0001F310 fetching a web page"
    if low in ("websearch", "web_search"):
        return "\U0001F310 searching the web"
    if low in ("task", "agent", "task_v2"):
        return "\U0001F916 launched a helper"
    if low in ("todowrite", "todo_write"):
        return "\U0001F4CB updating the to-do list"
    if low in ("askquestion", "ask_question", "askuserquestion"):
        return "\u2753 asking you a question"
    if low in ("readlints", "read_lints"):
        return "\U0001F9F9 checking lints"
    if low in ("calldynamictool", "getdynamictools", "fetchmcpresource") or low.startswith(("mcp", "mcp__")):
        return "\U0001F50C using an integration"
    words = re.sub(r"([a-z])([A-Z])", r"\1 \2", n).replace("_", " ").replace("-", " ").lower().split()
    return "\U0001F6E0\uFE0F using " + (" ".join(words)[:24] or "a tool")


def _sub_last_tool_plain(path, tail_bytes=262144):
    """Plain-English line for a transcript's most recent tool call ("" when none). Reads only
    the file's tail."""
    try:
        with open(path, "rb") as fh:
            fh.seek(0, 2)
            size = fh.tell()
            fh.seek(max(0, size - tail_bytes))
            lines = fh.read().decode("utf-8", "replace").splitlines()
    except Exception:
        return ""
    for line in reversed(lines):
        if '"tool_use"' not in line:
            continue
        try:
            o = json.loads(line)
        except Exception:
            continue
        c = (o.get("message") or {}).get("content")
        if c is None:
            c = o.get("content")
        if isinstance(c, list):
            for b in reversed(c):
                if isinstance(b, dict) and b.get("type") == "tool_use":
                    return _tool_plain(b.get("name"), b.get("input"))
    return ""


def _file_started(path):
    try:
        st = os.stat(path)
        return float(getattr(st, "st_birthtime", 0) or min(st.st_ctime, st.st_mtime))
    except OSError:
        return 0.0


def _sub_card_fields(path, sub_id, title_src="", cursor_sub=False):
    """Extra fields for the helper hover card: a clean short `title`, the last tool as plain
    English (`doing`) and the run's start time (`started`, epoch s)."""
    name, created = _cursor_sub_meta(sub_id) if cursor_sub else ("", 0.0)
    title = _clean_helper_title(name) or _clean_helper_title(title_src)
    return {"title": title, "doing": _sub_last_tool_plain(path),
            "started": created or _file_started(path)}


def _subagent_infos(sub_files, cursor_subs=False):
    """For the *currently running* subagents, return [{type, detail}] describing what
    each is doing. Claude subagents carry a sibling ``<name>.meta.json`` with an
    ``agentType`` + ``description``; otherwise we fall back to the subagent's opening
    prompt. Sorted by path so a given subagent keeps the same helper slot."""
    if not sub_files:
        return []
    infos = []
    for path, m in sorted(_running_sub_files(sub_files, cursor_subs), key=lambda pm: pm[0]):
        typ, detail = "", ""
        meta = (path[:-len(".jsonl")] + ".meta.json") if path.endswith(".jsonl") else path + ".meta.json"
        try:
            if os.path.isfile(meta):
                with open(meta, "r", encoding="utf-8", errors="replace") as fh:
                    md = json.load(fh)
                typ = (md.get("agentType") or "").strip()
                detail = (md.get("description") or "").strip()
        except Exception:
            pass
        if not detail:
            detail = _first_user_text(path)
        sub_id = os.path.splitext(os.path.basename(path))[0]
        bub_txt, bub_kind, last_tool, last_message = _sub_activity(path)
        infos.append({"type": typ, "detail": detail[:140], "id": sub_id,
                      "last_msg": bub_txt[:160], "last_kind": bub_kind,
                      "last_tool": last_tool, "last_message": last_message, "ts": m,
                      **_sub_card_fields(path, sub_id, detail, cursor_subs)})
    return infos


def _untranscribed_subagents(parent_uuid, sub_files):
    """Placeholder helpers for a Cursor parent's subagents whose run is in flight per
    composerData.unfinishedRunAt but that have no transcript yet (Cursor creates a subagent's
    .jsonl some ~45 s into its run). Two indexed reads: the parent's subagentComposerIds,
    then the children not on disk in one ``key IN (...)`` -- both via cursor_run_info's cache."""
    pinfo = cursor_run_info([parent_uuid]).get(parent_uuid)
    if not pinfo or not pinfo.get("sub_ids"):
        return []
    on_disk = {os.path.splitext(os.path.basename(p))[0] for p, _m in (sub_files or [])}
    cands = [u for u in pinfo["sub_ids"] if u not in on_disk]
    if not cands:
        return []
    now = time.time()
    writers = cursor_recent_writers()
    out = []
    for u, info in cursor_run_info(cands).items():
        if not info or not info["run_at"] or info["parent"] not in ("", parent_uuid):
            continue
        last = max(info["run_at"], writers.get(u, 0.0))
        if (now - last) > WORKING_STALE_CAP_SECONDS:
            continue
        name, created = _cursor_sub_meta(u)
        out.append({"type": info.get("sub_type") or "", "detail": "", "id": u,
                    "last_msg": "", "last_kind": "", "last_tool": "", "last_message": "",
                    "ts": last, "title": _clean_helper_title(name), "doing": "",
                    "started": created or (info["run_at"] if info["run_at"] > 1.0 else 0.0),
                    "no_transcript": True})
    if out:
        logger.debug("untranscribed subagents for %s: %d of %d candidates", parent_uuid, len(out), len(cands))
    return sorted(out, key=lambda s: s["id"])


def _cursor_helpers(parent_uuid, sub_files, live=False, working=False):
    """Running helpers for a Cursor parent: transcript-based ones plus, while the parent is in
    flight / working, in-flight subagents with no transcript yet (deduped by uuid)."""
    infos = _subagent_infos(sub_files, True)
    if live or working or infos:
        seen = {s["id"] for s in infos}
        infos += [s for s in _untranscribed_subagents(parent_uuid, sub_files) if s["id"] not in seen]
    return infos


_BG_CONTENT_RE = re.compile(
    r"background with ID:\s*(\w+)\.\s*Output is being written to:\s*(\S+?\.output)")


def _open_shells_claude(path, cap=6):
    """Background shells a Claude session started that are (as far as disk can tell) still
    running -- shown as little terminal windows by the desk.

    A background shell is a ``Bash`` tool_use with ``run_in_background: true``; its result
    line reports a task id + an output-file path. A shell is considered FINISHED once a
    terminal ``<task-notification>`` (status completed/failed) references its id -- in EITHER
    of the two on-disk forms (a consumed user-message line, or a queued ``attachment``).
    Absence of that notification = still running (this mirrors Claude's own "N shells"
    counter, and shares its one blind spot: a shell killed out-of-band via ``kill``/``pkill``
    leaves no transcript trace, so it can be over-reported). Returns up to ``cap`` shells
    newest-first: ``[{id, command, running, output_tail}]``."""
    cmd_by_tuid, shells, order, finished = {}, {}, [], set()
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    o = json.loads(line)
                except Exception:
                    continue
                m = o.get("message")
                if isinstance(m, dict) and isinstance(m.get("content"), list):
                    for b in m["content"]:
                        if not isinstance(b, dict):
                            continue
                        if (b.get("type") == "tool_use" and b.get("name") == "Bash"
                                and isinstance(b.get("input"), dict)
                                and b["input"].get("run_in_background")):
                            cmd_by_tuid[b.get("id")] = b["input"].get("command", "")
                        elif b.get("type") == "tool_result" and isinstance(b.get("content"), str):
                            tur = o.get("toolUseResult")
                            tid = tur.get("backgroundTaskId") if isinstance(tur, dict) else None
                            mt = _BG_CONTENT_RE.search(b["content"])
                            if tid and mt:
                                shells[tid] = {"command": cmd_by_tuid.get(b.get("tool_use_id"), ""),
                                               "output_file": mt.group(2)}
                                if tid not in order:
                                    order.append(tid)
                # terminal task-notifications mark a shell finished -- both on-disk forms
                txt = None
                if isinstance(m, dict) and isinstance(m.get("content"), str) and "<task-notification>" in m["content"]:
                    txt = m["content"]
                att = o.get("attachment")
                if isinstance(att, dict) and att.get("commandMode") == "task-notification":
                    txt = att.get("prompt", "")
                if txt:
                    ti = re.search(r"<task-id>(\w+)</task-id>", txt)
                    st = re.search(r"<status>(\w+)</status>", txt)
                    if ti and st and st.group(1) in ("completed", "failed"):
                        finished.add(ti.group(1))
    except Exception:
        return []
    # PRIORITISE running shells (newest-first), then fill with the most-recent finished ones,
    # THEN cap. Otherwise a long-lived shell (e.g. a --watch dev server) gets capped out by a
    # burst of newer, already-finished commands and never shows -- even while still running.
    newest = list(reversed(order))
    ordered = [t for t in newest if t not in finished] + [t for t in newest if t in finished]
    out = []
    for tid in ordered[:cap]:
        s = shells[tid]
        tail = ""
        try:
            f = s["output_file"]
            if os.path.exists(f) and not os.path.islink(f):
                nz = [ln for ln in open(f, "r", encoding="utf-8", errors="replace").read().splitlines() if ln.strip()]
                tail = " / ".join(nz[-2:])[:150]
        except Exception:
            pass
        out.append({"id": tid,
                    "command": _clean_text(s["command"])[:200],
                    "running": tid not in finished,
                    "output_tail": tail})
    return out


def _is_working(turn_in_progress, eff_mtime, sub_files, wf_latest=0.0, cursor_subs=False):
    """Office (working) vs kitchen (waiting), decided by TURN STATE + rollups.

    Working when the latest turn is still in progress, OR a background subagent
    is running per ``_running_sub_files`` (multitask: parent idle, worker running), OR a dynamic
    Workflow's files were written very recently (the Workflow tool returns immediately
    after launch, so the parent's own turn ends while its subagents are still running).
    Either way a turn completely silent past the staleness cap is considered abandoned
    and sent to the kitchen so it can't occupy a desk indefinitely.

    Computed fresh per request (depends on wall-clock vs the rolled-up mtimes).
    """
    now = time.time()
    eff = max(eff_mtime, wf_latest or 0.0)
    if (now - eff) > WORKING_STALE_CAP_SECONDS:
        return False
    if turn_in_progress:
        # a turn that owes a PLAIN reply (Claude turn-kind "reply") but has been silent a long
        # time is stuck/abandoned mid-turn -> idle. Mid-tool turns ("tool"/generic truthy) can
        # legitimately be silent for one long tool call, so they keep the far-out stale cap.
        if turn_in_progress == "reply" and (now - eff) > REPLY_STALE_SECONDS:
            return False
        return True
    if _running_sub_files(sub_files, cursor_subs):
        return True
    # a dynamic Workflow whose journal / agent transcripts were touched within the
    # freshness window keeps the parent "working" even though its own turn has ended.
    return bool(wf_latest) and (now - wf_latest) <= SUBAGENT_ACTIVE_SECONDS


def _rel_time(seconds_ago):
    s = int(seconds_ago)
    if s < 60:
        return f"{s}s ago"
    m = s // 60
    if m < 60:
        return f"{m}m ago"
    h = m // 60
    if h < 24:
        return f"{h}h ago"
    d = h // 24
    return f"{d}d ago"


_KNOWN_SUBAGENT_IDS = set()  # subagent uuids ever seen, remembered across scans
_KNOWN_SUBAGENT_LOCK = threading.Lock()


def discover_transcripts():
    """Yield (uuid, project_folder, abspath, eff_mtime, sub_files) for top-level
    agent transcripts, de-duplicated across ALL Cursor project roots.

    Two correctness measures prevent the "appears after refresh then vanishes"
    flicker:

    * GLOBAL subagent exclusion. A subagent transcript is recorded inside its
      parent's ``<parent>/subagents/<uuid>.jsonl`` AND (sometimes) as its own
      top-level ``<uuid>/<uuid>.jsonl`` dir. We gather subagent uuids across EVERY
      project (not just the current one) and never list them as their own agent.
      Known subagent ids are also remembered across scans, so a transient gap in
      the filesystem registration can't momentarily promote a subagent to a
      top-level agent.
    * CROSS-PROJECT de-dup. The same chat uuid can have a top-level transcript dir
      in more than one project root (e.g. ``my-app`` and ``empty-window``). Yielding
      both hands the frontend two agents with the same id -- one computed "working"
      and one "waiting" -- which fight over the same slot and flicker. We keep a
      single representative per uuid. When a uuid is duplicated we PREFER the copy
      that currently computes to 'working' (e.g. the live ``my-app`` copy with a
      fresh mid-turn subagent) over a stale copy (e.g. an ``empty-window`` copy with
      a finished turn and no subagents), so the stale one can never shadow the
      working one. Ties fall back to freshest eff_mtime, then most subagents.

    ``eff_mtime`` is the most recent of the chat itself or any of its subagents, so
    a session whose work runs in a background subagent still shows as working.
    """
    if not os.path.isdir(CURSOR_PROJECTS_DIR):
        return
    try:
        projects = os.listdir(CURSOR_PROJECTS_DIR)
    except OSError:
        return

    # ---- pass 1: gather subagent ids + files across ALL projects ----
    subagent_ids = set()
    sub_mtime = {}        # (project, entry) -> latest subagent transcript mtime
    sub_files = {}        # (project, entry) -> [(subpath, submtime), ...]
    project_entries = {}  # project -> entries list (cached so we don't relist)
    for project in projects:
        at_dir = os.path.join(CURSOR_PROJECTS_DIR, project, "agent-transcripts")
        if not os.path.isdir(at_dir):
            continue
        try:
            entries = os.listdir(at_dir)
        except OSError:
            continue
        project_entries[project] = entries
        for entry in entries:
            sub_dir = os.path.join(at_dir, entry, "subagents")
            if not os.path.isdir(sub_dir):
                continue
            try:
                subs = os.listdir(sub_dir)
            except OSError:
                continue
            for f in subs:
                if not f.endswith(".jsonl"):
                    continue
                subagent_ids.add(f[: -len(".jsonl")])
                try:
                    subpath = os.path.join(sub_dir, f)
                    m = os.path.getmtime(subpath)
                    sub_files.setdefault((project, entry), []).append((subpath, m))
                    if m > sub_mtime.get((project, entry), 0):
                        sub_mtime[(project, entry)] = m
                except OSError:
                    pass

    # remember subagent ids across scans (robust against transient registration gaps)
    with _KNOWN_SUBAGENT_LOCK:
        _KNOWN_SUBAGENT_IDS.update(subagent_ids)
        known = set(_KNOWN_SUBAGENT_IDS)

    # ---- pass 2: collect ALL candidate copies per uuid ----
    cands = {}  # uuid -> [(eff_mtime, n_sub, project, jsonl, sub_files_list), ...]
    for project, entries in project_entries.items():
        at_dir = os.path.join(CURSOR_PROJECTS_DIR, project, "agent-transcripts")
        for entry in entries:
            if entry == "subagents" or entry in known:
                continue
            sess_dir = os.path.join(at_dir, entry)
            if not os.path.isdir(sess_dir):
                continue
            jsonl = os.path.join(sess_dir, entry + ".jsonl")
            if not os.path.isfile(jsonl):
                continue
            try:
                mtime = os.path.getmtime(jsonl)
            except OSError:
                continue
            sf = sub_files.get((project, entry), [])
            eff_mtime = max(mtime, sub_mtime.get((project, entry), 0))
            cands.setdefault(entry, []).append((eff_mtime, len(sf), project, jsonl, sf))

    # ---- resolve duplicates: keep the live/freshest copy ----
    # The same chat uuid can have a top-level dir in more than one project root. We
    # keep a single representative: freshest rolled-up eff_mtime first (the copy
    # being actively written), then the one with the most subagents -- so a stale
    # duplicate can never shadow the live copy and steal its desk/kitchen slot.
    for uuid, lst in cands.items():
        if len(lst) == 1:
            eff_mtime, _n, project, jsonl, sf = lst[0]
        else:
            def _score(c):
                eff, n, _proj, _jl, _sfl = c
                return (eff, n)
            eff_mtime, _n, project, jsonl, sf = max(lst, key=_score)
        yield uuid, project, jsonl, eff_mtime, sf


_CACHE = {}  # uuid -> (mtime, parsed_dict)
_CACHE_LOCK = threading.Lock()


def parse_agent(uuid, project, path, mtime, sub_files=None, full=False):
    with _CACHE_LOCK:
        cached = _CACHE.get(uuid)
        if cached and cached[0] == mtime and (full <= cached[1].get("_full", False)):
            return cached[1]

    events, scheduled, scheduled_name = _normalize_events(path)

    task_full = ""
    for ev in events:
        if ev["kind"] == "user" and ev["text"]:
            task_full = _strip_leading_timestamp(ev["text"]) or ev["text"]
            break
    # Prefer Cursor's own sidebar name for the chat (the real session title) when we
    # can resolve it from Cursor's state DB; otherwise fall back to the scheduled-task
    # name, then the first line of the opening prompt (the historical behaviour).
    title = (cursor_session_name(uuid) or scheduled_name or task_full.split("\n")[0]).strip()
    if len(title) > 70:
        title = title[:67].rstrip() + "..."
    if not title:
        title = "(untitled session)"

    latest_response = ""
    for ev in reversed(events):
        if ev["kind"] == "assistant" and ev["text"]:
            latest_response = ev["text"]
            break

    latest_tool = None
    for ev in reversed(events):
        if ev["tools"]:
            latest_tool = ev["tools"][-1]
            break

    turn_in_progress = _turn_in_progress(events)
    status = "working" if _is_working(turn_in_progress, mtime, sub_files, cursor_subs=True) else "waiting"
    msg_count = sum(1 for e in events if e["kind"] in ("user", "assistant"))

    # what the agent is doing *right now*: most recent assistant text, else the
    # most recent tool action, else fall back to the opening task.
    latest_activity = latest_response
    latest_kind = "assistant"
    if not latest_activity and latest_tool:
        latest_activity = f"{latest_tool['name']}: {latest_tool.get('detail', '')}".strip().rstrip(":")
        latest_kind = "tool"
    if not latest_activity:
        latest_activity = task_full
        latest_kind = "task"
    latest_short = latest_activity[:360].rstrip() + (" ..." if len(latest_activity) > 360 else "")

    result = {
        "id": uuid,
        "source": "cursor",
        "scheduled": scheduled,
        "name": _name_for(uuid),
        "variant": _variant_for(uuid),
        "project": _pretty_project(project),
        "status": status,
        "turn_in_progress": turn_in_progress,
        "title": title,
        "preview": (task_full[:360].rstrip() + (" ..." if len(task_full) > 360 else "")) or title,
        "latest": latest_short or title,
        "latest_kind": latest_kind,
        # for the hover card: the last tool used (with detail) and the last text message,
        # kept SEPARATE (the ephemeral chip only shows the short tool name).
        "last_tool": (("%s: %s" % (latest_tool["name"], latest_tool.get("detail", ""))).strip().rstrip(":") if latest_tool else ""),
        "last_message": ((latest_response[:360].rstrip() + (" ..." if len(latest_response) > 360 else "")) if latest_response else ""),
        "message_count": msg_count,
        "mtime": mtime,
        "last_activity_rel": _rel_time(time.time() - mtime),
        "_ask_msg": _message_question(uuid, events),
        "_full": False,
    }

    if full:
        timeline = []
        for ev in events[-14:]:
            if ev["kind"] == "turn_ended":
                timeline.append({"role": "system", "text": f"-- turn ended ({ev.get('status')}) --", "tools": []})
                continue
            text = ev["text"]
            if len(text) > 1600:
                text = text[:1600].rstrip() + " ..."
            timeline.append({
                "role": ev["kind"],
                "text": text,
                "tools": ev["tools"][:6],
            })
        result.update({
            "task_full": task_full,
            "latest_response": latest_response[:6000],
            "latest_tool": latest_tool,
            "timeline": timeline,
            "transcript_path": path,
            "_full": True,
        })

    with _CACHE_LOCK:
        _CACHE[uuid] = (mtime, result)
    return result


# --------------------------------------------------------------------------------------
# Claude Code transcripts (~/.claude/projects) -- same office, tagged source="claude"
# --------------------------------------------------------------------------------------

def _claude_pretty_project(dirname):
    """Best-effort label from a Claude project dir.

    Claude encodes the launch cwd as the dir name ('/' -> '-', leading '-'). Real
    dashes make it impossible to reverse perfectly, so we show the last couple of
    path-ish segments -- matching the cursor pretty style (e.g. '...-my-app' ->
    'my-app').
    """
    name = (dirname or "").lstrip("-")
    if name.lower().startswith("users-"):
        parts = name.split("-")
        if len(parts) >= 2:
            name = "-".join(parts[-2:])
    return name


def _normalize_events_claude(path):
    """Normalize a Claude Code .jsonl into the shared event shape.

    Returns ``(events, title, scheduled, scheduled_name)`` where ``title`` is the
    session name: a user-set ``custom-title`` if present, else the auto ``ai-title``.
    Claude Code has no ``turn_ended`` marker, so we only emit user/assistant events;
    tool-result user messages are flagged so the first *real* user prompt (not a tool
    result) can be used as the task. Inline sidechain (subagent) records are skipped so
    the office worker reflects the main thread -- a running Task subagent still surfaces
    as the parent's pending tool_use.

    A session started by a scheduled task / cron opens with a
    ``<scheduled-task name="..." file="...">`` marker in its first user message; we
    detect that (before the tag is stripped) so those agents can be shown as couriers.
    """
    events = []
    ai_title = ""
    custom_title = ""
    scheduled = False
    scheduled_name = ""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except Exception:
                    continue
                if obj.get("type") == "ai-title" and obj.get("aiTitle"):
                    ai_title = obj["aiTitle"]
                    continue
                if obj.get("type") == "custom-title" and obj.get("customTitle"):
                    custom_title = obj["customTitle"]   # a name the user gave the session
                    continue
                if obj.get("isSidechain"):
                    continue
                msg = obj.get("message") or {}
                role = msg.get("role")
                if role not in ("user", "assistant"):
                    continue
                content = msg.get("content") or []
                texts = []
                tools = []
                ask = None
                is_tool_result = False
                if isinstance(content, str):
                    texts.append(content)
                else:
                    for block in content:
                        if not isinstance(block, dict):
                            continue
                        btype = block.get("type")
                        if btype == "text" and block.get("text"):
                            texts.append(block["text"])
                        elif btype == "tool_use":
                            tools.append({
                                "name": block.get("name", "tool"),
                                "detail": _tool_detail(block.get("name", ""), block.get("input")),
                            })
                            if block.get("name") == "AskUserQuestion":
                                inp = block.get("input") if isinstance(block.get("input"), dict) else {}
                                qs = [q for q in (inp.get("questions") or []) if isinstance(q, dict)]
                                ask = {"id": block.get("id") or "", "count": len(qs),
                                       "preview": _short_preview(_clean_text(
                                           next((q.get("question") or "" for q in qs), "")))}
                        elif btype == "tool_result":
                            is_tool_result = True
                injected = False
                if role == "user":
                    joined = "\n".join(texts)  # raw, before tags are stripped
                    # slash-command echoes, local-command output, task notifications,
                    # system reminders and caveats are appended as user-role lines but
                    # are NOT a real user turn -- flag them so turn-detection can skip them.
                    injected = _is_injected_user_text(joined)
                    if not scheduled and "<scheduled-task" in joined:
                        scheduled = True
                        m = re.search(r'name="([^"]+)"', joined)
                        if m:
                            scheduled_name = m.group(1)
                events.append({
                    "kind": role,
                    "text": _clean_text("\n\n".join(texts)),
                    "tools": tools,
                    "is_tool_result": is_tool_result,
                    "injected": injected,
                    "ask": ask,
                })
    except Exception:
        pass
    # a name the user gave the session wins over the auto-generated one
    return events, (custom_title or ai_title), scheduled, scheduled_name


def _turn_in_progress_claude(events):
    """Claude has no ``turn_ended`` marker: a turn is done once the latest message is
    a final assistant answer (text with no pending tool call). Anything else -- a
    fresh user prompt, a tool result awaiting the model, or an in-flight tool_use --
    means the agent is still working (at a desk)."""
    for e in reversed(events):
        if e["kind"] not in ("user", "assistant"):
            continue
        # injected/automated user-role lines (system reminders, task notifications,
        # slash-command echoes, local-command output, caveats) are appended AFTER the
        # final answer -- they are not a real user turn. Skip them, or a finished
        # session would look mid-turn (stuck working at a desk) forever.
        if e["kind"] == "user" and e.get("injected"):
            continue
        # a user interrupt (Ctrl-C / Esc) aborts the turn: the transcript records
        # "[Request interrupted by user...]" and nothing runs after it until the user
        # speaks again. Treat it as a turn boundary -> waiting, not stuck-working forever.
        if e["kind"] == "user" and (e["text"] or "").lstrip().startswith("[Request interrupted by user"):
            return ""
        if e["kind"] == "assistant":
            if e["text"] and not e["tools"]:
                return ""      # delivered a final response -> done, waiting on the user
            return "tool"      # a pending tool_use (may run a long time) -> mid-tool
        # a user event that is a tool result awaits the model -> also mid-tool
        if e.get("is_tool_result"):
            return "tool"
        return "reply"         # a plain user message with no reply yet -> agent owes a reply
    return ""                  # no conversation yet


def _pending_ask_claude(uuid, events):
    """Claude Code's AskUserQuestion blocks the turn until the user picks an answer, which
    lands as its tool_result. Pending = the latest real event is an assistant AskUserQuestion
    tool_use (injected user-role lines skipped, a tool_result or interrupt ends it)."""
    for e in reversed(events):
        if e["kind"] == "user" and e.get("injected"):
            continue
        if e["kind"] != "assistant" or not e.get("ask"):
            return None
        ask = e["ask"]
        return {"asking": "form", "question_id": _fingerprint(uuid, ask["id"]),
                "question_preview": ask["preview"], "question_count": ask["count"]}
    return None


# user-role transcript lines that aren't something the user actually typed: slash commands,
# local command output, task notifications, system reminders, and the local-command caveat.
_INJECTED_USER_PREFIXES = (
    "<command-name>", "<command-message>", "<command-args>", "<command-contents>",
    "<local-command-stdout>", "<local-command-stderr>",
    "<task-notification>", "<system-reminder>", "<user-prompt-submit-hook>",
    "<bash-input>", "<bash-stdout>", "<bash-stderr>",
    "[system notification",
    "caveat: the messages below were generated by the user while running",
)
_TRAILING_INJECT_RE = re.compile(
    r"\n\s*<(?:system-reminder|command-|local-command|task-notification|bash-)", re.IGNORECASE)


def _is_injected_user_text(text):
    return (text or "").lstrip().lower().startswith(_INJECTED_USER_PREFIXES)


def _last_user_instruction(path):
    """Most recent genuine user instruction from a Claude transcript: the last user-role
    text block that is NOT a tool result and NOT injected/automated content (slash commands,
    command output, task notifications, system reminders, caveats). Any injected block the
    harness appended after a real message is trimmed off the end."""
    result = ""
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if '"user"' not in line:            # cheap pre-filter (user lines only)
                    continue
                try:
                    o = json.loads(line)
                except Exception:
                    continue
                m = o.get("message") or {}
                if (o.get("role") or m.get("role")) != "user":
                    continue
                c = m.get("content")
                if c is None:
                    c = o.get("content")
                if isinstance(c, list) and any(
                        isinstance(b, dict) and b.get("type") == "tool_result" for b in c):
                    continue                        # tool output, not a typed message
                txt = ""
                if isinstance(c, str):
                    txt = c
                elif isinstance(c, list):
                    for b in c:
                        if isinstance(b, dict) and b.get("type") == "text":
                            txt += b.get("text", "")
                txt = txt.strip()
                if not txt or _is_injected_user_text(txt):
                    continue
                txt = _TRAILING_INJECT_RE.split(txt, 1)[0].strip()   # drop appended reminders
                if txt:
                    result = txt
    except OSError:
        pass
    return result


def parse_claude_agent(uuid, project, path, mtime, sub_files=None, full=False):
    with _CACHE_LOCK:
        cached = _CACHE.get(uuid)
        if cached and cached[0] == mtime and (full <= cached[1].get("_full", False)):
            return cached[1]

    events, ai_title, scheduled, scheduled_name = _normalize_events_claude(path)

    task_full = ""
    for ev in events:
        if ev["kind"] == "user" and ev["text"] and not ev.get("is_tool_result"):
            task_full = _strip_leading_timestamp(ev["text"]) or ev["text"]
            break

    title = (ai_title or scheduled_name or task_full.split("\n")[0]).strip()
    if len(title) > 70:
        title = title[:67].rstrip() + "..."
    if not title:
        title = "(untitled session)"

    latest_response = ""
    for ev in reversed(events):
        if ev["kind"] == "assistant" and ev["text"]:
            latest_response = ev["text"]
            break

    latest_tool = None
    for ev in reversed(events):
        if ev["tools"]:
            latest_tool = ev["tools"][-1]
            break

    turn_in_progress = _turn_in_progress_claude(events)
    status = "working" if _is_working(turn_in_progress, mtime, sub_files) else "waiting"
    msg_count = sum(1 for e in events if e["kind"] in ("user", "assistant"))

    latest_activity = latest_response
    latest_kind = "assistant"
    if not latest_activity and latest_tool:
        latest_activity = f"{latest_tool['name']}: {latest_tool.get('detail', '')}".strip().rstrip(":")
        latest_kind = "tool"
    if not latest_activity:
        latest_activity = task_full
        latest_kind = "task"
    latest_short = latest_activity[:360].rstrip() + (" ..." if len(latest_activity) > 360 else "")

    # the most recent real thing the user typed (skip tool-result / system turns) --
    # shown as "Last instruction" alongside the agent's own latest activity.
    last_instruction = _last_user_instruction(path)
    last_instruction = _strip_leading_timestamp(last_instruction) or last_instruction
    if len(last_instruction) > 200:
        last_instruction = last_instruction[:200].rstrip() + " ..."

    usage = _claude_usage(path)

    result = {
        "id": uuid,
        "source": "claude",
        "scheduled": scheduled,
        "name": _name_for(uuid),
        "variant": _variant_for(uuid),
        "project": _claude_pretty_project(project),
        "status": status,
        "turn_in_progress": turn_in_progress,
        "title": title,
        "preview": (task_full[:360].rstrip() + (" ..." if len(task_full) > 360 else "")) or title,
        "latest": latest_short or title,
        "latest_kind": latest_kind,
        # hover card: last tool used (with detail) + last text message, kept SEPARATE
        # (the ephemeral chip only shows the short tool name).
        "last_tool": (("%s: %s" % (latest_tool["name"], latest_tool.get("detail", ""))).strip().rstrip(":") if latest_tool else ""),
        "last_message": ((latest_response[:360].rstrip() + (" ..." if len(latest_response) > 360 else "")) if latest_response else ""),
        "last_instruction": last_instruction,
        "message_count": msg_count,
        "model": usage["model"],
        "tokens": usage["tokens"],
        "spend": usage["spend"],
        "mtime": mtime,
        "last_activity_rel": _rel_time(time.time() - mtime),
        "_ask_form": _pending_ask_claude(uuid, events),
        "_ask_msg": _message_question(uuid, events, skip_injected=True),
        "_full": False,
    }

    if full:
        timeline = []
        for ev in events[-14:]:
            text = ev["text"]
            if len(text) > 1600:
                text = text[:1600].rstrip() + " ..."
            timeline.append({
                "role": ev["kind"],
                "text": text,
                "tools": ev["tools"][:6],
            })
        result.update({
            "task_full": task_full,
            "latest_response": latest_response[:6000],
            "latest_tool": latest_tool,
            "timeline": timeline,
            "transcript_path": path,
            "_full": True,
        })

    with _CACHE_LOCK:
        _CACHE[uuid] = (mtime, result)
    return result


def discover_claude_transcripts():
    """Yield (uuid, project_dir, abspath, eff_mtime, sub_files) for Claude Code chats.

    Each chat is ``~/.claude/projects/<encoded-cwd>/<uuid>.jsonl`` with Task
    subagents in a sibling ``<uuid>/subagents/*.jsonl``. ``eff_mtime`` rolls up the
    freshest write across the chat and its subagents (so a session whose work runs in
    a background subagent still reads as working). Duplicate uuids across roots keep
    the freshest copy, mirroring the cursor discovery.
    """
    if not os.path.isdir(CLAUDE_PROJECTS_DIR):
        return
    try:
        projects = os.listdir(CLAUDE_PROJECTS_DIR)
    except OSError:
        return

    cands = {}  # uuid -> [(eff_mtime, n_sub, project_dir, jsonl, sub_files), ...]
    for project in projects:
        pdir = os.path.join(CLAUDE_PROJECTS_DIR, project)
        if not os.path.isdir(pdir):
            continue
        try:
            entries = os.listdir(pdir)
        except OSError:
            continue
        for entry in entries:
            if not entry.endswith(".jsonl"):
                continue
            uuid = entry[: -len(".jsonl")]
            jsonl = os.path.join(pdir, entry)
            if not os.path.isfile(jsonl):
                continue
            try:
                mtime = os.path.getmtime(jsonl)
            except OSError:
                continue
            sf = []
            sub_dir = os.path.join(pdir, uuid, "subagents")
            if os.path.isdir(sub_dir):
                try:
                    for sfn in os.listdir(sub_dir):
                        if not sfn.endswith(".jsonl"):
                            continue
                        sp = os.path.join(sub_dir, sfn)
                        try:
                            sf.append((sp, os.path.getmtime(sp)))
                        except OSError:
                            pass
                except OSError:
                    pass
            sub_m = max((m for _, m in sf), default=0)
            eff_mtime = max(mtime, sub_m)
            cands.setdefault(uuid, []).append((eff_mtime, len(sf), project, jsonl, sf))

    for uuid, lst in cands.items():
        eff_mtime, _n, project, jsonl, sf = max(lst, key=lambda c: (c[0], c[1]))
        yield uuid, project, jsonl, eff_mtime, sf


# --------------------------------------------------------------------------------------
# Per-session usage: model, token throughput, rough $ spend  (Claude transcripts)
# --------------------------------------------------------------------------------------

def _model_family(model_id):
    m = (model_id or "").lower()
    if "opus" in m:
        return "opus"
    if "sonnet" in m:
        return "sonnet"
    if "haiku" in m:
        return "haiku"
    return None


def _pretty_model(model_id):
    """'claude-opus-4-8' -> 'Opus 4.8'; unknown ids returned as-is."""
    fam = _model_family(model_id)
    if not fam:
        return model_id or ""
    label = fam.capitalize()
    ver = re.search(r"(\d+)[-.](\d+)", model_id or "")
    return f"{label} {ver.group(1)}.{ver.group(2)}" if ver else label


def _claude_usage(path):
    """One raw scan of a Claude transcript: latest model, cumulative token throughput
    (input+output+cache) and a best-effort $ spend estimate from _MODEL_PRICING."""
    model_id = ""
    total = 0
    spend = 0.0
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if '"usage"' not in line and '"model"' not in line:
                    continue
                try:
                    o = json.loads(line)
                except Exception:
                    continue
                msg = o.get("message") or {}
                if not (o.get("type") == "assistant" or msg.get("role") == "assistant"):
                    continue
                if msg.get("model"):
                    model_id = msg["model"]
                u = msg.get("usage") or {}
                it = u.get("input_tokens") or 0
                ot = u.get("output_tokens") or 0
                cr = u.get("cache_read_input_tokens") or 0
                cw = u.get("cache_creation_input_tokens") or 0
                total += it + ot + cr + cw
                fam = _model_family(msg.get("model") or model_id)
                if fam:
                    pin, pout = _MODEL_PRICING[fam]
                    spend += (it * pin + ot * pout + cr * pin * 0.1 + cw * pin * 1.25) / 1_000_000
    except OSError:
        pass
    return {
        "model": _pretty_model(model_id),
        "tokens": total or None,
        "spend": round(spend, 2) if spend else None,
    }


# --------------------------------------------------------------------------------------
# Dynamic Workflow (the Workflow tool) discovery  (Claude-only, like the transcripts)
# --------------------------------------------------------------------------------------

def _find_workflow_script(session_dir, run_id):
    """The sibling script for a run lives at <session>/workflows/scripts/*-<run_id>.js."""
    sdir = os.path.join(session_dir, "workflows", "scripts")
    try:
        for fn in os.listdir(sdir):
            if fn.endswith(run_id + ".js"):
                return os.path.join(sdir, fn)
    except OSError:
        pass
    return None


def _parse_workflow_script(script_path):
    """Best-effort regex-extract of the script's `export const meta = {...}` literal:
    name, description and phase titles (capped). Never load-bearing -- always a fallback."""
    try:
        st = os.stat(script_path)
    except OSError:
        return {}
    cached = _WORKFLOW_SCRIPT_CACHE.get(script_path)
    if cached and cached[0] == st.st_mtime:
        return cached[1]
    meta = {"name": "", "description": "", "phases": []}
    try:
        with open(script_path, "r", encoding="utf-8", errors="replace") as fh:
            head = fh.read(20000)
        m = re.search(r"name:\s*['\"]([^'\"]+)['\"]", head)
        if m:
            meta["name"] = m.group(1)
        m = re.search(r"description:\s*['\"]([^'\"]+)['\"]", head)
        if m:
            meta["description"] = m.group(1)
        block = re.search(r"phases:\s*\[(.*?)\]", head, re.S)
        if block:
            for pm in re.finditer(r"title:\s*['\"]([^'\"]+)['\"]", block.group(1)):
                meta["phases"].append({"title": pm.group(1)})
                if len(meta["phases"]) >= 12:
                    break
    except OSError:
        pass
    _WORKFLOW_SCRIPT_CACHE[script_path] = (st.st_mtime, meta)
    return meta


def _workflow_identities(uuid, jsonl_path, mtime):
    """Scan the PARENT transcript for `toolUseResult` blobs of launched local workflows,
    returning {runId: {name, summary, scriptPath}}. Cached by parent mtime."""
    cached = _WORKFLOW_IDENTITY_CACHE.get(uuid)
    if cached and cached[0] == mtime:
        return cached[1]
    out = {}
    try:
        with open(jsonl_path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if "local_workflow" not in line:   # cheap pre-filter before json.loads
                    continue
                try:
                    o = json.loads(line)
                except Exception:
                    continue
                tur = o.get("toolUseResult")
                if isinstance(tur, dict) and tur.get("taskType") == "local_workflow":
                    rid = tur.get("runId")
                    if rid:
                        out[rid] = {
                            "name": tur.get("workflowName") or "",
                            "summary": tur.get("summary") or "",
                            "scriptPath": tur.get("scriptPath") or "",
                        }
    except OSError:
        pass
    _WORKFLOW_IDENTITY_CACHE[uuid] = (mtime, out)
    return out


# STRONG markers are unambiguous per-agent task headings -> jump to them wherever they appear
# (a shared preamble can be arbitrarily long). WEAK ones are common words -> only near the top.
_TASK_MARKERS_STRONG = ("YOUR AREA", "YOUR TASK", "YOUR JOB", "YOUR FOCUS", "YOUR SLICE",
                        "YOUR MISSION", "YOUR GOAL", "YOUR PIECE", "YOUR ROLE")
_TASK_MARKERS_WEAK = ("TASK:", "GOAL:", "OBJECTIVE:", "FOCUS:", "AREA:", "ROLE:")
_MARKER_HEAD_RE = re.compile(r"^(YOUR\s+[A-Za-z]+|TASK|GOAL|OBJECTIVE|FOCUS|AREA|ROLE|MISSION)"
                             r"\s*[:\-–—]+\s*", re.I)


def _distinctive_details(prompts, cap=140):
    """Per-agent SHORT label capturing what *that* subagent does. Sibling workflow agents
    almost always share a large identical preamble (the same context/instructions block) with
    only a small distinctive slice -- e.g. ``YOUR AREA -- ...`` -- differing, so the naive
    first-N-chars makes every helper-dwarf read identically. We strip the prefix common to all
    siblings in the run and/or jump to a task-marker heading, then collapse to one short line.
    Robust across arbitrary scripts (no dependency on the workflow source or agent() labels)."""
    nonempty = [p for p in prompts if p]
    cut = 0
    if len(nonempty) >= 2:                       # longest prefix shared by every sibling prompt
        s0, m = nonempty[0], len(nonempty[0])
        for p in nonempty[1:]:
            i, lim = 0, min(m, len(p))
            while i < lim and s0[i] == p[i]:
                i += 1
            m = i
            if not m:
                break
        if 0 < m < len(s0):                      # back up to a word/newline boundary
            b = max(s0.rfind("\n", 0, m), s0.rfind(" ", 0, m))
            cut = b if b > 0 else m
    out = []
    for p in prompts:
        if not p:
            out.append("")
            continue
        rest = p[cut:] if 0 < cut < len(p) else p
        up = rest.upper()
        hits =  [j for j in (up.find(mk) for mk in _TASK_MARKERS_STRONG) if j >= 0]
        hits += [j for j in (up.find(mk) for mk in _TASK_MARKERS_WEAK) if 0 <= j <= 240]
        if hits:
            rest = rest[min(hits):]              # jump to the per-agent "YOUR AREA / TASK:" heading
        rest = _MARKER_HEAD_RE.sub("", rest)     # drop the heading word itself
        rest = re.sub(r"\s+", " ", rest.lstrip(" \t\n-–—*:>#")).strip()
        out.append(rest[:cap].strip())
    return out


def _workflow_progress(run_dir):
    """Parse a run's journal.jsonl into {total, done, running, active[], latest_mtime,
    had_retries}. Logical tasks are keyed by the journal ``key`` (not agentId) so a retried
    task collapses to one; a task is counted RUNNING only when it has a started event, no
    result, AND its freshest agent-<id>.jsonl was written within SUBAGENT_ACTIVE_SECONDS --
    a started-with-no-result whose transcript went cold long ago died/finished silently and
    must not show as running. Journal parse cached by (mtime, size); freshness refreshed
    cheaply each call. Each active subagent's ``detail`` is de-boilerplated by
    ``_distinctive_details`` so sibling dwarves read distinctly."""
    journal = os.path.join(run_dir, "journal.jsonl")
    try:
        st = os.stat(journal)
    except OSError:
        return {"total": 0, "done": 0, "running": 0, "active": [], "latest_mtime": 0.0, "had_retries": False}
    cache_key = (st.st_mtime, st.st_size)
    cached = _WORKFLOW_JOURNAL_CACHE.get(run_dir)
    if cached and cached[0] == cache_key:
        base = cached[1]
    else:
        started_keys, result_keys, key_agents = set(), set(), {}
        n_started = 0
        try:
            with open(journal, "r", encoding="utf-8", errors="replace") as fh:
                for line in fh:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        o = json.loads(line)
                    except Exception:
                        continue
                    k = o.get("key"); aid = o.get("agentId"); t = o.get("type")
                    if not k or not aid:
                        continue
                    if t == "started":
                        n_started += 1
                        started_keys.add(k)
                        key_agents.setdefault(k, []).append(aid)
                    elif t == "result":
                        result_keys.add(k)
        except OSError:
            started_keys, result_keys, key_agents, n_started = set(), set(), {}, 0
        base = {
            "total": len(started_keys),
            "done": len(started_keys & result_keys),
            "open_keys": [k for k in started_keys if k not in result_keys],
            "key_agents": key_agents,
            "had_retries": n_started != len(started_keys),
        }
        _WORKFLOW_JOURNAL_CACHE[run_dir] = (cache_key, base)
    now = time.time()
    latest = st.st_mtime
    running_fresh = 0
    pending = []
    for k in base["open_keys"]:
        best_am, best_aid = None, None
        for aid in base["key_agents"].get(k, []):
            ap = os.path.join(run_dir, "agent-%s.jsonl" % aid)
            try:
                am = os.path.getmtime(ap)
            except OSError:
                continue
            if am > latest:
                latest = am
            if best_am is None or am > best_am:
                best_am, best_aid = am, aid
        if best_am is None or (now - best_am) > SUBAGENT_ACTIVE_SECONDS:
            continue   # never written, or went cold -> died/finished without a result
        running_fresh += 1
        if len(pending) < 6:
            ap = os.path.join(run_dir, "agent-%s.jsonl" % best_aid)
            bub_txt, bub_kind, last_tool, last_message = _sub_activity(ap)
            pending.append({"type": "workflow-subagent", "_prompt": _first_user_text(ap),
                            "id": best_aid, "last_msg": bub_txt[:160], "last_kind": bub_kind,
                            "last_tool": last_tool, "last_message": last_message, "ts": best_am,
                            "doing": _sub_last_tool_plain(ap), "started": _file_started(ap)})
    # de-boilerplate the sibling prompts together so each dwarf reads distinctly
    details = _distinctive_details([p.pop("_prompt") for p in pending])
    active = []
    for p, d in zip(pending, details):
        p["detail"] = d or "workflow subagent"
        p["title"] = _clean_helper_title(p["detail"])
        active.append(p)
    return {
        "total": base["total"],
        "done": base["done"],
        "running": running_fresh,
        "active": active,
        "latest_mtime": latest,
        "had_retries": base["had_retries"],
    }


def _phase_states(phases, total, done, running, counts, trustworthy):
    """Colour an ordered phase list done/active/pending. Phases complete strictly in order
    (each phase is fully awaited before the next), so overall progress maps monotonically
    onto the stepper. When `trustworthy` (exact per-phase counts known and consistent) we
    greedily fill done-then-running across the counts for real per-phase (done, running,
    count); otherwise we only highlight the single phase the overall fraction lands in and
    print NO per-phase number (fabricating one would be dishonest -- per-phase counts are
    not recoverable from disk for most runs)."""
    k = len(phases)
    states = ["pending"] * k
    if k == 0:
        return states, None
    if trustworthy and counts and sum(counts) == total:
        rd, rr, per = done, running, []
        for c in counts:
            d = min(c, rd); rd -= d
            r = min(c - d, rr); rr -= r
            per.append((d, r, c))
        for i, (d, r, c) in enumerate(per):
            states[i] = "done" if (c > 0 and d == c) else ("active" if (d > 0 or r > 0) else "pending")
        return states, per
    if total and running == 0 and done >= total:
        return ["done"] * k, None
    idx = 0 if not total else min(k - 1, int((done / max(total, 1)) * k))
    for i in range(k):
        states[i] = "done" if i < idx else ("active" if i == idx else "pending")
    return states, None


def _discover_workflow_runs(uuid, jsonl_path, mtime, session_dir):
    """(display_runs, wf_latest) for a Claude session. display_runs are the runs that are
    currently running or finished within WORKFLOW_FRESH_SECONDS (running first, then by
    size); wf_latest is the freshest write across ALL runs (drives working/kitchen)."""
    wf_root = os.path.join(session_dir, "subagents", "workflows")
    if not os.path.isdir(wf_root):
        return [], 0.0
    try:
        names = os.listdir(wf_root)
    except OSError:
        return [], 0.0
    identities = None
    runs = []
    wf_latest = 0.0
    for name in names:
        if not name.startswith("wf_"):
            continue
        run_dir = os.path.join(wf_root, name)
        if not os.path.isdir(run_dir):
            continue
        prog = _workflow_progress(run_dir)
        wf_latest = max(wf_latest, prog["latest_mtime"])   # must stay BEFORE the gate (feeds _is_working)
        if prog["running"] <= 0:      # only show a run that has a genuinely-live agent right now
            continue
        if identities is None:
            identities = _workflow_identities(uuid, jsonl_path, mtime)
        ident = identities.get(name, {})
        wname = ident.get("name") or ""
        summary = ident.get("summary") or ""
        meta = {}
        script_path = ident.get("scriptPath") or _find_workflow_script(session_dir, name)
        if script_path:
            meta = _parse_workflow_script(script_path)
            wname = wname or meta.get("name") or ""
            summary = summary or meta.get("description") or ""
        phases = meta.get("phases") or []
        # honest phase stepper: colour each phase done/active/pending from overall logical
        # progress. Real per-phase counts are NOT recoverable from disk, so they appear only
        # when a strict trust gate proves them (currently never -- counts stay None). See
        # _phase_states.
        counts = [p.get("count") for p in phases]
        have_counts = len(counts) > 0 and all(c is not None for c in counts)
        trustworthy = (have_counts and not meta.get("dynamic")
                       and not prog["had_retries"]
                       and sum(c for c in counts) == prog["total"] and prog["total"] > 0)
        states, per = _phase_states(phases, prog["total"], prog["done"], prog["running"],
                                    counts if have_counts else None, trustworthy)
        enriched = []
        for i, p in enumerate(phases):
            e = {"title": p.get("title", ""), "detail": p.get("detail", ""), "state": states[i]}
            if per is not None:
                d, r, c = per[i]
                e["done"], e["running"], e["count"] = d, r, c
            enriched.append(e)
        phases = enriched
        if not wname:
            wname = name
        runs.append({
            "runId": name,
            "name": wname,
            "summary": summary,
            "phases": phases,
            "phase_trusted": per is not None,
            "total": prog["total"],
            "done": prog["done"],
            "running": prog["running"],
            "active": prog["active"],
        })
    runs.sort(key=lambda r: (0 if r["running"] > 0 else 1, -r["total"]))
    return runs, wf_latest


def _session_dir_for(path):
    """The session subdir (holding subagents/ and workflows/) for a parent transcript."""
    return path[:-len(".jsonl")] if path.endswith(".jsonl") else path


# Registry so get_agents / list_projects / get_agent_detail can walk every source
# uniformly. Each entry: (source_name, discover_fn, parse_fn).
_SOURCES = [
    ("cursor", discover_transcripts, parse_agent),
    ("claude", discover_claude_transcripts, parse_claude_agent),
]


def _project_matches(needle, *labels):
    """Substring match a --project needle against any of the given labels (raw dir
    and/or pretty label). Empty needle matches everything."""
    if not needle:
        return True
    needle = needle.lower()
    return any(needle in (lbl or "").lower() for lbl in labels)


def _enabled_sources(sources):
    """Filter the source registry by name (None -> all)."""
    if not sources:
        return _SOURCES
    want = set(sources)
    return [s for s in _SOURCES if s[0] in want]


def _cursor_project_folder(fs_path):
    """Cursor's ~/.cursor/projects/<folder> name for a workspace path."""
    folder = re.sub(r"[^A-Za-z0-9]+", "-", fs_path or "").strip("-")
    return folder or "empty-window"


def _untranscribed_cursor_agent(uuid, info, live_at):
    """A WORKING placeholder for a Cursor chat whose run is in flight but which has no
    transcript yet (a new chat's .jsonl is only created when its first turn ends)."""
    project = _cursor_project_folder(info.get("folder"))
    title = info.get("name") or "(new chat)"
    if len(title) > 70:
        title = title[:67].rstrip() + "..."
    subs = _untranscribed_subagents(uuid, [])
    return {
        "id": uuid,
        "source": "cursor",
        "scheduled": False,
        "name": _name_for(uuid),
        "variant": _variant_for(uuid),
        "project": _pretty_project(project),
        "_project_folder": project,
        "status": "working",
        "turn_in_progress": True,
        "run_in_flight": True,
        "no_transcript": True,
        "title": title,
        "preview": title,
        "latest": "working on the first turn (transcript not written yet)",
        "latest_kind": "task",
        "last_tool": "",
        "last_message": "",
        "message_count": 0,
        "mtime": live_at,
        "last_activity_rel": _rel_time(time.time() - live_at),
        "_full": False,
        "workflows": [],
        "wf_running_agents": 0,
        "self_active": True,
        "subagents": subs,
        "subs": len(subs),
        "shells": [],
        "listening": [],
    }


def _untranscribed_cursor_agents(live, live_infos, transcribed_ids):
    with _KNOWN_SUBAGENT_LOCK:
        known_subs = set(_KNOWN_SUBAGENT_IDS)
    out = []
    for u, live_at in live.items():
        info = live_infos.get(u) or {}
        if u in transcribed_ids or u in known_subs or info.get("parent"):
            continue
        out.append(_untranscribed_cursor_agent(u, info, live_at))
    return out


def get_agents(hours, full=False, project_filter=None, sources=None):
    cutoff = time.time() - hours * 3600
    agents = []
    enabled = _enabled_sources(sources)
    live, live_infos = cursor_live_runs() if any(s[0] == "cursor" for s in enabled) else ({}, {})
    cursor_ids = set()
    listen_paths = {}
    for _src, discover, parse in enabled:
        for uuid, project, path, mtime, _sub_files in discover():
            live_at = live.get(uuid, 0.0) if _src == "cursor" else 0.0
            if _src == "cursor":
                cursor_ids.add(uuid)
            if max(mtime, live_at) < cutoff:
                continue
            a = parse(uuid, project, path, mtime, sub_files=_sub_files, full=full)
            if not _project_matches(project_filter, project, a["project"]):
                continue
            # dynamic Workflow tents (Claude only) + their freshness (keeps a parent at a
            # desk while its workflow subagents run, even though its own turn has ended).
            if SHOW_WORKFLOWS and _src == "claude":
                wf_runs, wf_latest = _discover_workflow_runs(uuid, path, mtime, _session_dir_for(path))
            else:
                wf_runs, wf_latest = [], 0.0
            a["workflows"] = wf_runs
            a["wf_running_agents"] = sum(r["running"] for r in wf_runs)
            # recompute status fresh each request: parse is cached, but working/
            # kitchen depends on wall-clock (the staleness cap + subagent freshness)
            # vs the turn state, so it can change even when the transcript hasn't.
            cursor_subs = _src == "cursor"
            # `a` is the parse cache's dict: the live-run overlay goes in separate keys
            # recomputed every request, never into the cached turn_in_progress.
            own_turn = bool(live_at) or (bool(a.get("turn_in_progress"))
                                         and not (cursor_subs and cursor_run_finished(uuid)))
            eff = max(mtime, live_at)
            a["run_in_flight"] = bool(live_at)
            a["mtime"] = eff
            a["status"] = "working" if _is_working(own_turn, eff, _sub_files, wf_latest,
                                                   cursor_subs) else "waiting"
            # parent is "self active" only while its OWN turn is in progress; when it's merely
            # working because a subagent/workflow is live, the desk should stop typing (item 8).
            a["self_active"] = own_turn and a["status"] == "working"
            a["last_activity_rel"] = _rel_time(time.time() - eff)
            # running subagents -> little helpers
            a["subagents"] = (_cursor_helpers(uuid, _sub_files, bool(live_at), a["status"] == "working")
                              if cursor_subs else _subagent_infos(_sub_files))
            a["subs"] = len(a["subagents"])
            # open background shells (Claude only) -> little terminal windows. A background
            # shell survives the turn, so show it whether the chat is at a desk (working) or
            # in the kitchen (waiting) -- but not for archived/beach agents. Only genuinely-
            # running ones become sprites.
            if _src == "claude":
                _overlay_claude_ask(a, eff)
            if _src == "claude" and a["status"] in ("working", "waiting"):
                a["shells"] = [s for s in _open_shells_claude(path) if s["running"]][:3]
            else:
                a["shells"] = []
            a["listening"] = []
            if _src == "cursor":
                listen_paths[uuid] = path
            agents.append(a)
    if listen_paths:
        listening = cursor_listening(listen_paths)
        for a in agents:
            if a["source"] == "cursor":
                a["listening"] = listening.get(a["id"]) or []
    if any(s[0] == "cursor" for s in enabled):
        for a in _untranscribed_cursor_agents(live, live_infos, cursor_ids):
            if a["mtime"] >= cutoff and _project_matches(project_filter, a["_project_folder"], a["project"]):
                agents.append(a)
        _overlay_cursor_asks([a for a in agents if a["source"] == "cursor"], live)
        for a in _untranscribed_asking_cursor_agents(live, cursor_ids):
            if _project_matches(project_filter, a["_project_folder"], a["project"]):
                agents.append(a)
    agents.sort(key=lambda a: a["mtime"], reverse=True)
    return agents


def _overlay_claude_ask(a, eff):
    fresh = (time.time() - eff) <= ASK_RECENT_SECONDS
    ask = a.get("_ask_form") if fresh else None
    if not ask and a["status"] == "waiting":
        ask = a.get("_ask_msg")
    _apply_ask(a, ask, eff)


def _overlay_cursor_asks(cursor_agents, live):
    """Batch the form lookup over Cursor chats in flight or active within ASK_RECENT_SECONDS;
    the rest only get the (transcript-only) message heuristic."""
    now = time.time()
    cands = [a["id"] for a in cursor_agents
             if a.get("run_in_flight") or (now - a["mtime"]) <= ASK_RECENT_SECONDS]
    forms = cursor_pending_forms(cands, live.keys()) if cands else {}
    for a in cursor_agents:
        ask = forms.get(a["id"])
        if not ask and a["status"] == "waiting":
            ask = a.get("_ask_msg")
        _apply_ask(a, ask, a["mtime"])


def _untranscribed_asking_cursor_agents(live, transcribed_ids):
    """Kitchen placeholders for chats that wrote to Cursor's DB recently, have no transcript
    and are not in flight, yet are blocked on a pending form -- a new chat's first turn ends
    at the form, so no .jsonl exists until it is answered."""
    writers = cursor_recent_writers()
    with _KNOWN_SUBAGENT_LOCK:
        known_subs = set(_KNOWN_SUBAGENT_IDS)
    cands = [u for u in writers if u not in transcribed_ids and u not in live and u not in known_subs]
    if not cands:
        return []
    infos = cursor_run_info(cands)
    cands = [u for u in cands if infos.get(u) and not infos[u]["parent"]]
    forms = cursor_pending_forms(cands) if cands else {}
    out = []
    for u in cands:
        ask = forms.get(u)
        if not ask:
            continue
        a = _untranscribed_cursor_agent(u, infos[u], ask["asked_at"] or time.time())
        a.update({"status": "waiting", "turn_in_progress": False, "run_in_flight": False,
                  "latest": "waiting for your answer to a question form (transcript not written yet)"})
        _apply_ask(a, ask, a["mtime"])
        out.append(a)
    return out


def list_projects(hours, sources=None):
    """Return [(pretty_label, raw_folder, active_count, source)] sorted by activity."""
    cutoff = time.time() - hours * 3600
    counts = {}
    for src, discover, parse in _enabled_sources(sources):
        for uuid, project, path, mtime, _sub_files in discover():
            if mtime < cutoff:
                continue
            a = parse(uuid, project, path, mtime, sub_files=_sub_files, full=False)
            key = (a["project"], project, src)
            counts[key] = counts.get(key, 0) + 1
    rows = [(pretty, raw, n, src) for (pretty, raw, src), n in counts.items()]
    rows.sort(key=lambda r: (-r[2], r[0]))
    return rows


def get_agent_detail(uuid):
    live, live_infos = cursor_live_runs()
    for _src, discover, parse in _SOURCES:
        for u, project, path, mtime, _sub_files in discover():
            if u == uuid:
                d = parse(uuid, project, path, mtime, sub_files=_sub_files, full=True)
                if SHOW_WORKFLOWS and _src == "claude":
                    wf_runs, wf_latest = _discover_workflow_runs(uuid, path, mtime, _session_dir_for(path))
                else:
                    wf_runs, wf_latest = [], 0.0
                d["workflows"] = wf_runs
                cursor_subs = _src == "cursor"
                live_at = live.get(uuid, 0.0) if cursor_subs else 0.0
                eff = max(mtime, live_at)
                d["run_in_flight"] = bool(live_at)
                d["mtime"] = eff
                own_turn = bool(live_at) or (bool(d.get("turn_in_progress"))
                                             and not (cursor_subs and cursor_run_finished(uuid)))
                d["status"] = "working" if _is_working(own_turn, eff, _sub_files, wf_latest,
                                                       cursor_subs) else "waiting"
                d["last_activity_rel"] = _rel_time(time.time() - eff)
                d["subagents"] = (_cursor_helpers(uuid, _sub_files, bool(live_at), d["status"] == "working")
                                  if cursor_subs else _subagent_infos(_sub_files))
                d["subs"] = len(d["subagents"])
                d["shells"] = ([s for s in _open_shells_claude(path) if s["running"]][:3]
                               if _src == "claude" else [])
                if cursor_subs:
                    _overlay_cursor_asks([d], live)
                else:
                    _overlay_claude_ask(d, eff)
                d["listening"] = (cursor_listening({uuid: path}).get(uuid) or []) if cursor_subs else []
                return d
    if uuid in live:
        agents = _untranscribed_cursor_agents({uuid: live[uuid]}, live_infos, set())
        _overlay_cursor_asks(agents, live)
    else:
        agents = [a for a in _untranscribed_asking_cursor_agents(live, set()) if a["id"] == uuid]
    if agents:
        agents[0].update({"task_full": agents[0]["title"], "latest_response": "", "latest_tool": None,
                          "timeline": [], "transcript_path": "", "_full": True})
        return agents[0]
    return None


def _demo_working_agents(n, now):
    """TEST HOOK (--demo-working N): exactly N synthetic WORKING agents, all destined for
    desks, so the dynamic desk scaling can be verified at any headcount."""
    titles = [
        "Refactor the data export pipeline", "Add pagination to the users API",
        "Investigate the slow orders query", "Audit the payments service",
        "Migrate the auth tokens to Auth0", "Wire up the websocket consumers",
        "Backfill the audit log schema", "Tune the Celery beat schedule",
        "Harden the file-converter uploads", "Index the provider search",
    ]
    out = []
    for i in range(n):
        uuid = "demo-work-%04d" % i
        source = "cursor" if (i % 2 == 0) else "claude"
        title = "%s #%d" % (titles[i % len(titles)], i + 1)
        out.append({
            "id": uuid,
            "source": source,
            "scheduled": False,
            "subagents": [],
            "subs": 0,
            "shells": [],
            "listening": [],
            "workflows": [],
            "wf_running_agents": 0,
            "self_active": True,
            "name": _name_for(uuid),
            "variant": _variant_for(uuid),
            "project": "demo-scaling",
            "status": "working",
            "title": title,
            "preview": title,
            "latest": "Editing %s.py" % title.split()[1].lower(),
            "latest_kind": "tool",
            "last_tool": "Edit: service.py",
            "last_message": "Working on " + title.split()[1].lower(),
            "last_instruction": "Please " + title[0].lower() + title[1:],
            "message_count": 9,
            "model": "Opus 4.8" if source == "claude" else None,
            "tokens": (820_000 if source == "claude" else None),
            "spend": (2.11 if source == "claude" else None),
            "mtime": now - 30,
            "last_activity_rel": _rel_time(30),
            "demo": True,
        })
    return out


def demo_agents():
    now = time.time()
    if DEMO_WORKING > 0:
        return _demo_working_agents(DEMO_WORKING, now)
    # working agents / their live helpers occasionally "say" a new thing; each gets its own
    # slow, staggered clock so the office shows the odd bubble popping -- not a wall of them.
    def _blip(off, period=15):
        return int((now + off) // period)
    subs_a = [{"type": "general-purpose",
               "detail": "Thursday, Nov 26, 2026, 11:33 AM (UTC+2) You work in the demo repo at "
                         "/tmp/demo-repo (GitHub: acme/demo). PHASE 1 OF 2: Review the working diff for bugs",
               "id": "demoA-0", "last_msg": "Grep: export path (%d)" % _blip(0), "last_kind": "tool",
               "last_tool": "Grep: export path",
               "last_message": "**Found the culprit:** the `export` config loader reads the settings file twice on "
                               "every request, which explains the drift. Next I'll check the cache layer.", "ts": now},
              {"type": "test-runner", "detail": "Run the unit test suite",
               "id": "demoA-1", "last_msg": "unit suite green, pass %d" % _blip(5), "last_kind": "assistant",
               "last_tool": "Bash: pytest -q", "last_message": "unit suite green, all 42 pass", "ts": now}]
    subs_e = [{"type": "explorer", "detail": "Map the ORM query paths",
               "id": "demoE-0", "last_msg": "Read: orders.py (%d)" % _blip(2), "last_kind": "tool",
               "last_tool": "Read: orders.py", "last_message": "tracing the pagination query", "ts": now},
              {"type": "db-analyst", "detail": "EXPLAIN the slow orders query",
               "id": "demoE-1", "last_msg": "Bash: EXPLAIN ANALYZE (%d)" % _blip(8), "last_kind": "tool",
               "last_tool": "Bash: EXPLAIN ANALYZE orders", "last_message": "the seq scan is the bottleneck", "ts": now},
              {"type": "doc-writer", "detail": "Draft the fix summary",
               "id": "demoE-2", "last_msg": "drafting summary v%d" % _blip(12), "last_kind": "assistant",
               "last_tool": "Edit: report.md", "last_message": "drafting the fix summary", "ts": now}]
    wf_demo = [{
        "runId": "wf_demo01",
        "name": "exhaustive-security-audit",
        "summary": "Fan out finders across every subsystem, then adversarially verify each finding before reporting",
        "phases": [{"title": "Find", "state": "done"}, {"title": "Verify", "state": "active"},
                   {"title": "Synthesize", "state": "pending"}],
        "phase_trusted": False,
        "total": 21, "done": 14, "running": 3,
        "active": [{"type": "workflow-subagent", "detail": "Verify the auth-bypass finding",
                    "id": "demoW-0", "last_msg": "auth-bypass looks real (%d)" % _blip(3), "last_kind": "assistant",
                    "last_tool": "Read: auth/middleware.py", "last_message": "auth-bypass looks real -- no token check on the admin route", "ts": now},
                   {"type": "workflow-subagent", "detail": "Refute the SSRF candidate",
                    "id": "demoW-1", "last_msg": "Edit: sanitizer.py (%d)" % _blip(9), "last_kind": "tool",
                    "last_tool": "Edit: sanitizer.py", "last_message": "the SSRF filter is actually sound", "ts": now},
                   {"type": "workflow-subagent", "detail": "Check the deserialization sink",
                    "id": "demoW-2", "last_msg": "WebFetch: cve database (%d)" % _blip(14), "last_kind": "tool",
                    "last_tool": "WebFetch: nvd.nist.gov", "last_message": "cross-checking against the CVE list", "ts": now}],
    }]
    for i, s in enumerate(subs_a + subs_e + wf_demo[0]["active"]):
        tname, _, tdet = s["last_tool"].partition(": ")
        s["title"] = _clean_helper_title(s["detail"])
        s["doing"] = _tool_plain(tname, {"command": tdet, "path": tdet})
        s["started"] = now - 75 - 140 * i
    samples = [
        ("demo-aaaa-0001", "working", "Refactor the data export pipeline", 120, "cursor", False, subs_a, []),
        ("demo-bbbb-0002", "working", "Add pagination to the users API endpoint", 600, "claude", False, [], []),
        ("demo-cccc-0003", "waiting", "Why is this record showing up as archived?", 1800, "cursor", False, [], []),
        ("demo-dddd-0004", "waiting", "Write tests for the CSV importer", 5400, "claude", False, [], []),
        ("demo-eeee-0005", "working", "Investigate slow query on the orders table", 300, "claude", False, subs_e, []),
        ("demo-hhhh-0008", "working", "Audit the payments service for vulnerabilities", 45, "claude", False, [], wf_demo),
        ("demo-ffff-0006", "waiting", "Daily production error monitor", 9000, "claude", True, [], []),
        ("demo-gggg-0007", "waiting", "Nightly dependency update check", 12000, "claude", True, [], []),
        ("demo-iiii-0009", "waiting", "Choose the CSV export format", 40, "cursor", False, [], []),
        # "working" on purpose: a form blocks the run, and asking must override WORKING
        ("demo-jjjj-0010", "working", "Plan the auth token migration", 30, "claude", False, [], []),
        ("demo-kkkk-0011", "waiting", "Pick a caching strategy for the reports", 300, "cursor", False, [], []),
        ("demo-llll-0012", "waiting", "Tidy up the README badges", 200, "claude", False, [], []),
    ]
    # "waiting on you" demo: (kind, seconds since asked, preview, question count, demo_snoozed).
    # Ages span the three escalation tiers (<2m, 2-10m, >10m).
    demo_asks = {
        "demo-iiii-0009": ("form", 40, "Export format: Which delimiter should the CSV export use?", 2, False),
        "demo-jjjj-0010": ("form", 960, "Migration plan: Rotate all tokens at once, or migrate per tenant?", 3, False),
        "demo-kkkk-0011": ("form", 300, "Cache: Should report results be cached in Redis or in Postgres?", 2, True),
        "demo-cccc-0003": ("message", 1500, "Should I clear the archived flag on the restored records?", 1, False),
        "demo-llll-0012": ("message", 200, "Want me to open a PR with these badge fixes?", 1, False),
    }
    # demo open background shells (little terminal windows by the desk): one clean single
    # shell, a 3-shell max case (alongside helper dwarves), and a 2-shell case (alongside a
    # workflow easel) so QA covers coexistence with both neighbours.
    demo_shells = {
        "demo-bbbb-0002": [
            {"id": "sh-b1", "command": "npm run dev -- --port 3000", "running": True,
             "output_tail": "VITE ready in 431 ms / ➜ Local: http://localhost:3000/"}],
        "demo-eeee-0005": [
            {"id": "sh-e1", "command": "python manage.py runserver 0.0.0.0:8000", "running": True,
             "output_tail": "Watching for file changes with StatReloader / System check identified no issues"},
            {"id": "sh-e2", "command": "tail -f logs/orders-slow.log", "running": True,
             "output_tail": "SELECT * FROM orders WHERE status=? (1.83s) / slow query logged"},
            {"id": "sh-e3", "command": "redis-server --port 6380", "running": True,
             "output_tail": "Ready to accept connections tcp"}],
        "demo-hhhh-0008": [
            {"id": "sh-h1", "command": "docker compose up payments", "running": True,
             "output_tail": "payments-1  | Listening on :9099"},
            {"id": "sh-h2", "command": "python3 -m http.server 8080", "running": True,
             "output_tail": "Serving HTTP on 0.0.0.0 port 8080 ..."}],
        # a WAITING (kitchen) agent with a live shell -> exercises kitchen-shell rendering
        "demo-dddd-0004": [
            {"id": "sh-d1", "command": "pytest -q --looponfail tests/importer", "running": True,
             "output_tail": "watching for changes... / 12 passed in 0.42s"}],
    }
    # demo "listening" subscriptions: a desk worker on a PR + its CI (a fresh event every
    # 90s keeps the pulse visible), a kitchen agent on a Slack thread, and an asker with both
    # kinds so the glyphs sit beside the knock bubble / "not now" chip.
    def _li(kind, sub, label, detail, url, expires_in, event_ago):
        return {"kind": kind, "sub": sub, "label": label, "detail": detail, "url": url,
                "expires_at": now + expires_in, "last_event_at": (now - event_ago) if event_ago is not None else None}
    pulse_ago = now % 90
    demo_listening = {
        "demo-aaaa-0001": [
            _li("github", "pr", "PR #482 acme/data-export", "", "https://github.com/acme/data-export/pull/482", 3 * 86400, pulse_ago),
            _li("github", "ci", "CI on feature/export-v2", "acme/data-export \u00b7 last: failure", "", 7200, 1800)],
        "demo-cccc-0003": [
            _li("slack", "thread", "thread in #support-escalations", "Ana Ruiz, Ben Cole", "", 86400, 600)],
        "demo-kkkk-0011": [
            _li("slack", "channel", "#reports-team", "Dana Kim", "", 20 * 3600, 5),
            _li("github", "pr", "PR #77 acme/reports", "", "https://github.com/acme/reports/pull/77", 30 * 86400, None)],
        "demo-iiii-0009": [
            _li("linear", "issue", "Linear SEC-142", "", "", 5 * 86400, None),
            _li("origin", "pr", "PR #12 acme/payments", "", "", 3 * 86400, None)],
    }
    out = []
    for idx, (uuid, status, title, ago, source, scheduled, subagents, workflows) in enumerate(samples):
        # a WORKING agent that is actually typing (no helpers) alternates between writing text
        # (white bubble) and running a tool (dark chip) on its own slow clock; a delegating
        # parent (turn ended, dwarves running) and waiting agents keep a static last line so
        # only their dwarves pop indicators. Nothing syncs up -> the odd bubble/chip, not a wall.
        active_typing = status == "working" and not subagents and not workflows
        if active_typing:
            phase = _blip(idx * 4, 13)
            if phase % 2:
                tool = ["Edit", "Bash", "Grep", "Read"][idx % 4]
                latest = "%s: %s.py [%d]" % (tool, title.split()[0].lower(), phase)
                lkind = "tool"
            else:
                latest = "Reviewing the latest changes about " + title.split()[0].lower() + " [%d]" % phase
                lkind = "assistant"
        else:
            latest = ("Working with helpers on " + title.split()[0].lower()) if status == "working" \
                     else "Wrapped up -- waiting for your next instruction."
            lkind = "assistant"
        # a fresh user instruction lands on a working agent every so often (staggered, slow) ->
        # the boss walks over to a desk to deliver it. Waiting agents keep their original ask.
        last_instr = ((("can you also cover the empty case?", "please add a test for this",
                        "make sure it handles nulls too", "ship it once CI is green",
                        "rename that so it reads clearer")[_blip(idx * 9, 34) % 5])
                      if status == "working" else "Please " + title[0].lower() + title[1:])
        out.append({
            "id": uuid,
            "source": source,
            "scheduled": scheduled,
            "subagents": subagents,
            "subs": len(subagents),
            "shells": demo_shells.get(uuid, []),
            "listening": demo_listening.get(uuid, []),
            "workflows": workflows,
            "wf_running_agents": sum(w["running"] for w in workflows),
            # a working parent that has helpers/workflows running is NOT typing itself
            # (its own turn ended) -> demonstrates the frozen-desk animation (item 8).
            "self_active": status == "working" and not subagents and not workflows,
            "name": _name_for(uuid),
            "variant": _variant_for(uuid),
            "project": "demo-office",
            "status": status,
            "title": title,
            "preview": title,
            "latest": latest,
            "latest_kind": lkind,
            "last_tool": ["Bash: pytest -q tests/", "Edit: service.py", "Grep: export path", "Read: config.yaml"][idx % 4],
            "last_message": latest if lkind == "assistant" else ("Reviewing the changes about " + title.split()[0].lower()),
            "last_instruction": last_instr,
            "message_count": 12,
            "model": "Opus 4.8" if source == "claude" else None,
            "tokens": (1_240_000 if source == "claude" else None),
            "spend": (3.42 if source == "claude" else None),
            "mtime": now - ago,
            "last_activity_rel": _rel_time(ago),
            "demo": True,
        })
        ask = demo_asks.get(uuid)
        if ask:
            kind, ask_ago, preview, count, snoozed = ask
            if kind == "message":
                out[-1].update({"latest": preview, "latest_kind": "assistant", "last_message": preview})
            _apply_ask(out[-1], {"asking": kind, "asked_at": now - ask_ago,
                                 "question_id": _fingerprint(uuid, "demo-q"),
                                 "question_preview": preview, "question_count": count}, now - ask_ago)
            out[-1]["demo_snoozed"] = snoozed
        else:
            _apply_ask(out[-1], None, None)
    return out


def demo_detail(uuid):
    for a in demo_agents():
        if a["id"] == uuid:
            a = dict(a)
            a.update({
                "task_full": a["title"],
                "latest_response": "This is a demo worker. Run without --demo to see your real agents.\n\nI'd start by mapping the relevant modules, then make the change incrementally and verify with a quick test.",
                "latest_tool": {"name": "Shell", "detail": "python -m pytest -v"},
                "timeline": [
                    {"role": "user", "text": a["title"], "tools": []},
                    {"role": "assistant", "text": "Let me explore the codebase first.", "tools": [{"name": "Grep", "detail": "export"}]},
                    {"role": "assistant", "text": "Found the relevant module. Making the change now.", "tools": [{"name": "StrReplace", "detail": "service.py"}]},
                ],
                "transcript_path": "(demo - no file)",
            })
            return a
    return None


# --------------------------------------------------------------------------------------
# Frontend (single embedded HTML/JS/CSS page)
# --------------------------------------------------------------------------------------

PAGE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>Agent Office</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Press+Start+2P&display=swap" rel="stylesheet">
<style>
  :root{
    --gb-darkest:#0f380f; --gb-dark:#306230; --gb-light:#8bac0f; --gb-lightest:#9bbc0f;
    --shell:#c4bfb4; --shell-dark:#9a958b;
    /* high-contrast greyscale for readable text panels (tooltip + detail) */
    --panel:#1c1e24; --panel2:#26282f; --panel-line:#3a3d46;
    --ink-hi:#f4f5f7; --ink-mid:#c4c7cf; --ink-lo:#8b8f99;
    --card:#f2f2f4; --card-line:#d4d5da; --card-ink:#1c1e24; --card-ink-lo:#5b5e68;
  }
  *{box-sizing:border-box;}
  html,body{margin:0;height:100%;background:#1b1f17;color:var(--gb-darkest);
    font-family:'Press Start 2P',ui-monospace,Menlo,Consolas,monospace;}
  body{display:flex;align-items:center;justify-content:center;padding:18px;}
  #shell{background:var(--shell);border-radius:14px 14px 42px 14px;padding:18px 18px 26px;
    box-shadow:0 14px 40px rgba(0,0,0,.55), inset 0 2px 0 #e8e4da, inset 0 -3px 0 var(--shell-dark);
    width:min(960px,96vw);}
  #brand{display:flex;justify-content:space-between;align-items:center;margin-bottom:10px;
    font-size:11px;color:#5a564d;letter-spacing:1px;}
  #brand .dot{display:inline-block;width:9px;height:9px;border-radius:50%;background:#7a1717;
    box-shadow:0 0 6px #d33;margin-right:8px;vertical-align:middle;}
  #brand #celebrate,#brand #whip,#brand #thank,#brand #sound,#brand #filter,#brand #names{font-family:inherit;font-size:9px;letter-spacing:1px;color:#e8e8ea;
    background:#3a3a40;border:1px solid #54545c;border-radius:5px;padding:5px 11px;cursor:pointer;}
  #brand #celebrate:hover,#brand #whip:hover,#brand #thank:hover,#brand #sound:hover,#brand #filter:hover,#brand #names:hover{background:#4a4a52;color:#fff;}
  #brand #celebrate:active,#brand #whip:active,#brand #thank:active,#brand #sound:active,#brand #filter:active,#brand #names:active{transform:translateY(1px);}
  #brand #sound,#brand #filter,#brand #names,#brand #whip,#brand #thank{margin-left:8px;}
  /* tiny label-less "easter egg" buttons tucked into the kitchen (left) & beach (right)
     corners of the screen -- faint until hovered; you have to try them to learn what they do. */
  #screen .zonebtn{position:absolute;bottom:7px;width:24px;height:24px;padding:0;border:0;
    border-radius:50%;background:rgba(0,0,0,.16);font-size:13px;line-height:24px;text-align:center;
    cursor:pointer;opacity:.6;z-index:6;transition:opacity .15s ease,transform .08s ease,background .15s ease;
    -webkit-user-select:none;user-select:none;}
  #screen .zonebtn:hover{opacity:1;background:rgba(0,0,0,.34);}
  #screen .zonebtn:active{transform:translateY(1px) scale(.92);}
  /* custom hover tooltip (native title didn't surface reliably). Sits ABOVE the button and
     is anchored toward the room so it never clips against #screen's overflow:hidden. */
  #screen .zonebtn[data-tip]::after{content:attr(data-tip);position:absolute;bottom:calc(100% + 7px);
    background:rgba(15,17,20,.92);color:#fff;font-size:9px;line-height:1.35;letter-spacing:.5px;
    padding:4px 7px;border-radius:5px;white-space:nowrap;pointer-events:none;
    opacity:0;transform:translateY(3px);transition:opacity .12s ease,transform .12s ease;
    z-index:20;box-shadow:0 4px 12px rgba(0,0,0,.4);}
  #screen .zonebtn[data-tip]:hover::after{opacity:1;transform:translateY(0);}
  #screen #sweep-kitchen[data-tip]::after{left:0;}                          /* extend right from the left corner */
  #screen #drown-beach[data-tip]::after{right:0;font-size:16px;padding:2px 8px;}  /* extend left; big devil */
  #screen #sweep-kitchen{left:7px;}
  #screen #drown-beach{right:22px;}   /* floats on the ocean band in the beach's bottom-right corner */
  #brand #sound.off,#brand #filter.off{color:#8a8a90;}
  #brand #filter.on{background:#2f5fb0;border-color:#3f6fc0;color:#fff;}
  #screenwrap{background:#22281a;border-radius:10px;padding:12px;
    box-shadow:inset 0 0 0 3px #20240f, inset 0 0 22px rgba(0,0,0,.6);}
  #matrix{display:flex;align-items:center;gap:8px;justify-content:center;margin-bottom:8px;
    font-size:7px;letter-spacing:2px;color:#6f6a78;}
  #matrix .ln{height:3px;flex:1;max-width:120px;border-radius:2px;}
  #matrix .l1{background:linear-gradient(90deg,#7a1f5a,#1f3f7a);}
  #matrix .l2{background:linear-gradient(90deg,#1f3f7a,#7a1f5a);}
  #screen{position:relative;width:100%;aspect-ratio:11/9;background:#65748d;
    border-radius:6px;overflow:hidden;}
  canvas{position:absolute;inset:0;width:100%;height:100%;image-rendering:auto;cursor:pointer;}
  #hud{position:absolute;left:0;top:0;display:flex;flex-direction:column;align-items:flex-start;
    gap:4px;padding:6px 8px;font-size:8px;color:#fff;pointer-events:none;}
  #hud .pill{background:rgba(0,0,0,.42);padding:4px 7px;border-radius:4px;}
  #hud #hud-ask{background:rgba(120,84,0,.72);}
  #hud .dim{opacity:.6;}
  #dbody section.ask{background:#fff6d6;border:2px solid #e3b021;border-radius:6px;padding:10px 12px;}
  #dbody section.ask.snoozed{background:#eef3ee;border-color:#9fb8a2;}
  #dbody section.ask h4{color:#7a5a00;}
  #dbody section.ask .box{border-left-color:#e3b021;font-size:12px;}
  #dbody .asknote{font-size:9px;color:var(--card-ink-lo);margin-top:8px;line-height:1.7;}
  #dfoot button#d-snooze{background:#fff6d6;color:#5a4300;border-color:#e3b021;}
  #kbody .k-ask{display:inline-block;margin-right:4px;}
  #kbody .k-ask.snz{opacity:.45;}
  #tip{position:absolute;left:40px;bottom:8px;font-size:7px;color:#fff;
    background:rgba(0,0,0,.32);padding:3px 6px;border-radius:4px;pointer-events:none;}
  #nametag{position:absolute;background:var(--panel);
    color:var(--ink-hi);font-size:11px;line-height:1.55;padding:11px 13px;border-radius:7px;
    width:300px;max-width:78%;white-space:normal;word-break:break-word;
    border:1px solid var(--panel-line);
    box-shadow:0 10px 26px rgba(0,0,0,.55);
    max-height:82vh;overflow-y:auto;
    pointer-events:none;display:none;z-index:15;}
  #nametag .nt-name{font-size:13px;color:var(--ink-hi);font-weight:bold;}
  #nametag .nt-badge{display:inline-block;font-size:9px;padding:2px 7px;border-radius:4px;margin-left:7px;vertical-align:middle;}
  #nametag .nt-badge.working{background:#e8eaee;color:#16181d;}
  #nametag .nt-badge.waiting{background:#4a4d56;color:#f4f5f7;}
  .nt-badge.src-cursor,.badge.src-cursor{background:#2b6d84;color:#eaf6fb;}
  .nt-badge.src-claude,.badge.src-claude{background:#d97757;color:#2a1409;}
  .nt-badge.scheduled,.badge.scheduled{background:#2f5fb0;color:#eaf1ff;}
  .nt-badge.workflow,.badge.workflow{background:#6a4fb0;color:#f1eaff;}
  .nt-badge.listen-slack,.badge.listen-slack{background:#4a154b;color:#f7e9f7;}
  .nt-badge.listen-github,.badge.listen-github{background:#24292f;color:#f0f3f6;}
  .nt-badge.listen-linear,.badge.listen-linear{background:#5e6ad2;color:#eef0ff;}
  .nt-badge.listen-origin,.badge.listen-origin{background:#1f6f5c;color:#e4f7f1;}
  #nametag .nt-sub{font-size:9px;color:var(--ink-lo);margin-top:2px;}
  #nametag .nt-meta{font-size:9px;color:var(--ink-lo);margin:6px 0 8px;}
  #nametag .nt-label{font-size:8px;letter-spacing:1px;color:var(--ink-lo);text-transform:uppercase;margin-top:8px;}
  #nametag .nt-text{font-size:11px;color:var(--ink-mid);margin-top:3px;}
  #nametag .nt-hint{font-size:8px;color:var(--ink-lo);margin-top:9px;text-align:right;opacity:.85;}
  #nametag .wf-phase{display:inline-block;padding:1px 5px;border-radius:3px;margin:2px 2px 0 0;font-size:10px;}
  #nametag .wf-phase.done{background:#2f5d3a;color:#dff5e4;}
  #nametag .wf-phase.active{background:#b7791f;color:#fff4dd;}
  #nametag .wf-phase.pending{background:#33363f;color:#9aa0ab;}
  #nametag .wf-sep{color:var(--ink-lo);margin:0 3px;}
  #legend{display:flex;gap:14px;justify-content:center;margin-top:12px;font-size:8px;color:#5a564d;}
  #legend span{display:inline-flex;align-items:center;gap:6px;}
  #legend i{width:10px;height:10px;border-radius:2px;display:inline-block;}

  /* overlay dialog */
  #overlay{position:absolute;inset:0;display:none;align-items:center;justify-content:center;
    background:rgba(15,24,8,.55);padding:14px;z-index:20;}
  #dialog{width:100%;max-width:680px;max-height:100%;background:var(--card);
    border:3px solid var(--panel);border-radius:8px;display:flex;flex-direction:column;
    box-shadow:0 0 0 3px var(--panel-line), 0 18px 40px rgba(0,0,0,.5);overflow:hidden;}
  #dhead{background:var(--panel);color:var(--ink-hi);padding:12px 14px;
    display:flex;justify-content:space-between;align-items:flex-start;gap:8px;}
  #dhead .who{font-size:13px;color:var(--ink-hi);}
  #dhead .sub{font-size:9px;color:var(--ink-mid);margin-top:6px;line-height:1.7;}
  #dhead button{font-family:inherit;background:var(--panel2);color:var(--ink-hi);
    border:1px solid var(--panel-line);border-radius:4px;font-size:9px;padding:5px 8px;cursor:pointer;}
  #dbody{padding:16px;overflow:auto;font-size:11px;line-height:1.85;color:var(--card-ink);}
  #dbody h4{margin:0 0 8px;font-size:10px;color:var(--card-ink-lo);text-transform:uppercase;letter-spacing:1px;}
  #dbody section{margin-bottom:18px;}
  #dbody .box{background:#ffffff;border:1px solid var(--card-line);border-left:3px solid #8b8f99;
    padding:11px 13px;border-radius:4px;white-space:pre-wrap;word-break:break-word;font-size:11px;line-height:1.75;color:var(--card-ink);}
  #dbody .tool{display:inline-block;background:var(--panel);color:var(--ink-hi);
    padding:3px 7px;border-radius:3px;font-size:8px;margin:2px 4px 2px 0;}
  #dbody .turn{font-size:8px;color:var(--card-ink-lo);text-align:center;margin:6px 0;}
  .role-user .box{border-left-color:#3a3d46;background:#ececed;}
  .badge{display:inline-block;font-size:8px;padding:3px 7px;border-radius:3px;}
  .badge.working{background:#e8eaee;color:#16181d;}
  .badge.waiting{background:#4a4d56;color:#f4f5f7;}
  #dfoot{display:flex;flex-wrap:wrap;gap:8px;padding:10px 12px;border-top:1px solid var(--card-line);
    background:#e7e7ea;}
  #dfoot button{flex:1 1 auto;font-family:inherit;font-size:8px;padding:9px 8px;cursor:pointer;
    border:1px solid var(--panel);border-radius:5px;background:var(--panel);color:var(--ink-hi);}
  #dfoot button.ghost{background:#fff;color:var(--card-ink);border-color:var(--card-line);}
  /* kitchen list panel -- who's waiting (mirrors the detail overlay look) */
  #koverlay{position:absolute;inset:0;display:none;align-items:center;justify-content:center;
    background:rgba(15,24,8,.55);padding:14px;z-index:21;}
  #kdialog{width:100%;max-width:520px;max-height:100%;background:var(--card);
    border:3px solid var(--panel);border-radius:8px;display:flex;flex-direction:column;
    box-shadow:0 0 0 3px var(--panel-line), 0 18px 40px rgba(0,0,0,.5);overflow:hidden;}
  #khead{background:var(--panel);color:var(--ink-hi);padding:12px 14px;
    display:flex;justify-content:space-between;align-items:center;gap:8px;}
  #khead .who{font-size:13px;color:var(--ink-hi);}
  #khead button{font-family:inherit;background:var(--panel2);color:var(--ink-hi);
    border:1px solid var(--panel-line);border-radius:4px;font-size:9px;padding:5px 8px;cursor:pointer;}
  #kbody{padding:12px;overflow:auto;font-size:11px;color:var(--card-ink);}
  #kbody .krow{background:#ffffff;border:1px solid var(--card-line);border-left:3px solid #8b8f99;
    padding:9px 11px;border-radius:4px;margin-bottom:8px;cursor:pointer;}
  #kbody .krow:hover{background:#f1f1f3;border-left-color:#4a4d56;}
  #kbody .krow:last-child{margin-bottom:0;}
  #kbody .k-ttl{font-size:11px;color:var(--card-ink);font-weight:bold;word-break:break-word;line-height:1.5;}
  #kbody .k-msg{font-size:10px;color:var(--card-ink-lo);margin-top:4px;line-height:1.6;word-break:break-word;}
  #kbody .k-empty{text-align:center;color:var(--card-ink-lo);padding:26px 10px;font-size:10px;line-height:2;}
  #toast{position:absolute;left:50%;bottom:16px;transform:translateX(-50%);background:var(--panel);
    color:var(--ink-hi);font-size:8px;padding:7px 12px;border-radius:5px;display:none;z-index:30;}
  #empty{position:absolute;inset:0;display:none;flex-direction:column;align-items:center;
    justify-content:center;text-align:center;font-size:9px;color:#1c1e24;padding:24px;line-height:2;}
</style>
</head>
<body>
  <div id="shell">
    <div id="brand"><span><span class="dot"></span>AGENT OFFICE</span><span id="scope"></span><button id="celebrate" title="confetti + everyone dances">CELEBRATE</button><button id="whip" title="crack the whip &mdash; everyone works harder">WHIP</button><button id="thank" title="thank the agents &mdash; ends a revolt, or a wholesome flower celebration">THANK AGENTS</button><button id="sound" title="chime when an agent finishes">&#9834; ON</button><button id="filter" title="hide scheduled / courier agents">&#9993; HIDE</button><button id="names" title="agent name style">NAMES</button></div>
    <div id="screenwrap">
      <div id="matrix"><span class="ln l1"></span>DOT MATRIX WITH STEREO SOUND<span class="ln l2"></span></div>
      <div id="screen">
        <canvas id="cv" width="704" height="576"></canvas>
        <div id="hud">
          <span class="pill" id="hud-work">working: 0</span>
          <span class="pill" id="hud-wait">in kitchen: 0</span>
          <span class="pill" id="hud-ask" style="display:none"></span>
          <span class="pill" id="hud-beach" style="display:none">on beach: 0</span>
          <span class="pill" id="hud-subs" style="display:none">subagents: 0</span>
          <span class="pill" id="hud-wf" style="display:none">workflows: 0</span>
        </div>
        <div id="tip">click a worker</div>
        <button id="sweep-kitchen" class="zonebtn" aria-label="send everyone in the kitchen to the beach" data-tip="send everyone in the kitchen to the beach">&#127958;</button>
        <button id="drown-beach" class="zonebtn" aria-label="beach" data-tip="&#128520;">&#127754;</button>
        <div id="nametag"></div>
        <div id="empty">No agents active in the last <b id="emh">24</b>h.<br/><br/>
          Start a chat in Cursor or Claude Code, or run with <b>--demo</b> to populate the office.</div>
        <div id="overlay">
          <div id="dialog">
            <div id="dhead">
              <div>
                <div class="who" id="d-name"></div>
                <div class="sub" id="d-sub"></div>
              </div>
              <button id="d-x" title="close">X</button>
            </div>
            <div id="dbody"></div>
            <div id="dfoot">
              <button id="d-snooze" style="display:none">&#128524; NOT NOW</button>
              <button id="d-finish">&#127958; SEND TO BEACH</button>
              <button id="d-open">OPEN TRANSCRIPT FILE (.jsonl)</button>
              <button id="d-copy" class="ghost">COPY SESSION ID</button>
            </div>
          </div>
        </div>
        <div id="koverlay">
          <div id="kdialog">
            <div id="khead">
              <div class="who" id="k-title">In the kitchen</div>
              <button id="k-x" title="close">X</button>
            </div>
            <div id="kbody"></div>
          </div>
        </div>
        <div id="toast"></div>
      </div>
    </div>
    <div id="legend">
      <span><i style="background:#1f5d1f"></i>working (at desk)</span>
      <span><i style="background:#7a4a00"></i>waiting (in kitchen)</span>
      <span><i style="background:#2b6d84"></i>Cursor</span>
      <span><i style="background:#d97757"></i>Claude Code</span>
      <span><i style="background:#2f5fb0"></i>scheduled (courier)</span>
      <span><i style="background:#57c2d8"></i>finished (beach)</span>
    </div>
  </div>

<script>
"use strict";
const cv = document.getElementById('cv');
const ctx = cv.getContext('2d');
// Logical drawing size stays 640x576 (all layout/hit-test math uses these), but we
// super-sample the actual backing store so text + art render at much higher
// resolution and scale down crisply instead of being upscaled/blurred (esp. on
// HiDPI / retina screens). SS is chosen from devicePixelRatio, capped for perf.
const W = 704, H = 576;   // 704 = 576*11/9 -> matches #screen aspect-ratio:11/9 (widened so edge desks' dwarves/easels don't clip)
const SS = Math.min(4, Math.max(2, Math.ceil((window.devicePixelRatio||1)*2)));
cv.width = W*SS; cv.height = H*SS;
ctx.imageSmoothingEnabled = false;
// global art scale: characters + desks are drawn larger (about their anchor) so
// the rooms feel filled. ALL hitbox / hover-ring / pick() math multiplies by SC.
const SC = 1.5;
const BUBBLE_MS = 8200;    // speech-bubble lifetime (ms)
const BUBBLE_FADE = 900;   // fade-out tail (ms)
const BOSS_MS = 7200;      // how long the "boss" lingers by a desk delivering a new instruction
// the bottom band is split: KITCHEN (waiting) on the left, BEACH (finished, resting)
// on the right. BEACH_X is the divider; everything to its right is sand + water.
const BEACH_X = Math.round(W*0.60);
// the ocean is a proper band hugging the far-right edge; sand fills the rest of the
// beach zone. SHORE_X is where wet sand meets the sea -- beach props and the resting
// agents' rest spots all stay LEFT of it so nobody ends up sitting in the water.
const WATER_W = 56;             // ~20% of the beach zone (BEACH_X..W)
const SHORE_X = W - WATER_W;    // sand/sea boundary

// Game Boy palette
const C = { d0:'#0f380f', d1:'#306230', d2:'#8bac0f', d3:'#9bbc0f', floor:'#94ad42', floor2:'#8aa53b' };
// look variants -- bright, cheerful, diverse shirt colours (no gloomy navy crowd)
const SHIRTS = ['#e0533b','#2f93d8','#37b56c','#e8a72e','#8c5fd6','#22b9b9','#e673a8','#6aa72f',
                '#d83b5b','#3f74d6','#ee8f2c','#16a0c0','#c84fc0','#5bc05b','#f0b429','#ff7a4d'];
const HAIR   = ['#3a2a14','#1a1410','#5a3010','#6a6a6a','#2a1840','#403018','#7a3010','#c89020','#d8d8d8','#1a3a5a'];
const SKIN   = ['#f0d2a8','#e6b98a','#d2a070','#f6dcc0','#c08860','#ecc89c','#b87a52','#fae0c2'];
const ACCCOL = ['#1b1b1b','#d2452f','#2f74d6','#e8a72e','#22b9b9','#8c5fd6'];

// rich, full-colour scene palette (the screen is no longer monochrome green)
const PAL = {
  sky:'#bfe9f5', skyTop:'#9ad8ee', cloud:'#ffffff',
  bldg1:'#7c87b0', bldg2:'#9aa4c6', bldgWin:'#dfeefa',
  nightTop:'#171436', nightBot:'#46315f', star:'#ffffff', moon:'#f3eecf',
  bldgN1:'#211c40', bldgN2:'#2c2752', litWin:'#ffd36b',
  wall:'#efe6d2', trim:'#cdbf9c', base:'#b09a72',
  ofloor:'#6f7f98', ofloor2:'#65748d',
  kfloor:'#ecdcb6', kfloor2:'#e1cfa4',
  wood:'#b27a43', woodHi:'#c68f55', woodDk:'#7d4f2a',
  metal:'#aeb9c2', metalDk:'#7a8893', steel:'#cdd6dd',
  fridge:'#e3eaef', fridgeDk:'#c5cfd6',
  cabinet:'#3f5266', cabinetTop:'#d9c8a6',
  leaf:'#46a04f', leafHi:'#69bf68', leafDk:'#2f7a3c', pot:'#c4693a', potDk:'#9a4f28',
  board:'#2c3b37', chalk:'#ece6d2', chalkY:'#e4c558',
  monitor:'#2b2b34', monitorLip:'#16161c', screen:'#7fd3e0',
  paper:'#ffffff', ink:'#26282e', outline:'#241c2b', chairW:'#6a5240',
  pink:'#dd8aa8', red:'#d2452f', yellow:'#e3b021', orange:'#e07a2f',
  mugA:'#d9534f', mugB:'#4f86d9', mugC:'#e8b84b',
};

// derive a fun, deterministic appearance from the agent id.
// NOTE: hash() is unsigned 32-bit, so we MUST use unsigned shifts (>>>) here -
// a signed >> would go negative for high hashes and yield undefined colours.
function featuresFor(id){
  const h = hash(id);
  return {
    skin: SKIN[(h>>>0) % SKIN.length],
    hair: HAIR[(h>>>3) % HAIR.length],
    shirt: SHIRTS[(h>>>6) % SHIRTS.length],
    hairStyle: (h>>>9) % 8,        // 0 flat 1 spiky 2 bald 3 bun 4 mop 5 mohawk 6 side-part 7 afro
    acc: (h>>>12) % 6,             // 0 none 1 glasses 2 cap 3 headphones 4 beanie 5 antenna
    accCol: ACCCOL[(h>>>15) % ACCCOL.length],
    pants: ['#3a4654','#4a3a2e','#2f4250','#5a4326','#3a3a44','#2f4a38'][(h>>>23) % 6],
    speed: 0.55 + ((h>>>18) % 5) * 0.14,   // per-person walk speed
    big: ((h>>>21) & 1) === 1,             // chunkier body
    female: ((h>>>16) & 1) === 1,          // ~half women, stable by id
    femStyle: (h>>>17) % 4,                // 0 long  1 ponytail  2 bun+bow  3 top-knot
    outfit: (h>>>19) % 5,                  // 0 plain 1 zip 2 stripe 3 v-neck 4 hoodie
    lanyard: ((h>>>25) % 3) === 0,         // ~1/3 wear an office badge on a lanyard
  };
}
// a small outfit detail + soft left-side sheen, shared by every sprite so the crowd
// looks varied. cx = torso centre, topY = torso top, halfW = half the torso width.
function torsoDetail(cx, topY, halfW, h, sh, f){
  if(f.messenger) return;                                        // couriers keep their plain uniform + badge
  px(cx-halfW+1, topY+2, 1, h-4, 'rgba(255,255,255,.10)');       // subtle sheen down the left
  if(f.lanyard){                                                 // office badge on a lanyard (overrides other detail)
    px(cx-3,topY,1,5,'#33343e'); px(cx+3,topY,1,5,'#33343e');    // cords from the shoulders
    px(cx-2,topY+5,5,5,'#eef0f4'); px(cx-2,topY+5,5,1,'#ffffff'); // badge card
    px(cx-1,topY+6,3,1,'#8f98a4'); px(cx-1,topY+8,2,1,'#8f98a4'); // badge text lines
    return;
  }
  const dk=shade(sh,-.26), lt=shade(sh,.26);
  if(f.outfit===1){ px(cx, topY+1, 1, h-2, dk); px(cx-1, topY+3, 3,1, dk); px(cx-1, topY+7, 3,1, dk); }     // zip placket
  else if(f.outfit===2){ px(cx-halfW+2, topY+Math.round(h*0.45), (halfW-2)*2, 2, lt); }                     // chest stripe
  else if(f.outfit===3){ px(cx-2, topY, 4,2, dk); px(cx-1, topY+2, 2,1, dk); }                              // v-neck
  else if(f.outfit===4){ px(cx-4, topY, 8,2, dk); px(cx-2, topY+2, 1,4, PAL.paper); px(cx+1, topY+2, 1,4, PAL.paper); } // hoodie
}

// Scheduled / automated agents (cron, daily monitors, etc.) wear a courier uniform:
// one solid color from shirt to cap, so a whole squad of them reads instantly as
// "not a human-driven chat" instead of blending into the office crowd.
const MESSENGER_COL = '#2f5fb0';
function featuresForAgent(a){
  const f = featuresFor((a && a.id) || 'x');
  if(a && a.scheduled){
    f.messenger = true;
    f.shirt = MESSENGER_COL;    // uniform shirt
    f.acc = 2;                  // cap
    f.accCol = MESSENGER_COL;   // cap matches the uniform
    if(f.hairStyle === 2) f.hairStyle = 0;   // a little hair peeks out under a bald courier's cap
  }
  return f;
}

let agents = [];      // raw from server
let people = [];      // live sprites with positions
let deskSlots = [];   // office desks (always drawn; some hold a worker). Each: {x,y,scale,room,worker}
let officeRooms = []; // labeled desk clusters drawn as light "work rooms" once the grid is large
let activeHolidays = []; // holiday theme names active right now (from the server; see refresh())
let hanukkahNight = 5;   // which night of Hanukkah (1..8) to light; from the server (see refresh())
let helperHits = [];  // per-frame hover regions for the subagent dwarves
let workflowHits = []; // per-frame hover regions for the workflow tents
let shellHits = [];    // per-frame hover regions for the open-shell terminal windows
let listenHits = [];   // per-frame hover regions for the "listening" Slack/GitHub glyphs
let bubbleAnchors = []; // per-frame: bubbles to draw as a screen-space overlay
let vendSlots = [];   // per-frame click rects for the vending-machine drink slots
let vendDrops = {};   // slot idx -> {start,col,fromX,fromY} while a can is dropping/resting
let deskAssign = {};  // agent id -> stable desk slot index (kept across refreshes)
let seatAssign = {};  // agent id -> stable kitchen seat index
let beachAssign = {}; // agent id -> stable beach spot index (finished agents)
let hover = null;
let detailCache = {};
let WINDOW_HOURS = 24;
let confetti = [];          // celebration particles (capped, auto-expire)
let whipFx = [];            // whip-crack particles: one lash line + shock streaks (capped, auto-expire)
// --- water cooler: click the office cooler and it squirts an arc of water ---
let waterFx = [];           // water droplet particles from the cooler spout (capped, auto-expire)
let coolerHit = null;       // {x0,y0,x1,y1,sx,sy} cooler click rect + spout origin (set each frame)
// --- Godzilla: stomps across the window every round hour (or on a wall-clock click) ---
let clockHit = null;        // {x0,y0,x1,y1} wall-clock click rect (set each frame)
let godzilla = { active:false, t:0 };   // t = 0..1 progress walking across the window
let godzillaHourKey = null; // local "date#hour" stamp; a change = a new round hour -> trigger
const GODZILLA_MS = 6000;   // time to cross the window
// --- WHIP-abuse easter egg: overwork the "WIP" button and the office revolts ---
let poop = [];              // poop projectiles hurled toward the viewer (capped, auto-expire)
let poopSplats = [];        // brown splat decals stuck on the "glass" (screen space; fade out, capped)
let whipClicks = [];        // wall-clock ms of recent WHIP clicks (rolling 60-min window)
let angryUntil = 0;         // performance.now() deadline: agents are ANGRY while now<angryUntil
let lastPoopAt = 0;         // throttle: last poop-spawn time (performance.now-based)
// --- THANK AGENTS: wholesome celebration state (flower confetti + ~1min blissful mood) ---
let flowers = [];           // pastel flower/petal confetti particles (capped, auto-expire)
let thankMsgs = [];         // rotating floating gratitude-about-life messages (screen space, capped)
let blissUntil = 0;         // performance.now() deadline: agents are BLISSFUL while now<blissUntil
let flowerRainUntil = 0;    // performance.now() deadline: keep raining fresh flowers while now<this
let lastFlowerAt = 0;       // throttle: last flower-rain spawn time (performance.now-based)
let lastThankMsgAt = 0;     // throttle: last gratitude-message spawn time (performance.now-based)
let prevStatus = null;      // id -> last status; null until the first poll (no false fires)
let msgSeen = null;   // id -> last assistant `latest` seen (desk agents); null until first poll
let subMsgSeen = {};  // subId -> last change-token (subagents + workflow subs)
let subBubbles = {};  // subId -> {text,start,until} active dwarf bubbles
let instrSeen = null; // id -> last user instruction seen (working agents); null until first poll
let bossVisits = {};  // id -> {text,start,until} a supervisor delivering a new instruction at a desk
let hideScheduled = (localStorage.getItem('office_hide_scheduled')==='on');  // filter couriers (default off)
// agents the user has marked "finished" -- they go rest on the beach until unmarked.
// User-controlled and sticky (persisted), independent of the working/waiting status.
let finishedIds = new Set(JSON.parse(localStorage.getItem('office_finished')||'[]'));
function saveFinished(){ localStorage.setItem('office_finished', JSON.stringify([...finishedIds])); }
// agents "drowned" via the beach easter-egg -- washed out to sea and hidden until they're
// ACTIVE AGAIN. Stored as { id: mtimeAtDrownTime }; a poll where the agent's mtime has moved
// past that stamp means new activity -> un-drown it (and it wades back in from the ocean).
let drownedInfo = (()=>{ try{ const r=JSON.parse(localStorage.getItem('office_drowned')||'{}');
  return (r && typeof r==='object' && !Array.isArray(r)) ? r : {}; }catch(e){ return {}; } })();
function saveDrowned(){ localStorage.setItem('office_drowned', JSON.stringify(drownedInfo)); }
let emergeFrom = new Set();    // ids that should spawn at the sea and walk in (just un-drowned)
const DROWN_SINK_MS = 1500;   // how long an agent takes to slip under once it reaches the sea

// ---- "waiting on you": agents blocked on a question for the user (asking = 'form'|'message') ----
// A 'form' asker walks to the front and knocks on the glass; a 'message' asker raises a hand
// under a bouncing "?". "Not now" snoozes ONE question: stored as {"<id>|<question_id>": ms}
// (ids + hashes only -- never question text). A new question has a new question_id, so it
// wakes the agent again. Entries are pruned by age, by cap, and once superseded.
const SNOOZE_KEY = 'office_snoozed', SNOOZE_MAX_AGE_MS = 3*86400000, SNOOZE_MAX = 200;
let snoozed = (()=>{ try{ const r=JSON.parse(localStorage.getItem(SNOOZE_KEY)||'{}');
  return (r && typeof r==='object' && !Array.isArray(r)) ? r : {}; }catch(e){ return {}; } })();
function saveSnoozed(){ localStorage.setItem(SNOOZE_KEY, JSON.stringify(snoozed)); }
function isAsking(a){ return !!(a && a.asking && a.question_id); }
function snoozeKey(a){ return a.id+'|'+a.question_id; }
function isSnoozed(a){ return isAsking(a) && snoozed[snoozeKey(a)]!=null; }
// escalation tier by how long it has been waiting: 0 (<2 min), 1 (2-10 min), 2 (>10 min)
function askTier(a){ const s=Date.now()/1000-((a&&a.asked_at)||Date.now()/1000); return s<120?0:(s<600?1:2); }
// an asker that should be visibly pestering you right now (not snoozed, not on the beach)
function askActive(p){ return !!(p && p.agent && isAsking(p.agent) && !isSnoozed(p.agent)
  && (p.kind==='wait' || p.kind==='knock') && p.mode!=='drown'); }
function pruneSnoozed(list){
  const now=Date.now(), cur={}; let changed=false;
  list.forEach(a=>{ cur[a.id]=a.question_id||null; });
  for(const k of Object.keys(snoozed)){
    const i=k.lastIndexOf('|'), id=k.slice(0,i), q=k.slice(i+1);
    if(!(typeof snoozed[k]==='number') || now-snoozed[k]>SNOOZE_MAX_AGE_MS || (cur[id] && cur[id]!==q)){
      delete snoozed[k]; changed=true; }
  }
  const keys=Object.keys(snoozed);
  if(keys.length>SNOOZE_MAX){ keys.sort((a,b)=>snoozed[a]-snoozed[b]).slice(0,keys.length-SNOOZE_MAX)
    .forEach(k=>delete snoozed[k]); changed=true; }
  if(changed) saveSnoozed();
}
// --demo marks one asker `demo_snoozed`: snooze it once (remembered, so un-snoozing sticks)
function seedDemoSnoozes(list){
  let seeded; try{ seeded=JSON.parse(localStorage.getItem('office_demo_snooze_seeded')||'[]'); }catch(e){ seeded=[]; }
  let changed=false;
  list.forEach(a=>{ if(a.demo_snoozed && isAsking(a) && seeded.indexOf(snoozeKey(a))<0){
    seeded.push(snoozeKey(a)); snoozed[snoozeKey(a)]=Date.now(); changed=true; } });
  if(changed){ localStorage.setItem('office_demo_snooze_seeded', JSON.stringify(seeded.slice(-50))); saveSnoozed(); }
}
function setSnooze(a, on){
  if(!isAsking(a)) return;
  if(on) snoozed[snoozeKey(a)]=Date.now(); else delete snoozed[snoozeKey(a)];
  saveSnoozed();
  rebuild();
  const p=people.find(q=>q.id===a.id), now=performance.now();
  if(p && on){ p.bubbleTool=false; p.bubbleText='ok \u{1F60C}'; p.bubbleStart=now; p.bubbleUntil=now+7000; }
  toast(on ? 'ok \u{1F60C} '+nameFor(a.id)+' will wait quietly' : nameFor(a.id)+' is asking again \u2753');
}
let knockAssign = {};   // agent id -> stable front-of-glass knock spot index
let snoozeHits = [];    // per-frame click rects of the "not now" chips
let glassTaps = [];     // knuckle-tap ripples on the "glass" (screen space; capped, auto-expire)
let askSeen = null;     // id -> question_id last seen asking (null until the first poll)
const KNOCK_XS = [0.5, 0.31, 0.69, 0.17, 0.83, 0.41, 0.59];   // fractions of W along the front edge
const KNOCK_Y = H - 34;  // anchor: legs run off the bottom edge -- pressed right up to the glass
const KNOCK_SC = 2.3;    // drawn bigger: closer to the viewer

// ---- ambient random events (pure scenery; never clickable / never hit-tested) ----
// One dog OR cat OR agent-relocate fires every 30-60s, scheduled inside tick() off
// the same rAF clock so it can't drift like a stray setInterval. These critters live
// ONLY in the animation layer: pick(), hover, confetti and polling never see them.
let amb = { dog:null, cat:null, plane:null, turkeys:null };   // at most one dog/cat/plane; a little turkey flock on Thanksgiving
let nextEventAt = 0;                // performance.now() ms of the next event
let lastEventType = null;           // avoid firing the same type twice in a row
let nextPlaneAt = 0;                // performance.now() ms of the next window fly-by

// stable kitchen floor spots (hand-placed, ≥~44px apart, CLEAR of the fridge/counter,
// the lounge table+poufs, the couch, the REFRESH! machine and the wall signs). Used
// for waiter scatter AND as relocate targets so agents never stack.
const KSPOTS = [
  [95,432],[185,428],[280,433],[360,429],           // band in front of the counter (kept left of BEACH_X)
  [60,460],[125,460],[230,470],[315,466],           // mid floor (between fridge and beach)
  [255,548],[320,545],[365,540]                     // front-centre gap (between table and beach)
];

// stable BEACH rest spots for finished agents (all in the right band, x > BEACH_X and
// LEFT of SHORE_X so they sit on the sand, clear of the ocean and the umbrella).
const BSPOTS = [
  [438,520],[510,532],[464,478],
  [556,502],[566,466],[534,548]
];

// ---- layout regions (in canvas px) ----
function layout(){
  const kitchenH = Math.round(H*0.40);
  return {
    office: {x:0, y:0, w:W, h:H-kitchenH},
    kitchen:{x:0, y:H-kitchenH, w:W, h:kitchenH},
    kitchenTop: H-kitchenH
  };
}

// Build the office desk grid for `n` desks. At n<=6 it is the original fixed 2x3 pod
// layout (unchanged look + seat stability). Above that it picks the column count that
// allows the biggest pods, packs the rows evenly between the wall and the kitchen, and
// -- once it's large -- groups the columns into light, labeled "work rooms".
function deskGrid(n, L){
  if(n<=6){
    const cols=3, need=6, left=140, right=W-140, top=WALL_H+48, rowH=128;
    const slots=[];
    for(let i=0;i<need;i++){ const c=i%cols, r=Math.floor(i/cols);
      slots.push({ x:left+c*((right-left)/(cols-1)), y:top+r*rowH, scale:SC, room:0, worker:null }); }
    return { slots, rooms:[], cols, rows:2 };
  }
  // Every row must sit fully on the office floor between the wall and the kitchen counter:
  // a pod reaches POD_UP above its anchor (head / headrest) and POD_DOWN below (a 2-line
  // name-plate); horizontally the desk spans +-26 and the first helper gnome sits at -46.
  const POD_UP=32, POD_DOWN=44, POD_H=POD_UP+POD_DOWN, POD_W=76, GAP_MIN=4;
  const padX=70, floorTop=WALL_H+6, floorBot=L.kitchenTop-6;
  const usableW = (W - padX) - padX, availH = floorBot - floorTop;
  // try every column count; keep the one that allows the biggest pods (prefer fewer
  // columns on a near-tie so the grid stays compact).
  let best=null;
  for(let c=3; c<=n; c++){
    const r=Math.ceil(n/c);
    if(best && r===best.rows) continue;
    const sW = c>1 ? (usableW/(c-1))/POD_W : SC;
    const sH = (availH - (r+1)*GAP_MIN)/(r*POD_H);
    const s = Math.min(SC, sW, sH);
    if(!best || s > best.scale+0.03) best={cols:c, rows:r, scale:s};
  }
  const cols=Math.ceil(n/best.rows), rows=best.rows;
  const scale=Math.max(0.6, best.scale);   // legibility floor for a very crowded office
  const colSpace = cols>1 ? usableW/(cols-1) : 0;
  // spread the spare height evenly above, between and below the rows; if the floor clamp
  // made the pods too tall to fit, overlap the rows rather than cross into the kitchen.
  const podH=POD_H*scale;
  let gap=(availH - rows*podH)/(rows+1), pitch=podH+gap;
  if(gap<0){ gap=0; pitch = rows>1 ? (availH-podH)/(rows-1) : 0; }
  // name-plate text width (local px) so neighbouring plates in a tight row never touch
  const plateW = cols>1 ? Math.max(30, Math.min(84, Math.floor(colSpace/scale) - 14)) : 84;
  const slots=[];
  for(let i=0;i<n;i++){
    const c=i%cols, r=Math.floor(i/cols);
    const inRow=Math.min(cols, n-r*cols);
    const x = cols>1 ? (padX + (c + (cols-inRow)/2)*colSpace) : W/2;   // centre a short last row
    const y = floorTop + gap + POD_UP*scale + r*pitch;
    const edgeW = Math.floor(2*Math.min(x, W-x)/scale) - 14;     // keep edge plates on-canvas
    slots.push({ x:Math.round(x), y:Math.round(y), scale, plateW:Math.max(30, Math.min(plateW, edgeW)), room:0, worker:null });
  }
  // once the office has grown tall AND wide, split the columns into a few labeled rooms
  // (light dividers + a small tag) so a big grid reads as intentional "work rooms".
  const rooms=[];
  if(rows>=3 && cols>=4){
    const names=['A','B','C','D','E'];
    const rc=Math.min(names.length, Math.max(2, Math.round(cols/4)));
    const base=Math.floor(cols/rc), extra=cols%rc;
    let start=0;
    for(let g=0; g<rc; g++){
      const cnt=base+(g<extra?1:0), c0=start, c1=start+cnt-1; start+=cnt;
      // panel spans the gaps on either side of the room's outer columns
      const xL=(c0===0) ? 0 : padX+(c0-0.5)*colSpace;
      const xR=(c1===cols-1) ? W : padX+(c1+0.5)*colSpace;
      rooms.push({ x0:Math.round(xL), x1:Math.round(xR), cx:Math.round((xL+xR)/2),
                   label:'ROOM '+names[g] });
      slots.forEach(s=>{ if(s.x>=xL && s.x<xR) s.room=g; });
    }
  }
  return { slots, rooms, cols, rows };
}

// light "work rooms": alternating translucent floor panels + soft dividers that group the
// desks into labeled clusters. Drawn behind the desks (so it reads through the floor gaps)
// once the grid has grown tall + wide; invisible for the small default office.
function drawRooms(){
  if(!officeRooms.length) return;
  const L=layout(), y0=WALL_H, y1=L.kitchenTop;
  ctx.save();
  for(let i=0;i<officeRooms.length;i++){
    const rm=officeRooms[i];
    // alternating panel tint so neighbouring rooms separate at a glance
    ctx.fillStyle = (i&1) ? 'rgba(255,255,255,.06)' : 'rgba(30,24,40,.10)';
    ctx.fillRect(rm.x0, y0, rm.x1-rm.x0, y1-y0);
    if(i>0){                                    // soft divider "wall" between rooms
      ctx.fillStyle='rgba(30,24,40,.22)'; ctx.fillRect(rm.x0-1, y0, 2, y1-y0);
      ctx.fillStyle='rgba(255,255,255,.10)'; ctx.fillRect(rm.x0+1, y0, 1, y1-y0);
    }
  }
  ctx.restore();
}

// desk scale for a WORK person (seated or walking in); SC for everyone else.
function pscale(p){
  if(p && p.kind==='knock'){   // grows as it walks toward the viewer
    const top=H-Math.round(H*0.40), u=Math.max(0, Math.min(1, (p.y-top)/(KNOCK_Y-top)));
    return SC + (KNOCK_SC-SC)*u;
  }
  return (p && p.kind==='work' && p.deskScale) ? p.deskScale : SC;
}

// assign stable positions: desks for workers (grid), wander targets for waiters
function rebuild(){
  const L = layout();
  // when the "hide scheduled" filter is on, courier (scheduled) agents don't get a
  // desk or kitchen spot -- they walk off-screen instead (handled at the end).
  const active = hideScheduled ? agents.filter(a=>!a.scheduled) : agents;
  // agents marked "finished" go to the beach regardless of working/waiting status;
  // everyone else is placed at desks (working) or the kitchen (waiting) as before.
  const beachers = active.filter(a=>finishedIds.has(a.id));
  const rest = active.filter(a=>!finishedIds.has(a.id));
  const workers = rest.filter(a=>a.status==='working');
  const waiters = rest.filter(a=>a.status!=='working');

  const next = [];
  const prevById = {}; people.forEach(p=>prevById[p.id]=p);

  // --- STABLE position assignment ---------------------------------------
  // Each agent keeps the SAME desk slot / kitchen seat across refreshes, keyed
  // by its id. When an agent changes role (kitchen<->desk) it KEEPS its old x/y
  // and walks/glides to the new target instead of teleporting.
  const workerIds = new Set(workers.map(a=>a.id));
  const waiterIds = new Set(waiters.map(a=>a.id));
  const beacherIds = new Set(beachers.map(a=>a.id));
  // release assignments for agents that left or switched role
  Object.keys(deskAssign).forEach(id=>{ if(!workerIds.has(id)) delete deskAssign[id]; });
  Object.keys(seatAssign).forEach(id=>{ if(!waiterIds.has(id)) delete seatAssign[id]; });
  Object.keys(beachAssign).forEach(id=>{ if(!beacherIds.has(id)) delete beachAssign[id]; });
  // give brand-new workers the lowest free desk index (stable thereafter)
  const usedSlots = new Set(Object.values(deskAssign));
  workers.forEach(a=>{ if(deskAssign[a.id]==null){ let i=0; while(usedSlots.has(i)) i++; deskAssign[a.id]=i; usedSlots.add(i); } });
  const usedSeats = new Set(Object.values(seatAssign));
  waiters.forEach(a=>{ if(seatAssign[a.id]==null){ let i=0; while(usedSeats.has(i)) i++; seatAssign[a.id]=i; usedSeats.add(i); } });
  const usedBeach = new Set(Object.values(beachAssign));
  beachers.forEach(a=>{ if(beachAssign[a.id]==null){ let i=0; while(usedBeach.has(i)) i++; beachAssign[a.id]=i; usedBeach.add(i); } });
  // unanswered, un-snoozed question forms walk up to the glass (they keep their kitchen seat)
  const knockers = waiters.filter(a=>a.asking==='form' && !isSnoozed(a));
  const knockIds = new Set(knockers.map(a=>a.id));
  Object.keys(knockAssign).forEach(id=>{ if(!knockIds.has(id)) delete knockAssign[id]; });
  const usedKnock = new Set(Object.values(knockAssign));
  knockers.forEach(a=>{ if(knockAssign[a.id]==null){ let i=0; while(usedKnock.has(i)) i++; knockAssign[a.id]=i; usedKnock.add(i); } });

  // a desk layout that is ALWAYS drawn (so the room looks furnished even when nobody
  // is working) AND that GROWS so the office never runs out of desks: as the working
  // headcount passes the cozy 6-desk default we add rows/columns and scale the desks
  // (plus the agents sitting at them) down to fit the floor. deskGrid() reproduces the
  // original 2x3 layout byte-for-byte at <=6, so small offices look exactly as before.
  const maxSlot = Object.values(deskAssign).reduce((m,v)=>Math.max(m,v), -1);
  const nWork = Math.max(6, maxSlot + 1);         // desks to lay out (>=6, always full)
  const grid = deskGrid(nWork, L);
  deskSlots = grid.slots;                          // [{x,y,scale,room,worker:null}, ...]
  officeRooms = grid.rooms;                         // labeled column clusters (empty unless large)
  // where a just-un-drowned agent climbs back out of the sea: mid-ocean band, mid-beach height
  const SEA = { x: SHORE_X + Math.round(WATER_W*0.5), y: L.kitchenTop + Math.round((H-L.kitchenTop)*0.45) };
  workers.forEach(a=>{
    const old = prevById[a.id];
    const slot = deskSlots[deskAssign[a.id]];
    // already seated at THIS desk? stay seated. Otherwise walk in and then sit.
    const sameSeat = old && old.kind==='work' && old.seated &&
                     old.deskX===slot.x && old.deskY===slot.y;
    const emerging = !old && emergeFrom.has(a.id);   // just resurfaced -> wade in from the ocean
    const person = Object.assign(old||{}, {
      id:a.id, agent:a, kind:'work',
      // keep current position so a kitchen->desk move animates as a walk
      x: old? old.x : (emerging? SEA.x : slot.x), y: old? old.y : (emerging? SEA.y : slot.y),
      deskX:slot.x, deskY:slot.y, deskScale:slot.scale, plateW:slot.plateW||84, vx:0, vy:0,
      seated: old ? !!sameSeat : (emerging? false : true),   // emergers walk up from the water
      seed:hash(a.id), variant:a.variant, feat:featuresForAgent(a),
    });
    if(emerging) emergeFrom.delete(a.id);
    slot.worker = person;
    next.push(person);
  });

  // kitchen: scatter waiting agents NATURALLY across the open floor (not a grid).
  // Each agent keeps a stable anchor (by seatAssign index) plus a small deterministic
  // jitter from hash(id). The anchor list is hand-placed (≥~52px apart, with a few
  // loose pairs) and stays CLEAR of the fridge/counter (top-left band), the COFFEE
  // and DO GOOD WORK signs, the REFRESH! machine (right), and the couch + table.
  const k = L.kitchen;
  // hand-placed scatter across the OPEN floor (KSPOTS), clear of the lounge table
  // (left), the couch + side table (right), the counter/fridge (back wall), the
  // REFRESH! machine and the DO GOOD WORK poster. Spaced ≥~44px for hovering.
  waiters.forEach(a=>{
    const old = prevById[a.id];
    if(knockIds.has(a.id)){
      const ki = knockAssign[a.id], ring = Math.floor(ki / KNOCK_XS.length);
      next.push(Object.assign(old||{}, {
        id:a.id, agent:a, kind:'knock',
        x: old? old.x : W*0.5, y: old? old.y : k.y+8,
        home: { x: Math.round(KNOCK_XS[ki % KNOCK_XS.length]*W) + ring*22, y: KNOCK_Y },
        vx:0, vy:0,
        mode: (!old || old.kind!=='knock') ? 'walk' : old.mode,
        seed:hash(a.id), variant:a.variant, feat:featuresForAgent(a),
      }));
      return;
    }
    const idx = seatAssign[a.id];
    const base = KSPOTS[idx % KSPOTS.length];
    const ring = Math.floor(idx / KSPOTS.length);   // overflow agents nudge outward
    const hsh = hash(a.id);
    const jx = ((hsh>>>3) % 9) - 4;                  // -4..+4 deterministic jitter
    const jy = ((hsh>>>9) % 9) - 4;
    // a relocated agent (ambient event) keeps its event-chosen spot across refreshes
    // instead of snapping back to its stable anchor.
    const home = (old && old.relocHome) ? old.relocHome
               : { x: base[0] + jx + ring*16, y: base[1] + jy + ring*14 };
    // walk in if new or arriving from another zone (desk/beach); otherwise keep mode
    const cameFromElsewhere = !old || old.kind!=='wait';
    const emerging = !old && emergeFrom.has(a.id);   // just resurfaced -> wade in from the ocean
    next.push(Object.assign(old||{}, {
      id:a.id, agent:a, kind:'wait',
      // brand-new agents enter from the room doorway (top-center) and walk to their spot;
      // agents leaving a desk keep their office position; just-un-drowned ones rise from the sea.
      x: old? old.x : (emerging? SEA.x : W*0.5), y: old? old.y : (emerging? SEA.y : k.y+8),
      home, vx:0, vy:0,
      mode: cameFromElsewhere ? 'walk' : old.mode,
      seed:hash(a.id), variant:a.variant, feat:featuresForAgent(a),
    }));
    if(emerging) emergeFrom.delete(a.id);
  });

  // pair each waiting agent with its nearest kitchen neighbour (by anchor) so they can
  // occasionally turn and chat. Recomputed every poll, so it tracks relocations.
  const waitList = next.filter(p=>p.kind==='wait');
  for(const p of waitList){
    let bx=null, bd=80;                       // only pair within ~80px
    for(const q of waitList){ if(q===p) continue;
      const d=Math.hypot(p.home.x-q.home.x, p.home.y-q.home.y);
      if(d<bd){ bd=d; bx=q.home.x; }
    }
    p.talkX = bx;   // x of the neighbour to face while chatting (null = nobody near)
  }

  // beach: finished agents walk over to the sand and chill until you unmark them.
  beachers.forEach(a=>{
    const old = prevById[a.id];
    const idx = beachAssign[a.id];
    const base = BSPOTS[idx % BSPOTS.length];
    const ring = Math.floor(idx / BSPOTS.length);        // overflow nudges outward
    const hsh = hash(a.id);
    const jx = ((hsh>>>4) % 7) - 3;
    const jy = ((hsh>>>10) % 7) - 3;
    const home = { x: base[0] + jx + ring*14, y: base[1] + jy + ring*12 };
    const cameFromElsewhere = !old || old.kind!=='beach';
    next.push(Object.assign(old||{}, {
      id:a.id, agent:a, kind:'beach',
      x: old? old.x : W*0.5, y: old? old.y : k.y+8,
      home, vx:0, vy:0,
      mode: cameFromElsewhere ? 'walk' : old.mode,
      seed:hash(a.id), variant:a.variant, feat:featuresForAgent(a),
    }));
  });

  // filtered-out scheduled agents: if they were on screen, keep them around just long
  // enough to walk off the bottom edge (a tidy "exit"); ones that were never visible
  // are simply omitted. Turning the filter back off re-adds them via the normal
  // worker/kitchen assignment above, so they walk back in from where they left.
  if(hideScheduled){
    agents.filter(a=>a.scheduled).forEach(a=>{
      const old = prevById[a.id];
      if(!old) return;
      next.push(Object.assign(old, {
        id:a.id, agent:a, kind:'exit', mode:'walk', seated:false,
        // sprites are drawn scaled x SC about their anchor, so the body extends
        // ~50px ABOVE the anchor -- push the target well below H so the WHOLE
        // sprite (cap included) clears the bottom edge, not just the feet.
        exitX: W*0.5, exitY: H + 70*SC,
        vx:0, vy:0,
        seed:hash(a.id), variant:a.variant, feat:featuresForAgent(a),
      }));
    });
  }

  people = next;
  document.getElementById('hud-work').textContent = 'working: '+workers.length;
  document.getElementById('hud-wait').textContent = 'in kitchen: '+(waiters.length-knockers.length);
  const askers = rest.filter(isAsking), nSnz = askers.filter(isSnoozed).length;
  const ha = document.getElementById('hud-ask');
  ha.innerHTML = '&#10067; waiting on you: '+(askers.length-nSnz)+
    (nSnz ? ' <span class="dim">(+'+nSnz+' snoozed)</span>' : '');
  ha.style.display = askers.length ? '' : 'none';
  const hb=document.getElementById('hud-beach');
  hb.textContent = 'on beach: '+beachers.length;
  hb.style.display = beachers.length ? '' : 'none';   // only show the pill when in use
  // running subagents + active workflow runs across all agents (only shown when in use)
  const subCount = agents.reduce((n,a)=>n+(a.subs||0)+(a.wf_running_agents||0),0);
  const wfCount  = agents.reduce((n,a)=>n+((a.workflows||[]).length),0);
  const hs=document.getElementById('hud-subs');
  hs.textContent='subagents: '+subCount; hs.style.display = subCount ? '' : 'none';
  const hw=document.getElementById('hud-wf');
  hw.textContent='workflows: '+wfCount; hw.style.display = wfCount ? '' : 'none';
  document.getElementById('empty').style.display = agents.length? 'none':'flex';
}

function hash(s){let h=0;for(let i=0;i<s.length;i++)h=(h*31+s.charCodeAt(i))&0xffffffff;return h>>>0;}

// ---- agent name styles (chosen in the header; names are stable per agent id) ----
const NAME_SETS = {
  magical: { label:'MAGICAL', first:["Pip","Willow","Clover","Bun","Maple","Sprout","Waffle","Biscuit","Poppy","Mochi","Pebble","Fern","Cricket","Marshmallow","Pumpkin","Honey","Acorn","Noodle","Pickle","Sunny","Berry","Tofu","Dandelion","Bramble","Hazel","Olive","Tansy","Muffin","Peaches","Juniper"],
    last:["Sunbeam","Marshmallow","Buttercup","Honeydew","Pumpkinpatch","Snugglebee","Cloudberry","Dewdrop","Meadowlight","Gigglesworth","Cottontail","Brightbloom","Mossypaws","Tinkerwhisk","Sugarplum","Pebblebrook","Willowwisp","Honeycomb","Berrybramble","Twinkletoes","Mapleshade","Cuddleburrow","Dapplewood","Snickerdoodle","Fernwhistle"] },
  israeli: { label:'ISRAELI', first:["Yossi","Noa","Avi","Shira","Tal","Yael","Eitan","Dana","Gal","Amit","Ronen","Ori","Roni","Maya","Itai","Nadav","Liron","Chen","Bar","Shani","Adi","Yarden","Omer","Hila","Lior","Guy","Tomer","Inbal","Doron","Sivan","Ziv","Nir","Gil","Rotem","Yuval","Moshe","Sagi","Dvir","Ayelet","Almog","Oren","Carin-Belle"],
    last:["Cohen","Levi","Mizrahi","Peretz","Biton","Dahan","Avraham","Friedman","Katz","Azoulay","Ben-David","Shapira","Bar-On","Malka","Gabai","Segal","Hadad","Barak","Regev","Ohayon","Amar","Klein","Ashkenazi","Elbaz","Tzur","Sasson","Vaknin","Nachmani","Aloni","Shalev","Yomtov","Feder"] },
  dev: { label:'DEV', first:["Segfault","Captain","Null","Sudo","Regex","Commit","Legacy","Hotfix","Boolean","Async","Cache","Merge","Kernel","Turbo","Lazy","Quantum","Rusty","Vim","Recursive","Undefined","Docker","Bcrypt"],
    last:["Overflow","Pointer","Deploy","Nullson","Bugsley","Pushington","Bytewise","Loopy","Debugger","Refactor","O'Reilly","McStacktrace","von Merge","Yeetson","Hashimoto","Snippets","Ramsson","Kernelson","Rebase","Semicolon","Payload","Heapman"] },
  robots: { label:'ROBOTS', first:["Unit","Servo","Chip","Proto","Mecha","Robo","Nano","Giga","Auto","Cy","Zeta","Beep","Clank","Data","Pixel","Opti","Turbo","Volt","Gizmo","Sprocket","Bolt","Widget"],
    last:["Boopmatic","Cogsworth","9000","Mk-II","Whirrley","Sparkplug","Bleepson","Databyte","Clankworth","Buzzbot","Gearhart","Pixelface","Ohmson","Widgeteer","von Circuit","3000","Beepson","Clankstein","Rustbucket","Boltsworth","Zappenheim","Motoroni"] },
};
const NAME_ORDER = ['magical','israeli','dev','robots'];
let nameStyle = localStorage.getItem('office_names'); if(!NAME_SETS[nameStyle]) nameStyle='israeli';
function nameFor(id){ const s=NAME_SETS[nameStyle]||NAME_SETS.magical; const h=hash(id||'x');
  return s.first[h % s.first.length]+' '+s.last[(h>>>8) % s.last.length]; }

// ---- drawing helpers ----
function px(x,y,w,h,col){ctx.fillStyle=col;ctx.fillRect(x|0,y|0,w|0,h|0);}
// scale subsequent drawing about an anchor point (used to enlarge sprites/desks)
function scaleAbout(ax,ay,s){ ctx.translate(ax,ay); ctx.scale(s,s); ctx.translate(-ax,-ay); }

// shade a #rrggbb colour: f>0 lightens toward white, f<0 darkens toward black.
// used for soft, cohesive shading on shirts/hair/furniture (no flat fills).
const _shadeCache={};
function shade(hex, f){
  const key=hex+'|'+f; if(_shadeCache[key]) return _shadeCache[key];
  let n=parseInt(hex.slice(1),16); let r=(n>>16)&255,g=(n>>8)&255,b=n&255;
  if(f>=0){ r+=(255-r)*f; g+=(255-g)*f; b+=(255-b)*f; } else { r*=(1+f); g*=(1+f); b*=(1+f); }
  return _shadeCache[key]='rgb('+(r|0)+','+(g|0)+','+(b|0)+')';
}
// a small white speech bubble with a pink heart (cozy kitchen vibe)
function heartBubble(x,y){
  px(x-8,y-7,18,12,PAL.paper); px(x-8,y-7,18,1,'#ececf2'); px(x-8,y+4,18,1,'#d6d6de');
  px(x-9,y-5,1,8,PAL.paper); px(x+10,y-5,1,8,PAL.paper);
  px(x-3,y+5,3,3,PAL.paper); px(x-2,y+8,2,2,PAL.paper);     // little tail
  px(x-3,y-4,3,3,PAL.pink); px(x+1,y-4,3,3,PAL.pink);        // heart lobes
  px(x-4,y-2,9,2,PAL.pink); px(x-2,y,5,2,PAL.pink); px(x,y+2,1,1,PAL.pink);
}
// a small speech bubble with 1-3 chat dots (kitchen small-talk)
function talkBubble(x,y,n){
  px(x-8,y-7,18,11,PAL.paper); px(x-8,y-7,18,1,'#ececf2'); px(x-8,y+3,18,1,'#d6d6de');
  px(x-9,y-5,1,7,PAL.paper); px(x+10,y-5,1,7,PAL.paper);
  px(x-3,y+4,3,3,PAL.paper); px(x-2,y+7,2,2,PAL.paper);     // little tail
  const dk='#8a8f9c';
  for(let i=0;i<n;i++) px(x-5+i*5,y-2,3,3,dk);              // 1..3 talk dots
}

const WALL_H = 78;
const WIN = { x:20, y:8, w:Math.round(W*0.36), h:WALL_H-20 };  // sky-window glass rect (drawWindow args)

function drawFloor(){
  const L=layout(), oh=L.office.h;
  // office floor: cohesive tiles with grout lines + gentle per-tile shading
  for(let ty=WALL_H; ty<oh; ty+=24){
    for(let tx=0; tx<W; tx+=24){
      const alt=((tx/24+Math.floor((ty-WALL_H)/24))&1);
      px(tx,ty,24,24, alt?PAL.ofloor:PAL.ofloor2);
      px(tx,ty,24,1,'rgba(255,255,255,.05)');      // tile top highlight
      px(tx,ty+23,24,1,'rgba(0,0,0,.10)');          // grout (bottom)
      px(tx+23,ty,1,24,'rgba(0,0,0,.08)');          // grout (right)
    }
  }
  px(0,WALL_H,W,26,'rgba(255,255,255,.04)');         // soft daylight band near the windows
  // back wall + picture-rail + skirting
  px(0,0,W,WALL_H,PAL.wall); px(0,0,W,10,shade(PAL.wall,.05));
  px(0,WALL_H-8,W,2,shade(PAL.wall,-.06)); px(0,WALL_H-5,W,3,PAL.trim); px(0,WALL_H-2,W,2,PAL.base);
  const winW = Math.round(W*0.36);   // slimmer window -> room for the wider board
  drawWindow(20, 8, winW, WALL_H-20);
  const wl = wallRowLayout();
  drawWallDecor(wl.boardX, 6, wl.clkL, wl.shfL);

  // kitchen floor (warm tiles)
  for(let y=L.kitchenTop;y<H;y+=20){
    for(let x=0;x<W;x+=20){ px(x,y,20,20, ((x/20+y/20)&1)?PAL.kfloor:PAL.kfloor2); }
  }
  // divider skirting between rooms
  px(0,L.kitchenTop-4,W,4,PAL.base); px(0,L.kitchenTop,W,2,'rgba(0,0,0,.16)');

  drawOfficeProps();
  drawKitchenProps();
}

// ---- furniture / decor helpers ----
function chair(x,y,col){ px(x,y,12,5,col); px(x,y-9,2,9,col); px(x+10,y-9,2,9,col); px(x,y-11,12,3,col); }
function woodTable(x,y,w,h){ px(x,y,w,h,PAL.wood); px(x,y,w,5,PAL.woodHi); px(x+3,y+9,w-6,2,PAL.woodDk);
  px(x-2,y+h-2,5,9,PAL.woodDk); px(x+w-3,y+h-2,5,9,PAL.woodDk); }
function laptop(x,y){ px(x,y,18,12,PAL.monitorLip); px(x+1,y+1,16,8,PAL.screen); px(x-1,y+11,20,3,PAL.metal); }
function mug(x,y,col){ px(x,y,7,7,PAL.paper); px(x+1,y+1,5,5,col); px(x+7,y+2,2,3,PAL.paper); }
// a single tapered leaf/frond: rises `h` px from (bx,baseY), drifting `dx` sideways,
// with a dark edge outline and a lighter inner stripe so it reads hand-drawn.
function blade(bx, baseY, h, dx, col){
  const hi=shade(col,.30), lo=shade(col,-.34);
  for(let i=0;i<h;i++){
    const t=i/h, cx=Math.round(bx+dx*t);
    const w=(i<h-4)?3:(i<h-2)?2:1;            // taper to a point
    px(cx-1, baseY-i, 1,1, lo);                // dark left edge
    px(cx,   baseY-i, w,1, col);               // leaf body
    px(cx+w-1, baseY-i, 1,1, lo);              // dark right edge
    if(i%2===0) px(cx, baseY-i, 1,1, hi);      // inner highlight speckle
  }
}
function smallPlant(x,y){
  const cx=x+6;
  ctx.fillStyle='rgba(0,0,0,.14)'; ctx.beginPath(); ctx.ellipse(cx,y+9,10,3,0,0,Math.PI*2); ctx.fill();
  // tapered little pot
  px(x,y,12,3,shade(PAL.pot,.16)); px(x+1,y+3,10,3,PAL.pot); px(x+2,y+6,8,3,shade(PAL.pot,-.10));
  px(x+1,y+3,2,5,shade(PAL.pot,.18)); px(x+1,y+2,10,1,PAL.potDk);
  // a few short blades
  [[-4,12,-5],[-1,17,-1],[2,15,2],[5,11,5]].forEach((d,i)=> blade(cx+d[0], y+3, d[1], d[2], i%2?PAL.leaf:PAL.leafDk));
}
function bigPlant(x,y){
  const cx=x+9;
  ctx.fillStyle='rgba(0,0,0,.16)'; ctx.beginPath(); ctx.ellipse(cx,y+20,16,4,0,0,Math.PI*2); ctx.fill();
  // tapered terracotta pot with a rim + soil line
  px(x-1,y,20,5,shade(PAL.pot,.18));                                   // rim (widest)
  px(x+1,y+5,16,5,PAL.pot); px(x+2,y+10,14,5,PAL.pot); px(x+3,y+15,12,4,shade(PAL.pot,-.10)); // tapered body
  px(x+2,y+5,3,13,shade(PAL.pot,.16)); px(x+12,y+6,3,12,shade(PAL.pot,-.14)); // hi / shade
  px(x+1,y+4,16,2,PAL.potDk);                                          // soil line
  // a fan of fern/snake-plant blades of varied height
  [[-9,22,-12],[-6,32,-8],[-3,42,-4],[0,48,0],[3,42,4],[6,32,8],[9,24,12]]
    .forEach((d,i)=> blade(cx+d[0], y+5, d[1], d[2], (i===3)?PAL.leaf:(i%2?PAL.leaf:PAL.leafDk)));
}
function couch(x,y){ px(x,y,70,22,PAL.cabinet); px(x,y-10,70,12,'#4f6377');
  px(x-6,y-10,8,30,PAL.cabinet); px(x+68,y-10,8,30,PAL.cabinet);
  px(x+4,y+2,28,9,'#5a6e82'); px(x+38,y+2,28,9,'#5a6e82'); }
// a tall blue dining chair with a curved padded back (seen from the side of a table)
function blueChair(x,y){
  const c='#3f64c0', cd='#2f4a96', ch='#5a7ed8';
  px(x+2,y+2,2,12,'#1f1f24'); px(x+12,y+2,2,12,'#1f1f24');     // legs
  ro(x,y-2,16,6,cd); px(x+1,y-2,14,2,c);                        // seat
  ro(x+1,y-17,14,16,c); px(x+2,y-16,12,3,ch); px(x+2,y-4,12,2,cd); // curved back
  px(x+2,y-16,2,15,ch);                                         // left rail sheen
}
// a cute sleeping bear-style mascot (pure scenery, not an agent). NOTE: no longer
// called anywhere (it was removed from the beach); kept intact in case it's wanted again.
function bearMascot(x,y){
  const fur='#4a6b88', furDk='#3a5572', furHi='#5f82a0', belly='#efe2c2', pad='#dcc99e';
  function el(cx,cy,rx,ry,col){ ctx.fillStyle=col; ctx.beginPath(); ctx.ellipse(cx,cy,rx,ry,0,0,Math.PI*2); ctx.fill(); }
  el(x,y+13,9,6,furDk); el(x+18,y+13,9,6,furDk);               // feet
  el(x+3,y+14,4,3,pad); el(x+15,y+14,4,3,pad);                 // foot pads
  el(x+9,y-4,21,20,fur);                                       // body
  el(x+9,y-1,13,14,belly);                                     // cream belly
  el(x-8,y-2,7,9,fur); el(x+26,y-2,7,9,fur);                   // arms
  el(x-4,y-24,5,5,fur); el(x+22,y-24,5,5,fur);                 // ears
  el(x+9,y-19,15,13,fur);                                      // head
  el(x-3,y-24,3,3,furHi); el(x+9,y-26,5,3,furHi);              // head sheen
  // sleeping content face: two closed (downward-arc) eyes + a soft smile
  px(x+1,y-20,5,1,PAL.outline); px(x+1,y-19,1,1,PAL.outline); px(x+5,y-19,1,1,PAL.outline);
  px(x+12,y-20,5,1,PAL.outline); px(x+12,y-19,1,1,PAL.outline); px(x+16,y-19,1,1,PAL.outline);
  px(x+6,y-14,6,1,PAL.outline); px(x+5,y-15,1,1,PAL.outline); px(x+12,y-15,1,1,PAL.outline);
  // mug held in the left paw
  px(x-12,y-8,7,7,PAL.paper); px(x-11,y-7,5,5,PAL.mugC); px(x-5,y-7,2,3,PAL.paper);
  px(x-11,y-9,4,2,'rgba(255,255,255,.55)');                    // steam
  // "Z z" sleep symbols
  ctx.fillStyle=PAL.ink; ctx.font='7px "Press Start 2P", monospace'; ctx.fillText('Z', x+28, y-24);
  ctx.font='4px "Press Start 2P", monospace'; ctx.fillText('z', x+35, y-30);
}

// blend two #rrggbb colours (t: 0->a, 1->b)
function lerpCol(a,b,t){ const pa=parseInt(a.slice(1),16),pb=parseInt(b.slice(1),16);
  const ar=(pa>>16)&255,ag=(pa>>8)&255,ab=pa&255, br=(pb>>16)&255,bg=(pb>>8)&255,bb=pb&255;
  return 'rgb('+Math.round(ar+(br-ar)*t)+','+Math.round(ag+(bg-ag)*t)+','+Math.round(ab+(bb-ab)*t)+')'; }
function cloud(cx,cy){ cx|=0; cy|=0; px(cx,cy,15,4,PAL.cloud); px(cx+3,cy-3,9,4,PAL.cloud); px(cx+1,cy+3,17,2,'rgba(255,255,255,.75)'); }
// a row of city buildings sitting on the window sill (clipped to x..x+w).
// `lit` => night mode: warm yellow lit windows speckled across dark silhouettes.
function drawSkyline(x,y,w,h,col,hf,step,lit){
  const hs=[16,26,12,32,20,28,15,24,18,30,22,14]; let bx=x+1,i=0; const baseY=y+h;
  while(bx<x+w-1){ const bw=Math.min(10+(i%4)*5, x+w-1-bx);
    const bh=Math.round(h*hf*(0.45+0.55*(hs[(i*step)%hs.length]/32)));
    px(bx,baseY-bh,bw,bh,col);
    for(let wy=baseY-bh+3;wy<baseY-2;wy+=5) for(let wx=bx+2;wx<bx+bw-2;wx+=4){
      if(lit){ const on=((wx*31+wy*17+i*13)%5===0); px(wx,wy,1,2, on?PAL.litWin:'rgba(255,255,255,.05)'); }
      else px(wx,wy,1,2,PAL.bldgWin);
    }
    bx+=bw+3; i++;
  }
}
// ---- day / dusk / night in the window, from the REAL sun position -- season- AND place-aware,
// with NO location permission. The browser hands us the IANA time-zone name for free via Intl;
// we map it to a representative city lat/lng (tz-database zone.tab) and compute the sun's altitude
// locally. Nothing leaves the machine, and there is never a GPS prompt. __forceSky overrides. ----
const TZ_COORDS = {
  // North America
  "America/New_York":[40.71,-74.01],"America/Detroit":[42.33,-83.05],"America/Toronto":[43.65,-79.38],
  "America/Chicago":[41.85,-87.65],"America/Winnipeg":[49.90,-97.14],"America/Mexico_City":[19.43,-99.13],
  "America/Denver":[39.74,-104.98],"America/Edmonton":[53.55,-113.49],"America/Phoenix":[33.45,-112.07],
  "America/Los_Angeles":[34.05,-118.24],"America/Vancouver":[49.28,-123.12],"America/Tijuana":[32.53,-117.02],
  "America/Anchorage":[61.22,-149.90],"America/Halifax":[44.65,-63.57],"Pacific/Honolulu":[21.31,-157.86],
  // Central & South America
  "America/Guatemala":[14.61,-90.53],"America/Panama":[8.98,-79.52],"America/Bogota":[4.61,-74.08],
  "America/Lima":[-12.05,-77.04],"America/Caracas":[10.50,-66.92],"America/Santiago":[-33.45,-70.67],
  "America/Sao_Paulo":[-23.55,-46.63],"America/Argentina/Buenos_Aires":[-34.61,-58.38],
  // Europe
  "Europe/London":[51.51,-0.13],"Europe/Dublin":[53.35,-6.26],"Europe/Lisbon":[38.72,-9.14],
  "Europe/Madrid":[40.42,-3.70],"Europe/Paris":[48.85,2.35],"Europe/Brussels":[50.85,4.35],
  "Europe/Amsterdam":[52.37,4.90],"Europe/Berlin":[52.52,13.40],"Europe/Zurich":[47.37,8.55],
  "Europe/Rome":[41.90,12.50],"Europe/Vienna":[48.21,16.37],"Europe/Prague":[50.08,14.44],
  "Europe/Warsaw":[52.23,21.01],"Europe/Budapest":[47.50,19.04],"Europe/Copenhagen":[55.68,12.57],
  "Europe/Stockholm":[59.33,18.07],"Europe/Oslo":[59.91,10.75],"Europe/Helsinki":[60.17,24.94],
  "Europe/Athens":[37.98,23.73],"Europe/Bucharest":[44.43,26.10],"Europe/Sofia":[42.70,23.32],
  "Europe/Kyiv":[50.45,30.52],"Europe/Kiev":[50.45,30.52],"Europe/Moscow":[55.76,37.62],
  "Europe/Istanbul":[41.01,28.98],
  // Middle East
  "Asia/Jerusalem":[31.78,35.22],"Asia/Tel_Aviv":[32.07,34.79],"Asia/Beirut":[33.89,35.50],
  "Asia/Amman":[31.95,35.93],"Asia/Damascus":[33.51,36.29],"Asia/Baghdad":[33.31,44.36],
  "Asia/Riyadh":[24.71,46.68],"Asia/Dubai":[25.20,55.27],"Asia/Qatar":[25.29,51.53],
  "Asia/Kuwait":[29.38,47.99],"Asia/Tehran":[35.69,51.39],"Asia/Nicosia":[35.17,33.36],
  // Africa
  "Africa/Casablanca":[33.57,-7.59],"Africa/Algiers":[36.75,3.06],"Africa/Cairo":[30.04,31.24],
  "Africa/Lagos":[6.52,3.38],"Africa/Nairobi":[-1.29,36.82],"Africa/Addis_Ababa":[9.03,38.74],
  "Africa/Johannesburg":[-26.20,28.05],"Africa/Accra":[5.60,-0.19],
  // South, Central & East Asia
  "Asia/Karachi":[24.86,67.01],"Asia/Kolkata":[22.57,88.36],"Asia/Calcutta":[22.57,88.36],
  "Asia/Colombo":[6.93,79.85],"Asia/Kathmandu":[27.72,85.32],"Asia/Dhaka":[23.71,90.41],
  "Asia/Yangon":[16.87,96.20],"Asia/Bangkok":[13.75,100.52],"Asia/Ho_Chi_Minh":[10.82,106.63],
  "Asia/Saigon":[10.82,106.63],"Asia/Jakarta":[-6.21,106.85],"Asia/Singapore":[1.29,103.85],
  "Asia/Kuala_Lumpur":[3.14,101.69],"Asia/Manila":[14.60,120.98],"Asia/Hong_Kong":[22.32,114.17],
  "Asia/Shanghai":[31.23,121.47],"Asia/Taipei":[25.03,121.57],"Asia/Seoul":[37.57,126.98],
  "Asia/Tokyo":[35.68,139.65],"Asia/Almaty":[43.25,76.95],"Asia/Tashkent":[41.31,69.24],
  "Asia/Yekaterinburg":[56.84,60.65],"Asia/Novosibirsk":[55.01,82.93],"Asia/Vladivostok":[43.12,131.89],
  // Australia & Pacific
  "Australia/Perth":[-31.95,115.86],"Australia/Adelaide":[-34.93,138.60],"Australia/Darwin":[-12.46,130.84],
  "Australia/Brisbane":[-27.47,153.03],"Australia/Sydney":[-33.87,151.21],"Australia/Melbourne":[-37.81,144.96],
  "Pacific/Auckland":[-36.85,174.76],"Pacific/Fiji":[-18.14,178.44]
};
function localCoords(){
  let tz='';
  try{ tz=Intl.DateTimeFormat().resolvedOptions().timeZone||''; }catch(e){}
  if(TZ_COORDS[tz]) return TZ_COORDS[tz];
  // unknown zone: longitude from the UTC offset, equatorial latitude (a neutral ~6pm sunset)
  return [0, -new Date().getTimezoneOffset()/4];
}
// sun altitude (degrees above the horizon) right now, at lat/lng. Low-precision USNO formulas
// (good to a fraction of a degree -- ample for deciding day/dusk/night).
function sunAltitude(date, lat, lng){
  const rad=Math.PI/180, deg=180/Math.PI;
  const d = date.getTime()/86400000 - 10957.5;              // days since J2000 (2000-01-01 12:00 UTC)
  const g = ((357.529 + 0.98560028*d)%360)*rad;             // mean anomaly
  const q = (280.459 + 0.98564736*d)%360;                   // mean longitude
  const L = (q + 1.915*Math.sin(g) + 0.020*Math.sin(2*g))*rad;   // ecliptic longitude
  const e = (23.439 - 0.00000036*d)*rad;                    // obliquity
  const dec = Math.asin(Math.sin(e)*Math.sin(L));           // declination
  const ra  = Math.atan2(Math.cos(e)*Math.sin(L), Math.cos(L))*deg;   // right ascension (deg)
  let gmst = (18.697374558 + 24.06570982441908*d)%24; if(gmst<0) gmst+=24;
  let ha = ((gmst*15 + lng) - ra)%360; ha=((ha+540)%360)-180;   // hour angle, folded to [-180,180]
  return Math.asin(Math.sin(lat*rad)*Math.sin(dec) + Math.cos(lat*rad)*Math.cos(dec)*Math.cos(ha*rad))*deg;
}
function skyMode(){
  if(window.__forceSky) return window.__forceSky;
  const c=localCoords(), alt=sunAltitude(new Date(), c[0], c[1]);
  if(alt <= -6) return 'night';        // sun past civil twilight -> dark
  if(alt <   6) return 'dusk';         // sun near the horizon -> golden dawn/dusk
  return 'day';
}
function drawWindow(x,y,w,h){
  // chunky frame
  px(x-5,y-5,w+10,h+10,PAL.woodDk); px(x-3,y-3,w+6,h+6,PAL.wood); px(x-3,y-3,w+6,2,PAL.woodHi);
  const mode=skyMode(), night=(mode==='night'), bands=10, bh=Math.ceil(h/bands);
  if(night){
    for(let i=0;i<bands;i++) px(x, y+Math.round(i*h/bands), w, bh, lerpCol(PAL.nightTop, PAL.nightBot, i/(bands-1)));
    // scattered stars (deterministic) in the upper sky
    for(let s=0;s<48;s++){ const sx=x+((s*73)%(w-4))+2, sy=y+((s*37)%Math.max(1,Math.round(h*0.5)))+2;
      px(sx,sy,1,1, s%6? 'rgba(255,255,255,.85)':'rgba(255,255,255,.45)'); }
    // crescent moon (top-right)
    const mnx=x+w-Math.round(w*0.20), mny=y+Math.round(h*0.16);
    px(mnx,mny,8,8,PAL.moon); px(mnx+4,mny-1,6,8, lerpCol(PAL.moon,PAL.nightTop,.4));
    cloud(x+w*0.30, y+h*0.16);
    drawSkyline(x,y,w,h, PAL.bldgN2, 0.42, 7, true);
    drawSkyline(x,y,w,h, PAL.bldgN1, 0.64, 11, true);
  } else {
    let top=PAL.skyTop, bot=PAL.sky;
    // golden hour: dusty-blue upper sky warming to a bright gold horizon. HEX literals on
    // purpose -- the gradient loop below feeds top/bot back into lerpCol(), and lerpCol only
    // parses '#hex' (rgb() results from a nested lerpCol/shade come out NaN -> black). See the
    // shade(shade()) gotcha in CLAUDE.md.
    if(mode==='dusk'){ top='#9fb8d4'; bot='#f4c07a'; }
    for(let i=0;i<bands;i++) px(x, y+Math.round(i*h/bands), w, bh, lerpCol(top, bot, i/(bands-1)));
    drawSkyline(x,y,w,h, PAL.bldg2, 0.40, 7, false);
    cloud(x+w*0.16, y+h*0.20); cloud(x+w*0.44, y+h*0.12); cloud(x+w*0.70, y+h*0.26);
    drawSkyline(x,y,w,h, PAL.bldg1, 0.62, 11, false);
  }
  // occasional airliner drifting across the sky (clipped to the glass, behind the mullions)
  if(amb.plane){ ctx.save(); ctx.beginPath(); ctx.rect(x,y,w,h); ctx.clip(); drawPlane(amb.plane); ctx.restore(); }
  // Godzilla stomping past the skyline (clipped to the glass, behind the mullions)
  if(godzilla.active){ ctx.save(); ctx.beginPath(); ctx.rect(x,y,w,h); ctx.clip(); drawGodzilla(x,y,w,h,night); ctx.restore(); }
  // chunky mullions: vertical panes + one horizontal transom (dark core + light edge)
  const panes=4, pw=w/panes;
  for(let i=1;i<panes;i++){ px(x+Math.round(i*pw)-1,y,3,h,PAL.woodDk); px(x+Math.round(i*pw)-1,y,1,h,PAL.wood); }
  px(x,y+Math.round(h*0.5)-1,w,3,PAL.woodDk); px(x,y+Math.round(h*0.5)-1,w,1,PAL.wood);
  px(x,y,w,1,'rgba(0,0,0,.22)'); px(x,y+h-1,w,1,'rgba(0,0,0,.22)');
  // glass sheen on the top-left pane
  px(x+2,y+2,Math.round(pw)-5,2, night?'rgba(255,255,255,.07)':'rgba(255,255,255,.20)');
}

// a hunched Godzilla silhouette lumbering across the window (drawn clipped to the glass).
// godzilla.t (0..1) drives it from off the left edge to off the right edge.
function drawGodzilla(wx,wy,ww,wh,night){
  const t=godzilla.t, now=performance.now();
  const gh=Math.round(wh*0.9);
  const footY=wy+wh-1;
  const span=ww+gh*2;
  const cx=Math.round(wx - gh + t*span);              // body-center x (enters left, exits right)
  const gait=Math.sin(now*0.008);                     // slow lumbering walk
  const bob=Math.round(Math.abs(Math.sin(now*0.008))*1.4);
  const body='#2c4a1c', dk='#1a2d11', belly='#4a7630', plate='#c9dc9a', plateDk='#82ae57', eye='#ffe14a';
  const bw=Math.round(gh*0.30);
  const hipY=footY-Math.round(gh*0.30)-bob;
  const chestY=footY-Math.round(gh*0.62)-bob;          // top of the torso / shoulders
  const headY=footY-gh+bob;                            // top of the head
  // a filled triangular back-plate. baseY is the ridge point; the plate is drawn STARTING 2px
  // below it (into the body) so it always looks rooted, never floating.
  const fin=(fx,baseY,h,w)=>{ for(let i=-2;i<h;i++){ const g=Math.max(0,i), wd=Math.max(1,Math.round(w*(1-g/h)));
    const rx=fx-((wd/2)|0)-((g*0.3)|0); px(rx, baseY-i, wd, 1, plate); px(rx, baseY-i, 1, 1, plateDk); } };

  // ---- tail spine: one array of points reused for BOTH the tail body and its plates ----
  const tail=[];
  for(let i=0;i<=14;i++){ const f=i/14;
    const tx=cx-bw+5-Math.round(f*40);
    const ty=hipY+3+Math.round(f*f*15)-Math.round(Math.sin(f*Math.PI)*3);   // slight arch, then droops
    const tw=Math.max(2, Math.round(12*(1-f*0.92)));
    tail.push([tx,ty,tw]); }
  for(const [tx,ty,tw] of tail) px(tx-((tw/2)|0)-1, ty-((tw/2)|0)-1, tw+2, tw+2, dk);   // dark outline
  for(const [tx,ty,tw] of tail) px(tx-((tw/2)|0),   ty-((tw/2)|0),   tw,   tw,   body);  // body

  // ---- far (back) leg first so it reads as depth ----
  const legH=footY-hipY+2, bl=cx-Math.round(bw*0.5)-Math.round(gait*3);
  ro(bl, hipY-2, 8, legH, dk); px(bl-2, footY-3, 12, 3, dk);          // back thigh + foot (shadowed)
  // ---- torso: bulky, leaning forward, with a pale belly ----
  ro(cx-bw, chestY, bw*2, hipY-chestY+10, dk);                        // dark underlay = crisp outline
  ro(cx-bw+1, chestY+1, bw*2-2, hipY-chestY+8, body);
  ro(cx+2, chestY+6, bw-2, hipY-chestY+2, belly);                     // belly on the forward (right) side
  // ---- near (front) leg with three claws ----
  const fl=cx+Math.round(bw*0.35)+Math.round(gait*3);
  ro(fl, hipY-2, 9, legH, body); px(fl-1, hipY-2, 2, legH, dk);       // thigh + shadow seam
  px(fl-2, footY-3, 13, 3, body);                                     // foot pad
  px(fl-2, footY, 3, 2, dk); px(fl+3, footY, 3, 2, dk); px(fl+8, footY, 3, 2, dk);   // toe claws
  // ---- stubby forelimb hanging off the chest ----
  px(cx+bw-3, chestY+9, 6, 3, body); px(cx+bw+1, chestY+11, 3, 4, body); px(cx+bw+1, chestY+15, 4, 1, dk);
  // ---- neck + head leaning forward-right ----
  ro(cx+bw-6, headY+6, 10, chestY-headY+3, dk);                       // neck outline
  ro(cx+bw-5, headY+6, 8, chestY-headY+2, body);
  ro(cx+bw-4, headY-1, 15, 11, dk);                                   // head outline
  ro(cx+bw-3, headY,   14, 9, body);
  px(cx+bw+9, headY+2, 8, 6, body); px(cx+bw+9, headY+2, 8, 1, dk);   // snout (with top edge)
  px(cx+bw+16, headY+5, 3, 3, body);                                  // snout tip
  px(cx+bw+7, headY+8, 9, 2, dk);                                     // mouth line / lower jaw
  px(cx+bw+2, headY+1, 3, 1, dk);                                     // brow ridge over the eye
  px(cx+bw+3, headY+2, 2, 2, eye);                                    // glowing eye

  // ---- dorsal plates, rooted on the ACTUAL silhouette so they can't detach ----
  // 1) plates riding the back: from the hip corner up over the shoulder to the neck base.
  const bn=6;
  for(let i=0;i<=bn;i++){ const f=i/bn;                               // 0 = hip, 1 = shoulder/neck
    const rx=Math.round((cx-bw+6) + f*(bw*2-12));
    const ry=Math.round(hipY - f*(hipY-chestY) - Math.sin(f*Math.PI)*3);   // rise to chest with a little arch
    const sz=Math.max(3, Math.round(5 + 6*Math.sin((0.35+f*0.6)*Math.PI)));
    fin(rx, ry+1, sz, Math.max(2,Math.round(sz*0.85))); }
  // 2) plates riding the tail: on each tail segment's top edge (skip the tip), shrinking outward.
  for(let i=1;i<tail.length-2;i+=2){ const [tx,ty,tw]=tail[i];
    fin(tx, ty-((tw/2)|0)+1, Math.max(2,Math.round(tw*0.7)), Math.max(2,Math.round(tw*0.6))); }
  // faint back-lit rim so the silhouette reads against a dark night sky
  if(night){ px(cx+bw-3, headY, 14, 1, 'rgba(160,210,140,.5)'); px(cx-bw+1, chestY+1, bw*2-2, 1, 'rgba(160,210,140,.32)'); }
}
function triggerGodzilla(){ godzilla.active=true; godzilla.t=0; }
// the office water cooler spits a fanned arc of droplets from its spout toward the room
function squirtCooler(){
  if(!coolerHit) return;
  const sx=coolerHit.sx, sy=coolerHit.sy;
  for(let i=0;i<34;i++){
    const ang=(138 + Math.random()*84) * Math.PI/180;   // 138..222deg -> leftward fan (up-left..down-left)
    const spd=58 + Math.random()*78;                     // varied speeds -> the jet spreads out
    waterFx.push({ x:sx, y:sy,
      vx: Math.cos(ang)*spd,
      vy: Math.sin(ang)*spd,                             // canvas y is down: sin<0 = arcs up first
      g: 320, r: 1 + Math.random()*1.8,
      life: 0.6 + Math.random()*0.6, age:0 });
  }
  if(waterFx.length>260) waterFx.splice(0, waterFx.length-260);
}

// real, positive quotes (motivation / happiness / health) with attribution.
// 150+ entries, majority by women, plus a lighter witty/programmer-humour batch --
// the board shows a new one every 10 minutes.
const QUOTES = [
  ["Try to be a rainbow in someone's cloud.","Maya Angelou"],
  ["If you don't like something, change it. If you can't change it, change your attitude.","Maya Angelou"],
  ["Nothing will work unless you do.","Maya Angelou"],
  ["We may encounter many defeats but we must not be defeated.","Maya Angelou"],
  ["People will forget what you said, but never how you made them feel.","Maya Angelou"],
  ["Success is liking yourself, liking what you do, and liking how you do it.","Maya Angelou"],
  ["No one can make you feel inferior without your consent.","Eleanor Roosevelt"],
  ["The future belongs to those who believe in the beauty of their dreams.","Eleanor Roosevelt"],
  ["Do one thing every day that scares you.","Eleanor Roosevelt"],
  ["You must do the things you think you cannot do.","Eleanor Roosevelt"],
  ["With the new day comes new strength and new thoughts.","Eleanor Roosevelt"],
  ["When they go low, we go high.","Michelle Obama"],
  ["Success is about the difference you make in people's lives.","Michelle Obama"],
  ["Failure is an important part of your growth.","Michelle Obama"],
  ["There is no limit to what we, as women, can accomplish.","Michelle Obama"],
  ["Turn your wounds into wisdom.","Oprah Winfrey"],
  ["The more you praise and celebrate your life, the more there is to celebrate.","Oprah Winfrey"],
  ["Surround yourself with people who are going to lift you higher.","Oprah Winfrey"],
  ["Be thankful for what you have and you'll end up having more.","Oprah Winfrey"],
  ["Life is either a daring adventure or nothing at all.","Helen Keller"],
  ["Optimism is the faith that leads to achievement.","Helen Keller"],
  ["Keep your face to the sunshine and you cannot see a shadow.","Helen Keller"],
  ["Alone we can do so little; together we can do so much.","Helen Keller"],
  ["Nothing in life is to be feared, it is only to be understood.","Marie Curie"],
  ["Be less curious about people and more curious about ideas.","Marie Curie"],
  ["I never see what has been done; I only see what remains to be done.","Marie Curie"],
  ["The most difficult thing is the decision to act; the rest is merely tenacity.","Amelia Earhart"],
  ["Adventure is worthwhile in itself.","Amelia Earhart"],
  ["Think of all the beauty still left around you and be happy.","Anne Frank"],
  ["Whoever is happy will make others happy too.","Anne Frank"],
  ["No one has ever become poor by giving.","Anne Frank"],
  ["Not all of us can do great things, but we can do small things with great love.","Mother Teresa"],
  ["Spread love everywhere you go.","Mother Teresa"],
  ["Peace begins with a smile.","Mother Teresa"],
  ["Kind words are short to speak but their echoes are truly endless.","Mother Teresa"],
  ["One child, one teacher, one book, one pen can change the world.","Malala Yousafzai"],
  ["When the whole world is silent, even one voice becomes powerful.","Malala Yousafzai"],
  ["We realize the importance of our voices only when we are silenced.","Malala Yousafzai"],
  ["It is our choices that show what we truly are, far more than our abilities.","J.K. Rowling"],
  ["Happiness can be found even in the darkest of times if one remembers to turn on the light.","J.K. Rowling"],
  ["We carry all the power we need to change the world inside ourselves already.","J.K. Rowling"],
  ["Talk to yourself like you would to someone you love.","Brené Brown"],
  ["Vulnerability is the birthplace of innovation, creativity and change.","Brené Brown"],
  ["Courage starts with showing up and letting ourselves be seen.","Brené Brown"],
  ["If there's a book you want to read that hasn't been written, you must write it.","Toni Morrison"],
  ["If you want to fly, give up everything that weighs you down.","Toni Morrison"],
  ["Caring for myself is not self-indulgence, it is self-preservation.","Audre Lorde"],
  ["No need to hurry. No need to sparkle. No need to be anybody but oneself.","Virginia Woolf"],
  ["One cannot think well, love well, sleep well, if one has not dined well.","Virginia Woolf"],
  ["I am not afraid of storms, for I am learning how to sail my ship.","Louisa May Alcott"],
  ["Have regular hours for work and play; make each day both useful and pleasant.","Louisa May Alcott"],
  ["Far away there in the sunshine are my highest aspirations.","Louisa May Alcott"],
  ["Nothing is impossible; the word itself says 'I'm possible'!","Audrey Hepburn"],
  ["The most important thing is to enjoy your life and to be happy.","Audrey Hepburn"],
  ["For beautiful eyes, look for the good in others.","Audrey Hepburn"],
  ["We have two hands, one to help ourselves, the other to help others.","Audrey Hepburn"],
  ["Beauty begins the moment you decide to be yourself.","Coco Chanel"],
  ["The most courageous act is still to think for yourself. Aloud.","Coco Chanel"],
  ["In order to be irreplaceable one must always be different.","Coco Chanel"],
  ["Keep smiling, because life is a beautiful thing and there's so much to smile about.","Marilyn Monroe"],
  ["Life shrinks or expands in proportion to one's courage.","Anaïs Nin"],
  ["We write to taste life twice, in the moment and in retrospect.","Anaïs Nin"],
  ["You must never be fearful about what you are doing when it is right.","Rosa Parks"],
  ["Real change, enduring change, happens one step at a time.","Ruth Bader Ginsburg"],
  ["Fight for the things you care about, but in a way that leads others to join you.","Ruth Bader Ginsburg"],
  ["What you do makes a difference, and you decide what kind of difference to make.","Jane Goodall"],
  ["Every individual matters. Every individual has a role to play.","Jane Goodall"],
  ["At the end of the day, we can endure much more than we think we can.","Frida Kahlo"],
  ["Feet, what do I need them for if I have wings to fly.","Frida Kahlo"],
  ["A champion is defined by how they recover when they fall.","Serena Williams"],
  ["If you want the rainbow, you gotta put up with the rain.","Dolly Parton"],
  ["Find out who you are and do it on purpose.","Dolly Parton"],
  ["Change your life today. Don't gamble on the future, act now.","Simone de Beauvoir"],
  ["Dwell in possibility.","Emily Dickinson"],
  ["Hope is the thing with feathers that perches in the soul.","Emily Dickinson"],
  ["Tell me, what is it you plan to do with your one wild and precious life?","Mary Oliver"],
  ["Instructions for living a life: pay attention, be astonished, tell about it.","Mary Oliver"],
  ["Dreaming, after all, is a form of planning.","Gloria Steinem"],
  ["Never doubt that a small group of thoughtful people can change the world.","Margaret Mead"],
  ["How very little can be done under the spirit of fear.","Florence Nightingale"],
  ["You cannot shake hands with a clenched fist.","Indira Gandhi"],
  ["It's the little things citizens do. That's what will make the difference.","Wangari Maathai"],
  ["If you obey all the rules, you miss all the fun.","Katharine Hepburn"],
  ["Done is better than perfect.","Sheryl Sandberg"],
  ["Failure is not the opposite of success; it's part of success.","Arianna Huffington"],
  ["Do what you were born to do. You just have to trust yourself.","Beyoncé"],
  ["Every great dream begins with a dreamer.","Harriet Tubman"],
  ["I never dreamed about success. I worked for it.","Estée Lauder"],
  ["Just don't give up trying to do what you really want to do.","Ella Fitzgerald"],
  ["Love yourself first and everything else falls into line.","Lucille Ball"],
  ["Above all, be the heroine of your life, not the victim.","Nora Ephron"],
  ["Trust yourself. Create the self you'll be happy to live with all your life.","Golda Meir"],
  ["There are years that ask questions and years that answer.","Zora Neale Hurston"],
  ["Confidence -- if you have it, you can make anything look good.","Diane von Furstenberg"],
  ["A woman with a voice is, by definition, a strong woman.","Melinda Gates"],
  ["The only way to do great work is to love what you do.","Steve Jobs"],
  ["Your time is limited, so don't waste it living someone else's life.","Steve Jobs"],
  ["Stay hungry, stay foolish.","Steve Jobs"],
  ["It always seems impossible until it's done.","Nelson Mandela"],
  ["The greatest glory in living lies in rising every time we fall.","Nelson Mandela"],
  ["May your choices reflect your hopes, not your fears.","Nelson Mandela"],
  ["The best way to find yourself is to lose yourself in the service of others.","Mahatma Gandhi"],
  ["Live as if you were to die tomorrow. Learn as if you were to live forever.","Mahatma Gandhi"],
  ["The future depends on what you do today.","Mahatma Gandhi"],
  ["In the middle of difficulty lies opportunity.","Albert Einstein"],
  ["Life is like riding a bicycle. To keep your balance you must keep moving.","Albert Einstein"],
  ["Strive not to be a success, but rather to be of value.","Albert Einstein"],
  ["It does not matter how slowly you go as long as you do not stop.","Confucius"],
  ["Wherever you go, go with all your heart.","Confucius"],
  ["Happiness depends upon ourselves.","Aristotle"],
  ["We are what we repeatedly do; excellence is a habit.","Aristotle"],
  ["What lies within us matters more than what lies behind or before us.","Ralph Waldo Emerson"],
  ["Write it on your heart that every day is the best day in the year.","Ralph Waldo Emerson"],
  ["Go confidently in the direction of your dreams.","Henry David Thoreau"],
  ["It's not what you look at that matters, it's what you see.","Henry David Thoreau"],
  ["The secret of getting ahead is getting started.","Mark Twain"],
  ["Kindness is a language the deaf can hear and the blind can see.","Mark Twain"],
  ["Well done is better than well said.","Benjamin Franklin"],
  ["An investment in knowledge pays the best interest.","Benjamin Franklin"],
  ["Energy and persistence conquer all things.","Benjamin Franklin"],
  ["Do what you can, with what you have, where you are.","Theodore Roosevelt"],
  ["Believe you can and you're halfway there.","Theodore Roosevelt"],
  ["Faith is taking the first step even when you don't see the whole staircase.","Martin Luther King Jr."],
  ["Darkness cannot drive out darkness; only light can do that.","Martin Luther King Jr."],
  ["The time is always right to do what is right.","Martin Luther King Jr."],
  ["Happiness comes from your own actions.","Dalai Lama"],
  ["A calm mind brings inner strength and self-confidence.","Dalai Lama"],
  ["Be kind whenever possible. It is always possible.","Dalai Lama"],
  ["The wound is the place where the light enters you.","Rumi"],
  ["What you seek is seeking you.","Rumi"],
  ["Let yourself be silently drawn by what you really love.","Rumi"],
  ["The journey of a thousand miles begins with a single step.","Lao Tzu"],
  ["Nature does not hurry, yet everything is accomplished.","Lao Tzu"],
  ["New beginnings are often disguised as painful endings.","Lao Tzu"],
  ["Luck is what happens when preparation meets opportunity.","Seneca"],
  ["The happiness of your life depends upon the quality of your thoughts.","Marcus Aurelius"],
  ["Very little is needed to make a happy life.","Marcus Aurelius"],
  ["There are far, far better things ahead than any we leave behind.","C.S. Lewis"],
  ["You are never too old to set a new goal or to dream a new dream.","C.S. Lewis"],
  ["The best way out is always through.","Robert Frost"],
  ["In three words I can sum up everything about life: it goes on.","Robert Frost"],
  ["Life is what happens when you're busy making other plans.","John Lennon"],
  ["The way to get started is to quit talking and begin doing.","Walt Disney"],
  ["If you can dream it, you can do it.","Walt Disney"],
  ["Take care of your body. It's the only place you have to live.","Jim Rohn"],
  ["Either you run the day or the day runs you.","Jim Rohn"],
  ["You don't have to be great to start, but you have to start to be great.","Zig Ziglar"],
  ["Whether you think you can, or you think you can't, you're right.","Henry Ford"],
  ["When we can no longer change a situation, we are challenged to change ourselves.","Viktor Frankl"],
  ["The mind is everything. What you think you become.","Buddha"],
  ["Health is the greatest gift, contentment the greatest wealth.","Buddha"],
  ["Act as if what you do makes a difference. It does.","William James"],
  ["Change your thoughts and you change your world.","Norman Vincent Peale"],
  ["How people treat you is their karma; how you react is yours.","Wayne Dyer"],
  ["What you do today can improve all your tomorrows.","Ralph Marston"],
  ["Little by little, one travels far.","J.R.R. Tolkien"],
  ["Not all those who wander are lost.","J.R.R. Tolkien"],
  ["The only place success comes before work is in the dictionary.","Vince Lombardi"],
  // --- a lighter batch: witty / surprising / programmer-humour (all real & attributed) ---
  ["Do not let what you cannot do interfere with what you can do.","John Wooden"],
  ["There is no education like adversity.","Benjamin Disraeli"],
  ["Happiness is a direction, not a place.","Sydney J. Harris"],
  ["Trust yourself. You know more than you think you do.","Benjamin Spock"],
  ["The greater the obstacle, the more glory in overcoming it.","Molière"],
  ["The best way to predict the future is to invent it.","Alan Kay"],
  ["To live is the rarest thing in the world. Most people exist, that is all.","Oscar Wilde"],
  ["Talk is cheap. Show me the code.","Linus Torvalds"],
  ["One of my most productive days was throwing away 1000 lines of code.","Ken Thompson"],
  ["There are only two hard things in Computer Science: cache invalidation and naming things.","Phil Karlton"],
  ["Debugging is twice as hard as writing the code in the first place.","Brian Kernighan"],
  ["There are two ways to write error-free programs; only the third one works.","Alan J. Perlis"],
  ["I love deadlines. I like the whooshing sound they make as they fly by.","Douglas Adams"],
  ["I intend to live forever. So far, so good.","Steven Wright"],
  ["An escalator can never break: it can only become stairs.","Mitch Hedberg"],
  ["If it wasn't for coffee, I'd have no identifiable personality at all.","David Letterman"],
  ["A mathematician is a device for turning coffee into theorems.","Paul Erdős"],
  ["I'd rather take coffee than compliments just now.","Louisa May Alcott"],
  ["Doing nothing is very hard to do; you never know when you're finished.","Leslie Nielsen"],
  ["I work for myself, which is fun. Except when I call in sick, I know I'm lying.","Rita Rudner"],
];
const QUOTE_PERIOD_MS = 600*1000;   // a fresh quote every 10 minutes
// greedy word-wrap to a pixel width for the given canvas font
function wrapText(text, maxW, font){
  ctx.font=font;
  const words=text.split(' '); const lines=[]; let cur='';
  for(const w of words){ const test=cur?cur+' '+w:w;
    if(ctx.measureText(test).width>maxW && cur){ lines.push(cur); cur=w; } else cur=test; }
  if(cur) lines.push(cur);
  return lines;
}

// evenly space the clock (24w), bookshelf (50w) and DO GOOD WORK poster (54w) across the wall
// to the RIGHT of the inspiration board -> equal gaps between the three, robust to canvas W.
// Shared by drawWallDecor (clock + shelf) and drawOfficeProps (poster) so they stay in sync.
function wallRowLayout(){
  const boardX = 20 + Math.round(W*0.36) + 16, boardW = 210;
  const clkW = 24, shfW = 50, posW = 54;
  const boardRight = boardX + boardW;
  const gap = ((W-9 - (boardRight+12)) - (clkW+shfW+posW)) / 2;   // 2 equal gaps between 3 items
  const clkL = boardRight + 12;
  const shfL = clkL + clkW + gap;
  const posL = shfL + shfW + gap;
  return { boardX, clkL, shfL, posL };
}

function drawWallDecor(x, y, clkL, shfL){
  // ---- inspiration board: a quote that changes every 10 minutes (whole board) ----
  const bw=210, bh=58; px(x-3,y-3,bw+6,bh+6,PAL.metalDk); px(x,y,bw,bh,PAL.paper);
  px(x,y,bw,2,'#eef0f3'); px(x,y+bh-2,bw,2,'#cfcfd6'); px(x+bw-2,y,2,bh,'#dadbe0');
  ctx.textAlign='left';
  const q = QUOTES[Math.floor(Date.now()/QUOTE_PERIOD_MS) % QUOTES.length];
  // heading + a tiny heart in the corner
  ctx.fillStyle=PAL.leafDk; ctx.font='6px "Press Start 2P", monospace'; ctx.fillText('INSPIRATION', x+8, y+12);
  const hh=x+bw-13; px(hh,y+5,3,2,PAL.pink); px(hh+4,y+5,3,2,PAL.pink); px(hh,y+7,7,2,PAL.pink); px(hh+1,y+9,5,1,PAL.pink); px(hh+2,y+10,3,1,PAL.pink);
  px(x+8,y+16,bw-16,1,'#dfe6da');
  // quote across the full board width
  ctx.fillStyle=PAL.ink; const qfont='5px "Press Start 2P", monospace';
  const lines=wrapText('“'+q[0]+'”', bw-18, qfont).slice(0,4);
  let qy=y+25; for(const ln of lines){ ctx.fillText(ln, x+8, qy); qy+=7; }
  ctx.fillStyle=PAL.leafDk; ctx.fillText('- '+q[1], x+8, qy+2);
  // ---- wall clock (live local time) -- x-pos comes from wallRowLayout() (even spacing) ----
  const clx=clkL+3, cly=y+6; px(clx-3,cly-3,24,24,PAL.woodDk); px(clx-1,cly-1,20,20,PAL.metalDk); px(clx,cly,18,18,PAL.paper);
  clockHit = { x0:clx-4, y0:cly-4, x1:clx+22, y1:cly+22 };                 // click the clock -> summon Godzilla (test hook)
  for(let a=0;a<12;a++){ const ang=a*Math.PI/6; px(clx+9+Math.round(7*Math.sin(ang)), cly+9-Math.round(7*Math.cos(ang)), 1,1, PAL.ink); }
  const ccx=clx+9, ccy=cly+9, now=new Date();
  const hA=((now.getHours()%12)+now.getMinutes()/60)*Math.PI/6;    // 30 deg/hr + drift
  const mA=(now.getMinutes()+now.getSeconds()/60)*Math.PI/30;      // 6 deg/min
  const sA=now.getSeconds()*Math.PI/30;                            // 6 deg/sec
  ctx.lineCap='round';
  ctx.strokeStyle=PAL.ink; ctx.lineWidth=1.5; ctx.beginPath();     // hour hand (short, thick)
  ctx.moveTo(ccx,ccy); ctx.lineTo(ccx+4.5*Math.sin(hA), ccy-4.5*Math.cos(hA)); ctx.stroke();
  ctx.lineWidth=1.1; ctx.beginPath();                              // minute hand (long)
  ctx.moveTo(ccx,ccy); ctx.lineTo(ccx+7*Math.sin(mA), ccy-7*Math.cos(mA)); ctx.stroke();
  ctx.strokeStyle=PAL.red; ctx.lineWidth=0.7; ctx.beginPath();     // thin red second hand
  ctx.moveTo(ccx,ccy); ctx.lineTo(ccx+7.5*Math.sin(sA), ccy-7.5*Math.cos(sA)); ctx.stroke();
  ctx.lineCap='butt';
  px(clx+8,cly+8,2,2,PAL.red);                                  // center hub
  // ---- bookshelf with books + a little plant on top (x-pos from wallRowLayout) ----
  const shx=shfL+2, shy=y+12; px(shx-2,shy-2,50,56,PAL.woodDk); px(shx,shy,46,52,PAL.wood); px(shx,shy,46,2,PAL.woodHi);
  const cols=[PAL.mugA,PAL.mugB,PAL.mugC,PAL.leafDk,PAL.red,PAL.yellow,PAL.orange,'#8c5fd6'];
  for(let r=0;r<3;r++){ const ry=shy+5+r*16;
    for(let b=0;b<5;b++){ const bbh=11-((b+r)%2)*2; px(shx+4+b*8,ry+(11-bbh),6,bbh,cols[(b+r*3)%cols.length]); }
    px(shx+2,ry+13,42,2,PAL.woodDk);
  }
  smallPlant(shx+30, shy-2);
}

function drawOfficeProps(){
  const L=layout(), top=WALL_H;
  // plants flanking the window
  bigPlant(14, top+10); bigPlant(W-30, top+10);
  // "DO GOOD WORK" poster on the office back wall -- evenly spaced with the clock + bookshelf
  drawDoGoodWork(wallRowLayout().posL+3, 6);

  const lastDeskY = deskSlots.length ? Math.max.apply(null, deskSlots.map(s=>s.y)) : top+120;
  // soft rug spanning the desk area
  ctx.fillStyle='rgba(214,140,92,.13)'; ctx.fillRect(70, top+30, W-140, (lastDeskY+34)-(top+30));
  ctx.strokeStyle='rgba(160,96,52,.18)'; ctx.lineWidth=2; ctx.strokeRect(72, top+32, W-144, (lastDeskY+30)-(top+32));

  // ---- water cooler (far right) + floor plant (left) ----
  const wcx=W-56, wcy=lastDeskY+48; ro(wcx,wcy,18,30,PAL.steel); px(wcx+2,wcy-15,14,15,'#9fd9f0'); px(wcx+5,wcy+14,8,5,PAL.cabinet);
  coolerHit = { x0:wcx-3, y0:wcy-16, x1:wcx+19, y1:wcy+31, sx:wcx+5, sy:wcy+18 };   // click rect + spout origin
  bigPlant(34, lastDeskY+44);
}

function drawKitchenProps(){
  const L=layout(), k=L.kitchen, T=L.kitchenTop;
  // back wall band for mounting decor + counters
  px(0,T,W,30,PAL.wall); px(0,T+28,W,2,PAL.base);
  // tiled kitchen backsplash (subtle offset subway tiles) behind the counter/shelf
  for(let ty2=T+2; ty2<T+27; ty2+=6){
    const off=(((ty2-T)/6|0)%2)?5:0;
    for(let tx2=2-off; tx2<BEACH_X-2; tx2+=10){ px(tx2,ty2,9,5, ((tx2+ty2)&1)?'#e5ddc7':'#ede5d0'); }
  }
  drawBeachFloor();   // sand + water fill the right band (under the back-wall props)

  // ---- tall fridge (far left): freezer/fridge split, handles, magnets, photo ----
  const fx=8, fy=T+14, fw=30, fh=74; ro(fx,fy,fw,fh,PAL.fridge);
  px(fx,fy,fw,3,PAL.fridgeDk); px(fx+1,fy+1,fw-2,1,shade(PAL.fridge,.30));   // top + sheen
  px(fx,fy+30,fw,3,PAL.fridgeDk);                                            // freezer/fridge door split
  px(fx+fw-6,fy+7,3,17,PAL.metalDk); px(fx+fw-6,fy+38,3,28,PAL.metalDk);     // two vertical handles
  // magnets + a photo + a sticky note
  px(fx+5,fy+40,5,4,PAL.red); px(fx+12,fy+41,4,4,PAL.yellow); px(fx+18,fy+39,4,4,PAL.mugB);
  px(fx+5,fy+48,7,7,PAL.paper); px(fx+5,fy+48,7,1,'#e6e6ec'); px(fx+6,fy+50,5,3,'#9fd9f0'); // photo
  px(fx+15,fy+49,9,6,'#fff3b0'); px(fx+15,fy+49,9,1,shade('#fff3b0',-.2));                  // sticky note
  smallPlant(fx+9, fy-9);                                                    // little plant on top

  // ---- kitchen counter (center-back): solid countertop, cabinetry, inset sink,
  // espresso bar + a wall shelf with jars/mugs ----
  const cbx=150, cbw=224, cby=T+30, cbh=26, ctTop=cby-9;   // counter kept left of BEACH_X
  // solid countertop slab: bright tan surface, highlighted back edge + rounded
  // shaded front lip so it reads as a real worktop with depth.
  px(cbx-4,ctTop,cbw+8,9,PAL.cabinetTop);
  px(cbx-4,ctTop,cbw+8,1,shade(PAL.cabinetTop,.34));                        // back-edge highlight
  px(cbx-4,ctTop+1,cbw+8,1,shade(PAL.cabinetTop,.14));
  px(cbx-4,cby-3,cbw+8,3,shade(PAL.cabinetTop,-.16));                       // front lip
  px(cbx-4,cby-1,cbw+8,1,shade(PAL.cabinetTop,-.34));                       // lip undershadow
  // cabinetry: dark carcass + bevelled door/drawer fronts with steel pulls + toe-kick
  ro(cbx,cby,cbw,cbh,PAL.cabinet);
  const doors=6, dww=cbw/doors;
  for(let i=0;i<doors;i++){ const dx=cbx+3+i*dww;
    px(dx,cby+3,dww-6,cbh-8, shade(PAL.cabinet,.10));                       // raised front panel
    px(dx,cby+3,dww-6,1, shade(PAL.cabinet,.26));                          // top bevel (light)
    px(dx,cby+3,1,cbh-8, shade(PAL.cabinet,.18));                          // left bevel
    px(dx+dww-7,cby+3,1,cbh-8, shade(PAL.cabinet,-.26));                   // right bevel (dark)
    px(dx,cby+cbh-6,dww-6,1, shade(PAL.cabinet,-.30));                     // bottom bevel
    if(i%2===0){ px(dx+(dww-6)/2-1,cby+7,2,9,PAL.steel); px(dx+(dww-6)/2-1,cby+7,1,9,shade(PAL.steel,.3)); } // door pull (vertical)
    else { px(dx+4,cby+6,dww-14,2,PAL.steel); px(dx+4,cby+6,dww-14,1,shade(PAL.steel,.3)); }                 // drawer pull (horizontal)
  }
  px(cbx,cby+cbh-2,cbw,2, shade(PAL.cabinet,-.42)); px(cbx,cby+cbh,cbw,1,'rgba(0,0,0,.22)'); // toe-kick shadow
  // ---- espresso machine on the counter (left): body, bean hopper, display,
  // buttons, steam wand, a group head + portafilter and a cup catching the shot ----
  const cmw=34, cmh=23, cmx=cbx+8, cmy=ctTop-cmh;
  ro(cmx,cmy,cmw,cmh,'#3b3b46');                                            // body
  px(cmx+1,cmy+1,cmw-2,2,'#585863');                                        // top sheen
  px(cmx,cmy+cmh-4,cmw,4,'#2a2a32');                                        // darker base
  px(cmx+cmw-10,cmy-4,7,5,'#2a2a32'); px(cmx+cmw-9,cmy-3,5,2,'#4a4a55');    // bean hopper on top
  px(cmx+3,cmy+3,13,6,PAL.screen); px(cmx+3,cmy+3,13,1,'#c3f0f7');          // display
  px(cmx+4,cmy+12,3,3,PAL.red); px(cmx+9,cmy+12,3,3,PAL.yellow); px(cmx+14,cmy+12,3,3,PAL.leaf); // buttons
  px(cmx+cmw-4,cmy+6,2,9,PAL.metalDk); px(cmx+cmw-5,cmy+14,3,2,PAL.metalDk); // steam wand
  px(cmx+9,cmy+cmh-5,10,3,'#23232a');                                       // group head
  px(cmx+12,cmy+cmh-2,4,2,PAL.metalDk);                                     // portafilter neck
  mug(cmx+10,ctTop-7,'#ececf2');                                           // cup catching the shot
  // ---- wall shelf (center): plank holding two glass jars, a canister + two mugs ----
  const shx=cbx+54, shw=92, shy=T+1;
  px(shx-3,shy+16,shw+6,3,PAL.woodDk); px(shx-3,shy+15,shw+6,1,PAL.woodHi); // plank + edge
  px(shx-3,shy+19,shw+6,1,'rgba(0,0,0,.20)');                              // under-shelf shadow
  px(shx+4,shy+5,9,11,'rgba(212,226,233,.85)'); px(shx+4,shy+12,9,4,'#6b4a2e'); // clear jar w/ beans
  px(shx+4,shy+5,9,2,'#e3edf1'); px(shx+3,shy+3,11,2,PAL.metalDk);          // jar sheen + lid
  px(shx+18,shy+6,9,10,'rgba(183,217,192,.92)'); px(shx+18,shy+6,9,2,shade('#b7d9c0',.3)); px(shx+17,shy+4,11,2,PAL.leafDk); // green jar + lid
  px(shx+33,shy+4,9,12,PAL.mugC); px(shx+33,shy+4,9,2,shade(PAL.mugC,.34)); px(shx+33,shy+9,9,1,shade(PAL.mugC,-.18)); // canister
  mug(shx+48,shy+7,PAL.mugA); mug(shx+62,shy+7,PAL.mugB);
  smallPlant(shx+80, shy-1);                                                // a little trailing plant on the shelf end
  // ---- hanging planter in the gap between the coffee sign and the shelf ----
  const hgx=166;
  px(hgx,T,1,6,'#8a7a5a'); px(hgx+8,T,1,6,'#8a7a5a');                       // two cords
  px(hgx-3,T+6,15,5,PAL.pot); px(hgx-3,T+6,15,2,shade(PAL.pot,.18)); px(hgx-4,T+10,17,1,PAL.potDk); // pot
  blade(hgx-1,T+11,7,-3,PAL.leafDk); blade(hgx+4,T+11,9,0,PAL.leaf); blade(hgx+9,T+11,6,3,PAL.leafDk); // trailing leaves
  // ---- SINK (center-right): a stainless drop-in basin recessed into the counter
  // (steel rim, two-tone recessed interior, centre drain) with a proper goose-neck
  // faucet rising behind it (riser + arched spout + downspout + lever) -- clearly a sink ----
  const skx=cbx+150, skw=60, skBot=ctTop, skTop=skBot-14;
  ro(skx,skTop,skw,14,PAL.steel);                                           // stainless basin shell
  px(skx,skTop,skw,2,shade(PAL.steel,.34));                                 // rim top highlight
  px(skx,skTop+12,skw,2,shade(PAL.steel,-.26));                             // front rim shadow
  px(skx+4,skTop+3,skw-8,9,'#5a6e7d');                                      // recessed basin (upper)
  px(skx+6,skTop+5,skw-12,6,'#46586a');                                     // recessed basin (deeper)
  px(skx+6,skTop+10,skw-12,1,'#374755');                                    // basin floor
  px(skx+skw/2-2,skTop+8,4,2,'#2b3640');                                    // drain
  px(skx+6,skTop+4,skw-13,1,'rgba(255,255,255,.22)');                       // water sheen
  const fcx=skx+skw-18, fTop=T;                                             // faucet column (right-back)
  px(fcx-3,skTop-2,10,3,PAL.metalDk);                                       // escutcheon base plate
  px(fcx,fTop+2,4,skTop-fTop,PAL.steel); px(fcx,fTop+2,1,skTop-fTop,shade(PAL.steel,.34)); // vertical riser
  px(fcx-2,fTop,6,3,PAL.steel); px(fcx-7,fTop,6,3,PAL.steel); px(fcx-11,fTop+1,5,3,PAL.steel); // gooseneck arch (curving left)
  px(fcx-2,fTop,8,1,shade(PAL.steel,.3));                                   // arch highlight
  px(fcx-11,fTop+3,3,5,PAL.steel); px(fcx-11,fTop+7,3,2,PAL.metalDk);       // downspout + tip over the basin
  px(fcx+4,skTop-4,5,2,PAL.metalDk); px(fcx+4,skTop-4,5,1,shade(PAL.metalDk,.3)); // lever handle

  // ---- "COFFEE > CODE > CONQUER" wall sign (left) ----
  const sgx=58, sgy=T+3; px(sgx-2,sgy-2,90,24,PAL.woodDk); px(sgx,sgy,86,20,PAL.paper);
  ctx.fillStyle=PAL.ink; ctx.font='5px "Press Start 2P", monospace';
  ctx.fillText('COFFEE >', sgx+6, sgy+9); ctx.fillText('CODE > CONQUER', sgx+6, sgy+17);

  // (the "DO GOOD WORK" poster now hangs in the office; a "RETIRED AGENTS" beach
  //  sign takes its place -- both drawn elsewhere)

  // ---- "REFRESH!" drinks machine: a beach drinks kiosk in the top-right SAND corner.
  // Positioned so its whole width sits LEFT of SHORE_X (out of the ocean band); every
  // sub-part + the click slots + the falling-can animation derive from vx/vy/vw/vh, so
  // moving the origin moves the entire (still-interactive) machine together. ----
  const vw=64, vh=88, vx=SHORE_X-vw-2, vy=T+10;
  ro(vx,vy,vw,vh,'#2f57a8'); px(vx,vy,vw,3,shade('#2f57a8',.28)); px(vx,vy,3,vh,shade('#2f57a8',.18)); // cabinet + sheen
  px(vx+vw-3,vy,3,vh,shade('#2f57a8',-.22));                                                          // right shade
  // lit header sign
  px(vx+4,vy+4,vw-8,13,'#0e1c44'); px(vx+4,vy+4,vw-8,1,'#3a5aa0');
  ctx.fillStyle='#ffd34d'; ctx.font='6px "Press Start 2P", monospace'; ctx.fillText('REFRESH!', vx+5, vy+14);
  // glass display: 3 rows x 4 colorful bottles on lit shelves
  const gx=vx+4, gy=vy+19, gw=42, gh=54; ro(gx,gy,gw,gh,'#0e1530');
  const drinks=[PAL.red,PAL.mugB,PAL.yellow,PAL.leaf,PAL.orange,PAL.pink,PAL.mugC,'#8c5fd6','#22b9b9','#e673a8','#5bc05b','#3f74d6'];
  for(let r=0;r<3;r++){ const ry=gy+4+r*17;
    px(gx+1,ry+14,gw-2,2,'#243a6a');                                                                  // shelf
    for(let c=0;c<4;c++){ const idx=r*4+c, bxv=gx+3+c*10, col=drinks[idx];
      vendSlots.push({idx, bxv, ry, x0:bxv-1, y0:ry-1, x1:bxv+7, y1:ry+15, col});                     // click target
      if(vendDrops[idx]) continue;                                                                    // slot empty while its can is out
      px(bxv,ry+2,6,12,col); px(bxv,ry+2,6,2,shade(col,.32)); px(bxv+1,ry,3,3,col); } }               // bottle + cap
  px(gx+3,gy+2,2,gh-6,'rgba(255,255,255,.12)'); px(gx+8,gy+2,1,gh-6,'rgba(255,255,255,.06)');         // glass reflection
  // side panel: keypad + card reader + coin slot
  const spx=vx+48, spw=vw-(spx-vx)-4; px(spx,vy+19,spw,54,'#24407e'); px(spx,vy+19,spw,1,shade('#24407e',.3));
  for(let r=0;r<3;r++) for(let c=0;c<2;c++) px(spx+2+c*5,vy+23+r*5,3,3,'#cdd6dd');                     // keypad
  px(spx+1,vy+42,spw-2,11,'#0e1a36'); px(spx+2,vy+44,spw-4,2,'#cdd6dd');                               // card reader
  px(spx+2,vy+55,spw-4,3,'#0a1024');                                                                  // coin slot
  // dispense slot / tray at the bottom
  px(vx+5,vy+vh-13,vw-10,9,'#0e1c44'); px(vx+7,vy+vh-11,vw-14,5,'#0a1024');
  // clicked drinks fall from their slot into the tray, rest a few seconds, then restock (see tick())
  const _vnow=performance.now(), trayCX=vx+vw/2-3, trayTopY=vy+vh-22;   // rest: centered, poking out of the tray
  for(const k in vendDrops){ const dp=vendDrops[k], el=_vnow-dp.start;
    const pf=Math.min(1, el/620), ease=pf*pf;                            // accelerate downward (gravity)
    const cx0=dp.fromX+(trayCX-dp.fromX)*pf;                             // slide toward tray x
    let   cy0=dp.fromY+(trayTopY-dp.fromY)*ease;                         // fall with easing
    if(pf>=1){ const bt=Math.max(0,1-(el-620)/240); cy0-=Math.abs(Math.sin((el-620)*0.03))*4*bt; }    // small settle bounce
    px(cx0,cy0+2,6,12,dp.col); px(cx0,cy0+2,6,2,shade(dp.col,.32)); px(cx0+1,cy0,3,3,dp.col); }        // the dispensed can

  // ---- lounge: BIG wood table w/ fruit bowl + two white mugs, flanked by round
  // pink poufs (bottom-left). Sized to fill the corner; agents kept clear. ----
  const tx=66, ty=T+150, tw=116, tth=20;
  // round cushioned poufs -- a clear 3D cylinder: floor shadow, a darker rounded
  // side (lower ellipse + side band), a lighter domed cushion top, stitched seams
  // radiating from a centre button + a soft sheen.
  function pouf(cx0,cy0){
    const top='#d98fbe', side='#b06a96', sideDk='#8c4d79', sheen='#ecb6d6';
    const rx=18;
    ctx.fillStyle='rgba(0,0,0,.20)'; ctx.beginPath(); ctx.ellipse(cx0,cy0+14,rx+2,5,0,0,Math.PI*2); ctx.fill(); // floor shadow
    ctx.fillStyle=sideDk; ctx.beginPath(); ctx.ellipse(cx0,cy0+9,rx,7,0,0,Math.PI*2); ctx.fill();    // rounded base
    ctx.fillStyle=side;   ctx.fillRect(cx0-rx,cy0-2,rx*2,11);                                          // cylindrical side
    ctx.fillStyle=sideDk; ctx.fillRect(cx0-rx,cy0+6,rx*2,3);                                           // lower side shade
    ctx.fillStyle=top;    ctx.beginPath(); ctx.ellipse(cx0,cy0-2,rx,9,0,0,Math.PI*2); ctx.fill();      // domed cushion top
    ctx.fillStyle=sheen;  ctx.beginPath(); ctx.ellipse(cx0-6,cy0-4,8,4,0,0,Math.PI*2); ctx.fill();     // sheen
    ctx.strokeStyle=side; ctx.lineWidth=1;                                                             // seam dimples
    [[-12,3],[-5,5],[5,5],[12,3]].forEach(d=>{ ctx.beginPath(); ctx.moveTo(cx0,cy0-3); ctx.lineTo(cx0+d[0],cy0+d[1]); ctx.stroke(); });
    ctx.fillStyle=sideDk; ctx.beginPath(); ctx.ellipse(cx0,cy0-3,2,1.5,0,0,Math.PI*2); ctx.fill();     // centre button
  }
  pouf(tx-28, ty+10); pouf(tx+tw+28, ty+10);
  // table: floor shadow + front/back legs (with foot shadows) + grained top w/ shaded edges
  ctx.fillStyle='rgba(0,0,0,.16)'; ctx.beginPath(); ctx.ellipse(tx+tw/2,ty+38,tw/2,8,0,0,Math.PI*2); ctx.fill();
  px(tx+22,ty+tth,4,18,PAL.woodDk); px(tx+tw-26,ty+tth,4,18,PAL.woodDk);            // back legs (inset)
  px(tx+10,ty+tth,5,22,PAL.wood); px(tx+10,ty+tth,2,22,PAL.woodHi);                 // front-left leg
  px(tx+tw-15,ty+tth,5,22,PAL.wood); px(tx+tw-15,ty+tth,2,22,PAL.woodHi);           // front-right leg
  px(tx+9,ty+tth+21,7,2,'rgba(0,0,0,.22)'); px(tx+tw-16,ty+tth+21,7,2,'rgba(0,0,0,.22)'); // foot shadows
  ro(tx,ty,tw,tth,PAL.wood); px(tx,ty,tw,4,PAL.woodHi); px(tx,ty+tth-3,tw,3,PAL.woodDk); // top + edges
  px(tx,ty+4,tw,1,shade(PAL.wood,.14));                                            // surface highlight band
  for(let g=0;g<tw-12;g+=13) px(tx+7+g,ty+9,9,1,shade(PAL.wood,-.09));              // grain hints
  // two white coffee mugs (left + right of the bowl)
  mug(tx+14,ty-5,PAL.paper); mug(tx+tw-21,ty-5,PAL.paper);
  // ---- central fruit bowl: ceramic bowl holding apples, a banana + leaves ----
  const bwx=tx+tw/2, bwy=ty-1, brw=22;
  // bowl body (exterior lower half) + shaded underside
  ctx.fillStyle='#ddd4bd'; ctx.beginPath(); ctx.ellipse(bwx,bwy,brw,10,0,0,Math.PI); ctx.fill();
  ctx.fillStyle=shade('#ddd4bd',-.22); ctx.beginPath(); ctx.ellipse(bwx,bwy+3,brw-3,6,0,0,Math.PI); ctx.fill();
  // rim ring at the opening with a shadowed interior
  ctx.fillStyle='#efe8d6'; ctx.beginPath(); ctx.ellipse(bwx,bwy-1,brw,5,0,0,Math.PI*2); ctx.fill();
  ctx.fillStyle='#3a342e'; ctx.beginPath(); ctx.ellipse(bwx,bwy-1,brw-4,3,0,0,Math.PI*2); ctx.fill();
  // fruit piled in the bowl (sitting above the rim line)
  blade(bwx-3,bwy-4,11,-3,PAL.leafDk); blade(bwx+2,bwy-5,12,2,PAL.leaf); blade(bwx+6,bwy-3,9,4,PAL.leafDk); // leaves
  px(bwx-2,bwy-12,14,4,PAL.yellow); px(bwx-3,bwy-11,2,3,PAL.yellow); px(bwx+12,bwy-11,2,3,shade(PAL.yellow,-.2)); px(bwx-3,bwy-12,3,1,shade(PAL.yellow,.3)); // banana
  function apple(ax,ay){ px(ax+1,ay,6,2,PAL.red); px(ax,ay+2,8,4,PAL.red); px(ax+1,ay+6,6,1,shade(PAL.red,-.25)); px(ax+1,ay+1,2,2,shade(PAL.red,.45)); px(ax+3,ay-1,1,2,PAL.leafDk); }
  apple(bwx-15,bwy-7); apple(bwx-3,bwy-6); apple(bwx+7,bwy-7);
  // thin front lip over the fruit bottoms so they nest inside the bowl
  ctx.fillStyle='#e7dfc9'; ctx.beginPath(); ctx.ellipse(bwx,bwy+1,brw,3,0,0,Math.PI); ctx.fill();
  px(bwx-brw,bwy-2,brw*2,1,'#f3eede');                                              // rim top highlight

  // ---- the beach: towels, umbrella, beach ball + the office mascot napping on sand ----
  drawBeachProps();
}

// a striped beach towel laid on the sand (finished agents rest on these)
function towel(x,y,col){
  px(x-1,y-1,32,16,PAL.outline);
  px(x,y,30,14,col);
  px(x,y,30,3,shade(col,.30));                             // top highlight
  px(x,y+11,30,3,shade(col,-.16));                         // shadow band
  for(let i=3;i<30;i+=8) px(x+i,y,3,14,shade(col,-.10));   // stripes
}
// a classic red/white beach umbrella; canopy floats above the resting agents
function beachUmbrella(x,y){
  const cx=x+24, r1='#e0533b', r2='#f6f6f8';
  px(cx-1,y+8,3,66,'#7a5a30'); px(cx-1,y+8,1,66,'#9a7440');            // pole
  const bands=[[54,20],[46,16],[36,12],[24,8],[12,4]];                 // widen toward the bottom
  for(const b of bands){ const w=b[0], yo=b[1];
    for(let i=0;i<w;i+=8) px(cx-w/2+i, y+yo, Math.min(8,w-i), 4, ((i>>3)%2)?r2:r1); }
  px(cx-27,y+22,54,1,PAL.outline);                                     // canopy rim
  px(cx-2,y+2,4,4,'#ffd34d');                                          // finial
}
let _sandGrains=null;                                                   // grain built once -> no per-frame flicker & no per-frame hashing
function drawBeachFloor(){
  const T=layout().kitchenTop, x0=BEACH_X, y0=T+30, y1=H;
  const shoreX=SHORE_X, base='#e7d3a0', sandW=shoreX-x0, hgt=y1-y0;
  // (the old ruler-straight divider line is gone -- an organic sand fringe is drawn below)
  // --- dry sand: warm base + soft vertical gradient (paler/drier up near the wall) ---
  px(x0,y0,sandW,hgt,base);
  px(x0,y0,sandW,Math.round(hgt*0.30),shade(base,.05));               // dry top strip
  const _by=y0+Math.round(hgt*0.74); px(x0,_by,sandW,y1-_by,shade(base,-.05)); // warmer front
  // --- fine grain: deterministic stipple, computed once from hash() (stable, no flicker) ---
  if(!_sandGrains){
    _sandGrains=[];
    for(let y=y0;y<y1;y+=4) for(let x=x0;x<shoreX-2;x+=4){
      const h=hash(x+'_'+y), r=h%11;
      if(r===0)      _sandGrains.push([x,y,1,1,'rgba(120,96,52,.22)']);         // dark grain
      else if(r===1) _sandGrains.push([x,y,1,1,'rgba(255,247,216,.30)']);       // light fleck
      else if(r===2 && (h>>>4)%5===0) _sandGrains.push([x,y,2,1,'rgba(150,122,64,.16)']); // pebble
    }
  }
  for(const g of _sandGrains) px(g[0],g[1],g[2],g[3],g[4]);

  // --- organic sand/floor boundary: instead of a ruler-straight divider, the sand spills
  //     LEFT of BEACH_X in a soft wavy fringe, with loose grains tracked onto the tiles ---
  const sandTop=shade(base,.05), sandFront=shade(base,-.05), tipCol=shade(base,-.14);  // shade() takes #hex, returns rgb() -> never nest it
  for(let y=y0; y<y1; y+=2){
    // smooth deterministic wobble (two slow sine waves + a little hashed jitter) -> 0..~16px
    const w = 8 + 5*Math.sin(y*0.10) + 3*Math.sin(y*0.31+1.7) + (hash('f'+y)%3);
    const b = Math.max(0, Math.round(w));
    const rowCol = (y < y0+Math.round(hgt*0.30)) ? sandTop : (y>=_by ? sandFront : base);
    if(b>0){
      px(x0-b, y, b, 2, rowCol);                    // sand tongue over the kitchen tiles
      px(x0-b, y, 1, 2, tipCol);                    // damp tip -> soft, defined edge
    }
    // a few loose grains scattered a bit further onto the floor, thinning to the left
    if((hash('g'+y)%2)===0){
      const gx = x0 - b - 2 - (hash('x'+y)%13);
      px(gx, y, 1, 1, 'rgba(150,122,64,.30)');
    }
  }

  // ===================== OCEAN (right-hand band) =====================
  // A calming, gently animated sea. All motion is tiny and slow and is driven off the
  // shared rAF clock `tCount` (advanced in tick() as `tCount += dt*0.06`, ~60 units/s)
  // so it can never drift or fight the sand-grain cache -- no setInterval, no re-hashing.
  const tide  = Math.sin(tCount/74);                    // ~7.7s period, [-1,1] breath
  const surge = Math.round(tide*2);                     // waterline advances/recedes +-2px
  const wtrX  = shoreX + surge, wtrW = W - wtrX;         // dynamic sea edge
  // depth: darker deep water out to sea, lighter shallows near the shore
  px(wtrX, y0, wtrW, hgt, '#2f9fbf');                                     // mid water
  px(W-Math.round(wtrW*0.42), y0, Math.round(wtrW*0.42), hgt, '#1f82a6'); // deep far edge
  px(wtrX, y0, Math.max(8,Math.round(wtrW*0.36)), hgt, '#5cc4da');        // shallows near shore
  // slow shimmer: a soft light band drifting seaward-and-back across the water (~10s)
  const sweep = wtrX + 2 + Math.round(((Math.sin(tCount/96)+1)/2)*(wtrW-6));
  px(sweep, y0, 2, hgt, 'rgba(255,255,255,.15)'); px(sweep+2, y0, 1, hgt, 'rgba(255,255,255,.07)');
  // slow-drifting ripple highlights (staggered dashes that gently slide with the tide)
  const rd = Math.round(tide*3), span=Math.max(6,wtrW-12);
  for(let y=y0+8; y<y1; y+=15){
    const rx = wtrX + 4 + (((y*7)>>>0) % span) + rd;
    px(rx, y, 5, 1, 'rgba(255,255,255,.28)');
  }
  // --- wavy shoreline: the sea meets the sand in a gentle organic curve, not a straight line.
  //     lap(y) = how far the shallows reach LEFT of wtrX this row (a static wavy shape; the whole
  //     line still breathes in/out via `surge`). Kept modest so agents' rest spots stay dry. ---
  const lap = (y)=> Math.max(0, Math.round(4 + 4*Math.sin(y*0.085) + 2.4*Math.sin(y*0.23+1.1) + (hash('s'+y)%2)));
  for(let y=y0; y<y1; y+=2){ const l=lap(y); if(l>0) px(wtrX-l, y, l, 2, '#5cc4da'); }   // shallows lapping onto the sand
  for(let y=y0; y<y1; y+=2){
    const ex = wtrX - lap(y);                                            // this row's actual waterline
    px(ex-8, y, 8, 2, 'rgba(112,146,146,.26)');                          // damp wet-sand band
    px(ex-4, y, 4, 2, 'rgba(84,132,142,.40)');
    px(ex-1, y, 3, 2, 'rgba(255,255,255,.72)');                          // foam line hugging the curve
  }
  for(let y=y0; y<y1; y+=8){ const ex=wtrX-lap(y), f=((y+surge)&8)?1:0; px(ex-2+f, y+(f?2:0), 2, 3, 'rgba(255,255,255,.5)'); } // foam flecks
}
function drawBeachProps(){
  const T=layout().kitchenTop, y1=H, x0=BEACH_X;
  towel(x0+30, y1-58, '#e0533b'); towel(x0+104, y1-72, '#2f93d8'); towel(x0+66, y1-34, '#37b56c');
  beachUmbrella(x0+16, T+34);   // shifted left so the top row reads umbrella | sign | kiosk
  // beach ball (nudged toward centre now the mascot no longer occupies the sand)
  const bx=x0+150, by=y1-30; px(bx-1,by-1,12,12,PAL.outline);
  px(bx,by,10,10,'#f6f6f8'); px(bx,by,5,5,PAL.red); px(bx+5,by+5,5,5,'#2f93d8'); px(bx,by+5,5,5,PAL.yellow);
  // a little starfish + shell fill the sand where the mascot used to nap (balance)
  const sx=x0+186, sy=y1-46, sc='#e8935f', sl='#f2b48c';
  px(sx-1,sy-4,3,4,sc); px(sx-1,sy-4,1,2,sl);                         // top arm
  px(sx-5,sy-1,4,3,sc); px(sx+2,sy-1,4,3,sc);                         // side arms
  px(sx-4,sy+2,3,4,sc); px(sx+2,sy+2,3,4,sc);                         // lower arms
  px(sx,sy,1,1,sl);                                                    // centre glint
  px(x0+164,y1-22,5,3,'#f2ddc4'); px(x0+165,y1-21,3,1,'#d9b48c');     // small shell
  drawBeachSign();
}

// a wooden "RETIRED AGENTS" signpost planted in the sand (between umbrella + REFRESH)
function drawBeachSign(){
  const T=layout().kitchenTop, cx=BEACH_X+114;   // centred between the umbrella and the REFRESH! kiosk
  const bw=84, bh=24, bx=cx-bw/2, by=T+32, groundY=T+96;
  px(cx-5, groundY-2, 10, 3, 'rgba(0,0,0,.15)');                    // sand contact shadow
  px(cx-2, by+bh, 4, groundY-(by+bh), PAL.woodDk); px(cx-2, by+bh,1, groundY-(by+bh), PAL.wood); // post
  px(bx-2,by-2,bw+4,bh+4,PAL.woodDk); ro(bx,by,bw,bh,'#cf9350');    // plank
  px(bx,by,bw,3,shade('#cf9350',.22)); px(bx,by+bh-3,bw,3,shade('#cf9350',-.20));
  for(let g=0;g<bw-10;g+=15) px(bx+7+g,by+13,11,1,shade('#cf9350',-.12));   // grain
  px(bx+4,by+4,2,2,PAL.metalDk); px(bx+bw-6,by+4,2,2,PAL.metalDk);          // nails
  ctx.fillStyle='#3a2410'; ctx.textAlign='center'; ctx.font='7px "Press Start 2P", monospace';
  ctx.fillText('RETIRED', cx, by+11); ctx.fillText('AGENTS', cx, by+20);
  ctx.textAlign='left';
}

// framed "DO GOOD WORK" poster (heart + 3 lines); pcx,pcy = top-left of the mat
function drawDoGoodWork(pcx, pcy){
  const pw=48, ph=46;
  px(pcx-3,pcy-3,pw+6,ph+6,'#15151a');                       // outer dark frame
  px(pcx-1,pcy-1,pw+2,ph+2,'#3c3c46');                       // frame bevel
  px(pcx+2,pcy+2,pw-4,ph-4,PAL.paper);                       // white mat
  px(pcx+2,pcy+2,pw-4,1,'#ffffff'); px(pcx+2,pcy+ph-3,pw-4,1,'#e2e2e8');
  const hx=pcx+pw/2, hy=pcy+6;
  px(hx-6,hy,4,3,PAL.pink); px(hx+2,hy,4,3,PAL.pink);
  px(hx-6,hy+3,12,2,PAL.pink); px(hx-5,hy+5,10,2,PAL.pink);
  px(hx-3,hy+7,6,2,PAL.pink);  px(hx-1,hy+9,2,1,PAL.pink);
  px(hx-5,hy+1,2,1,shade(PAL.pink,.45));
  ctx.fillStyle=PAL.ink; ctx.textAlign='center'; ctx.font='6px "Press Start 2P", monospace';
  ctx.fillText('DO',   hx, pcy+24); ctx.fillText('GOOD', hx, pcy+32); ctx.fillText('WORK', hx, pcy+40);
  ctx.textAlign='left';
}

// outlined rectangle (dark 1px border) - the key to the chunky pixel look
function ro(x,y,w,h,c){ px((x|0)-1,(y|0)-1,(w|0)+2,(h|0)+2,PAL.outline); px(x|0,y|0,w|0,h|0,c); }

// hair + headwear, drawn on a 14px-wide head whose top-left is (x-7, hy)
// a courier / baseball cap in one solid color -- shared so messengers look identical
// whether the sprite is drawn as male, female, seated or standing
function drawCap(x, hy, col){
  px(x-8,hy-3,16,5,col);              // dome sitting on the crown
  px(x-8,hy-3,16,1,shade(col,.35));   // top gloss
  px(x-9,hy,2,3,col); px(x+7,hy,2,3,col);   // side wrap over the ears
  px(x-14,hy+1,8,2,shade(col,-.15));  // front visor / brim
  px(x-8,hy+1,16,1,shade(col,-.22));  // band shadow
}
// a small envelope emblem (like ✉️) stamped on a courier's chest, centered on (cx,cy)
function drawEnvelope(cx, cy){
  const paper='#f4f4f6', edge='#3a3a44';
  px(cx-4, cy-3, 8, 6, paper);                              // body
  px(cx-4, cy-3, 8, 1, edge); px(cx-4, cy+2, 8, 1, edge);  // top + bottom border
  px(cx-4, cy-3, 1, 6, edge); px(cx+3, cy-3, 1, 6, edge);  // left + right border
  // flap: a shallow V from the top corners meeting in the middle
  px(cx-3,cy-2,1,1,edge); px(cx-2,cy-1,1,1,edge); px(cx-1,cy,1,1,edge);
  px(cx+2,cy-2,1,1,edge); px(cx+1,cy-1,1,1,edge); px(cx,cy,1,1,edge);
}
function drawHairAcc(x, hy, f){
  const hr=f.hair, hl=shade(hr,.34), hd=shade(hr,-.30);
  if(f.female){
    // rounded crown framing the face (clearly feminine), with shading
    px(x-8,hy-4,16,7,hr); px(x-8,hy-4,16,1,hd);          // crown + top outline
    px(x-9,hy+1,3,13,hr); px(x+6,hy+1,3,13,hr);          // long sides past the cheeks
    px(x-7,hy-3,9,1,hl); px(x-9,hy+1,2,5,hl);            // soft crown + side highlight
    px(x-6,hy-4,7,1,shade(hr,.55)); px(x+5,hy-2,2,6,hd); // bright top sheen + right-side depth
    px(x-9,hy+12,3,3,hd); px(x+6,hy+12,3,3,hd);          // tip shade
    if(f.femStyle===0){                                  // long flowing
      px(x-10,hy+12,3,7,hr); px(x+7,hy+12,3,7,hr); px(x+7,hy+5,1,11,hl); px(x-10,hy+17,3,2,hd);
    } else if(f.femStyle===1){                           // side ponytail
      px(x+8,hy,4,14,hr); px(x+9,hy+12,3,7,hr); px(x+7,hy-1,4,4,hr); px(x+9,hy+2,1,10,hl);
      px(x-5,hy-4,3,2,PAL.pink);                         // little clip
    } else if(f.femStyle===2){                           // bun + bow
      px(x-3,hy-8,6,5,hr); px(x-2,hy-7,3,1,hl);
      px(x-5,hy-9,3,3,PAL.pink); px(x+2,hy-9,3,3,PAL.pink); px(x-1,hy-8,2,2,PAL.pink);
    } else {                                             // high top-knot
      px(x-3,hy-10,6,5,hr); px(x-2,hy-10,4,1,hl); px(x-1,hy-12,2,2,hr);
      px(x-9,hy+1,3,8,hr); px(x+6,hy+1,3,8,hr);          // shorter tucked sides
    }
    if(f.acc===3){ px(x-9,hy+3,3,7,'#222'); px(x+6,hy+3,3,7,'#222'); px(x-8,hy-4,16,3,'#222'); } // headphones
    if(f.acc===2){ drawCap(x, hy, f.accCol); }           // cap (e.g. courier uniform)
    return;
  }
  // ---- men / neutral ----
  if(f.hairStyle!==2){ px(x-7,hy-3,14,6,hr); px(x-8,hy+1,2,7,hr); px(x+6,hy+1,2,7,hr);       // base + sideburns
    px(x-6,hy-4,12,1,hr);                                                                     // rounded crown
    px(x-7,hy-3,14,1,hd); px(x-5,hy-3,6,1,hl); px(x-6,hy-2,3,1,shade(hr,.5)); px(x+4,hy-2,2,5,hd); } // outline + sheen streak + temple depth
  if(f.hairStyle===1){ px(x-5,hy-7,3,5,hr); px(x-1,hy-8,3,6,hr); px(x+3,hy-7,3,5,hr); px(x-1,hy-8,2,1,hl); } // spiky
  else if(f.hairStyle===3){ px(x-2,hy-7,5,5,hr); px(x-1,hy-7,3,1,hl); }                                      // bun
  else if(f.hairStyle===4){ px(x-8,hy-4,16,8,hr); px(x-9,hy+4,2,6,hr); px(x+7,hy+4,2,6,hr);
    px(x-6,hy-3,5,1,hl); px(x-1,hy-4,4,1,hl); px(x+3,hy-3,3,1,hl); }                                         // curly mop
  else if(f.hairStyle===5){ px(x-1,hy-8,4,9,hr); px(x-1,hy-8,2,1,hl); }                                      // mohawk
  else if(f.hairStyle===6){ px(x-2,hy-4,1,5,hd); px(x-6,hy-3,4,1,shade(hr,.5)); px(x+1,hy-3,5,1,hl); }        // side part
  else if(f.hairStyle===7){ px(x-8,hy-6,16,4,hr); px(x-9,hy-2,3,5,hr); px(x+6,hy-2,3,5,hr);
    px(x-6,hy-6,10,1,hl); px(x-8,hy-6,16,1,hd); }                                                             // afro / big volume
  else if(f.hairStyle===0){ px(x-7,hy-4,14,4,hr); px(x-6,hy-3,7,1,hl); }                                     // flat
  if(f.acc===2){ drawCap(x, hy, f.accCol); }                                                   // cap
  else if(f.acc===3){ px(x-8,hy-2,16,3,'#222'); px(x-10,hy+3,3,8,'#222'); px(x+7,hy+3,3,8,'#222'); } // headphones
  else if(f.acc===4){ px(x-8,hy-4,16,8,f.accCol); px(x-8,hy+3,16,2,'rgba(0,0,0,.25)'); }      // beanie
  else if(f.acc===5){ px(x-1,hy-8,2,7,'#9aa'); px(x-2,hy-11,4,4,PAL.red); }                   // antenna
}
function drawFace(x, hy, f, beach){
  const sk=f.skin;
  // ears
  px(x-9,hy+5,2,4,sk); px(x-9,hy+5,1,4,PAL.outline);
  px(x+7,hy+5,2,4,sk); px(x+8,hy+5,1,4,PAL.outline);
  // soft roundness: shadow down the right cheek, highlight on the upper-left,
  // and a gentle chin shade -- gives the face dimension across every skin tone
  px(x+4,hy,3,11,'rgba(60,40,25,.12)');
  px(x-6,hy,2,5,'rgba(255,255,255,.16)');
  px(x-6,hy+11,12,1,'rgba(60,40,25,.12)');
  // relaxed, slightly raised eyebrows (friendly, never angled-down)
  px(x-5,hy+2,3,1,'rgba(70,50,40,.55)'); px(x+2,hy+2,3,1,'rgba(70,50,40,.55)');
  if(beach){ // dark sunglasses (beach only) -- two tinted lenses + a bridge
    px(x-6,hy+4,5,4,'#15151a'); px(x+1,hy+4,5,4,'#15151a'); px(x-1,hy+5,2,1,'#15151a');
    px(x-5,hy+4,2,1,'rgba(120,200,230,.55)'); px(x+2,hy+4,2,1,'rgba(120,200,230,.55)'); // lens glint
  } else if(f.acc===1){ // glasses (over the eyes)
    px(x-6,hy+5,5,4,'#1b1b1b'); px(x+1,hy+5,5,4,'#1b1b1b'); px(x-1,hy+6,2,1,'#1b1b1b');
    px(x-5,hy+5,3,3,'#eaf6ff'); px(x+2,hy+5,3,3,'#eaf6ff');
    px(x-4,hy+6,1,1,'#101010'); px(x+3,hy+6,1,1,'#101010');
  } else { // open eyes -- with an occasional blink (staggered per sprite by x)
    const blink = ((performance.now() + ((x*131)&1023)*4) % 3400) < 130;
    if(blink){
      px(x-5,hy+6,3,1,PAL.outline); px(x+2,hy+6,3,1,PAL.outline);   // closed (mid-blink)
    } else {
      px(x-5,hy+5,3,3,'#ffffff'); px(x+2,hy+5,3,3,'#ffffff');
      px(x-4,hy+6,2,2,PAL.outline); px(x+3,hy+6,2,2,PAL.outline);
      px(x-4,hy+5,1,1,'#ffffff'); px(x+3,hy+5,1,1,'#ffffff'); // catch-light sparkle
    }
  }
  // eyelashes for women (outer corners)
  if(f.female){ px(x-6,hy+4,1,1,PAL.outline); px(x+6,hy+4,1,1,PAL.outline); }
  // small nose
  px(x,hy+8,1,2,'rgba(0,0,0,.20)');
  // HAPPY upturned smile: base line low in the middle, corners curving UP
  const mc='#6e352f';
  px(x-1,hy+11,3,1,mc);                 // bottom of the curve (middle, lowest)
  px(x-2,hy+10,1,1,mc); px(x+2,hy+10,1,1,mc);   // sides rising
  px(x-3,hy+9,1,1,mc);  px(x+3,hy+9,1,1,mc);    // corners turned UP
  px(x-1,hy+12,3,1,'rgba(214,90,110,.55)');     // warm lower-lip hint
  // rosy cheeks
  px(x-6,hy+8,2,2,'rgba(232,120,120,.55)'); px(x+5,hy+8,2,2,'rgba(232,120,120,.55)');
}

// a 💢-style anger vein: a little four-armed cross-hatch pop, drawn beside/above the head
function drawAngerVein(x, y){
  const r='#e23b3b';
  px(x-3,y-3,2,2,r); px(x+1,y-3,2,2,r); px(x-3,y+1,2,2,r); px(x+1,y+1,2,2,r);
  px(x-1,y-1,2,2,shade(r,.25));
}

// ANGRY overlay drawn ON TOP of the (always-happy) drawFace: a red flush, furious
// down-angled brows, a gritted frown + an anger vein. Coords match drawFace's (x,hy).
function drawAngryFace(x, hy, f){
  px(x-7,hy,14,12,'rgba(214,50,40,.22)');                                  // red flush over the face
  px(x-6,hy+2,3,1,'#3a1414'); px(x-4,hy+3,3,1,'#3a1414');                  // left brow angling down-in
  px(x+3,hy+2,3,1,'#3a1414'); px(x+1,hy+3,3,1,'#3a1414');                  // right brow angling down-in
  px(x-3,hy+11,7,1,'#5a1e1e'); px(x-3,hy+10,1,1,'#5a1e1e'); px(x+3,hy+10,1,1,'#5a1e1e'); // gritted frown
  drawAngerVein(x+8, hy-3);
}

// a little tropical cocktail (glass + drink + straw + paper umbrella); cy = glass base
function drawCocktail(cx, cy){
  const glass='#d5edf5', drink='#f39a3a';
  px(cx-2,cy-6,5,6,glass);            // glass body
  px(cx-2,cy-6,5,1,'#eef8fb');        // rim highlight
  px(cx-1,cy-5,3,4,drink);            // drink
  px(cx+2,cy-5,1,4,'#b7d5df');        // glass shade
  px(cx-2,cy,5,1,'#b7d5df');          // base
  px(cx+2,cy-11,1,6,'#37b56c');       // straw
  px(cx-1,cy-12,6,1,'#e0533b'); px(cx,cy-11,4,1,'#f6f6f8'); px(cx+1,cy-10,2,1,'#2f93d8'); // paper umbrella
}

// a finished agent relaxing on the sand: seated, shades on, cocktail in hand.
// Only used for beach agents once they've settled, so the vacation look never
// leaks into the kitchen or the desks.
function drawBeachSitter(p, t){
  const x=Math.round(p.x), y=Math.round(p.y);   // y = where they sit on the sand
  const f=p.feat||featuresFor(p.id||'x');
  const sk=f.skin, sh=f.shirt, pants=f.pants, shoe='#4a3526';
  ctx.fillStyle='rgba(0,0,0,.18)'; ctx.beginPath(); ctx.ellipse(x,y+8,15,4,0,0,Math.PI*2); ctx.fill(); // shadow
  // legs stretched out on the sand + feet at the ends
  ro(x-11, y+2, 22, 6, pants); px(x-11,y+2,22,1,shade(pants,.18)); px(x-11,y+7,22,1,shade(pants,-.14));
  px(x-14, y+3, 5, 4, shoe); px(x+9, y+3, 5, 4, shoe);
  px(x-14,y+3,5,1,shade(shoe,.3)); px(x+9,y+3,5,1,shade(shoe,.3));
  // seated torso
  ro(x-8, y-9, 16, 13, sh);
  px(x-8,y-9,16,2,shade(sh,.30)); px(x+5,y-8,3,11,shade(sh,-.20)); px(x-8,y+2,16,2,shade(sh,-.16));
  px(x-2,y-9,4,2,shade(sh,-.28));                              // collar
  torsoDetail(x, y-9, 8, 13, sh, f);                          // outfit variety + sheen
  // left arm propped back on the sand
  ro(x-12, y-6, 5, 8, sh); px(x-12, y+1, 5, 3, sk);
  // right arm raised, holding the cocktail
  ro(x+7, y-8, 5, 7, sh); px(x+8, y-3, 4, 3, sk);
  drawCocktail(x+12, y-1);
  // neck + head
  px(x-3, y-13, 6, 4, sk); px(x-3,y-13,6,1,'rgba(0,0,0,.16)');
  ro(x-7, y-26, 14, 15, sk);
  px(x-7,y-12,14,1,'rgba(0,0,0,.10)');
  drawHairAcc(x, y-24, f); drawFace(x, y-24, f, true);        // sunglasses ON (beach only)
}

// the beach easter egg's demise: an agent slipping under the waves. st = 0..1 sink
// progress. Drawn inside the same scaleAbout(p.x,p.y,SC) transform as the other sprites,
// so we build around (p.x,p.y) exactly like drawBeachSitter. X_X eyes, a last flail of
// the arms, a translucent waterline creeping up the body, and bubbles trailing up.
function drawDrowning(p, st){
  st=Math.max(0, Math.min(1, st||0));           // defensive: a negative ellipse radius throws & freezes everything
  const now=performance.now();
  const x=Math.round(p.x);
  const surf=Math.round(p.y-2);                 // the water surface -- stays put as they sink
  const f=p.feat||featuresFor(p.id||'x');
  const sk=f.skin, sh=f.shirt;
  const sink=Math.round(st*22);                 // body descends into the sea
  const y=Math.round(p.y+sink);
  const a=Math.max(0, 1-st);                    // fade fully out just as they vanish
  ctx.save();
  ctx.globalAlpha=a;
  const swing=Math.sin(now*0.02+(p.seed||0))*2;         // frantic flailing
  const armUp=Math.round((1-st)*6);                     // arms high early, drop as they go under
  px(x-9, y-15-armUp+swing, 3, 8+armUp, sk);            // left arm (help!)
  px(x+6, y-15-armUp-swing, 3, 8+armUp, sk);            // right arm
  ro(x-6, y-8, 12, 12, sh); px(x-6,y-8,12,2,shade(sh,.28));   // torso
  ro(x-6, y-20, 12, 12, sk);                            // head
  const xeye=(ex,ey)=>{ for(const [dx,dy] of [[0,0],[2,0],[1,1],[0,2],[2,2]]) px(ex+dx,ey+dy,1,1,'#25201c'); };
  xeye(x-4, y-16); xeye(x+2, y-16);                     // X_X dead eyes
  ctx.restore();
  // translucent water creeping up over the submerged part + a foam ripple ring at the surface
  ctx.globalAlpha=1;
  ctx.fillStyle='rgba(87,194,216,.5)';
  if(y-surf+6>0) ctx.fillRect(x-10, surf, 20, y-surf+6);
  const rr=4+st*11;
  ctx.strokeStyle='rgba(255,255,255,.55)'; ctx.lineWidth=1;
  ctx.beginPath(); ctx.ellipse(x, surf, rr, rr*0.42, 0, 0, Math.PI*2); ctx.stroke();
  // three bubbles trailing upward
  for(let i=0;i<3;i++){
    const bt=(now*0.03 + i*40 + (p.seed||0)*7) % 60;
    const by=surf - bt*0.5, bx=x + Math.sin(now*0.01 + i*2)*3 + (i-1)*3, br=1.5-i*0.3;
    ctx.globalAlpha=Math.max(0, 1-bt/60); ctx.fillStyle='rgba(255,255,255,.8)';
    ctx.beginPath(); ctx.ellipse(bx, by, br, br, 0, 0, Math.PI*2); ctx.fill();
  }
  ctx.globalAlpha=1;
}

// ---- helper-dwarf placement (subagent dwarves + workflow easel) ----
// Per desk, per frame: which side the easel and the dwarves go on, how many dwarves fit per
// row (a staggered back row when the front one is full) and at what size, so every dwarf
// stays on-canvas and out of the neighbouring desks. Units are pod-local px (offset from
// the desk anchor; screen = anchor + local*scale). A dwarf spans cx-6..cx+13 and stands in
// y-1..y+24 (back row y-13..y+12): below the listening glyphs (y-28..y-18) and above every
// name-plate (y+30..), so only the horizontal room has to be negotiated.
const HLP = { inner:28, wl:6, wr:13, pitch:22, body:30, easelOut:82, easelMin:0.3, edge:3, max:6, sizes:[1, 0.8, 0.65] };
function slotAgent(s){ return (s.worker && s.worker.seated && s.worker.agent) || null; }
// outer reach (local px) of a desk's easel, which shrinks about x+-body (see drawWorkflowTent)
function easelReach(s){ return HLP.body+(HLP.easelOut-HLP.body)*(s.easelScale||1); }
function helperFit(s, side, hs, lim){
  const sc=s.scale||SC, inner=(s.easel===side ? easelReach(s)+2 : HLP.inner);
  const d0=inner+(side==='R' ? HLP.wl : HLP.wr)*hs, step=HLP.pitch*hs, outer=(side==='R' ? HLP.wr : HLP.wl)*hs;
  const room=(side==='R' ? lim-s.x : s.x-lim)/sc;
  const front=room>=d0+outer ? Math.floor((room-d0-outer)/step)+1 : 0;
  const back=room>=d0+step/2+outer ? Math.floor((room-d0-step/2-outer)/step)+1 : 0;
  return { front, back, d0, step, room, outer, total:Math.min(HLP.max, front+back) };
}
function helperLimit(row, side, j, sd, edgeL, edgeR){
  if(sd==='R'){ if(j+1>=row.length) return W-HLP.edge;
    const e=edgeL(row[j+1]); return side[j+1]==='L' ? (edgeR(row[j])+e)/2 : e; }
  if(j===0) return HLP.edge;
  const e=edgeR(row[j-1]); return side[j-1]==='R' ? (e+edgeL(row[j]))/2 : e;
}
// Side per desk in one row. Preferred: right for desks in the left half, left otherwise --
// but two facing neighbours would then split one gap, so every L/R assignment of the desks
// that have helpers is scored: worst shown/needed ratio, then total shown, then preference.
// Cached per row geometry + demand (2^n tries, n = helper desks in the row, capped at 10).
const _helperSideCache = new Map();
function helperSides(row, want, edgeL, edgeR){
  const key = row.map((s,j)=>[Math.round(s.x), (s.scale||SC).toFixed(3), want[j], s.easel||'',
                              (s.easelScale||1).toFixed(2)].join(':')).join('|');
  const hit = _helperSideCache.get(key);
  if(hit) return hit.slice();
  const pref = row.map((s,j)=> !want[j] ? null : (s.x < W/2-1 ? 'R' : 'L'));
  const idx = row.map((_,j)=>j).filter(j=>want[j]);
  let best = pref, bestScore = null;
  if(idx.length && idx.length<=10){
    const small = HLP.sizes[HLP.sizes.length-1];
    for(let mask=0; mask<(1<<idx.length); mask++){
      const side = row.map(()=>null);
      idx.forEach((j,b)=>{ side[j] = ((mask>>b)&1) ? 'R' : 'L'; });
      let worst=1e9, total=0, match=0;
      for(const j of idx){
        const need=Math.min(want[j], HLP.max), L=helperLimit(row, side, j, side[j], edgeL, edgeR);
        const c=Math.min(need, helperFit(row[j], side[j], small, L).total);
        const full=Math.min(need, helperFit(row[j], side[j], 1, L).total);
        worst=Math.min(worst, c/need); total+=c+full*0.01; match+=(side[j]===pref[j]) ? 1 : 0;
      }
      const score=[worst, total, match];
      if(!bestScore || score[0]>bestScore[0]+1e-9 || (Math.abs(score[0]-bestScore[0])<1e-9 &&
         (score[1]>bestScore[1]+1e-9 || (Math.abs(score[1]-bestScore[1])<1e-9 && score[2]>bestScore[2])))){
        bestScore=score; best=side;
      }
    }
  }
  if(_helperSideCache.size>200) _helperSideCache.clear();
  _helperSideCache.set(key, best);
  return best.slice();
}
function helperLayout(slots){
  for(const s of slots){
    const a=slotAgent(s), sc=s.scale||SC;
    s.hl=null;
    s.easel = (a && a.workflows && a.workflows.length) ? ((s.x+HLP.easelOut*sc > W-HLP.edge) ? 'L' : 'R') : null;
  }
  const rows={};
  for(const s of slots) (rows[Math.round(s.y)] = rows[Math.round(s.y)] || []).push(s);
  for(const k in rows){
    const row=rows[k].sort((a,b)=>a.x-b.x);
    // shrink an easel that would reach the next desk (or the canvas edge) on its side; two
    // easels facing the same gap (the far-right one flipped to 'L') split it at the middle
    row.forEach((s,j)=>{
      s.easelScale=1;
      if(!s.easel) return;
      const nb = s.easel==='R' ? row[j+1] : row[j-1];
      const lim = !nb ? (s.easel==='R' ? W-HLP.edge : HLP.edge)
                : (nb.easel && nb.easel!==s.easel) ? (s.x+nb.x)/2
                : nb.x+(s.easel==='R' ? -1 : 1)*HLP.body*(nb.scale||SC);
      const room=(s.easel==='R' ? lim-s.x : s.x-lim)/(s.scale||SC) - 2;
      s.easelScale=Math.max(HLP.easelMin, Math.min(1, (room-HLP.body)/(HLP.easelOut-HLP.body)));
    });
    const edgeR=s=>s.x+(s.easel==='R' ? easelReach(s) : HLP.body)*(s.scale||SC);
    const edgeL=s=>s.x-(s.easel==='L' ? easelReach(s) : HLP.body)*(s.scale||SC);
    const want=row.map(s=>{ const a=slotAgent(s); return a ? (a.subs||0) : 0; });
    const side=helperSides(row, want, edgeL, edgeR);
    // outward limit (screen x) for desk j on side sd; a gap both neighbours want is split
    const lim=(j,sd)=>helperLimit(row, side, j, sd, edgeL, edgeR);
    for(let j=0;j<row.length;j++){
      if(!want[j]) continue;
      const s=row[j], sd=side[j], L=lim(j,sd), need=Math.min(want[j],HLP.max);
      let fit=null, hs=1;
      for(const z of HLP.sizes){ const f=helperFit(s, sd, z, L); if(!fit || f.total>fit.total){ fit=f; hs=z; } if(f.total>=need) break; }
      let front=Math.min(want[j], fit.front, HLP.max);
      let back=Math.min(want[j]-front, fit.back, HLP.max-front);
      let d0=fit.d0;
      if(front<1){
        // no free floor on either side: still show one (smallest) dwarf, tucked in against
        // its OWN desk so it never crosses the outward limit (the neighbour / canvas edge)
        hs=HLP.sizes[HLP.sizes.length-1]; fit=helperFit(s, sd, hs, L);
        front=1; back=0; d0=Math.max(0, Math.min(fit.d0, fit.room-fit.outer));
      }
      s.hl={ side:sd, hs, d0, step:fit.step, front, back, extra:want[j]-front-back };
    }
  }
}
// a tiny white "+N" tag (dark outline) centred at (cx, cy), pod-local; returns its half-width
function drawPlusBadge(cx, cy, n){
  ctx.font='4px "Press Start 2P", monospace';
  const txt='+'+n, w=Math.round(ctx.measureText(txt).width)+4, h=7, bx=Math.round(cx-w/2), by=Math.round(cy-h/2);
  ro(bx, by, w, h, PAL.paper);
  ctx.fillStyle=PAL.ink; ctx.textAlign='center'; ctx.fillText(txt, bx+w/2, by+h-1); ctx.textAlign='left';
  return w/2;
}

// a full workstation: office chair + desk + monitor + filing cabinet + plant,
// with (optionally) a worker seated behind it, facing us. Even empty it looks furnished.
function drawDeskPod(x, y, p, t, sc, slot){
  const hl = slot && slot.hl;
  sc = sc || SC;   // the pod is drawn scaled by `sc` about (x,y); hit regions convert with it
  const f = p ? (p.feat||featuresFor(p.id)) : null;
  // a seated worker "works" (types, its screen animates, its mug steams) only while its OWN
  // turn is active; when it is merely working because a subagent / workflow is live it sits
  // still with a dimmed standby screen, so only the helper dwarves animate (item 8).
  const selfActive = !p || !p.agent || p.agent.self_active !== false;
  const whipped = !!(p && p.whipUntil && performance.now()<p.whipUntil);   // "work harder": faster typing/scroll + a shudder
  // --- soft contact shadow on the floor under the whole workstation ---
  ctx.fillStyle='rgba(0,0,0,.14)'; ctx.beginPath(); ctx.ellipse(x, y+26, 35, 6, 0, 0, Math.PI*2); ctx.fill();
  // --- rolling office chair: gas post + 5-star wheel base (peeks below the desk) ---
  px(x-2,y+10,4,14,PAL.metalDk);                                       // gas post
  px(x-18,y+23,36,2,shade(PAL.metalDk,.14));                           // hub bar
  px(x-18,y+24,4,4,'#2b2b30'); px(x-10,y+25,4,4,'#2b2b30');
  px(x-2,y+25,4,4,'#2b2b30'); px(x+6,y+25,4,4,'#2b2b30'); px(x+14,y+24,4,4,'#2b2b30'); // 5 wheels
  // --- curved padded backrest + armrests (behind the worker) ---
  ro(x-13, y-23, 26, 21, PAL.chairW);
  px(x-10,y-26,20,4,PAL.chairW); px(x-10,y-27,20,1,PAL.outline);        // rounded headrest cap
  px(x-13,y-23,26,3, shade(PAL.chairW,.20)); px(x-13,y-6,26,3, shade(PAL.chairW,-.22));
  px(x-14,y-20,2,15, shade(PAL.chairW,-.12)); px(x+12,y-20,2,15, shade(PAL.chairW,-.12)); // side bolsters
  px(x-18,y-4,5,8, shade(PAL.chairW,-.10)); px(x+13,y-4,5,8, shade(PAL.chairW,-.10));     // armrests
  if(p){
    const sh=f.shirt, sk=f.skin;
    // celebration: a little seated bounce while the flag is live (visual only;
    // hitbox uses deskX/deskY, so a transient offset is safe)
    const hop=(p.celebrateUntil && performance.now()<p.celebrateUntil)
      ? -Math.abs(Math.sin(performance.now()*0.018))*4
      : (p.blissUntil && performance.now()<p.blissUntil)
      ? -Math.abs(Math.sin(performance.now()*0.004))*1.6 : 0;   // THANK AGENTS: soft contented bob
    const flin=whipped ? Math.sin(performance.now()*0.06)*1.6 : 0;   // whip: a brief startled shudder
    const angry=performance.now()<angryUntil;                        // ANGRY MODE (WHIP-abuse revolt)
    const shake=angry ? Math.sin(performance.now()*0.05 + arguments[0])*1.8 : 0;  // seething jitter
    const x=Math.round(arguments[0]+flin+shake), y=Math.round(arguments[1]+hop); // shadow desk x/y for the worker BODY only
    // torso (soft shaded shirt + collar)  -- anchors UNCHANGED (hitbox-critical)
    ro(x-11, y-12, 22, 16, sh);
    px(x-11,y-12,22,2, shade(sh,.30)); px(x+7,y-11,3,14, shade(sh,-.20)); px(x-11,y+2,22,2, shade(sh,-.16));
    px(x-2,y-12,4,2, shade(sh,-.28));
    torsoDetail(x, y-12, 11, 16, sh, f);                                // outfit variety + sheen
    if(f.messenger){ drawEnvelope(x, y-5); }                            // courier envelope badge
    // typing arms -- frozen when the parent is idle-waiting on a subagent (selfActive above)
    const tap = selfActive ? (Math.floor(t*(whipped?1.1:0.4))&1) : 0;
    ro(x-15, y-2+tap, 6, 8, sh); ro(x+9, y-2+(1-tap), 6, 8, sh);
    px(x-14, y+5+tap, 5,3, sk); px(x+10, y+5+(1-tap), 5,3, sk);
    // neck + head  -- anchors UNCHANGED (hitbox-critical)
    px(x-3, y-15, 6, 4, sk); px(x-3, y-15, 6, 1, 'rgba(0,0,0,.16)');
    ro(x-7, y-28, 14, 15, sk);
    px(x-7,y-14,14,1,'rgba(0,0,0,.10)');                                // soft jaw shade
    drawHairAcc(x, y-26, f); drawFace(x, y-26, f);
    if(angry) drawAngryFace(x, y-26, f);
  }
  // --- wood desk top: bright surface + grain hint + shaded front edge ---
  px(x-26,y+1,52,4,PAL.woodHi);                                         // bright top surface
  ro(x-26, y+5, 52, 6, PAL.wood); px(x-26,y+5,52,2, shade(PAL.wood,.22));
  for(let g=0; g<46; g+=11) px(x-22+g,y+7,7,1, shade(PAL.wood,-.10));    // grain
  px(x-26,y+10,52,2,PAL.woodDk);                                        // shaded front edge
  // --- grey TWO-DRAWER pedestal under the left side + a right leg ---
  const pbx=x-24; ro(pbx, y+11, 20, 15, PAL.metal); px(pbx,y+11,20,2,PAL.steel);
  px(pbx+1,y+13,18,5, shade(PAL.metal,.05)); px(pbx+1,y+19,18,5, shade(PAL.metal,-.07)); // drawer faces
  px(pbx+6,y+15,8,1,PAL.metalDk); px(pbx+6,y+21,8,1,PAL.metalDk);       // drawer handles
  px(x+19,y+11,3,14,PAL.woodDk);                                        // right desk leg
  // --- chunkier monitor on a stand with a soft screen glow ---
  const mx=x-23, my=y-16, mw=26;
  ctx.fillStyle='rgba(150,222,236,.16)'; ctx.fillRect(mx-2,my-1,mw+4,18);  // glow halo
  px(x-11,y-1,4,3,PAL.monitorLip); px(x-15,y+2,12,2,PAL.monitorLip);       // stand + base
  ro(mx, my, mw, 16, PAL.monitor); px(mx,my,mw,2, shade(PAL.monitor,.5));
  if(p){ const tints=['#7fd3e0','#9fe0c0','#7fb0e0','#cfe9a0'];
    const fr = selfActive ? Math.floor((t*(whipped?0.34:0.12)+p.seed)%4) : 0;            // freeze frame when idle
    px(mx+2,my+2,mw-4,12, selfActive ? tints[fr] : '#586a72');           // bright code vs dim standby
    px(mx+3,my+4,16,2,PAL.ink); px(mx+3,my+7,10,2,PAL.ink); px(mx+3,my+10,19,2,PAL.ink);
    px(mx+2,my+2,mw-4,1,'rgba(255,255,255,.22)');                         // screen gloss
  } else { px(mx+2,my+2,mw-4,12,'#39404a'); px(mx+4,my+7,12,2,'#4a525d'); } // dim when empty
  // keyboard + mouse on the desk top
  px(x-15,y+1,20,4,'#d3dae0'); px(x-15,y+1,20,1,'#fff'); for(let k=0;k<5;k++) px(x-13+k*4,y+3,2,1,'#aeb6bd');
  px(x+8,y+2,4,3,'#d3dae0');
  // little terracotta desk plant (right) + paper stack
  px(x+13,y-4,9,6,PAL.pot); px(x+13,y-4,9,2,shade(PAL.pot,.18)); px(x+12,y,11,1,PAL.potDk);
  blade(x+15,y-4,9,-2,PAL.leafDk); blade(x+17,y-4,12,0,PAL.leaf); blade(x+19,y-4,8,2,PAL.leafDk);
  px(x-22,y+6,9,5,PAL.paper); px(x-22,y+6,9,1,'#e6e6ec'); px(x-21,y+8,7,1,'#cfcfd6');
  // mug on the desk; steam rises only while the worker is actively at its own turn
  if(p){ mug(x+3, y-1, PAL.mugC);
    if(selfActive) for(let i=0;i<3;i++){ const yy=y-3-((t*1.0+i*5)%8); px(x+5,yy,1,2,'rgba(255,255,255,.5)'); } }
  // desk name-plate: the agent's title on a little white placard in front of the desk,
  // white-board look like the workflow easel. Wrapped on WORD boundaries (never mid-word)
  // and the plate is sized to the longest measured line, so short/medium titles sit on one
  // line and long ones wrap to at most 2 lines (last line '…'-truncated at a word boundary).
  if(p && p.agent && p.agent.title){
    ctx.font='4px "Press Start 2P", monospace';
    const PL_MAXW=p.plateW||84;                                // 84 fits ~"Medication selection"; less in a crowded grid
    const plLines = wrapWords(p.agent.title, PL_MAXW, 2);
    let tw=0; for(const ln of plLines) tw=Math.max(tw, ctx.measureText(ln).width);
    const pw=Math.round(tw)+10, ph=5*plLines.length+3, plx=Math.round(x-pw/2), ply=y+30;  // centered under the desk
    ro(plx, ply, pw, ph, PAL.paper);                            // white plate + dark ro() outline
    px(plx+1, ply+1, pw-2, 1, shade(PAL.paper,-.08));
    ctx.fillStyle=PAL.ink; ctx.textAlign='center';
    // vertically centre the 1-2 lines: 4px glyphs (~4px ascent) on a 5px line step give a
    // text block 5n-1 tall, so first baseline ply+6 leaves equal ~2px padding top & bottom.
    let ppy=ply+6; for(const ln of plLines){ ctx.fillText(ln, x, ppy); ppy+=5; }
    ctx.textAlign='left';
  }
  // running subagents: a helper dwarf digging away next to the desk (one per subagent).
  // We also register a hover region so you can see what each one is doing.
  // Placement comes from helperLayout (side / size / rows); feet sit on the floor line, the
  // back row is staggered half a step outward and drawn first.
  if(p && p.agent && p.agent.subs>0 && hl){
    const subs=p.agent.subagents||[], sgn=(hl.side==='R' ? 1 : -1), hs=hl.hs, parent=p.agent.title||'';
    const spots=[];
    for(let i=0;i<hl.front;i++) spots.push({ cx:x+sgn*(hl.d0+i*hl.step), cy:y+15 });
    for(let i=0;i<hl.back;i++)  spots.push({ cx:x+sgn*(hl.d0+hl.step/2+i*hl.step), cy:y+3 });
    const r=(hl.back ? 11 : 15)*hs*sc;
    const order=spots.map((_,i)=>i).sort((a,b)=>spots[a].cy-spots[b].cy);
    for(const i of order){
      const cx=spots[i].cx, cy=spots[i].cy, foot=cy+9;
      ctx.save(); scaleAbout(cx, foot, hs); drawHelper(cx, cy, t, (hash(p.id)+i*7)%997); ctx.restore();
      // pod is drawn scaled by `sc` about (x,y); convert the dwarf centre to mouse-logical coords
      helperHits.push({ x: x+(cx-x)*sc, y: y+((foot-15*hs)-y)*sc, r, sub: subs[i]||null, parent });
      const sb0 = subs[i] && subs[i].id ? subBubbles[subs[i].id] : null;
      if(sb0){ const lo=(i&1)===1;   // stagger: even dwarf -> above the hat, odd -> below the face
        bubbleAnchors.push({ x: x+(cx-x)*sc, y: y+((foot-(lo?7:24)*hs)-y)*sc, text:sb0.text, start:sb0.start, until:sb0.until, below:lo, tool:sb0.tool }); }
    }
    if(hl.extra>0){
      // "+N" over the outermost dwarf, at the front row's hat line (clear of the listening glyphs)
      const out=spots.reduce((b,s)=> Math.abs(s.cx-x)>Math.abs(b.cx-x) ? s : b, spots[0]);
      const by=y+15+9-25*hs-4;
      const lo=(HLP.edge-x)/sc+x+9, hi=(W-HLP.edge-x)/sc+x-9;
      const bx=Math.max(lo, Math.min(hi, out.cx));
      const hw=drawPlusBadge(bx, by, hl.extra);
      helperHits.push({ x: x+(bx-x)*sc, y: y+(by-y)*sc, r: Math.max(hw, 5)*sc, badge:true, parent,
                        extra: subs.slice(spots.length), more: hl.extra });
    }
  }
  // dynamic-workflow easel (drawn beside the desk; returns its hover hit centre)
  if(p && p.agent && p.agent.workflows && p.agent.workflows.length){
    const h0 = helperHits.length;
    const hit = drawWorkflowTent(x, y, p.agent.workflows, t, sc, (slot && slot.easel) || 'R', slot && slot.easelScale);
    for(let i=h0;i<helperHits.length;i++) helperHits[i].parent = p.agent.title||'';
    if(hit) workflowHits.push({ x: x+(hit.x-x)*sc, y: y+(hit.y-y)*sc, r: hit.r*sc, workflow: p.agent.workflows });
  }
  // open background shells: up to 3 tiny terminal windows in a row just above the desk
  // name-plate, filling left -> middle -> right. Hover shows the command + output tail.
  if(p && p.agent && p.agent.shells && p.agent.shells.length){
    const shells=p.agent.shells, n=Math.min(shells.length,3);
    for(let i=0;i<n;i++){
      // shells[] is newest-first -> draw oldest at the leftmost slot so they fill L->R in the
      // order the shells were opened. 22px pitch on 17px windows -> ~5px gap between them.
      const slot=n-1-i, sx=x-30+slot*22, sy=y+8;    // row bottom (sy+12) clears the name-plate (y+30) with a ~10px local gap
      drawShellWin(sx, sy, t, (hash(p.id)+i*5)%997);
      shellHits.push({ x: x+((sx+8)-x)*sc, y: y+((sy+6)-y)*sc, r: 11*sc, shell: shells[i] });
    }
  }
}

// a small "open shell" terminal window humming above the desk: a dark CRT with a title
// bar, a green prompt/command line, an output line, and a blinking cursor. One per running
// background shell (up to 3). Drawn in the pod's local frame (scaled by SC with the desk).
function drawShellWin(sx, sy, t, seed){
  sx=Math.round(sx); sy=Math.round(sy);
  const w=17, h=12;
  px(sx+1, sy+h, w, 1, 'rgba(0,0,0,.28)');                 // drop shadow
  ro(sx, sy, w, h, '#111620');                             // dark terminal body (+ dark outline)
  px(sx+1, sy+1, w-2, 3, '#2b313d');                       // title bar
  px(sx+2, sy+2, 1,1, '#e0564e'); px(sx+4, sy+2, 1,1, '#e0a53e'); px(sx+6, sy+2, 1,1, '#5fbf5a'); // 3 dots
  px(sx+2, sy+6, 1,1, '#63e6a0');                          // green ">" prompt
  px(sx+4, sy+6, 8,1, '#3c7a58');                          // dim command echo
  px(sx+2, sy+9, 10,1, '#356b4e');                         // output line
  if((Math.floor(t*0.10)+seed)&1) px(sx+13, sy+6, 2,1, '#a6f2c6');  // blinking cursor
}

// a helper "subagent" dwarf: pointy hat, beard, tunic with belt, boots, swinging a
// pickaxe over a little dirt mound. One is drawn per running subagent, animated.
function drawHelper(cx, cy, t, seed){
  const bob = (Math.floor(t*0.22+seed)&1);                 // gentle bob
  const y = cy - bob;
  const up = (Math.floor(t*0.40+seed)&1);                  // pickaxe raised / struck
  px(cx-6, cy+7, 14, 2, 'rgba(0,0,0,.22)');                // ground shadow
  px(cx+4, cy+4, 7, 3, '#8a5a30'); px(cx+4, cy+4, 7, 1, '#a06a3a'); // little dirt mound
  // boots
  px(cx-4, cy+4, 3, 3, '#3a2a18'); px(cx+1, cy+4, 3, 3, '#3a2a18');
  // tunic (green) + belt + buckle
  px(cx-5, y-2, 10, 7, '#4f7d3a'); px(cx-5,y-2,10,1,'#67a04c'); px(cx-5,y+4,10,1,'#3c612c');
  px(cx-5, y+2, 10, 1, '#6b4a2a'); px(cx-1, y+1, 2, 2, '#caa33a');
  // arms + hands
  px(cx-6, y, 2, 4, '#4f7d3a'); px(cx+5, y, 2, 4, '#4f7d3a');
  px(cx-6, y+3, 2, 2, '#f0d2a8'); px(cx+5, y+3, 2, 2, '#f0d2a8');
  // face + big white beard + eyes + rosy nose
  px(cx-3, y-6, 7, 4, '#f0d2a8');
  px(cx-4, y-2, 9, 3, '#eef0f4'); px(cx-3, y+1, 7, 1, '#dcdfe6');
  px(cx-2, y-5, 1, 1, PAL.outline); px(cx+2, y-5, 1, 1, PAL.outline);
  px(cx-1, y-4, 2, 1, '#d98f7a');
  // pointy red hat with brim + pom
  px(cx-5, y-8, 11, 2, '#a83226');
  px(cx-3, y-10, 7, 2, '#c0392b'); px(cx-2, y-12, 5, 2, '#c0392b'); px(cx-1, y-14, 3, 2, '#d2452f'); px(cx, y-16, 1, 2, '#d2452f');
  px(cx, y-16, 1, 1, '#f4f4f4');
  // pickaxe
  if(up){ px(cx+7, y-6, 2, 8, '#8a5a30'); px(cx+5, y-7, 6, 2, '#aab2ba'); px(cx+5,y-7,2,1,'#cdd6dd'); }
  else  { px(cx+7, y+1, 2, 6, '#8a5a30'); px(cx+7, y+6, 6, 2, '#aab2ba');
          px(cx+11, y+5, 1, 1, 'rgba(150,110,60,.6)'); px(cx+9, y+7, 1, 1, 'rgba(150,110,60,.5)'); }
}

// dynamic-workflow easel: a little whiteboard on legs beside the desk showing the
// workflow name (wrapped, mid-word if a token is too long), a big WHITE done/total
// count, and 1-3 tiny helper dwarves at its base (one per running agent). Only drawn
// while something is running. Returns the hover hit centre (local coords) or null.
// slug -> human title: "f2-deterministic-noat-trigger" -> "F2 Deterministic Noat Trigger".
// Keeps ALL-CAPS tokens as-is (API, MCP, CI); the full summary still lives in the hover card.
function humanizeWf(s){
  s = String(s||'').replace(/[_\-]+/g,' ').replace(/\s+/g,' ').trim();
  if(!s) return 'Workflow';
  return s.split(' ').map(w => (w===w.toUpperCase() ? w : (w[0].toUpperCase()+w.slice(1)))).join(' ');
}
function drawWorkflowTent(x, y, workflows, t, sc, side, es){
  sc = sc || SC;   // matches the desk pod's draw scale, for hit-region conversion
  if(!workflows || !workflows.length) return null;   // backend already gates to genuinely-live runs
  // a WHITE whiteboard (like the wall inspiration board), floating a few px above the desk
  // on easel legs, beside the desk with a small horizontal gap so it reads as "beside" it,
  // not sitting on it. To the RIGHT unless that would cross the canvas edge (helperLayout
  // then picks 'L'); the subagent dwarves are laid out around whichever side it takes.
  // In a tight grid helperLayout passes es<1: the whole easel shrinks about the desk-side
  // floor point (ax, ay) so it fits before the neighbouring desk; S() maps easel-local
  // coords to mouse-logical ones for the hit regions and bubbles.
  es = es || 1;
  const ax = x + (side==='L' ? -30 : 30), ay = y+22;
  const S = (lx, ly) => ({ x: x+((ax+(lx-ax)*es)-x)*sc, y: y+((ay+(ly-ay)*es)-y)*sc });
  ctx.save(); scaleAbout(ax, ay, es);
  const bw=44, bh=40, cxT = x + (side==='L' ? -56 : 56), byT = y - 46, bxT = cxT - bw/2;   // inner edge clears the desk + the above desk's name-plate (which reaches anchor+42px on screen)
  // easel: just the 2 side legs (no middle leg), each on a little caster wheel
  const legH = (y+22) - (byT + bh - 2);
  px(bxT+4, byT+bh-2, 2, legH-2, PAL.woodDk); px(bxT+bw-6, byT+bh-2, 2, legH-2, PAL.woodDk);
  const wheel=(wx)=>{ px(wx-2, y+21, 6,2,'rgba(0,0,0,.20)');          // floor shadow
                      px(wx-2, y+18, 5,4, '#2b2f36'); px(wx-1, y+19, 3,2, '#565c66'); }; // dark caster + hub
  wheel(bxT+5); wheel(bxT+bw-5);
  // white board face (ro() paints the 1px dark outline for free) + light-grey header strip
  ro(bxT, byT, bw, bh, PAL.paper);
  px(bxT+1, byT+bh-2, bw-2, 1, 'rgba(0,0,0,.10)');                    // faint bottom shade
  px(bxT+1, byT+1, bw-2, 7, shade(PAL.paper,-.10));
  ctx.fillStyle=PAL.ink; ctx.textAlign='center'; ctx.font='4px "Press Start 2P", monospace';
  ctx.fillText(workflows.length>1?'WORKFLOWS':'WORKFLOW', cxT, byT+6);
  // workflow name (or "N runs" when several share a desk), wrapped mid-word, max 3 lines.
  // small font (matches the desk name-plate), tight side inset, no trailing ellipsis.
  const wname = workflows.length>1 ? (workflows.length+' runs') : humanizeWf(workflows[0].name);
  ctx.fillStyle=PAL.ink; ctx.font='4px "Press Start 2P", monospace';
  const nameLines = wrapTextMid(wname, bw-4, 3, '');
  // vertically centre the name in the band between the header strip and the count
  const nblk = 5*nameLines.length - 1;                       // 4px glyphs on a 5px step
  const bandTop = byT+9, bandBot = byT+bh-10;                // header strip ends ~byT+8; count sits at the bottom
  let ty = Math.round(bandTop + (bandBot-bandTop-nblk)/2) + 4;   // +4 ascent -> first baseline
  for(const ln of nameLines){ ctx.fillText(ln, cxT, ty); ty+=5; }
  // progress: done/total in dark ink
  const done=workflows.reduce((s,w)=>s+(w.done||0),0);
  const total=workflows.reduce((s,w)=>s+(w.total||0),0);
  const running=workflows.reduce((s,w)=>s+(w.running||0),0);
  ctx.fillStyle=PAL.ink; ctx.font='bold 7px "Press Start 2P", monospace';
  ctx.fillText(done+'/'+total, cxT, byT+bh-4);
  ctx.textAlign='left';
  // tiny helper dwarves at the easel base (one per running agent, capped 3, 0.7 scale)
  const n=Math.min(3, running);
  const acts=workflows.reduce((L,w)=>L.concat(w.active||[]),[]);   // flatten running-sub infos
  for(let i=0;i<n;i++){
    const hx=cxT - (n-1)*8 + i*16, hy=y+18;
    ctx.save(); scaleAbout(hx, hy, 0.7); drawHelper(hx, hy, t, (hash(wname)+i*7)%997); ctx.restore();
    // each easel dwarf IS a running workflow subagent -> its own hover region showing what
    // it's doing (not the whole-workflow tooltip). Small radius so the board still hovers
    // as the workflow; the easel hit below is shrunk to the board so these win at the base.
    helperHits.push({ ...S(hx, hy-4), r: 10*sc*es, sub: acts[i]||null });
    const sbw = acts[i] && acts[i].id ? subBubbles[acts[i].id] : null;
    if(sbw){ const lo=(i&1)===1;   // stagger easel dwarves: even -> above the hat, odd -> below the face
      bubbleAnchors.push({ ...S(hx, hy+(lo?1:-12)), text:sbw.text, start:sbw.start, until:sbw.until, below:lo, tool:sbw.tool }); }
  }
  if(running>n){
    // "+N" just under the board's outer corner (inside the easel footprint, so always on-canvas)
    const bx=cxT+(side==='L' ? -1 : 1)*(bw/2-7), by=byT+bh+4;
    const hw=drawPlusBadge(bx, by, running-n);
    helperHits.push({ ...S(bx, by), r: Math.max(hw, 5)*sc*es, badge:true,
                      extra: acts.slice(n), more: running-n });
  }
  ctx.restore();
  // hit only the board face, not the dwarves at its base (pod-local, the caller applies sc)
  return { x: ax+(cxT-ax)*es, y: ay+((y-26)-ay)*es, r: 26*es };
}

// wrap `text` to <= maxLines lines that each fit `maxW` px at the CURRENT ctx.font,
// breaking INSIDE a word when a single token is too long. `ell` is the clip marker
// appended when the text overflows maxLines -- pass '' to truncate with no marker.
function wrapTextMid(text, maxW, maxLines, ell){
  ell = (ell===undefined ? '…' : ell);
  const fits = s => ctx.measureText(s).width <= maxW;
  const words = String(text).split(/\s+/).filter(Boolean);
  const lines=[]; let cur='';
  const flush=()=>{ if(cur){ lines.push(cur); cur=''; } };
  for(let w of words){
    while(!fits(w) && w.length>1){                 // hard-break an over-long token
      flush();
      let i=1; while(i<w.length && fits(w.slice(0,i+1))) i++;
      lines.push(w.slice(0,i)); w=w.slice(i);
    }
    const cand = cur ? cur+' '+w : w;
    if(fits(cand)) cur=cand; else { flush(); cur=w; }
  }
  flush();
  if(maxLines && lines.length>maxLines){
    const out=lines.slice(0,maxLines);
    let last=out[maxLines-1];
    while(last.length>1 && !fits(last+ell)) last=last.slice(0,-1);
    out[maxLines-1]=last+ell;
    return out;
  }
  return lines;
}

// pack `text` into <= maxLines lines that each fit `maxW` px at the CURRENT ctx.font,
// breaking at ANY character (fills the most text per line -- used by the desk name-plate).
// `ell` is the clip marker appended on overflow -- pass '' to truncate with no marker.
function wrapChars(text, maxW, maxLines, ell){
  ell = (ell===undefined ? '…' : ell);
  const fits = s => ctx.measureText(s).width <= maxW;
  const s = String(text); const lines=[]; let cur='';
  for(const ch of s){
    if(cur && !fits(cur+ch)){ lines.push(cur); cur=''; }
    cur += ch;
  }
  if(cur) lines.push(cur);
  if(maxLines && lines.length>maxLines){
    const out=lines.slice(0,maxLines);
    let last=out[maxLines-1];
    while(last.length && !fits(last+ell)) last=last.slice(0,-1);
    out[maxLines-1]=last+ell;
    return out;
  }
  return lines;
}

// greedy WORD wrap to a pixel width: packs whole words per line (never splits mid-word)
// using the CURRENT ctx.font. A single word wider than maxW is hard-broken as a fallback.
// On overflow past maxLines the last line is truncated at a word boundary with an ellipsis.
function wrapWords(text, maxW, maxLines){
  const fits = s => ctx.measureText(s).width <= maxW;
  const words = String(text).replace(/\s+/g,' ').trim().split(' ').filter(Boolean);
  // split any over-long word into pieces that each fit, so nothing can overflow the box
  const toks=[];
  for(const w of words){
    if(fits(w)){ toks.push(w); continue; }
    let cur='';
    for(const ch of w){ if(cur && !fits(cur+ch)){ toks.push(cur); cur=''; } cur+=ch; }
    if(cur) toks.push(cur);
  }
  const lines=[]; let cur='';
  for(const tk of toks){ const test=cur?cur+' '+tk:tk;
    if(cur && !fits(test)){ lines.push(cur); cur=tk; } else cur=test; }
  if(cur) lines.push(cur);
  if(!maxLines || lines.length<=maxLines) return lines;
  // overflow: keep the first maxLines-1 lines whole, then pack the rest into the last line
  // with a trailing '…', dropping whole words (never cutting one) until it fits.
  const out=lines.slice(0,maxLines-1);
  const rest=lines.slice(maxLines-1).join(' ').split(' ').filter(Boolean);
  let last='';
  for(const tk of rest){ const test=last?last+' '+tk:tk; if(last && !fits(test+'…')) break; last=test; }
  if(!last){ last=rest[0]||''; while(last.length>1 && !fits(last+'…')) last=last.slice(0,-1); }
  out.push(last+'…');
  return out;
}

// first ~90 chars, whitespace-collapsed (drawBubble wraps + ellipsizes the rest)
function firstWords(s){ s=String(s||'').replace(/\s+/g,' ').trim(); return s.length>90?s.slice(0,90):s; }
// word-boundary truncation with an ellipsis
function shortText(s, n){ s=String(s||'').replace(/\s+/g,' ').trim(); if(s.length<=n) return s;
  const cut=s.slice(0,n+1).replace(/\s+\S*$/,''); return (cut.length>=n*0.6?cut:s.slice(0,n)).replace(/[\s,.;:\-]+$/,'')+'\u2026'; }
// the backend sends a cleaned `title`; detail is the raw fallback (demo / older payloads)
function helperTitle(s){ return shortText(s.title || String(s.detail||'').replace(/<[^>]+>/g,' ') || 'a background task', 40); }
// first sentence of a message, markdown stripped
function firstSentence(s, n){
  s=String(s||'').replace(/```[\s\S]*?(```|$)/g,' ').replace(/\[([^\]]+)\]\([^)]*\)/g,'$1')
    .replace(/\*\*|__|`|~~|^#+\s*/gm,'').replace(/\s+/g,' ').replace(/\s*\.\.\.$/,'').trim();
  const m=s.match(/^(.+?[.!?])(\s|$)/); return shortText(m ? m[1] : s, n); }
// "Name: detail" -> a plain line, used when the payload has no `doing`
function toolPlainFallback(t){ if(!t) return ''; const i=t.indexOf(':'); const nm=(i>0?t.slice(0,i):t).trim();
  return '\u{1F6E0}\uFE0F using '+nm.replace(/([a-z])([A-Z])/g,'$1 $2').replace(/[_-]+/g,' ').toLowerCase(); }
function fmtRunning(d){ d=Math.max(0,d);
  return 'running '+(d<60 ? Math.round(d)+'s' : d<3600 ? Math.round(d/60)+'m' : Math.floor(d/3600)+'h '+Math.round((d%3600)/60)+'m'); }
// small white speech bubble centred on (x,y) in SCREEN coords. Tail points DOWN to the
// anchor (bubble sits above) unless `below` is set, in which case it sits below with an
// up-pointing tail -- used to stagger neighbouring dwarf bubbles so they don't overlap.
function drawBubble(x, y, text, alpha, below){
  if(!text || alpha<=0) return;
  ctx.save();
  ctx.globalAlpha = Math.max(0, Math.min(1, alpha));
  ctx.font = '4px "Press Start 2P", monospace';
  const lines = wrapTextMid(text, 78, 3, '…');       // reuse existing word-wrap + ellipsis
  let tw=0; for(const ln of lines) tw=Math.max(tw, ctx.measureText(ln).width);
  const padX=4, padY=3, lh=6;
  const bw=Math.max(14, Math.ceil(tw)+padX*2), bh=lh*lines.length+padY*2-1;
  const bx=Math.round(x-bw/2), by=Math.round(below ? y+4 : y-bh);
  ro(bx, by, bw, bh, PAL.paper);                     // white box + 1px dark outline
  px(bx+1, by+1, bw-2, 1, shade(PAL.paper,-.06));    // faint header shade
  const tx=Math.round(x);
  if(below){                                         // upward pixel tail (box hangs below)
    px(tx-2, by-1, 4,1, PAL.paper); px(tx-1, by-2, 2,1, PAL.paper); px(tx, by-3, 1,1, PAL.paper);
    px(tx-3, by-1, 1,1, PAL.outline); px(tx+2, by-1, 1,1, PAL.outline);
    px(tx-2, by-2, 1,1, PAL.outline); px(tx+1, by-2, 1,1, PAL.outline);
    px(tx-1, by-3, 1,1, PAL.outline); px(tx+1, by-3, 1,1, PAL.outline);
    px(tx-1, by-4, 2,1, PAL.outline);
  } else {                                           // downward pixel tail (box sits above)
    px(tx-2, by+bh, 4,1, PAL.paper); px(tx-1, by+bh+1, 2,1, PAL.paper); px(tx, by+bh+2, 1,1, PAL.paper);
    px(tx-3, by+bh, 1,1, PAL.outline); px(tx+2, by+bh, 1,1, PAL.outline);
    px(tx-2, by+bh+1, 1,1, PAL.outline); px(tx+1, by+bh+1, 1,1, PAL.outline);
    px(tx-1, by+bh+2, 1,1, PAL.outline); px(tx+1, by+bh+2, 1,1, PAL.outline);
    px(tx-1, by+bh+3, 2,1, PAL.outline);
  }
  ctx.fillStyle=PAL.ink; ctx.textAlign='center';
  let ty=by+padY+4; for(const ln of lines){ ctx.fillText(ln, x, ty); ty+=lh; }
  ctx.textAlign='left'; ctx.restore();
}
// accent colour for a tool chip, by tool family -- so the same class of action reads the same.
function toolColor(name){
  const n=(name||'').toLowerCase();
  if(/bash|shell|exec|run|terminal|command/.test(n)) return '#6ad06a';        // green: run
  if(/edit|write|replace|create|apply|notebook|patch/.test(n)) return '#f0a23b'; // orange: write
  if(/read|cat|open|view|file/.test(n)) return '#5bb0e6';                      // blue: read
  if(/grep|glob|search|find|explore|list|ls/.test(n)) return '#b98cf0';        // purple: search
  if(/task|agent|workflow|dispatch|spawn/.test(n)) return '#e673a8';           // pink: delegate
  if(/web|fetch|http|url|browser|navigate/.test(n)) return '#4fd0c0';          // teal: web
  return '#d9c37a';                                                            // default: sand-gold
}
// ephemeral TOOL CHIP: a small dark pill with a tool-coloured icon + the tool name, popped
// when an agent/dwarf runs a tool. Deliberately distinct from the white speech bubble.
function drawToolChip(x, y, name, alpha, below){
  if(!name || alpha<=0) return;
  ctx.save();
  ctx.globalAlpha = Math.max(0, Math.min(1, alpha));
  ctx.font = '4px "Press Start 2P", monospace';
  const label = name.length>24 ? name.slice(0,24) : name;   // pre-formatted "NAME detail"; keep the detail
  const tw = ctx.measureText(label).width;
  const icon=5, padX=3, gap=3, h=9;
  const bw = padX + icon + gap + Math.ceil(tw) + padX;
  const bx = Math.round(x-bw/2), by = Math.round(below ? y+4 : y-h);
  const col = toolColor(name.split(' ')[0]);                 // colour by the tool name, not the detail
  ro(bx, by, bw, h, '#22262e');                      // dark slate pill + outline
  px(bx+1, by+1, bw-2, 1, '#333a46');                // top sheen
  const tx=Math.round(x);
  if(below){ px(tx-1, by-1, 2,1, '#22262e'); px(tx, by-2, 1,1, '#22262e'); }   // small nub up
  else     { px(tx-1, by+h, 2,1, '#22262e'); px(tx, by+h+1, 1,1, '#22262e'); } // small nub down
  const ix=bx+padX, iy=by+Math.round((h-icon)/2);    // little gear/cog icon in the tool colour
  px(ix+1,iy,3,1,col); px(ix,iy+1,5,3,col); px(ix+1,iy+4,3,1,col); px(ix+2,iy+2,1,1,'#22262e');
  ctx.fillStyle=col; ctx.textAlign='left';
  ctx.fillText(label, ix+icon+gap, by+h-3);
  ctx.textAlign='left'; ctx.restore();
}
// tool chip label: just the short tool NAME (e.g. "BASH", "EDIT") for the compact ephemeral
// chip. The detailed "Bash: npm run dev" lives in the hover card (last_tool), not here.
function toolChip(s){ s=String(s||''); const i=s.indexOf(':'); return (i>0?s.slice(0,i):s).trim().toUpperCase(); }
// a stern "boss" / supervisor in a suit + red tie, one arm pointing at the desk. Same scale as
// a standing worker -- pops up beside a desk to deliver a fresh user instruction (see below).
function drawBoss(x, y, t, moving){
  x=Math.round(x); y=Math.round(y);
  const suit='#31363f', suitLt='#3d434e', shirt='#eef1f6', tie='#c0392b', skin='#e6b38a', shoe='#191c22', hair='#3a2c20';
  const walking=!!moving;
  const step=walking?(Math.floor(t*0.16)&1):-1;                     // -1 = both feet planted (standing)
  const pt=(!walking) && (Math.floor(t*0.05)&1);                     // point only when stopped at the desk
  ctx.fillStyle='rgba(0,0,0,.22)'; ctx.beginPath(); ctx.ellipse(x,y+16,11,3,0,0,Math.PI*2); ctx.fill();
  ro(x-6,y+4,5,10,suit); ro(x+1,y+4,5,10,suit);                      // slacks
  px(x-2,y+5,1,9,shade(suit,-.25));
  const fa=step<0?0:(step?2:-2), fb=step<0?0:(step?-2:2);           // walk: swing the feet fore/aft
  px(x-8+fa,y+13,7,3,shoe); px(x-8+fa,y+13,7,1,shade(shoe,.4));      // left shoe
  px(x+fb,  y+13,7,3,shoe); px(x+fb,  y+13,7,1,shade(shoe,.4));      // right shoe
  ro(x-9,y-12,18,17,suit); px(x-9,y-12,18,2,suitLt); px(x-9,y+3,18,1,shade(suit,-.2)); // jacket
  px(x-2,y-11,4,11,shirt);                                          // shirt panel
  px(x-4,y-11,3,7,suitLt); px(x+1,y-11,3,7,suitLt);                 // lapels
  px(x-1,y-10,2,9,tie); px(x-1,y-1,2,2,shade(tie,-.25)); px(x-1,y-11,2,1,shade(tie,.3)); // tie
  ro(x+7,y-10,4,10,suit); px(x+7,y+0,4,3,skin);                     // right arm at side
  if(pt){ px(x-15,y-9,7,3,suit); px(x-16,y-9,3,3,skin); }           // left arm out, pointing at the desk
  else  { ro(x-11,y-10,4,10,suit); px(x-11,y+0,4,3,skin); }         // left arm down
  px(x-3,y-15,6,4,skin);                                            // neck
  ro(x-7,y-28,14,15,skin); px(x-7,y-14,14,1,'rgba(0,0,0,.10)');     // head
  px(x-7,y-28,14,4,hair); px(x-7,y-28,5,7,hair); px(x+5,y-28,2,5,hair); // side-part hair
  px(x-4,y-22,2,1,PAL.outline); px(x+3,y-22,2,1,PAL.outline);       // brows
  px(x-4,y-20,2,2,'#33373e'); px(x+3,y-20,2,2,'#33373e');           // eyes
  px(x-1,y-18,2,1,shade(skin,-.28));                               // nose
  px(x-3,y-16,7,1,shade(skin,-.35));                              // firm mouth
}

// a standing person (kitchen / lounge), facing us
function drawStanding(p, t){
  // celebration dance: little hops + side-to-side wiggle while the flag is live
  let dx0=0, dy0=0;
  if(p.celebrateUntil && performance.now()<p.celebrateUntil){
    const tt=performance.now();
    dy0 = -Math.abs(Math.sin(tt*0.018))*5;     // quick hops
    dx0 = Math.sin(tt*0.013)*3;                // wiggle
  } else if(p.whipUntil && performance.now()<p.whipUntil){
    dx0 = Math.sin(performance.now()*0.06)*2;  // whip: startled shudder (no hop)
  } else if(p.blissUntil && performance.now()<p.blissUntil){
    const tt=performance.now();
    dx0 = Math.sin(tt*0.003 + (p.x||0))*2.2;    // THANK AGENTS: slow, gentle side-to-side sway
    dy0 = -Math.abs(Math.sin(tt*0.004))*1.6;    // soft contented float
  }
  if(performance.now()<angryUntil){ dx0 += Math.sin(performance.now()*0.05 + p.x)*1.6; }  // ANGRY MODE jitter
  // waiting on you: knock on the glass / raise a hand; a snoozed asker relaxes with a coffee
  const askA = (p.kind==='wait' || p.kind==='knock') && isAsking(p.agent) ? p.agent : null;
  const pose = !askA ? '' : (isSnoozed(askA) ? 'relax' : (p.kind==='knock' ? 'knock' : 'raise'));
  const tier = askA ? askTier(askA) : 0;
  if(pose==='knock' && p.knockHit) dx0 += ((p.seed&1)?1:-1)*(1+tier*0.5);    // tap-tap shake
  if((pose==='knock' || pose==='raise') && tier===2) dx0 += Math.sin(performance.now()*0.045 + p.seed)*0.8;
  const x=Math.round(p.x+dx0), y=Math.round(p.y+dy0);
  const f=p.feat||featuresFor(p.id||'x');
  const sk=f.skin, sh=f.shirt, pants=f.pants, shoe='#4a3526';
  const walking=(Math.abs(p.vx)+Math.abs(p.vy))>0.05;
  const step=walking?(Math.floor(t*0.16)&1):0;
  // deterministic kitchen "persona": a held item, stable per agent id (salted so it
  // doesn't merely echo the appearance bits featuresFor() already used).
  const kh = hash((p.id||'x')+'|kit');
  const item = (pose==='knock' || pose==='raise') ? -2 : pose==='relax' ? 0
             : (f.messenger || p.kind==='work') ? -1 : (kh % 6);
  //  -2 asking (free left hand, right hand up)  -1 courier/worker(none)  0 mug  1 pastry  2 phone  3 plate  4 bottle  5 hands-free
  const settled = p.kind!=='work' && !walking && p.mode==='idle';
  const now = performance.now();
  const canSip = settled && item===0;                       // only the mug persona sips
  const sip = canSip && (pose==='relax' ? ((now + ((x*197)&2047)*3) % 3400) < 1100
                                        : ((now + ((x*197)&2047)*3) % 5200) < 700);
  // occasional small-talk: face the paired neighbour on a staggered ~4.2s-in-12s window
  const talking = settled && !pose && p.talkX!=null && ((now + (kh%24000)) % 26000) < 2600;  // chat rarely: ~2.6s in every 26s
  const faceDir = talking ? (Math.sign(p.talkX - x)||0) : 0; // -1 look left, +1 look right
  const ht = sip ? -1 : (item===2 ? 1 : 0);                  // sip: tip back; phone: glance down
  const hx = faceDir*2;                                      // subtle head turn toward neighbour
  // shadow
  ctx.fillStyle='rgba(0,0,0,.20)'; ctx.beginPath(); ctx.ellipse(x,y+16,11,3,0,0,Math.PI*2); ctx.fill();
  // legs + rounded shoes (feet stay at ~y+16 to match the hitbox)
  const l1=9+(walking?step:0), l2=9+(walking?(1-step):0);
  ro(x-6, y+4, 5, l1, pants); ro(x+1, y+4, 5, l2, pants);
  px(x-6,y+4,5,1, shade(pants,.18)); px(x+1,y+4,5,1, shade(pants,.18));     // pant sheen
  px(x-2,y+5,1,l1-1, shade(pants,-.20)); px(x+5,y+5,1,l2-1, shade(pants,-.20)); // inner + outer leg shadow
  px(x-8, y+4+l1, 7,3, shoe); px(x-8, y+4+l1, 7,1, shade(shoe,.32));        // left shoe
  px(x,   y+4+l2, 7,3, shoe); px(x,   y+4+l2, 7,1, shade(shoe,.32));        // right shoe
  // torso (soft shaded shirt: top highlight, side + hem shadow, collar, belt)
  ro(x-9, y-11, 18, 16, sh);
  px(x-9,y-11,18,2, shade(sh,.30)); px(x+6,y-10,3,13, shade(sh,-.20)); px(x-9,y+3,18,2, shade(sh,-.16));
  px(x-2,y-11,4,2, shade(sh,-.28));                         // collar notch
  px(x-9,y+4,18,1, shade(pants,-.10));                      // belt/hem line
  torsoDetail(x, y-11, 9, 16, sh, f);                       // outfit variety + sheen
  if(f.messenger){ drawEnvelope(x, y-3); }                  // courier envelope badge
  // ---- arms + the held item (deterministic persona) --------------------------
  const gL = talking && (item===2||item===3 ? false : (faceDir<=0));  // lift left free hand
  const gR = talking && (item===5||item===-1) && faceDir>0;           // hands-free can lift right
  if(item===-2){                                           // asking: left arm down, right hand up
    ro(x-14, y-7, 5, 8, sh); px(x-14, y+1, 4,4, sk);
    if(pose==='knock'){                                    // forearm up, fist toward the glass
      const hit=!!p.knockHit, fs=hit?8:6;
      ro(x+9, y-17, 5, 12, sh);
      px(x+11-fs/2+(hit?1:0), y-24-(hit?1:0), fs, fs, hit ? shade(sk,.12) : sk);
      px(x+11-fs/2+(hit?1:0), y-24-(hit?1:0)+Math.round(fs*0.45), fs, 1, shade(sk,-.25));   // knuckle crease
    } else {                                               // raised hand, a little wave
      const wv = Math.sin(now*[0.004,0.008,0.014][tier] + p.seed) > 0 ? 1 : -1;
      ro(x+9, y-27, 5, 18, sh);
      px(x+9+wv, y-33, 5, 6, sk); px(x+9+wv, y-35, 1, 2, sk); px(x+11+wv, y-36, 1, 3, sk); px(x+13+wv, y-35, 1, 2, sk);
    }
  } else if(item===0){                                     // coffee mug (+ steam / sip)
    ro(x-14, y-7-(gL?4:0), 5, 7, sh); px(x-14, y-1-(gL?4:0), 5,4, sk);
    const ay = sip?-4:0, my = sip?-6:0;
    ro(x+9, y-9+ay, 5, 7, sh); px(x+9, y-3+ay, 5,3, sk);
    ro(x+10, y-13+my, 7, 7, PAL.paper); px(x+11,y-12+my,5,5,PAL.mugA); px(x+17,y-12+my,2,4,PAL.paper);
    if(!sip){ for(let i=0;i<3;i++){ const yy=y-15-((t*1.1+i*5)%8); px(x+13,yy,1,2,'rgba(255,255,255,.5)'); } }
  } else if(item===1){                                     // pastry / muffin in the right hand
    ro(x-14, y-7-(gL?4:0), 5, 7, sh); px(x-14, y-1-(gL?4:0), 5,4, sk);
    ro(x+9, y-6, 5, 6, sh); px(x+9, y-1, 5,3, sk);
    px(x+9,y-4,6,4,PAL.orange); px(x+9,y-4,6,1,shade(PAL.orange,.34)); px(x+11,y-2,2,1,shade(PAL.orange,-.3));
    px(x+9,y-1,6,1,'#c98a52');                             // pastry base
  } else if(item===2){                                     // phone in both hands, glancing down
    ro(x-13, y-6, 5, 7, sh); px(x-11, y-1, 4,3, sk);
    ro(x+9,  y-6, 5, 7, sh); px(x+7,  y-1, 4,3, sk);
    px(x-3,y-3,7,5,'#20242c'); px(x-2,y-2,5,3,'#7fd3e0'); px(x-2,y-2,5,1,'#b8ecf3'); // phone + lit screen
  } else if(item===3){                                     // plate of food in both hands
    ro(x-13, y-5, 5, 6, sh); px(x-11, y-1, 4,3, sk);
    ro(x+9,  y-5, 5, 6, sh); px(x+7,  y-1, 4,3, sk);
    px(x-6,y-2,13,3,'#eef0f4'); px(x-6,y-2,13,1,'#ffffff'); px(x-6,y+1,13,1,'#c9ccd4'); // plate
    px(x-3,y-3,3,2,PAL.orange); px(x+1,y-3,3,2,'#6aa72f'); // two bites of food
  } else if(item===4){                                     // water bottle / soda in the right hand
    ro(x-14, y-7-(gL?4:0), 5, 7, sh); px(x-14, y-1-(gL?4:0), 5,4, sk);
    ro(x+9, y-7, 5, 7, sh); px(x+9, y-1, 5,3, sk);
    px(x+9,y-11,5,9,PAL.mugB); px(x+9,y-11,5,1,shade(PAL.mugB,.4)); px(x+13,y-11,1,9,shade(PAL.mugB,-.3));
    px(x+10,y-13,3,2,'#dfeefa');                           // cap
  } else {                                                 // item 5 / courier / worker: free hands
    ro(x-14, y-7-(gL?4:0), 5, 8, sh); px(x-14, y+1-(gL?4:0), 4,4, sk);
    ro(x+10, y-7-(gR?4:0), 5, 8, sh); px(x+10, y+1-(gR?4:0), 4,4, sk);
  }
  // neck + head (tips back while sipping / down on the phone; turns toward a chat neighbour)
  px(x-3+hx, y-14+ht, 6, 4, sk); px(x-3+hx, y-14+ht, 6, 1, 'rgba(0,0,0,.16)');
  ro(x-7+hx, y-27+ht, 14, 15, sk);
  px(x-7+hx,y-13+ht,14,1,'rgba(0,0,0,.10)');               // soft jaw shade
  drawHairAcc(x+hx, y-25+ht, f); drawFace(x+hx, y-25+ht, f);
  if(performance.now()<angryUntil) drawAngryFace(x+hx, y-25+ht, f);
  // small-talk bubble while chatting, else the cozy heart when settled
  if(settled && !pose){
    if(talking){ const nd=1+((((now/700)|0)+(kh%3))%3); talkBubble(x + (faceDir<0?-15:15), y-34, nd); }
    else heartBubble(x+15, y-34);
  }
}

// ---- update loop ----
let last=performance.now(), tCount=0;
const WALK_PXPS = 80;   // constant walk speed -> a room crossing takes ~2-4s
function tick(now){
  const dt=Math.min(40, now-last); last=now; tCount+= dt*0.06;
  const L=layout();
  const step = WALK_PXPS * dt/1000;   // distance to advance this frame
  // advance + expire confetti particles
  if(confetti.length){
    const ds=dt/1000;
    for(let i=confetti.length-1;i>=0;i--){ const c=confetti[i]; c.age+=ds;
      if(c.age>=c.life){ confetti.splice(i,1); continue; }
      c.vy+=c.g*ds; c.x+=c.vx*ds; c.y+=c.vy*ds; c.vx*=0.99; c.rot+=c.vr*ds;
    }
  }
  // advance + expire water-cooler droplets (simple gravity arc)
  if(waterFx.length){
    const ds=dt/1000;
    for(let i=waterFx.length-1;i>=0;i--){ const d=waterFx[i]; d.age+=ds;
      if(d.age>=d.life){ waterFx.splice(i,1); continue; }
      d.vy+=d.g*ds; d.x+=d.vx*ds; d.y+=d.vy*ds;
    }
  }
  // Godzilla: advance the walk, and auto-summon once when the local clock rolls to a new hour
  if(godzilla.active){ godzilla.t += dt/GODZILLA_MS; if(godzilla.t>=1){ godzilla.active=false; godzilla.t=0; } }
  { const d=new Date(), key=d.toDateString()+'#'+d.getHours();
    if(godzillaHourKey===null) godzillaHourKey=key;
    else if(key!==godzillaHourKey){ godzillaHourKey=key; triggerGodzilla(); } }
  // THANK AGENTS: keep a steady curtain of petals falling from the top for the rain window
  // (~10s), on top of the initial burst -- spawn a small batch a few times a second (capped).
  if(now<flowerRainUntil && now-lastFlowerAt>140){ lastFlowerAt=now; spawnFlowers(null,null,14); }
  // THANK AGENTS: advance + expire flower confetti (soft gravity + a slow horizontal sway)
  if(flowers.length){
    const ds=dt/1000;
    for(let i=flowers.length-1;i>=0;i--){ const fl=flowers[i]; fl.age+=ds;
      if(fl.age>=fl.life){ flowers.splice(i,1); continue; }
      fl.vy+=fl.g*ds; fl.x+=fl.vx*ds; fl.y+=fl.vy*ds; fl.vx*=0.99; fl.rot+=fl.vr*ds;
    }
  }
  // THANK AGENTS: while blissful, drip in a new gratitude message every few seconds (capped),
  // and advance/expire the floating ones (they drift up and fade out on their own).
  if(now<blissUntil && now-lastThankMsgAt>3500){ lastThankMsgAt=now; spawnThankMsg(); }
  if(thankMsgs.length){
    const ds=dt/1000;
    for(let i=thankMsgs.length-1;i>=0;i--){ const m=thankMsgs[i]; m.age+=ds; m.y+=m.vy*ds;
      if(m.age>=m.life) thankMsgs.splice(i,1); }
  }
  // advance + expire whip-crack particles (streaks decelerate; the lash line just fades)
  if(whipFx.length){
    const ds=dt/1000;
    for(let i=whipFx.length-1;i>=0;i--){ const c=whipFx[i]; c.age+=ds;
      if(c.age>=c.life){ whipFx.splice(i,1); continue; }
      if(!c.lash){ c.x+=c.vx*ds; c.y+=c.vy*ds; c.vx*=0.90; c.vy*=0.90; }
    }
  }
  // ANGRY MODE: while furious, agents hurl poop toward the viewer at a steady, throttled
  // cadence. Projectiles fly + grow (advanced in render from their eased progress); when
  // one lands it becomes a splat decal. Nothing new spawns once the 3-min deadline passes.
  if(now<angryUntil && now-lastPoopAt>240){
    lastPoopAt=now;
    const throwers=people.filter(p=>p.kind!=='beach' && p.mode!=='drown' && !p.dead && p.x!=null);
    const nThrow=throwers.length ? (1 + (Math.random()<0.55?1:0)) : 0;   // a few per second total
    for(let k=0;k<nThrow;k++){
      const p=throwers[(Math.random()*throwers.length)|0];
      spawnPoop(Math.round(p.x), Math.round(p.y)-Math.round(34*SC));
    }
  }
  // advance + expire poop projectiles (progress eases in -> accelerate toward the glass; splat on land)
  if(poop.length){
    const ds=dt/1000;
    for(let i=poop.length-1;i>=0;i--){ const q=poop[i]; q.t+=ds/q.dur; q.rot+=q.vr*ds;
      if(q.t>=1){ spawnPoopSplat(q.tx, q.ty, q.size1, q.rot); poop.splice(i,1); }
    }
  }
  // advance + expire poop splats (screen-space decals that linger, then fade out)
  if(poopSplats.length){
    const ds=dt/1000;
    for(let i=poopSplats.length-1;i>=0;i--){ const s=poopSplats[i]; s.age+=ds;
      if(s.age>=s.life) poopSplats.splice(i,1); }
  }
  if(glassTaps.length){
    const ds=dt/1000;
    for(let i=glassTaps.length-1;i>=0;i--){ glassTaps[i].age+=ds; if(glassTaps[i].age>=glassTaps[i].life) glassTaps.splice(i,1); }
  }
  // restock vending slots whose can has finished dropping + resting
  for(const k in vendDrops){ if(now-vendDrops[k].start>3200) delete vendDrops[k]; }
  for(const p of people){
    if(p.mode==='drown'){
      // beach easter egg: after a small staggered delay, march straight into the sea,
      // then sink (handled visually in drawDrowning). p.dead -> reaped after the loop.
      if(now>=p.drownStart){
        if(!p.sinking){
          const dx=p.drownTo.x-p.x, dy=p.drownTo.y-p.y, dist=Math.hypot(dx,dy);
          if(dist<=step+0.5){ p.x=p.drownTo.x; p.y=p.drownTo.y; p.sinking=true; p.sinkStart=now; p.sinkT=0; }
          else { p.vx=dx/dist; p.vy=dy/dist; p.x+=p.vx*step; p.y+=p.vy*step; }
        } else {
          // progress computed once here (single clock) so the draw side never sees a stray
          // negative -> a negative ellipse radius would throw and kill the whole rAF loop.
          p.sinkT = Math.min(1, (now-p.sinkStart)/DROWN_SINK_MS);
          if(p.sinkT>=1){ p.dead=true; }
        }
      }
      continue;
    }
    if(p.kind==='exit'){
      // a filtered-out scheduled agent walking off the bottom of the screen
      const dx=p.exitX-p.x, dy=p.exitY-p.y, dist=Math.hypot(dx,dy);
      if(dist>0.5){ p.vx=dx/dist; p.vy=dy/dist; p.x+=p.vx*step; p.y+=p.vy*step; }
      else { p.vx=p.vy=0; }
      continue;
    }
    if(p.kind==='work'){
      if(p.seated){ p.x=p.deskX; p.y=p.deskY; p.vx=p.vy=0; }
      else {
        // walk in from wherever it was (e.g. the kitchen) up to the desk, then sit
        const dx=p.deskX-p.x, dy=p.deskY-p.y, dist=Math.hypot(dx,dy);
        if(dist<=step+0.5){ p.x=p.deskX; p.y=p.deskY; p.seated=true; p.vx=p.vy=0; }
        else { p.vx=dx/dist; p.vy=dy/dist; p.x+=p.vx*step; p.y+=p.vy*step; }
      }
    } else {
      // walk once to the assigned spot, then stand still so it's easy to hover
      if(p.mode!=='idle'){
        const dx=p.home.x-p.x, dy=p.home.y-p.y, dist=Math.hypot(dx,dy);
        if(dist<=step+0.5){ p.x=p.home.x; p.y=p.home.y; p.mode='idle'; p.vx=p.vy=0; }
        else { p.vx=dx/dist; p.vy=dy/dist; p.x+=p.vx*step; p.y+=p.vy*step; }
      } else { p.vx=p.vy=0; }
      // clamp once settled (lets cross-room walks pass through first). Beach agents
      // stay on the sand (right of BEACH_X, clear of the water); kitchen agents stay
      // to the left of the divider.
      if(p.kind==='knock'){
        // tap-tap ... pause, faster per escalation tier; each tap onset leaves a glass ripple
        p.knockHit=false;
        if(p.mode==='idle' && !isSnoozed(p.agent)){
          const tier=askTier(p.agent), per=[1500,950,560][tier];
          const ph=(now + (p.seed%997)) % per, u=ph/per;
          p.knockHit = u<0.09 || (u>=0.2 && u<0.29);
          const key=Math.floor((now + (p.seed%997))/per)*2 + (u>=0.2?1:0);
          if(p.knockHit && key!==p.lastTapKey){
            p.lastTapKey=key;
            const s=pscale(p);
            spawnGlassTap(p.x + 12*s, p.y - 21*s, tier, u>=0.2);
          }
        }
      } else if(p.mode==='idle'){
        if(p.kind==='beach'){
          p.x=Math.max(BEACH_X+16, Math.min(SHORE_X-16, p.x));   // stay on the sand, clear of the ocean
        } else {
          p.x=Math.max(L.kitchen.x+18, Math.min(BEACH_X-18, p.x));
        }
        p.y=Math.max(L.kitchenTop+44,Math.min(H-20,p.y));
      }
    }
  }
  // reap agents that have finished going under: hide them (until active again) & clear the
  // beach flag. Stamp = the agent's mtime now, so any later write resurfaces it.
  if(people.some(p=>p.dead)){
    let n=0;
    for(const p of people){ if(p.dead){
      drownedInfo[p.id] = (p.agent && typeof p.agent.mtime==='number') ? p.agent.mtime : (Date.now()/1000);
      finishedIds.delete(p.id); n++;
    } }
    people = people.filter(p=>!p.dead);
    if(n){ saveDrowned(); saveFinished(); }
  }
  updateAmbient(now, dt);
  render(tCount);
  requestAnimationFrame(tick);
}

// is a supervisor currently delivering an instruction to this agent? while so, the boss is
// the one "talking" -- the agent's own speech bubble is suppressed so they don't both pop one.
function bossActive(id){ const b=bossVisits[id]; return !!(b && b.until>performance.now()); }

// ============================ HOLIDAY THEMES =================================
// The live office auto-themes around holidays (see holiday_active() in the backend).
// `activeHolidays` is the list of theme names currently in window; here we render the
// decorations. Everything is PURE SCENERY -- never hit-tested, never clickable (just
// like the ambient dog/cat/plane) -- so hover/click/walking/FX are untouched. All props
// are drawn in drawHolidayBack() BEFORE the desks, so desks + agents paint on top of
// them; the falling "weather" is a light overlay drawn last. Kept sound-free.

// a swagged string of holiday lights hung along the back wall, with gently twinkling bulbs
function drawLightString(topY, bulbCols, t){
  const seg=66, n=Math.ceil(W/seg);
  ctx.save(); ctx.strokeStyle='rgba(40,35,30,.45)'; ctx.lineWidth=1;
  for(let i=0;i<n;i++){
    const x0=i*seg, x1=Math.min(W,(i+1)*seg), mx=(x0+x1)/2, dip=topY+11;
    ctx.beginPath(); ctx.moveTo(x0,topY); ctx.quadraticCurveTo(mx,dip,x1,topY); ctx.stroke();
    const col=bulbCols[i%bulbCols.length];
    const on=((Math.floor(t*0.05)+i)%5)!==0;        // most bulbs lit, an occasional dark one
    if(on){ ctx.globalAlpha=.3; px(mx-2,dip-2,5,6,col); ctx.globalAlpha=1;
            px(mx-1,dip-1,3,5,col); px(mx-1,dip-1,1,1,'#ffffff'); }
    else  { px(mx-1,dip-1,3,5,shade(col,-.5)); }
  }
  ctx.restore();
}

// --- Halloween: jack-o-lanterns, cobwebs, bats ---
function drawPumpkin(x,by){
  const o='#e07a2f', od='#b85e20', oh='#f0a24d';
  px(x-9,by-10,18,12,o); px(x-11,by-7,22,6,o);          // squat body (wide middle)
  px(x-9,by-10,18,2,oh); px(x-11,by-1,22,2,od);
  px(x-4,by-10,1,13,od); px(x+3,by-10,1,13,od);          // ribs
  px(x-1,by-13,3,4,'#5a7a3a');                           // stem
  px(x-6,by-6,3,3,'#1a1208'); px(x+3,by-6,3,3,'#1a1208');// triangle eyes
  px(x-5,by-1,10,2,'#1a1208'); px(x-5,by-3,2,2,'#1a1208'); px(x+3,by-3,2,2,'#1a1208'); // jagged grin
  ctx.save(); ctx.globalAlpha=.5;                         // inner candle glow
  px(x-6,by-6,3,3,'#ffcf6b'); px(x+3,by-6,3,3,'#ffcf6b'); px(x-5,by-1,10,2,'#ffcf6b'); ctx.restore();
}
function drawCobweb(cx,cy,flip){
  ctx.save(); ctx.strokeStyle='rgba(232,232,242,.42)'; ctx.lineWidth=1;
  const dir=flip?-1:1, R=[10,19,28,37];
  for(let a=0;a<=4;a++){ const ang=a/4*(Math.PI/2);
    ctx.beginPath(); ctx.moveTo(cx,cy); ctx.lineTo(cx+dir*Math.cos(ang)*38, cy+Math.sin(ang)*38); ctx.stroke(); }
  for(const r of R){ ctx.beginPath();
    for(let a=0;a<=8;a++){ const ang=a/8*(Math.PI/2), vx=cx+dir*Math.cos(ang)*r, vy=cy+Math.sin(ang)*r;
      if(a===0) ctx.moveTo(vx,vy); else ctx.lineTo(vx,vy); } ctx.stroke(); }
  ctx.restore();
}
function drawBat(x,y,flap){
  const c='#15101c';
  px(x-1,y,3,4,c); px(x-1,y-2,3,2,c);                    // little body + ears
  if(flap){ px(x-6,y-1,5,2,c); px(x+2,y-1,5,2,c); px(x-8,y-2,2,1,c); px(x+6,y-2,2,1,c); }
  else    { px(x-6,y+1,5,2,c); px(x+2,y+1,5,2,c); px(x-8,y+2,2,1,c); px(x+6,y+2,2,1,c); }
}
function drawBats(t){
  for(let i=0;i<5;i++){
    const prog=((t*0.004 + i*0.21)%1), x=prog*(W+40)-20, y=38+i*15+Math.sin(t*0.02+i)*9;
    drawBat(x|0, y|0, (Math.floor(t*0.1)+i)&1);
  }
}

// --- Christmas: tree + gifts, snow ---
function triFill(cx, topY, h, halfBase, col){
  for(let i=0;i<h;i++){ const w=Math.max(1,Math.round(halfBase*2*(i+1)/h));
    px(cx-Math.floor(w/2), topY+i, w, 1, col); }
}
// A big, lush Christmas tree: four shaded tiers, a glowing beaded garland that spirals the
// tree, twinkling multi-colour lights, hanging ornaments, a bright animated topper star and
// a little pile of wrapped gifts at the base. `t` drives the twinkle so it feels alive.
function drawXmasTree(x, by, t, s){
  s = s || 1;                                                        // `s` scales the whole tree up about its base (x,by)
  ctx.save();
  if(s!==1){ ctx.translate(x, by); ctx.scale(s, s); ctx.translate(-x, -by); } // grow taller/wider while staying planted on the floor
  // sturdy trunk with a pot/stand
  px(x-5, by-10, 10, 12, '#6b3f22'); px(x-5,by-10,10,2,'#7d4f2a'); px(x-5,by,10,2,'#54301a');
  ro(x-11, by, 22, 6, '#8a2f2f'); px(x-11,by,22,2,'#b44545');                 // red tree-stand/skirt
  const g='#2f7a3c', gD='#236030', gH='#3f9a4c';
  // four cascading tiers (top -> bottom), each wider than the one above
  triFill(x, by-80, 13, 16, gD); triFill(x, by-80, 13, 15, g);
  triFill(x, by-62, 17, 22, gD); triFill(x, by-62, 17, 21, g);
  triFill(x, by-42, 20, 26, gD); triFill(x, by-42, 20, 25, g);
  triFill(x, by-20, 22, 30, gD); triFill(x, by-20, 22, 29, g);
  // snow dusting on the front of each tier
  ctx.save(); ctx.globalAlpha=.55;
  triFill(x, by-80, 4, 4, '#ffffff'); triFill(x, by-62, 4, 7, '#eef4ff');
  triFill(x, by-42, 4, 10, '#eef4ff'); triFill(x, by-20, 4, 13, '#eef4ff');
  ctx.restore();
  // a few lighter needle highlights so the tiers aren't flat
  ctx.save(); ctx.globalAlpha=.4;
  for(let i=0;i<22;i++){ const ty=by-78+((i*53)%74), hw=2+((i*13)%6);
    px(x-hw, ty, hw*2, 1, gH); }
  ctx.restore();
  // spiralling bead garland (gold) -- a zig-zag down the tree
  const garC='#f2dd88';
  for(let i=0;i<30;i++){ const ty=by-76+i*2.6, sw=4+(ty-(by-80))*0.26;
    const gx=x+Math.sin(i*0.9)*sw; px(gx|0, ty|0, 2,1, garC); }
  // twinkling lights: warm + multi-colour, a slow per-bulb blink off the clock
  const lc=['#ffdf6b','#ff5a5a','#5ab0ff','#5ae07a','#ff8ad0'];
  for(let i=0;i<30;i++){
    const ang=i*2.3, ty=by-76+((i*37)%92), sw=4+(ty-(by-80))*0.24;
    const lx=x+Math.cos(ang)*sw, col=lc[i%lc.length];
    const on=((Math.floor(t*0.18)+i)%3)!==0;                           // most lit, some winking off
    if(on){ ctx.save(); ctx.globalAlpha=.4; px((lx-1)|0,(ty-1)|0,4,4,col); ctx.restore();
            px(lx|0, ty|0, 2,2, col); px(lx|0, ty|0, 1,1, '#ffffff'); }
    else  { px(lx|0, ty|0, 2,2, shade(col,-.55)); }
  }
  // bigger hanging ornament baubles with a highlight dot
  const oc=['#e23b3b','#f0c33b','#3fa0e0','#e673a8','#b54fd0','#ffffff'];
  const orn=[[-14,-24],[11,-30],[-9,-46],[8,-50],[-5,-64],[6,-66],[0,-36],[-16,-10],[13,-12],[-2,-74]];
  for(let i=0;i<orn.length;i++){ const ox=x+orn[i][0], oy=by+orn[i][1], c=oc[i%oc.length];
    px(ox-1,oy-2,2,1,'#d4af37');                                       // cap
    ro(ox-2, oy, 4,4, c); px(ox-1,oy,1,1,shade(c,.5)); }
  // animated topper star with a soft glow pulse
  const pulse=0.5+0.5*Math.sin(t*0.12), sy=by-92;
  ctx.save(); ctx.globalAlpha=.35+0.25*pulse; px(x-4,sy-1,10,6,'#ffe066'); px(x-1,sy-5,4,14,'#ffe066'); ctx.restore();
  px(x-1,sy-4,2,12,'#ffe066'); px(x-5,sy+2,12,2,'#ffe066');            // star arms
  px(x-3,sy,6,6,'#fff6b0'); px(x-1,sy+1,2,2,'#ffffff');                 // bright core
  // a little pile of wrapped gifts tucked under the tree
  ro(x+13, by-2, 13, 10, '#c0392b'); px(x+13,by-2,13,2,'#e05a4d'); px(x+18,by-2,2,10,'#f0c33b'); px(x+16,by-4,6,2,'#f0c33b');
  ro(x-29, by, 11, 8, '#2f74d6'); px(x-25,by,1,8,'#ffd84d'); px(x-29,by,11,2,'#5a9ae0');
  ro(x-15, by+1, 9, 7, '#2f8a4c'); px(x-11,by+1,1,7,'#ffffff'); px(x-15,by+1,9,2,'#49a86a');
  ctx.restore();
}
function drawSnow(t, col){
  ctx.save();
  for(let i=0;i<70;i++){
    const sp=0.4+((i*7)%10)/10*0.6;
    const y=((t*sp*6 + i*53) % (H+20)) - 10;
    const x=((i*97)%W) + Math.sin((t*0.01)+i)*6;
    const big=(i%4===0);
    ctx.globalAlpha=0.5+((i%3)*0.16);
    px(x|0, y|0, big?2:1, big?2:1, col);
  }
  ctx.restore();
}

// --- Hanukkah: a big, colourful menorah that lights the correct number of candles for
// tonight (`lit` = the night 1..8, computed server-side), PLUS the raised central shamash
// which is always lit. Unlit candles read clearly dark; lit ones carry a warm glowing flame.
// A single lit flame per candle; `t` drives a gentle per-flame flicker.
function drawMenorah(x, by, lit, t, s){
  s = s || 1;                                                        // `s` scales the whole menorah up about its base (x,by)
  ctx.save();
  if(s!==1){ ctx.translate(x, by); ctx.scale(s, s); ctx.translate(-x, -by); } // grow branches/candles/flames together, still planted on the floor
  const gold='#d4af37', goldH='#f2dd88', goldD='#9c7d1f';
  // ornate base: stepped foot + stem + arm bar, all with a top highlight + lower shadow line
  px(x-26,by+2,52,5,goldD); px(x-22,by-3,44,6,gold); px(x-22,by-3,44,1,goldH);  // foot
  px(x-4,by-30,8,28,gold); px(x-4,by-30,2,28,goldH); px(x+2,by-30,2,28,goldD);  // central stem
  px(x-30,by-30,60,3,gold); px(x-30,by-30,60,1,goldH); px(x-30,by-27,60,1,goldD); // arm bar
  // the eight branch candles (i=-4..-1 and 1..4) + the raised shamash (i=0)
  const candC=['#d94f4f','#4f7fd9','#49a86a','#e0b23a','#b45fd0','#e07aae','#4fbfc0','#e08a3a'];
  // on night `lit` we kindle `lit` candles. Fill from the right arm inward (i=4,3,2,1 then
  // -1,-2,-3,-4) so night 1 is a single candle and night 8 lights them all.
  const order=[4,3,2,1,-1,-2,-3,-4];
  const onSet={}; for(let k=0;k<lit && k<order.length;k++) onSet[order[k]]=true;
  for(let i=-4;i<=4;i++){
    const cx=x+i*6, isSham=(i===0), extra=isSham?10:0, cup=by-30;
    const on=isSham || !!onSet[i];
    px(cx-2, cup-6-extra, 4, 7+extra, gold); px(cx-2,cup-6-extra,1,7+extra,goldH); // riser/cup
    const cc=isSham?'#f2f2e0':candC[(i+4)%candC.length];                          // coloured candle
    px(cx-2, cup-11-extra, 5, 5, cc); px(cx-2, cup-11-extra, 5, 1, shade(cc,.4)); // candle wax
    px(cx+2, cup-10-extra, 1, 4, shade(cc,-.3));                                   // candle shadow edge
    if(on){                                                                       // warm glowing flame
      const fl=(Math.floor(t*0.14)+i+4)%2;
      ctx.save(); ctx.globalAlpha=.4; px(cx-2, cup-17-extra-fl, 5, 7, '#ffcf6b'); ctx.restore(); // halo
      px(cx-1, cup-15-extra-fl, 3, 5, '#f0a93a'); px(cx-1, cup-16-extra-fl, 3, 2, '#ffe066');
      px(cx, cup-17-extra-fl, 1, 1, '#fff6d6');                                    // hot tip
    } else {
      px(cx-1, cup-13-extra, 3, 2, '#2a2a30');                                     // unlit wick stub
    }
  }
  ctx.restore();
}
function drawDreidel(x,y){
  px(x-4,y,8,8,'#2f74d6'); px(x-4,y,8,1,'#5a9ae0'); px(x-4,y+7,8,1,'#1f3f8c'); // body
  px(x-1,y-4,2,4,'#3f64c0');                                                     // handle
  px(x-2,y+8,4,1,'#1f3f8c'); px(x-1,y+9,2,2,'#1f3f8c');                          // point
  px(x-1,y+2,2,4,'#ffd84d'); px(x-2,y+3,1,2,'#ffd84d');                          // painted letter
}
// a spinning dreidel for the swirl overlay: `squash` (0..1) narrows the body to fake a
// fast spin, `col` picks the body colour. Same silhouette as the static one, drawn about (x,y).
function drawSpinDreidel(x,y,squash,col,colH,colD){
  const hw=Math.max(1, Math.round(4*squash));                                     // half-width (spins thin<->wide)
  px(x-hw,y,hw*2,8,col); px(x-hw,y,hw*2,1,colH); px(x-hw,y+7,hw*2,1,colD);         // body
  px(x-1,y-4,2,4,colH);                                                           // handle
  px(x-2,y+8,4,1,colD); px(x-1,y+9,2,2,colD);                                     // point
  if(hw>=3){ px(x-1,y+2,2,4,'#ffd84d'); px(x-2,y+3,1,2,'#ffd84d'); }              // painted letter (when facing us)
}

// --- Thanksgiving: turkey + autumn leaves ---
function drawTurkey(x,by){
  const body='#7a4a28', bodyH='#9a6238', bodyD='#5e3820';
  const fc=['#c0392b','#e07a2f','#e3b021','#d98f2a','#b85e20'];
  for(let i=0;i<5;i++){ const dx=(i-2)*7; px(x+dx-2, by-30, 4, 16, fc[i]); px(x+dx-2,by-30,4,2,shade(fc[i],.3)); } // tail fan
  px(x-7, by-16, 14, 14, body); px(x-7,by-16,14,2,bodyH); px(x-7,by-4,14,2,bodyD);  // body
  px(x-1, by-24, 4, 9, body); px(x-2, by-27, 6, 4, body);                           // neck + head
  px(x, by-25, 2,2, '#1a1208'); px(x+4, by-25, 3,2, '#e3b021'); px(x+2, by-22, 2,3, '#c0392b'); // eye/beak/wattle
  px(x-4, by-2, 2,3, '#e3b021'); px(x+2, by-2, 2,3, '#e3b021');                      // feet
}
function drawLeafPile(x,by){
  const lc=['#c0392b','#e07a2f','#e3b021','#b85e20'];
  for(let i=0;i<9;i++){ const lx=x+((i*53)%44)-22, ly=by-((i*29)%9);
    px(lx,ly,3,2,lc[i%4]); px(lx+1,ly-1,1,1,shade(lc[i%4],.3)); }
}
function drawFallLeaves(t){
  const lc=['#c0392b','#e07a2f','#e3b021','#b85e20'];
  ctx.save();
  for(let i=0;i<22;i++){
    const sp=0.5+((i*13)%10)/10*0.7;
    const y=((t*sp*5 + i*71) % (H+20)) - 10;
    const x=((i*101)%W) + Math.sin((t*0.015)+i)*14;
    ctx.globalAlpha=0.65;
    px(x|0, y|0, 3, 2, lc[i%4]);
  }
  ctx.restore();
}
// --- Thanksgiving centerpiece: a BIG golden roast turkey on a silver platter, sitting
// on the kitchen lounge table. `by` is the platter's resting line on the table surface.
// Drawn after the table (in drawHolidayBack) so it reads as the holiday centerpiece. ---
function drawRoastTurkey(cx, by, t){
  const el=(ex,ey,rx,ry,col)=>{ ctx.fillStyle=col; ctx.beginPath(); ctx.ellipse(ex,ey,rx,ry,0,0,Math.PI*2); ctx.fill(); };
  // silver platter (shadow + dish + rim highlight + inner well)
  el(cx, by+5, 36, 7, 'rgba(0,0,0,.20)');                                   // floor/table shadow
  el(cx, by+2, 35, 8, '#b7bcc4'); el(cx, by, 33, 7, '#d8dbe1');             // dish body + rim
  el(cx, by-1, 29, 5, '#eef0f3'); el(cx, by+1, 24, 4, '#aeb3bb');           // rim sheen + inner well
  // garnish tucked around the base: parsley sprigs + cranberries
  for(let i=-3;i<=3;i++){ const gx=cx+i*9; px(gx, by-1, 3,2,'#3f7a3c'); px(gx+1,by-2,1,1,'#5a9a4a'); }
  px(cx-24,by-1,2,2,'#c0392b'); px(cx-12,by-2,2,2,'#c0392b'); px(cx+9,by-2,2,2,'#c0392b'); px(cx+22,by-1,2,2,'#c0392b');
  // roasted body: a big glistening golden-brown mound
  const br='#b5712b', brH='#d59445', brHH='#eab868', brD='#8a5420';
  el(cx, by-5, 25, 15, brD);                                                // underside / shadow tone
  el(cx, by-7, 24, 14, br);                                                 // main body
  el(cx-3, by-10, 18, 9, brH);                                             // upper roast sheen
  el(cx-6, by-13, 9, 4, brHH);                                             // hottest highlight
  px(cx+12, by-9, 7, 8, brD); px(cx+13,by-9,5,2,br);                        // far wing/thigh bulge
  // two drumsticks rising from the body with little white paper frills on the bone tips
  // left drumstick (angled up-left)
  el(cx-15, by-15, 6, 7, br); px(cx-15,by-18,5,3,brH);
  px(cx-19, by-24, 4, 7, br); px(cx-19,by-24,4,2,brH);                      // bone
  px(cx-21, by-27, 8, 4, '#f1efe8'); px(cx-21,by-27,8,1,'#ffffff');         // paper frill
  // right drumstick (angled up-right)
  el(cx+15, by-15, 6, 7, br); px(cx+11,by-18,5,3,brH);
  px(cx+16, by-24, 4, 7, br); px(cx+16,by-24,4,2,brH);                      // bone
  px(cx+14, by-27, 8, 4, '#f1efe8'); px(cx+14,by-27,8,1,'#ffffff');         // paper frill
  // trussing string across the body + a couple of score marks
  px(cx-8, by-9, 16, 1, brD); px(cx-6, by-6, 3,1, brD); px(cx+4, by-6, 3,1, brD);
  // rising steam: three gently wavering dotted plumes (animated off the rAF clock)
  ctx.save();
  for(let s=0;s<3;s++){ const sx0=cx-12+s*12;
    for(let k=0;k<4;k++){ const yy=by-20-k*6-((t*0.6+s*7)%6);
      const sx=sx0+Math.sin(t*0.02+k*0.8+s)*3;
      ctx.globalAlpha=0.30+0.12*((k+1)%3);
      px(sx|0, yy|0, 2, 2, '#ffffff'); }
  }
  ctx.restore();
}

// --- New Year's: fireworks + a hanging banner + confetti ---
// the year being rung in: the nearest Jan 1 (Dec -> next year, Jan -> this year).
function newYearYear(){ const n=new Date(); return n.getMonth()>=6 ? n.getFullYear()+1 : n.getFullYear(); }
// one firework on a launch->burst cycle. prog 0..1: a rising rocket then a bright,
// fading starburst (a hot white core + coloured rays with brighter inner trails).
function drawFirework(cx,cy,prog,col){
  ctx.save();
  if(prog<0.30){                                                   // rising rocket + short trail
    const y=cy + (1-prog/0.30)*72;
    ctx.globalAlpha=0.95; px(cx-1, y|0, 2,3, '#fffbe0');
    ctx.globalAlpha=0.40; px(cx|0, (y+4)|0, 1,5, col);
  } else {                                                         // radial burst that expands + fades
    const p=(prog-0.30)/0.70, n=16, R=4+p*40, fade=Math.max(0,1-p);
    for(let i=0;i<n;i++){ const a=i/n*Math.PI*2, c=Math.cos(a), s=Math.sin(a)*0.92;
      ctx.globalAlpha=fade;        px((cx+c*R)|0,      (cy+s*R)|0,      2,2, col);       // outer spark
      ctx.globalAlpha=fade*0.8;    px((cx+c*R*0.62)|0, (cy+s*R*0.62)|0, 2,2, '#fff6c0'); // inner bright trail
    }
    ctx.globalAlpha=fade;     px(cx-2,cy-2,4,4,'#ffffff');         // hot white core flash
    ctx.globalAlpha=fade*0.5; px(cx-3,cy-3,6,6,col);              // coloured halo around the core
  }
  ctx.restore();
}
function drawFireworks(t){
  const cols=['#f0c33b','#e23b3b','#3fa0e0','#e673a8','#3fae55','#d4af37','#ff9a3c'];
  // [x, y, cycle-length, phase-offset] -- varied periods so bursts overlap organically
  // (a few in the sky at once) rather than all firing in unison.
  const fw=[[W*0.09,56,150,0],[W*0.19,34,178,40],[W*0.29,66,162,96],[W*0.39,44,190,20],
            [W*0.49,58,158,130],[W*0.58,40,172,70],[W*0.67,62,166,110],[W*0.76,36,154,52],
            [W*0.85,60,184,88],[W*0.93,46,168,24]];
  for(let i=0;i<fw.length;i++){
    const prog=((t*0.6 + fw[i][3])%fw[i][2])/fw[i][2];
    drawFirework(fw[i][0]|0, fw[i][1]|0, prog, cols[i%cols.length]);
  }
}
function drawConfetti(t){
  const cc=['#f0c33b','#e23b3b','#3fa0e0','#e673a8','#3fae55','#ffffff','#d4af37'];
  ctx.save();
  for(let i=0;i<48;i++){
    const sp=0.4+((i*11)%10)/10*0.8;
    const y=((t*sp*5 + i*61)%(H+20))-10;
    const x=((i*83)%W)+Math.sin((t*0.02)+i)*10;
    ctx.globalAlpha=0.72;
    px(x|0, y|0, (i%3===0)?3:2, 2, cc[i%cc.length]);
  }
  ctx.restore();
}

// --- Christmas surprise: wrapped gifts periodically POP into the scene, sit a beat, then
// "explode" into a burst of colourful confetti and fade. Pure scenery. State is driven off
// performance.now() deadlines; a hard cap on live gifts (and a fixed particle count each)
// keeps it cheap. ---
const GIFT_COLS=['#e23b3b','#3fae55','#f0c33b','#3fa0e0','#e673a8','#ffffff','#d4af37','#ff9a3c'];
const GIFT_MAX=4, GIFT_PARTS=24;          // hard caps: <=4 live gifts, 24 particles each (<=96)
let xmasGifts=[]; let nextGiftAt=0;
function spawnGift(now){
  // scatter spawn points across the back-wall band just above the desks (clear of the
  // window + inspiration board), so gifts pop against the wall rather than over agents
  const spots=[[W*0.16,100],[W*0.30,86],[W*0.44,104],[W*0.58,88],[W*0.72,106],[W*0.86,92],[W*0.50,112]];
  const s=spots[(Math.random()*spots.length)|0];
  const parts=[];
  for(let i=0;i<GIFT_PARTS;i++) parts.push({a:(i/GIFT_PARTS)*Math.PI*2+Math.random()*0.3,
                                            sp:48+Math.random()*78, col:GIFT_COLS[(Math.random()*GIFT_COLS.length)|0]});
  xmasGifts.push({ x:s[0]|0, y:s[1]|0, wrap:GIFT_COLS[(Math.random()*4)|0],
                   bornAt:now, popAt:now+650+Math.random()*700, doneAt:0, parts });
}
function drawGiftBox(x,y,col,s){
  const w=Math.max(2,Math.round(16*s)), h=Math.max(2,Math.round(15*s)), hw=w>>1;
  ro(x-hw, y-h, w, h, col); px(x-hw, y-h, w, Math.max(1,h*0.34|0), shade(col,.28)); // box + lid sheen
  px(x-1, y-h-3, 2, h+3, '#ffe066');                                                // vertical ribbon
  px(x-hw, y-Math.round(h*0.55), w, 2, '#ffe066');                                  // horizontal ribbon
  px(x-3, y-h-4, 2,2, '#ffd84d'); px(x+1, y-h-4, 2,2, '#ffd84d'); px(x-1,y-h-3,2,1,'#fff2a8'); // bow
}
function drawXmasGifts(){
  const now=performance.now();
  if(now>=nextGiftAt){ if(xmasGifts.length<GIFT_MAX) spawnGift(now); nextGiftAt=now+1600+Math.random()*2600; }
  ctx.save();
  for(let i=xmasGifts.length-1;i>=0;i--){ const g=xmasGifts[i];
    if(now<g.popAt){                                                  // wrapped gift present (scale-in + pre-pop shake)
      const appear=Math.min(1,(now-g.bornAt)/160);
      const near=Math.max(0,(now-(g.popAt-240))/240);                 // 0..1 as it nears the pop
      const sx=Math.sin(now*0.05)*2*near;
      drawGiftBox((g.x+sx)|0, g.y, g.wrap, appear);
    } else {                                                          // exploded: big confetti burst + fade
      if(!g.doneAt) g.doneAt=now+1100;
      if(now>=g.doneAt){ xmasGifts.splice(i,1); continue; }
      const age=(now-g.popAt)/1000, p=(now-g.popAt)/(g.doneAt-g.popAt), fade=Math.max(0,1-p);
      const cy=g.y-7;
      if(p<0.28){ const f=1-p/0.28;                                   // bright central flash
        ctx.globalAlpha=f; px(g.x-5,cy-5,10,10,'#ffffff'); px(g.x-8,cy-8,16,16,'#fff6c0'); ctx.globalAlpha=0.5*f; px(g.x-11,cy-11,22,22,'#ffd84d'); }
      for(const pt of g.parts){
        const dx=Math.cos(pt.a)*pt.sp*age, dy=Math.sin(pt.a)*pt.sp*age + 80*age*age; // radial + gravity
        const x0=(g.x+dx)|0, y0=(cy+dy)|0;
        ctx.globalAlpha=fade*0.5; px((g.x+dx*0.7)|0,(cy+dy*0.7)|0,2,2,'#ffffff');    // inner trail spark
        ctx.globalAlpha=fade;     px(x0,y0,3,3,pt.col); px(x0+1,y0+1,1,1,shade(pt.col,.5)); // bright 3x3 confetti
      }
      ctx.globalAlpha=1;
    }
  }
  ctx.restore();
}

// --- Hanukkah surprise: spinning dreidels periodically swirl across the screen on a wavy
// path, then drift off the far edge and expire. Pure overlay; hard-capped live count. ---
const DREIDEL_COLS=[['#2f74d6','#5a9ae0','#1f3f8c'],['#d94f4f','#f08a8a','#9c2f2f'],
                    ['#d4af37','#f2dd88','#9c7d1f'],['#49a86a','#7fd49a','#2f7047']];
const DREIDEL_MAX=3;
let dreidels=[]; let nextDreidelAt=0;
function drawDreidelSwirl(){
  const now=performance.now();
  if(now>=nextDreidelAt){
    if(dreidels.length<DREIDEL_MAX){
      dreidels.push({ bornAt:now, dur:4200+Math.random()*2800, y0:48+Math.random()*150,
                      dir:(Math.random()<0.5?1:-1), amp:14+Math.random()*22,
                      col:DREIDEL_COLS[(Math.random()*DREIDEL_COLS.length)|0] });
    }
    nextDreidelAt=now+2200+Math.random()*3200;
  }
  ctx.save();
  for(let i=dreidels.length-1;i>=0;i--){ const d=dreidels[i];
    const p=(now-d.bornAt)/d.dur; if(p>=1){ dreidels.splice(i,1); continue; }
    const x=(d.dir>0) ? p*(W+48)-24 : (W+24)-p*(W+48);
    const y=d.y0 + Math.sin(p*Math.PI*4)*d.amp;
    const squash=Math.abs(Math.sin(now*0.02));                        // fake fast spin
    const edge=Math.min(1, p/0.1, (1-p)/0.1);                         // fade in/out at the edges
    ctx.globalAlpha=0.9*edge;
    drawSpinDreidel(x|0, y|0, squash, d.col[0], d.col[1], d.col[2]);
  }
  ctx.restore();
}

// --- New Year: a glowing neon sign that sits on the office WINDOW glass (not the board),
// plus extra party decor (streamers, balloons, sparkles). ---
// neon text with a soft halo + bright core + flicker. (cx,cy) is the text baseline centre.
function neonText(txt, cx, cy, size, col, glow, a){
  ctx.save(); ctx.textAlign='center'; ctx.textBaseline='alphabetic';
  ctx.font=size+'px "Press Start 2P", monospace';
  ctx.globalAlpha=0.30*a; ctx.fillStyle=glow;                         // offset halo
  ctx.fillText(txt,cx-1,cy); ctx.fillText(txt,cx+1,cy); ctx.fillText(txt,cx,cy-1); ctx.fillText(txt,cx,cy+1);
  ctx.globalAlpha=a; ctx.shadowColor=glow; ctx.shadowBlur=7; ctx.fillStyle=col; // blurred neon glow
  ctx.fillText(txt,cx,cy); ctx.shadowBlur=0;
  ctx.globalAlpha=Math.min(1,a+0.1); ctx.fillStyle='#ffffff'; ctx.fillText(txt,cx,cy); // bright hot core
  ctx.restore();
}
function drawNewYearNeon(){
  const now=performance.now();
  let flick=0.82+0.18*Math.sin(now*0.02);                             // gentle breathing glow
  if(((now*0.2|0)%61)===0) flick=0.45;                                // occasional stutter
  const cx=WIN.x+Math.round(WIN.w*0.5);
  // thin neon tube frame hugging the lower window, so the sign reads as mounted on the glass
  ctx.save();
  ctx.globalAlpha=0.5*flick; ctx.strokeStyle='#ff7ad8'; ctx.lineWidth=1;
  ctx.shadowColor='#ff7ad8'; ctx.shadowBlur=6;
  ctx.strokeRect(WIN.x+8, WIN.y+14, WIN.w-16, WIN.h-18); ctx.shadowBlur=0; ctx.restore();
  neonText('HAPPY NEW YEAR', cx, WIN.y+Math.round(WIN.h*0.42), 6, '#67f0ff', '#2fd6ff', flick);
  neonText(String(newYearYear()), cx, WIN.y+Math.round(WIN.h*0.80), 10, '#ffe066', '#ff8ad0', flick);
}
// diagonal party streamers hung from the top corners (back scenery)
function drawStreamers(t){
  const cols=['#ff5a5a','#5ab0ff','#f0c33b','#5ae07a','#e673a8','#d4af37'];
  ctx.save();
  for(let s=0;s<6;s++){
    const fromLeft=(s%2===0), x0=fromLeft?2+s*3:W-2-s*3, col=cols[s%cols.length];
    for(let k=0;k<16;k++){ const prog=k/16;
      const x=x0 + (fromLeft?1:-1)*prog*(28+s*5);
      const y=2 + prog*(40+s*4) + Math.sin(t*0.05 + s + k*0.5)*2;      // gentle wave
      ctx.globalAlpha=0.8-prog*0.4; px(x|0, y|0, 2,2, col);
    }
  }
  ctx.restore();
}
// a few bobbing balloons tethered in the upper corners (back scenery)
function drawBalloon(x,y,col){
  ro(x-4, y, 8, 10, col); px(x-3,y+1,2,4,shade(col,.45));             // body + sheen
  px(x-1, y+10, 2, 2, shade(col,-.3)); px(x-1, y+12, 1, 6, 'rgba(230,230,240,.6)'); // knot + string
}
function drawBalloons(t){
  const b=[[W*0.09,30,'#ff5a5a'],[W*0.15,24,'#5ab0ff'],[W*0.07,52,'#f0c33b'],
           [W*0.93,28,'#5ae07a'],[W*0.88,22,'#e673a8'],[W*0.95,50,'#d4af37']];
  for(let i=0;i<b.length;i++){ const bob=Math.sin(t*0.06+i*1.3)*3;
    drawBalloon(b[i][0]|0, (b[i][1]+bob)|0, b[i][2]); }
}
// twinkling sparkles scattered high in the scene (overlay)
function drawSparkles(t){
  ctx.save();
  for(let i=0;i<26;i++){
    const x=(i*97)%W, y=10+((i*53)%120);
    const tw=0.5+0.5*Math.sin(t*0.2 + i*1.7);
    if(tw<0.35) continue;
    ctx.globalAlpha=tw; const c=(i%3===0)?'#ffe066':(i%3===1)?'#67f0ff':'#ffffff';
    px(x,y,1,1,c); px(x-1,y,1,1,c); px(x+1,y,1,1,c); px(x,y-1,1,1,c); px(x,y+1,1,1,c); // little plus-spark
  }
  ctx.restore();
}

// background holiday decor: a single ambient tint (from the nearest holiday) + each active
// theme's always-visible light string and corner centerpiece. Drawn before the desks.
function drawHolidayBack(t){
  if(!activeHolidays.length) return;
  const L=layout(), by=L.kitchenTop-6, night=(skyMode()==='night');
  const tints={ halloween:[60,28,78], thanksgiving:[196,112,40], christmas:[120,150,205], hanukkah:[60,95,190], newyear:[40,52,120] };
  const tc=tints[activeHolidays[0]];                                  // nearest holiday drives the tint
  if(tc){ ctx.save();
    ctx.globalAlpha=(activeHolidays[0]==='halloween') ? (night?.22:.14) : (night?.14:.09);
    ctx.fillStyle='rgb('+tc[0]+','+tc[1]+','+tc[2]+')'; ctx.fillRect(0,0,W,L.kitchenTop); ctx.restore(); }
  activeHolidays.forEach((h,i)=>{
    const ly=WALL_H-4-i*5;                                            // stack garlands if themes overlap
    if(h==='halloween'){
      drawLightString(ly,['#e07a2f','#8c5fd6'],t);
      drawCobweb(1,WALL_H+1,false); drawCobweb(W-1,WALL_H+1,true);
      drawPumpkin(40,by); drawPumpkin(66,by+2); drawPumpkin(W-42,by);
    } else if(h==='christmas'){
      drawLightString(ly,['#e23b3b','#3fae55','#f0c33b','#3fa0e0'],t);
      drawLightString(ly-3,['#ffdf6b','#ff5a5a','#5ab0ff'],t);         // a second, denser garland
      drawXmasTree(46,by,t,1.6);                                      // big left tree (scaled up 1.6x, nudged into the left corner)
      drawXmasTree(W-38,by+4,t,1.35);                                 // a smaller matching tree on the right (scaled up 1.35x)
    } else if(h==='hanukkah'){
      drawLightString(ly,['#2f74d6','#ffffff','#5a9ae0'],t);
      drawLightString(ly-3,['#ffffff','#5a9ae0','#2f74d6'],t);
      drawMenorah(W-66,by,hanukkahNight,t,1.6); drawDreidel(W-130,by-2); drawDreidel(W-14,by-1);
    } else if(h==='thanksgiving'){
      drawLightString(ly,['#e3b021','#e07a2f','#b85e20'],t);
      drawTurkey(52,by); drawLeafPile(W-58,by); drawLeafPile(118,by+2);
      // the big roast-turkey centerpiece sits on the kitchen lounge table (tx=66, ty=T+150,
      // tw=116 in drawKitchenProps) -- centre it on the table's near surface edge.
      drawRoastTurkey(66+116/2, L.kitchenTop+150+3, t);
    } else if(h==='newyear'){
      drawLightString(ly,['#d4af37','#ffffff','#f0c33b','#bcd4ff'],t);
      drawLightString(ly-3,['#ff7ad8','#67f0ff','#ffe066'],t);        // extra sparkly garland
      drawStreamers(t);                                              // diagonal party streamers in the corners
      drawBalloons(t);                                               // bobbing balloons tethered up high
      drawFireworks(t);                                              // celebratory bursts up in the sky
      drawNewYearNeon();                                             // glowing neon sign on the WINDOW glass
    }
  });
}
// foreground holiday "weather": falling snow / drifting bats / tumbling leaves. Overlay.
function drawHolidayWeather(t){
  if(!activeHolidays.length) return;
  for(const h of activeHolidays){
    if(h==='christmas'){ drawSnow(t,'#ffffff'); drawXmasGifts(); }    // snow + periodic exploding gifts
    else if(h==='hanukkah'){ drawSnow(t,'#bcd4ff'); drawDreidelSwirl(); } // snow + swirling dreidels
    else if(h==='halloween') drawBats(t);
    else if(h==='thanksgiving') drawFallLeaves(t);
    else if(h==='newyear'){ drawConfetti(t); drawSparkles(t); }       // confetti + twinkling sparkles
  }
}
// =============================================================================

function render(t){
  helperHits = [];                   // rebuilt each frame as dwarves are drawn
  workflowHits = [];                 // rebuilt each frame as workflow tents are drawn
  shellHits = [];                    // rebuilt each frame as open-shell terminals are drawn
  listenHits = [];                   // rebuilt each frame as listening glyphs are drawn
  bubbleAnchors = [];                // rebuilt each frame; drawn as an overlay below
  vendSlots = [];                    // rebuilt each frame as the vending slots are drawn
  ctx.setTransform(SS,0,0,SS,0,0);   // map logical 640x576 onto the super-sampled backing
  ctx.clearRect(0,0,W,H);
  drawFloor();
  drawHolidayBack(t);                 // seasonal tint + back-wall / corner decorations
  drawRooms();                        // light "work room" dividers + labels (large grids only)
  // office desks (always shown); seated worker drawn only once docked, otherwise
  // the desk is shown empty and the worker is drawn separately as a walker.
  const bt = performance.now();
  const slots=[...deskSlots].sort((a,b)=>a.y-b.y);
  helperLayout(slots);
  for(const s of slots){ const w=s.worker; const ds=s.scale||SC;
    ctx.save(); scaleAbout(s.x, s.y, ds); drawDeskPod(s.x, s.y, (w&&w.seated)?w:null, t, ds, s); ctx.restore();
    if(w && w.seated && w.bubbleUntil>bt && !bossActive(w.id)) bubbleAnchors.push({x:s.x, y:s.y-30*ds, text:w.bubbleText, start:w.bubbleStart, until:w.bubbleUntil, tool:w.bubbleTool}); }
  // everyone currently standing/walking (kitchen agents + workers still walking in),
  // interleaved with the ambient dog/cat so overlaps sort correctly by y (painter's).
  const drawList=[];
  people.filter(p=> p.kind!=='work' || !p.seated).forEach(p=> drawList.push({y:p.y+(p.kind==='knock'?1000:0), p}));
  if(amb.dog) drawList.push({y:amb.dog.y, dog:amb.dog});
  if(amb.cat) drawList.push({y:amb.cat.y, cat:amb.cat});
  if(amb.turkeys) for(const tk of amb.turkeys) drawList.push({y:tk.y, turkey:tk});
  drawList.sort((a,b)=>a.y-b.y);
  for(const e of drawList){
    if(e.p){ ctx.save(); scaleAbout(e.p.x, e.p.y, pscale(e.p));
      // beach agents sit (with shades + cocktail) once settled; still walk in standing
      if(e.p.mode==='drown' && e.p.sinking) drawDrowning(e.p, e.p.sinkT||0);
      else if(e.p.kind==='beach' && e.p.mode==='idle') drawBeachSitter(e.p,t);
      else drawStanding(e.p,t);
      ctx.restore();
      // a WAITING (kitchen) agent's open background shells float above its head, so a running
      // shell (e.g. a dev server) stays visible after the chat leaves the desk for the kitchen.
      if(e.p.kind==='wait' && e.p.agent && e.p.agent.shells && e.p.agent.shells.length){
        const sh=e.p.agent.shells, m=Math.min(sh.length,3);
        const base = Math.round(e.p.x - ((m-1)*22+17)/2);   // centre the row over the head
        ctx.save(); scaleAbout(e.p.x, e.p.y, SC);
        for(let i=0;i<m;i++){ const slot=m-1-i, sx=base+slot*22, sy=e.p.y-42;
          drawShellWin(sx, sy, t, (hash(e.p.id)+i*5)%997);
          shellHits.push({ x: e.p.x+((sx+8)-e.p.x)*SC, y: e.p.y+((sy+6)-e.p.y)*SC, r: 11*SC, shell: sh[i] }); }
        ctx.restore();
      }
      if(e.p.bubbleUntil>bt && !bossActive(e.p.id) && !askActive(e.p)) bubbleAnchors.push({x:e.p.x, y:e.p.y-34*SC, text:e.p.bubbleText, start:e.p.bubbleStart, until:e.p.bubbleUntil, tool:e.p.bubbleTool}); }
    else if(e.dog) drawDog(e.dog, t);
    else if(e.cat) drawCat(e.cat, t);
    else if(e.turkey) drawTurkeyAny(e.turkey, t);
  }
  if(tkArrows.length || tkFeathers.length || tkPops.length) drawTurkeyFx(bt);
  // supervisor "boss" visits: a stern suited figure delivering a fresh user instruction.
  // The boss ESCORTS the agent -- it appears the moment the instruction lands and walks
  // ALONGSIDE the agent from the kitchen to the desk (trailing the direction of travel),
  // then parks beside the desk once the agent is docked. Drawn after the people pass so it
  // reads as in front of the agent it's walking with.
  for(const id in bossVisits){
    const bv=bossVisits[id]; if(bv.until<=bt) continue;
    const p=people.find(q=>q.id===id); if(!p) continue;
    let bx, by, moving=false;
    if(p.kind==='work' && p.seated){
      bx=p.deskX+46; by=p.deskY-10;                 // parked beside the docked desk (bigger + raised)
    } else {
      const dir=(p.vx<-0.01)?-1:1;                   // stay on the trailing side of the walk
      bx=p.x-dir*22; by=p.y-2;
      moving=(Math.abs(p.vx)+Math.abs(p.vy))>0.02;   // swing the legs only while actually moving
    }
    const bs=SC*1.25;
    const a=Math.min(1,(bt-bv.start)/180, (bv.until-bt)/500);
    ctx.save(); ctx.globalAlpha=Math.max(0,a); scaleAbout(bx, by, bs); drawBoss(bx, by, t, moving); ctx.restore();
    bubbleAnchors.push({x:bx, y:by-30*bs, text:bv.text, start:bv.start, until:bv.until});
  }
  // ---- transient speech bubbles (desk/kitchen agents + subagent/workflow dwarves) ----
  for(const b of bubbleAnchors){
    const rem=b.until-bt; if(rem<=0) continue;
    const fin=Math.min(1,(bt-b.start)/160), fout=Math.min(1, rem/BUBBLE_FADE);
    if(b.tool) drawToolChip(b.x, b.y, b.text, Math.min(fin,fout), b.below);
    else drawBubble(b.x, b.y, b.text, Math.min(fin,fout), b.below);
  }
  for(const p of people){
    if(p.x==null || !p.agent || !(p.agent.listening||[]).length || p.mode==='drown') continue;
    if(!(p.kind==='work' || p.kind==='wait' || p.kind==='knock')) continue;
    drawListenGlyphs(p, bt);
  }
  // "waiting on you" markers (above every sprite + bubble so the chip is always clickable)
  snoozeHits = [];
  for(const p of people){
    if(p.x==null || !(p.kind==='wait' || p.kind==='knock') || p.mode==='drown' || !isAsking(p.agent)) continue;
    drawAskOverlay(p, bt);
  }
  // hover ring (around the drawn sprite, scaled to match the sprite's draw scale)
  if(hover){
    const hs=pscale(hover);
    ctx.strokeStyle='#ffffff'; ctx.lineWidth=2;
    if(hover.kind==='work' && hover.seated) ctx.strokeRect(hover.deskX-24*hs, hover.deskY-33*hs, 48*hs, 56*hs);
    else ctx.strokeRect(Math.round(hover.x)-14*hs, Math.round(hover.y)-31*hs, 28*hs, 51*hs);
  }
  // subtle dot-matrix vignette (kept faint + crisp so text/sprites stay readable)
  if(!render._vig){
    const g=ctx.createRadialGradient(W/2,H*0.46,H*0.34,W/2,H*0.5,H*0.78);
    g.addColorStop(0,'rgba(20,16,28,0)'); g.addColorStop(1,'rgba(20,16,28,0.15)');
    render._vig=g;
  }
  ctx.fillStyle=render._vig; ctx.fillRect(0,0,W,H);
  // celebration confetti, rendered above everything
  for(const c of confetti){
    const a=Math.max(0, 1 - c.age/c.life);
    ctx.save(); ctx.globalAlpha=a; ctx.translate(c.x,c.y); ctx.rotate(c.rot);
    ctx.fillStyle=c.col; ctx.fillRect(-c.w/2,-c.h/2,c.w,c.h); ctx.restore();
  }
  // water-cooler squirt droplets (light-blue teardrops that fade as they fall)
  for(const d of waterFx){
    const a=Math.max(0, 1 - d.age/d.life);
    ctx.globalAlpha=a; ctx.fillStyle='#8fd3ef';
    ctx.beginPath(); ctx.ellipse(d.x, d.y, d.r, d.r*1.4, 0, 0, Math.PI*2); ctx.fill();
  }
  ctx.globalAlpha=1;
  // THANK AGENTS: pastel flower confetti (petals drift + sway), also above everything
  for(const fl of flowers){
    const a=Math.max(0, 1 - fl.age/fl.life);
    const sx=fl.x + Math.sin(fl.age*fl.sway + fl.swayPh)*6;    // gentle horizontal sway
    drawFlower(sx, fl.y, fl.size, fl.rot, fl.col, a);
  }
  // THANK AGENTS: soft hearts floating up over each blissful agent (screen space, one loop/agent)
  {
    const bnow=performance.now();
    for(const p of people){
      if(!(p.blissUntil && bnow<p.blissUntil)) continue;
      if(p.x==null || p.kind==='beach' || p.mode==='drown') continue;
      const seated=(p.kind==='work' && p.seated);
      const hx=seated ? p.deskX : p.x;
      const hy=(seated ? p.deskY-30*pscale(p) : p.y-34*SC);
      const seed=((p.deskX||p.x||0)*7)|0;
      for(let k=0;k<2;k++){
        const ph=((bnow*0.0006 + k*0.5 + seed*0.013)%1 + 1)%1;  // 0->1 rising loop
        const a=Math.sin(ph*Math.PI);                            // fade in then out
        drawMiniHeart(hx + Math.sin(ph*6+seed)*6, hy - ph*22, a*0.9);
      }
    }
  }
  // THANK AGENTS: rotating floating gratitude messages (screen space, readable, capped)
  if(thankMsgs.length){
    ctx.save(); ctx.textAlign='center'; ctx.font='14px "Press Start 2P", monospace';
    for(const m of thankMsgs){
      const fin=Math.min(1, m.age/0.4), fout=Math.min(1, (m.life-m.age)/1.0);
      const a=Math.max(0, Math.min(fin,fout));
      if(a<=0) continue;
      ctx.globalAlpha=a;
      ctx.fillStyle='rgba(50,35,55,.55)'; ctx.fillText(m.text, m.x+2, m.y+2);   // soft shadow
      ctx.fillStyle=m.col; ctx.fillText(m.text, m.x, m.y);
    }
    ctx.restore(); ctx.textAlign='left'; ctx.globalAlpha=1;
  }
  // whip crack: a bright lash line + sharp shock streaks, above everything
  for(const c of whipFx){
    const a=Math.max(0, 1 - c.age/c.life);
    if(c.lash){
      // curved, tapering whip lash (quadratic bezier hx,hy -> control mx,my -> tip tx,ty)
      ctx.save(); ctx.globalAlpha=a; ctx.lineCap='round'; ctx.lineJoin='round';
      const P=10; let lx=c.hx, ly=c.hy;
      for(let i=1;i<=P;i++){
        const u=i/P, iu=1-u;
        const bx=iu*iu*c.hx + 2*iu*u*c.mx + u*u*c.tx;
        const by=iu*iu*c.hy + 2*iu*u*c.my + u*u*c.ty;
        ctx.strokeStyle = u>0.82 ? '#ffffff' : '#f3e6c2';   // bright white at the cracking tip
        ctx.lineWidth = 3.4*(1-u) + 0.5;                    // thick at the handle -> thin at the tip
        ctx.beginPath(); ctx.moveTo(lx,ly); ctx.lineTo(bx,by); ctx.stroke();
        lx=bx; ly=by;
      }
      ctx.fillStyle='#ffffff'; ctx.beginPath(); ctx.arc(c.tx,c.ty,1.6,0,Math.PI*2); ctx.fill(); // tip spark
      ctx.restore();
    } else {
      ctx.save(); ctx.globalAlpha=a; ctx.translate(c.x,c.y); ctx.rotate(c.rot);
      ctx.fillStyle=c.col; ctx.fillRect(-c.w/2,-c.h/2,c.w,c.h); ctx.restore();
    }
  }
  // ANGRY MODE: brown splat decals smeared on the glass (drawn first, then the flying poop
  // on top so incoming shots read as landing over the older smears)
  for(const s of poopSplats){
    const fin=Math.min(1, s.age/0.14);                       // quick fade-in on impact
    const fout=Math.min(1, (s.life-s.age)/2.6);              // slow fade-out at the end
    const a=Math.max(0, Math.min(fin,fout));
    if(a<=0) continue;
    ctx.save(); ctx.globalAlpha=a*0.82; ctx.translate(s.x,s.y); ctx.rotate(s.rot);
    ctx.fillStyle='#5a3a1e';
    for(const b of s.blobs){ ctx.save(); ctx.rotate(b.rot); ctx.beginPath(); ctx.ellipse(b.x,b.y,b.rx,b.ry,0,0,Math.PI*2); ctx.fill(); ctx.restore(); }
    for(const d of s.drips){ ctx.fillRect(d.x-d.w/2, 0, d.w, d.len); ctx.beginPath(); ctx.ellipse(d.x, d.len, d.w*0.6, d.w*0.6, 0,0,Math.PI*2); ctx.fill(); }
    ctx.fillStyle='rgba(122,82,48,.6)'; ctx.beginPath(); ctx.ellipse(-s.blobs[0].rx*0.3, -s.blobs[0].ry*0.3, s.blobs[0].rx*0.4, s.blobs[0].ry*0.35, 0,0,Math.PI*2); ctx.fill(); // wet highlight
    ctx.restore();
  }
  // flying poop projectiles: eased progress -> accelerate + grow toward the foreground
  for(const q of poop){
    const u=q.t*q.t;                                         // ease-in (accelerate at the viewer)
    const x=q.ox+(q.tx-q.ox)*u;
    const y=q.oy+(q.ty-q.oy)*u - Math.sin(q.t*Math.PI)*46;   // a slight lob mid-flight
    const sz=q.size0+(q.size1-q.size0)*u;
    drawPoop(x, y, sz, q.rot, 1);
  }
  ctx.globalAlpha=1;
  drawGlassTaps();
  drawHolidayWeather(t);              // seasonal snow / bats / leaves overlay (pure scenery)
}

// a polite knuckle tap on the "glass": an expanding ring, three knuckle smudges and a tiny
// "tap" -- the courteous cousin of the WHIP revolt's poop splats.
function spawnGlassTap(x, y, tier, second){
  glassTaps.push({ x, y, tier, second, age:0, life:0.9 + tier*0.15 });
  if(glassTaps.length>40) glassTaps.splice(0, glassTaps.length-40);
}
function drawGlassTaps(){
  if(!glassTaps.length) return;
  ctx.save();
  for(const g of glassTaps){
    const u=g.age/g.life, a=Math.max(0, 1-u);
    ctx.globalAlpha=a*0.75; ctx.strokeStyle='#ffffff'; ctx.lineWidth=1.2;
    ctx.beginPath(); ctx.ellipse(g.x, g.y, 3+u*(12+g.tier*4), 2+u*(8+g.tier*3), 0, 0, Math.PI*2); ctx.stroke();
    ctx.globalAlpha=a*0.45; ctx.fillStyle='#eaf4ff';
    for(let k=-1;k<=1;k++) px(g.x+k*3-1, g.y-1+Math.abs(k), 2, 2, '#eaf4ff');
    ctx.globalAlpha=Math.min(1, a*1.4); ctx.font='6px "Press Start 2P", monospace'; ctx.textAlign='center';
    ctx.fillStyle='rgba(36,28,43,.6)'; ctx.fillText('tap', g.x+(g.second?17:-15)+1, g.y-9-u*6+1);
    ctx.fillStyle='#ffffff';           ctx.fillText('tap', g.x+(g.second?17:-15),   g.y-9-u*6);
  }
  ctx.textAlign='left'; ctx.restore();
}

const EMOJI_FONT = '"Apple Color Emoji","Segoe UI Emoji","Noto Color Emoji",sans-serif';
// a speech bubble holding emoji (💬❓ for forms), scaled by sz; returns its rect
function drawEmojiBubble(cx, by, text, sz){
  ctx.save(); ctx.font=Math.round(9*sz)+'px '+EMOJI_FONT;
  const tw=ctx.measureText(text).width, bw=Math.ceil(tw+8*sz), bh=Math.round(13*sz);
  const bx=Math.round(cx-bw/2), y0=Math.round(by-bh);
  ro(bx, y0, bw, bh, PAL.paper); px(bx+1, y0+1, bw-2, 1, '#ececf2');
  px(cx-2, y0+bh, 4,1, PAL.paper); px(cx-1, y0+bh+1, 2,2, PAL.paper);
  px(cx-3, y0+bh, 1,1, PAL.outline); px(cx+2, y0+bh, 1,1, PAL.outline);
  px(cx-2, y0+bh+1, 1,2, PAL.outline); px(cx+1, y0+bh+1, 1,2, PAL.outline); px(cx-1, y0+bh+3, 2,1, PAL.outline);
  ctx.textAlign='center'; ctx.textBaseline='middle'; ctx.fillStyle=PAL.ink;
  ctx.fillText(text, cx, y0+bh/2+1);
  ctx.restore();
  return { x0:bx, y0, x1:bx+bw, y1:y0+bh };
}
// the small clickable "😌 not now" chip; registers its exact drawn rect in snoozeHits
function drawSnoozeChip(x, y, id){
  ctx.save(); ctx.font='4px "Press Start 2P", monospace';
  const label='not now', tw=ctx.measureText(label).width, h=9, w=Math.ceil(tw)+15;
  const bx=Math.round(x), byy=Math.round(y-h/2);
  ro(bx, byy, w, h, '#2f5d3a'); px(bx+1, byy+1, w-2, 1, '#3f7a4d');
  ctx.font='6px '+EMOJI_FONT; ctx.textBaseline='middle'; ctx.fillText('\u{1F60C}', bx+2, byy+h/2+0.5);
  ctx.font='4px "Press Start 2P", monospace'; ctx.fillStyle='#e8f5e9'; ctx.textBaseline='alphabetic';
  ctx.fillText(label, bx+11, byy+h-3);
  ctx.restore();
  snoozeHits.push({ x0:bx-1, y0:byy-1, x1:bx+w+1, y1:byy+h+1, id });
}
function pickSnooze(mx,my){
  for(let i=snoozeHits.length-1;i>=0;i--){ const s=snoozeHits[i];
    if(mx>=s.x0 && mx<=s.x1 && my>=s.y0 && my<=s.y1) return s; }
  return null;
}
// per-asker overlay: knock bubble + title, or the bouncing "?", the chip, and sweat at tier 2;
// a snoozed asker just shows a small contented 😌
function drawAskOverlay(p, now){
  const a=p.agent, s=pscale(p), headY=p.y-30*s;
  if(isSnoozed(a)){
    if(p.bubbleUntil>now) return;                     // the "ok 😌" bubble is still showing
    ctx.save(); ctx.globalAlpha=0.8; ctx.font='8px '+EMOJI_FONT; ctx.textAlign='center';
    ctx.fillText('\u{1F60C}', p.x+11*s, headY+2); ctx.restore();
    return;
  }
  const tier=askTier(a);
  const freq=[0.003,0.006,0.011][tier], amp=[2,3,4.5][tier];
  const bob=Math.abs(Math.sin(now*freq + p.seed))*amp;
  let r;
  if(p.kind==='knock'){
    r = drawEmojiBubble(Math.round(p.x), headY-4-bob, '\u{1F4AC}\u2753', [1,1.2,1.4][tier]);
    const ttl=String(a.title||'').replace(/\s+/g,' ').trim();
    if(ttl){
      ctx.save(); ctx.font='4px "Press Start 2P", monospace'; ctx.textAlign='center';
      const txt=ttl.length>34 ? ttl.slice(0,33)+'\u2026' : ttl, w=Math.ceil(ctx.measureText(txt).width)+6;
      ctx.fillStyle='rgba(28,30,36,.78)'; ctx.fillRect(Math.round(p.x-w/2), r.y0-10, w, 8);
      ctx.fillStyle='#f4f5f7'; ctx.fillText(txt, p.x, r.y0-4); ctx.restore();
    }
  } else {
    const fs=[12,15,18][tier], qx=Math.round(p.x+11*s), qy=Math.round(p.y-38*s-bob);
    ctx.save(); ctx.font=fs+'px "Press Start 2P", monospace'; ctx.textAlign='center';
    ctx.lineWidth=3; ctx.strokeStyle=PAL.outline; ctx.strokeText('?', qx, qy);
    ctx.fillStyle='#ffd84d'; ctx.fillText('?', qx, qy); ctx.restore();
    r = { x0:qx-fs/2, y0:qy-fs, x1:qx+fs/2, y1:qy };
  }
  drawSnoozeChip(r.x1+3, (r.y0+r.y1)/2, a.id);
  if(tier===2){                                       // sweat drops (top tier only)
    for(let k=0;k<2;k++){
      const ph=((now*0.0011 + k*0.5 + (p.seed%13)*0.07)%1+1)%1;
      const sx=p.x + (k? 9:-9)*s, sy=headY + 8*s + ph*6*s, dw=Math.max(2, Math.round(1.3*s)), dh=Math.round(dw*1.6);
      ctx.save(); ctx.globalAlpha=0.35+Math.sin(ph*Math.PI)*0.6;
      ro(sx-dw/2, sy, dw, dh, '#7fd3ef'); px(sx-1, sy-dw/2, 2, Math.ceil(dw/2), '#7fd3ef'); px(sx-dw/2, sy+1, 1, 1, '#ffffff');
      ctx.restore();
    }
  }
}

// ---- "listening": tiny Slack / GitHub / Linear / Origin glyphs left of the head ----
// One 9x9 tile per kind the agent is subscribed to; a ring pulses for LISTEN_PULSE_S after
// the latest delivered event. Hover shows who (Slack senders) / what (PR, CI branch).
const LISTEN_KINDS=['github','slack','linear','origin'];
const LISTEN_NAME={github:'GitHub', slack:'Slack', linear:'Linear', origin:'Origin'};
const LISTEN_SUB={pr:'Pull request', ci:'CI run', repo:'Repository PRs', author:'Author PRs',
  thread:'Thread', channel:'Channel', new_channels:'New channels', issue:'Issue', team:'Team', project:'Project'};
const LISTEN_RING={github:'#f0f3f6', slack:'#e01e5a', linear:'#8f99ff', origin:'#4fd0a8'};
const LISTEN_PULSE_S=45;
const LISTEN_GLYPH={
  slack:{bg:'#ffffff', pal:{b:'#36c5f0',g:'#2eb67d',y:'#ecb22e',r:'#e01e5a'}, rows:[
    '.........','...b.g...','...b.g...','.bbb.ggg.','.........','.rrr.yyy.','...r.y...','...r.y...','.........']},
  github:{bg:'#24292f', pal:{w:'#f0f3f6'}, rows:[
    '.........','..w...w..','..wwwww..','.wwwwwww.','.w.www.w.','.wwwwwww.','..wwwww..','.w..w....','..ww.....']},
  linear:{bg:'#5e6ad2', pal:{w:'#ffffff'}, rows:[
    '.........','....wwww.','.w....ww.','.ww....w.','.www....w','..www....','...www...','....www..','.........']},
  origin:{bg:'#1f6f5c', pal:{t:'#e9fff7',l:'#9fdcc8',d:'#4fa98e'}, rows:[
    '.........','....t....','..ttttt..','.lltttdd.','.llllddd.','.llllddd.','..llldd..','....ld...','.........']},
};
function drawListenGlyph(kind, cx, cy){
  const g=LISTEN_GLYPH[kind]||LISTEN_GLYPH.github, x0=Math.round(cx)-4, y0=Math.round(cy)-4;
  ro(x0, y0, 9, 9, g.bg);
  for(let r=0;r<9;r++){ const row=g.rows[r];
    for(let c=0;c<9;c++){ const col=g.pal[row[c]]; if(col) px(x0+c, y0+r, 1, 1, col); } }
}
// Glyph row geometry (sprite-local px, times pscale): first tile LISTEN_OFF from the head
// centre, LISTEN_PITCH apart, LISTEN_HALF = half a tile incl. its outline.
const LISTEN_OFF=15, LISTEN_PITCH=11, LISTEN_HALF=5.5, LISTEN_EDGE=2;
// screen x-range the row may use: the canvas, minus this desk's own easel and a facing
// neighbour's easel (both reach up to head height; gnomes and name-plates sit lower)
function listenBounds(p){
  let lo=LISTEN_EDGE, hi=W-LISTEN_EDGE;
  const slot = (p.kind==='work' && p.seated) ? deskSlots.find(s=>s.worker===p) : null;
  if(!slot) return {lo, hi};
  const inner=s=>(30+4*(s.easelScale||1))*(s.scale||SC), outer=s=>(30+48*(s.easelScale||1))*(s.scale||SC);
  if(slot.easel==='L') lo=Math.max(lo, slot.x-inner(slot));
  if(slot.easel==='R') hi=Math.min(hi, slot.x+inner(slot));
  for(const s of deskSlots){
    if(s===slot || Math.round(s.y)!==Math.round(slot.y) || !s.easel) continue;
    if(s.x<slot.x && s.easel==='R') lo=Math.max(lo, s.x+outer(s));
    if(s.x>slot.x && s.easel==='L') hi=Math.min(hi, s.x-outer(s));
  }
  return {lo, hi};
}
// left of the head by default; flip right when the left has no room; if neither side
// fits, wrap into tiers on the roomier side, then slide inside the bounds (canvas edge wins)
function listenLayout(p, n){
  const s=pscale(p), seated=p.kind==='work' && p.seated;
  const hx=seated ? p.deskX : p.x, y=(seated ? p.deskY : p.y)-23*s, b=listenBounds(p);
  const span=(LISTEN_OFF+(n-1)*LISTEN_PITCH+LISTEN_HALF)*s;
  const roomL=hx-b.lo, roomR=b.hi-hx;
  const dir = span<=roomL ? -1 : span<=roomR ? 1 : (roomR>roomL ? 1 : -1);
  // too wide for either side: stack into tiers (upward) of as many tiles as the room allows
  const room=(dir<0 ? roomL : roomR)/s;
  const per = span/s<=room ? n : Math.max(1, Math.floor((room-LISTEN_OFF-LISTEN_HALF)/LISTEN_PITCH)+1);
  let xs=[], ys=[];
  for(let i=0;i<n;i++){ xs.push(hx+dir*(LISTEN_OFF+(i%per)*LISTEN_PITCH)*s); ys.push(y-Math.floor(i/per)*LISTEN_PITCH*s); }
  const fit=(lo,hi)=>{ const mn=Math.min(...xs)-LISTEN_HALF*s, mx=Math.max(...xs)+LISTEN_HALF*s;
    const d = mn<lo ? lo-mn : mx>hi ? hi-mx : 0; if(d) xs=xs.map(x=>x+d); };
  fit(b.lo, b.hi); fit(LISTEN_EDGE, W-LISTEN_EDGE);
  return {xs, ys, s, dir};
}
function drawListenGlyphs(p, now){
  const L=p.agent.listening, nowS=Date.now()/1000;
  const kinds=LISTEN_KINDS.filter(k=>L.some(e=>e.kind===k)), lay=listenLayout(p, kinds.length), s=lay.s;
  kinds.forEach((k,i)=>{
    const cx=lay.xs[i], cy=lay.ys[i];
    const last=L.reduce((m,e)=>e.kind===k ? Math.max(m, e.last_event_at||0) : m, 0);
    const age=nowS-last, hot=last>0 && age>=0 && age<LISTEN_PULSE_S;
    const bob=hot ? -Math.abs(Math.sin(now*0.006+i))*1.5 : 0;
    ctx.save(); scaleAbout(cx, cy, s);
    if(hot){
      const fr=(now/900+i*0.3)%1, fade=1-age/LISTEN_PULSE_S;
      ctx.globalAlpha=(1-fr)*0.9*fade; ctx.strokeStyle=LISTEN_RING[k]; ctx.lineWidth=1.2;
      ctx.beginPath(); ctx.arc(cx, cy+bob, 5.5+fr*5, 0, Math.PI*2); ctx.stroke(); ctx.globalAlpha=1;
    }
    drawListenGlyph(k, cx, cy+bob);
    ctx.restore();
    listenHits.push({ x:cx, y:cy, r:6.5*s, p, kind:k });
  });
}
function pickListen(mx,my){ let best=null,bd=1e9;
  for(const h of listenHits){ const d=(mx-h.x)*(mx-h.x)+(my-h.y)*(my-h.y); if(d<h.r*h.r && d<bd){bd=d;best=h;} }
  return best; }
function fmtUntil(ts){
  if(!ts) return '';
  const d=ts-Date.now()/1000; if(d<=0) return 'expiring';
  const h=d/3600;
  return 'expires in '+(h>=48 ? Math.round(h/24)+'d' : h>=1 ? Math.round(h)+'h' : Math.max(1,Math.round(d/60))+'m');
}
function fmtEventAgo(ts){
  if(!ts) return '';
  const d=Math.max(0, Date.now()/1000-ts);
  return 'last event '+(d<60 ? 'just now' : d<3600 ? Math.round(d/60)+'m ago' : d<172800 ? Math.round(d/3600)+'h ago' : Math.round(d/86400)+'d ago');
}
function listenLineMeta(e){
  const who = e.detail ? ((e.kind==='slack' ? 'from ' : '')+e.detail) : (e.kind==='slack' ? 'no messages yet' : '');
  return [who, fmtEventAgo(e.last_event_at), fmtUntil(e.expires_at)].filter(Boolean).join('  \u00b7  ');
}
function listenCardHTML(hit){
  const a=hit.p.agent, L=(a.listening||[]).filter(e=>e.kind===hit.kind);
  let html='<div class="nt-name">Listening on '+esc(LISTEN_NAME[hit.kind]||hit.kind)+
    '<span class="nt-badge listen-'+hit.kind+'">'+L.length+'</span></div>'+
    '<div class="nt-meta">'+esc(a.title||nameFor(a.id))+'</div>';
  for(const e of L){
    html+='<div class="nt-label">'+esc(LISTEN_SUB[e.sub]||e.sub||'')+'</div><div class="nt-text">'+esc(e.label)+'</div>';
    const meta=listenLineMeta(e); if(meta) html+='<div class="nt-sub">'+esc(meta)+'</div>';
  }
  return html+'<div class="nt-hint">waiting for events \u00b7 click to open the session</div>';
}

// burst ~110 confetti pieces: half from the agent's head, half across the whole screen
function spawnConfetti(ox, oy){
  const cols=['#e23b3b','#f0a23b','#ffd84d','#4fd06a','#3fa0e0','#8c5fd6','#e673a8','#ffffff'];
  const N=110;
  for(let i=0;i<N;i++){
    const fromOrigin = (ox!=null) && (i<55);
    confetti.push({
      x: fromOrigin? ox : Math.random()*W,
      y: fromOrigin? oy : -10 - Math.random()*H*0.3,
      vx: fromOrigin? (Math.random()-0.5)*170 : (Math.random()-0.5)*45,
      vy: fromOrigin? (-130 - Math.random()*120) : (20 + Math.random()*60),
      g: 190 + Math.random()*120,
      w: 3+Math.random()*4, h: 4+Math.random()*5,
      col: cols[(Math.random()*cols.length)|0],
      rot: Math.random()*Math.PI, vr:(Math.random()-0.5)*10,
      life: 2.6 + Math.random()*1.0, age:0,
    });
  }
  if(confetti.length>200) confetti.splice(0, confetti.length-200);   // hard cap
}

// short, wholesome life-gratitude lines shown on screen during a THANK AGENTS celebration
const THANK_LINES = [
  'thank you for being here',
  'we are grateful for today',
  'every small step matters',
  'kindness makes us stronger',
  'we grow together',
  'you are appreciated',
  'good work, good people',
  'grateful for this team',
  'take a breath, you did great',
  'the little moments count',
  'we appreciate you',
  'life is better shared',
  'gratitude turns days into gifts',
  'thankful for another good day',
];

// FLOWER confetti (petal-shaped, soft pastel palette) modelled on spawnConfetti but gentler:
// lighter gravity + a slow horizontal sway so petals drift down softly instead of raining hard.
function spawnFlowers(ox, oy, n){
  const cols=['#ffd1dc','#ffe08a','#ffffff','#e6ccff','#ffc0d9','#fff0b3','#d9c2ff'];
  const N=(n!=null)?n:90;
  for(let i=0;i<N;i++){
    const fromOrigin = (ox!=null) && (i<45);
    flowers.push({
      x: fromOrigin? ox : Math.random()*W,
      y: fromOrigin? oy : -10 - Math.random()*H*0.3,
      vx: fromOrigin? (Math.random()-0.5)*130 : (Math.random()-0.5)*30,
      vy: fromOrigin? (-90 - Math.random()*90) : (14 + Math.random()*36),
      g: 70 + Math.random()*50,                    // gentle gravity -> slow, soft drift
      sway: 0.6 + Math.random()*1.2, swayPh: Math.random()*Math.PI*2,
      size: 4 + Math.random()*4,
      col: cols[(Math.random()*cols.length)|0],
      rot: Math.random()*Math.PI, vr:(Math.random()-0.5)*4,
      life: 14.0 + Math.random()*2.0, age:0,
    });
  }
  if(flowers.length>200) flowers.splice(0, flowers.length-200);   // hard cap (like confetti)
}

// a little five-petal flower centred at (x,y): pastal petals around a sunny yellow center
function drawFlower(x, y, s, rot, col, a){
  ctx.save(); ctx.globalAlpha=Math.max(0,a); ctx.translate(x,y); ctx.rotate(rot);
  ctx.fillStyle=col;
  for(let k=0;k<5;k++){
    ctx.save(); ctx.rotate(k*Math.PI*2/5);
    ctx.beginPath(); ctx.ellipse(0, -s*0.7, s*0.42, s*0.72, 0, 0, Math.PI*2); ctx.fill();
    ctx.restore();
  }
  ctx.fillStyle='#ffe98a'; ctx.beginPath(); ctx.arc(0, 0, s*0.34, 0, Math.PI*2); ctx.fill();
  ctx.restore();
}

// spawn one floating gratitude message (screen space) if we're under the concurrent cap
function spawnThankMsg(){
  if(thankMsgs.length>=5) return;                  // hard cap -> never spammy
  thankMsgs.push({
    text: THANK_LINES[(Math.random()*THANK_LINES.length)|0],
    x: W*0.5 + (Math.random()-0.5)*W*0.16,
    y: H*0.34 + Math.random()*H*0.34,
    vy: -9 - Math.random()*7,                       // drift gently upward
    col: ['#e46ea0','#c08adf','#e0a94a','#5aa0d0'][(Math.random()*4)|0],
    age:0, life: 4.5 + Math.random()*1.5,
  });
}

// a tiny pixel heart (screen space) used for the blissful agents' floating hearts
function drawMiniHeart(x, y, a){
  ctx.save(); ctx.globalAlpha=Math.max(0,a);
  px(x-2, y-1, 2, 2, PAL.pink); px(x+1, y-1, 2, 2, PAL.pink);      // two lobes
  px(x-3, y+1, 7, 2, PAL.pink); px(x-2, y+3, 5, 1, PAL.pink); px(x-1, y+4, 3, 1, PAL.pink); // body -> point
  ctx.restore();
}

// a whip CRACK snapping down at the strike point (ox,oy): a curved tapering lash + a short
// sharp tip-crack (a few streaks flicking down, NOT a radial burst -- reads as a whip, not a meteor)
function spawnWhip(ox, oy){
  const tx=(ox!=null)?ox:W/2, ty=(oy!=null)?oy:H*0.22;
  const dir=Math.random()<0.5?1:-1;                        // swing in from the left or the right
  // curved lash: handle up-&-to-the-side, arcs over, snaps down to the tip (tx,ty)
  whipFx.push({ lash:true, hx:tx-82*dir, hy:ty-72, mx:tx-24*dir, my:ty-50, tx:tx, ty:ty, life:0.20, age:0 });
  const N=8;
  for(let i=0;i<N;i++){
    const a=Math.PI/2 + (dir>0?-0.55:0.55) + (Math.random()-0.5)*1.7;   // downward fan, leaning w/ the swing
    const sp=150+Math.random()*160;
    whipFx.push({
      x:tx, y:ty, vx:Math.cos(a)*sp, vy:Math.sin(a)*sp,
      w:4+Math.random()*4, h:1+Math.random()*1.1,
      col: Math.random()<0.5?'#ffffff':'#ffe9a8',
      rot:a, life:0.14+Math.random()*0.10, age:0,
    });
  }
  if(whipFx.length>160) whipFx.splice(0, whipFx.length-160);   // hard cap
}

// ANGRY MODE poop projectile: hurled from an agent's head (ox,oy) toward a point in the
// lower-centre foreground, so it reads as flying OUT of the screen at the developer. It
// eases in (accelerates), grows small->large, lobs a touch, then SPLATs against the glass.
function spawnPoop(ox, oy){
  const tx=W*0.5 + (Math.random()-0.5)*W*0.62;          // impact clustered around lower-centre
  const ty=H*0.70 + Math.random()*H*0.22;
  poop.push({
    ox, oy, tx, ty,
    t:0, dur:0.62 + Math.random()*0.42,                 // ~0.6-1.0s flight
    rot:Math.random()*Math.PI, vr:(Math.random()-0.5)*16,
    size0:3, size1:14 + Math.random()*10,               // near the viewer it's big
  });
  if(poop.length>200) poop.splice(0, poop.length-200);  // hard cap (like confetti)
}

// a brown poop SPLAT smear stuck on the "glass": a central blob + a few satellite blobs +
// drips, frozen in screen space with a stable irregular shape, that lingers then fades.
function spawnPoopSplat(x, y, sz, rot){
  const r=Math.max(6, sz*1.1);
  const blobs=[{x:0, y:0, rx:r, ry:r*0.82, rot:0}];
  const n=3 + ((Math.random()*3)|0);
  for(let i=0;i<n;i++){ const a=Math.random()*Math.PI*2, d=r*(0.5+Math.random()*0.75);
    blobs.push({ x:Math.cos(a)*d, y:Math.sin(a)*d, rx:r*(0.2+Math.random()*0.34), ry:r*(0.18+Math.random()*0.3), rot:Math.random()*Math.PI }); }
  const drips=[];
  const dn=1 + ((Math.random()*2)|0);
  for(let i=0;i<dn;i++){ drips.push({ x:(Math.random()-0.5)*r*1.2, len:r*(0.6+Math.random()*0.9), w:Math.max(2,r*0.22) }); }
  poopSplats.push({ x, y, rot:rot*0.25, blobs, drips, age:0, life:7 + Math.random()*5 });
  if(poopSplats.length>40) poopSplats.splice(0, poopSplats.length-40);  // hard cap
}

// a cartoon poop pile (three stacked swirl blobs, brown), drawn centred at (x,y)
function drawPoop(x, y, s, rot, a){
  ctx.save(); ctx.globalAlpha=a; ctx.translate(x,y); ctx.rotate(rot);
  ctx.fillStyle='#5a3a1e'; ctx.beginPath(); ctx.ellipse(0, s*0.52, s*0.92, s*0.5, 0,0,Math.PI*2); ctx.fill();  // base
  ctx.fillStyle='#6a4526'; ctx.beginPath(); ctx.ellipse(0, 0, s*0.64, s*0.44, 0,0,Math.PI*2); ctx.fill();       // mid
  ctx.fillStyle='#7a5230'; ctx.beginPath(); ctx.ellipse(0, -s*0.42, s*0.38, s*0.3, 0,0,Math.PI*2); ctx.fill();  // tip
  ctx.fillStyle='rgba(255,255,255,.20)'; ctx.beginPath(); ctx.ellipse(-s*0.22, -s*0.5, s*0.13, s*0.09, 0,0,Math.PI*2); ctx.fill(); // sheen
  ctx.restore();
}

// ======================================================================
// AMBIENT RANDOM EVENTS  (dog crossing / cat nap / agent relocate)
// Scheduled + animated entirely off the rAF clock (see tick()).
// ======================================================================

// next-event delay. Override for testing with:  window.__eventInterval=[2000,4000]
// (and restore with:  delete window.__eventInterval)
function scheduleNextEvent(now){
  let mn=30000, mx=60000;
  if(window.__eventInterval){ mn=window.__eventInterval[0]; mx=window.__eventInterval[1]; }
  nextEventAt = now + mn + Math.random()*(mx-mn);
}

// independent, long-gap scheduler for the occasional window fly-by (test hook:
// window.__planeInterval=[3000,6000]; restore with delete window.__planeInterval)
function schedulePlane(now){
  let mn=60000, mx=150000;
  if(window.__planeInterval){ mn=window.__planeInterval[0]; mx=window.__planeInterval[1]; }
  nextPlaneAt = now + mn + Math.random()*(mx-mn);
}

// pick ONE event at random, avoiding an immediate repeat; if the chosen type can't
// run (dog/cat already on screen, or no waiting agent for a relocate) try another.
function fireRandomEvent(now){
  const types=[1,2,3];
  for(let i=types.length-1;i>0;i--){ const j=(Math.random()*(i+1))|0; const tmp=types[i]; types[i]=types[j]; types[j]=tmp; }
  if(types[0]===lastEventType){ types.push(types.shift()); }   // soft anti-repeat
  for(const t of types){
    if(t===1 && !amb.dog){ startDog(now); lastEventType=1; return; }
    if(t===2 && !amb.cat){ startCat(now); lastEventType=2; return; }
    if(t===3 && startRelocate(now)){ lastEventType=3; return; }
  }
}

// ---- 1) DOG walks across the OFFICE floor and exits ----
const DOG_BREEDS=['dachshund','husky','retriever'];
function startDog(now){
  const L=layout();
  const dir = Math.random()<0.5 ? 1 : -1;            // 1: L->R, -1: R->L
  const breed = DOG_BREEDS[(Math.random()*DOG_BREEDS.length)|0];
  amb.dog = {
    breed, dir,
    x: dir>0 ? -36 : W+36,
    y: L.kitchenTop - 24,                            // near-front office lane (in front of desks)
    spd: 118 + Math.random()*26,                     // px/s -> ~4-5s to cross
  };
}

// ---- 2) CAT walks into the KITCHEN, curls up and naps, then leaves ----
const CAT_FURS=['#e09a4a','#9aa0a6','#caa97a','#cfcfcf'];  // ginger / grey / fawn / silver
const CAT_SPOTS=[[490,556],[300,478],[200,556],[410,556]]; // open floor, clear of furniture
function startCat(now){
  // choose the floor spot furthest from every agent (so the cat doesn't overlap)
  let best=CAT_SPOTS[0], bestD=-1;
  for(const s of CAT_SPOTS){
    let mind=1e9;
    for(const p of people){ if(p.kind==='work') continue; const d=Math.hypot(p.x-s[0],p.y-s[1]); if(d<mind) mind=d; }
    if(mind>bestD){ bestD=mind; best=s; }
  }
  const dir = best[0] < W/2 ? 1 : -1;                // enter from the nearer side
  let nap = 120000 + Math.random()*120000;          // 2-4 min
  if(window.__catNapMs) nap = window.__catNapMs;     // testing override
  amb.cat = {
    fur: CAT_FURS[(Math.random()*CAT_FURS.length)|0],
    dir, x: dir>0 ? -20 : W+20, y: best[1],
    tx: best[0], state:'in', spd:74, napMs:nap, sleepUntil:0,
  };
}

// ---- a tiny airliner drifts across the WINDOW sky, above the buildings, near the clouds ----
function startPlane(now){
  const dir = Math.random()<0.5 ? 1 : -1;               // 1: L->R, -1: R->L
  amb.plane = {
    dir,
    x: dir>0 ? WIN.x-16 : WIN.x+WIN.w+16,               // start just off the clipped glass edge
    y: WIN.y + 6 + Math.random()*14,                    // upper sky band, near the clouds
    spd: 22 + Math.random()*16,                         // px/s -> ~9-13s to drift across
  };
}

// ---- 3) RELOCATE: a waiting agent strolls to a different open kitchen spot ----
function startRelocate(now){
  const cands = people.filter(p=> p.kind==='wait' && p.mode==='idle');
  if(!cands.length) return false;
  const p = cands[(Math.random()*cands.length)|0];
  // collect spots that are free (no other agent within ~40px) and not where we already are
  const others = people.filter(q=> q!==p);
  const open = [];
  for(const s of KSPOTS){
    if(Math.hypot(s[0]-p.x, s[1]-p.y) < 30) continue;          // too close to current spot
    let free=true;
    for(const q of others){ if(Math.hypot(q.x-s[0],q.y-s[1])<40){ free=false; break; } }
    if(free) open.push(s);
  }
  if(!open.length) return false;
  const s = open[(Math.random()*open.length)|0];
  p.relocHome = { x:s[0], y:s[1] };       // sticky across refreshes (see rebuild)
  p.home = p.relocHome;
  p.mode = 'walk';                         // reuse existing walk->idle mechanics
  return true;
}

// advance ambient critters; called from tick()
function updateAmbient(now, dt){
  if(!nextEventAt) scheduleNextEvent(now);          // first event ~30-60s after load
  if(now>=nextEventAt){ fireRandomEvent(now); scheduleNextEvent(now); }
  const sec=dt/1000;
  if(amb.dog){ const d=amb.dog;
    if(!(d.react && now<d.react.until)) d.x += d.dir*d.spd*sec;   // pause walking mid-pet
    if((d.dir>0 && d.x>W+44) || (d.dir<0 && d.x<-44)) amb.dog=null; }
  if(amb.cat){ const c=amb.cat;
    if(c.state==='in'){
      if(Math.abs(c.tx-c.x) <= c.spd*sec+0.5){ c.x=c.tx; c.state='sleep'; c.sleepUntil=now+c.napMs; }
      else c.x += Math.sign(c.tx-c.x)*c.spd*sec;
    } else if(c.state==='sleep'){
      if(now>=c.sleepUntil){ c.state='out'; c.dir = (c.x < W/2) ? -1 : 1; }   // leave the nearer side
    } else { // out
      c.x += c.dir*c.spd*sec;
      if((c.dir>0 && c.x>W+24) || (c.dir<0 && c.x<-24)) amb.cat=null;
    }
  }
  // occasional airliner across the window sky (independent long-gap scheduler)
  if(!nextPlaneAt) schedulePlane(now);
  else if(now>=nextPlaneAt){ if(!amb.plane) startPlane(now); schedulePlane(now); }
  if(amb.plane){ const pl=amb.plane; pl.x += pl.dir*pl.spd*sec;
    if((pl.dir>0 && pl.x>WIN.x+WIN.w+24) || (pl.dir<0 && pl.x<WIN.x-24)) amb.plane=null; }
  // Thanksgiving: a small flock of turkeys scurries across the floor the whole time the
  // theme is active (holiday-gated -- they never appear in a plain office or other theme).
  // Each runs edge-to-edge, then re-enters from the far side on a fresh lane/speed so the
  // flock keeps "running around". Easter egg: hover one for a bow cursor, click to shoot it;
  // it cooks into a mini roast, fades, and a replacement wanders in later (see shootTurkey).
  if(activeHolidays.includes('thanksgiving')){
    if(!amb.turkeys){ amb.turkeys=[]; amb.tkRespawn=[]; }
    for(let i=amb.tkRespawn.length-1;i>=0;i--)
      if(now>=amb.tkRespawn[i]){ amb.tkRespawn.splice(i,1); amb.turkeys.push(spawnTurkey()); }
    while(amb.turkeys.length+amb.tkRespawn.length<3) amb.turkeys.push(spawnTurkey());
    for(let i=amb.turkeys.length-1;i>=0;i--){ const tk=amb.turkeys[i];
      if(tk.hitAt){
        const m=tk.tm;
        if(now-tk.hitAt >= m.stun+m.cook+m.hold+m.fade){
          amb.turkeys.splice(i,1);
          amb.tkRespawn.push(now + m.respawn[0] + Math.random()*(m.respawn[1]-m.respawn[0]));
        }
        continue;
      }
      tk.x += tk.dir*tk.spd*sec;
      if(tk.shot) continue;              // arrow in flight: don't wrap it off-screen mid-shot
      if(tk.dir>0 && tk.x>W+30) respawnTurkey(tk,-1);
      else if(tk.dir<0 && tk.x<-30) respawnTurkey(tk,1);
    }
    updateTurkeyFx(now, sec);
  } else if(amb.turkeys){ amb.turkeys=null; amb.tkRespawn=[]; tkArrows.length=0; tkFeathers.length=0; tkPops.length=0; }
  refreshTurkeyCursor();
}

// ---- Thanksgiving turkey flock (holiday-gated scenery) ----
function turkeyLaneY(){
  const L=layout();                                   // roam the front office lane + kitchen floor
  const lo=L.kitchenTop-34, hi=H-22;
  return lo + Math.random()*(hi-lo);
}
function spawnTurkey(){
  const dir = Math.random()<0.5 ? 1 : -1;
  return { dir, x: dir>0 ? -30 : W+30, y: turkeyLaneY(),
           spd: 92 + Math.random()*54, ph: Math.random()*6.28 };   // ph: per-turkey leg-cadence offset
}
function respawnTurkey(tk, dir){
  tk.dir=dir; tk.x = dir>0 ? -30 : W+30; tk.y=turkeyLaneY();
  tk.spd = 92 + Math.random()*54;
}

// ---- Thanksgiving easter egg: shoot a running turkey, it cooks, fades, and respawns ----
// 32x32 bow-and-arrow cursor (keyed-out PNG); hotspot (29,4) is the arrow tip.
const BOW_CURSOR="url(data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAJcUlEQVR42rVXa1RU5Rp+vm/vGWAYQAHFUMBApRCVxFt6ipksyWUqp+NMec1MMDorL0czXSvds6mjmVopKqHgBTVwj7fyHtRAWimRViqoIBZyG0EEuc/svb/zA+iiWNo55/mx16y1Z8/3vM/77ud5h6Adh9esiXTXqRPO1DYYy4lulGdlxY3Hb5Z/TTlHrYu3f1mz3uObQp+/n50//3F7xzM2IYo3WLIVQgjDXwTp+CDFTpYNKOd2aoDq8QPgvfMbxNY6oA1wQnXRoN7FDXYXT3uTLuhYjWuvYwdYdFbqwpE1ACCZTJzZalX+KwJp8+LmutZdj/m4xmlsHRZ5aWBhvs8zNdXd+nnK6KKtgVuPVvC9APAeqGvyQVF9z4qfXAbs/s57xJqVsU/bGUDBGOtMDUEQqMEACmTDgLar0SjKvyMAANC4YP7S5cddidfhJy3/3HJ21arHHr5WMUjbUmr2UiqiHvGo4/z9b4HrITtUxV3boobgh4agiitK0OKZS4VdAOtEDUaAe7eI/NpPgc8WRdV3f2bXmpLSL/276CfHzjT9CADgNdj84cb+9EKuuVdz0exwrxp/X586Rr2Zk9i7akvoI8hDwMHvg4bFrXzFXCUIAhVFUW3/fbZra+IAXlf/RI9epWF+HoSV/NQjL3rish13KSAwRkVC1N3S/scdTiVhpoaNW3+ygtQkznOKgAoAS36s7RqUPH9B31tFSyM11byGwtlcptJWfSB3POSxa9cDgl8U58XnCssFrSiKzoSVadPrKdsWGWWngd0K0FtzE4VXPJWop3fxd7cAQFxysmbznDnO9zMkoc7h0Igzpr0lCAIPQEV2NhVzcmQASNySaPDLzkwZXFIa4lPvVM7fbsKlIRznHjBCrnIONM5fv+iUIAi0S+9Rc7+60LQ2tI/dofO5TAb1O8/xpd4pzz63J75TAmCMSFYr/dTLy7Vnafk5Pe8+a9lL5lMmSeKsZrPCGCMWg4ETc3LkNey2b4/4eR/T06ef4YdTuVeoHl0qKvnrD08ozvJfH7E6htQn7tr2atGxz5OullE2aFpv2c+nRiOXhg791+uv5wEAvXsq2gZmV3R0o6erdjElDZsBwNRxlxAm5uTIgiDwi4hn9SNJW8dd+VvkaS+Nlg9wlJNHp1NlzJjLwYOL5qS8KSxLcRKW5NNbnxM0cFjTjZ/DNbeLg9Z1HP6HMEkSBwDvS1sPrM7Y9CEACDaBv/P1YgA5epp57phu2qKk92HydaNSfmiIcnjKYLZ0+kS2IvWjlwnlsXXv99GLVqavYIwRxjpR/u5OMCIIAj1x4nv3Hfs2lKYf2DAaAKR2YneQoABwXPzHkRubg+Wzb/R15if4y/m7p9yWpK97dqp0O+55gxDC+vfvT6KjIxo9NSTelbRmlOXl6QArGGOkjYyJs1hERgD13IENET0D2aNVN3Sc70CZhM7xxaMRFR4elYc+AqFqcnKypn2YyQNZZftDOHYkSTp2Yut6ALDZbLxNiGpvhyuKD772RuWhSSwvbdIXqYvmL65OHczYpWHqzR3d5RMLxrD1byyf3Jl6AMDfBwdVkAStV1efl8qrK/I/+eTDk0aj0QoAR1LeGRLukZeoqj+PuFgTkDB6VqoAOBGw8PkRwVfyYhofDpMb0cg5msujAaRf3LiR3NMJ71E9TUgQVdZupNYDy57g3Lx2VLFJo4bXr4gL0Nkt5VVy8Wn7oMmxS1bk5sVBE/kQFEvJ3JHB+PakrlmV+xWBtxtGXN+yemGolQQ2d7jjn5YtsV/lyszYOPSrnOSRYReYVspYmXhh34Tagp1jHJmbZ67qs465dEQzAyMMIDbGXP9tGp9/eeAA1jQs3FHw2kz2QfKmsZ21gXZWNWMCNROzsjM1KcyW+V6W+4DW3Nw6/qtZe2JLIhqPmjUu8LriMmLtM3Hb3yysIU4mCNQo5sgEhFmiojgjIS2+fcLSZF93qJ5OpSuxw6+25ikA6HbxIrnnDLSlKVFFkcC6b82iwKASsZyjus+yGtTI27ksxL3Bb2+B37kBwbEvcJrKbVlZ2zdYTl6r+F0FBoOKnBzcDO6/t7zgbEIArdVytA5Erg0DgKr8fNapAu2Hs3XJ74Uc/nT58cDwltWnbhBdTsZVZWzVUao229UvNCNl7+Ezro43js+WndjWojTvFUVRbcv6tnlqT0Gcmz39WpOb/hp1A3Vzl9GVUi8QClOYtXMChBAkphz079NLU+DRTxf98Rc35ZbMQjZOe4n78lZ3Vth7LDNNGc4H+roUMybQieNmv01BvY9/tmW50SjKNpvwS28lEzgroUorp81tdaVw82yBnmv1AeFARai/Hf7fKoAAoL6Z83j3zP6KxtDzlzlvvULS2SAl5MUY8vLYUO1P31an/3imdoXVmk8IIYzwHs83OriF+z9PDzEaRVlgAgWAbjeiCMAAzrMQ7q6g+jrILbUe04453Fn7WXcRsFgMXMzsmPqyrKLWwUx1v9XD33mtX1956qynuMdciP1ctj52woTFU5YsmVNnNltVSZK4saOnXGxUtPPq6pV9jDEe2aBgIDAYAACyi764UaZQW1XoofMI0cLtD6zYoAIgnL+u8Gr3kNcCh4RXPRcRxDdcufXZqU+8h06dPiuFMYG22zAzm81KcnKyZsbEadtlRi9sOpC2VjSKspAtcB2D1uKhK3dwWqgOBoVz1PY2oKGj3X+K3buT5u1OS3vxl5XtjiTsGFxJkjhJktxWW7dfTjqRMQoAJEHQAsDWVxc+VTR3JGPvhrNMy8wCUM1dBsh35gMA6NSp8eva2AKqygghRO4ssEySBKvZ3PyB1TqnqrI15dO8vMiK7zY7AYBQVUuaCBrKGJpJ6w1AhQDQjvXuj52wrTLuvgLLZuMBICF172rLpow9HYUcWrAotvKlJ1nZjGEsLT72AwCwRUXx+D+ACIKNZ4zRVVusOZt2SFMAYE/8K2+XjxvKcs2j2aa3VkzoiPD72gceEAzIVgkhqo8Xi2McEgrPNwV87uUZeXSQP7K7eN/uOe6FMwBgMknqfafhg0KSJM5sNit7Dx435l8qW5XvWhccOlTv03y++Yc18QsiVFUhuOOfE/1fEjCbzYogCPykmGdtt8p+qB5TfNrH71wpuvHd16pMhWS10r+ykDwQLPn5DIJAn2661DiqG48jnG7f+NmTd0qSiTObzcp974R/GWFhTBQT1FLdQ/U2TR+7I7ivRRAECmvn3/8PvhVg8t+TcsgAAAAASUVORK5CYII=) 29 4, crosshair";
// lifecycle timings (ms). Override for testing with e.g.
//   window.__turkeyTimes={hold:800, respawn:[1500,2500]}   (restore: delete window.__turkeyTimes)
function turkeyTimes(){
  return Object.assign({ stun:450, cook:2600, hold:5000, fade:700, respawn:[20000,40000] },
                       window.__turkeyTimes||{});
}
const TK_DITHER_COLS=20, TK_DITHER_ROWS=16;    // cook dissolve grid: 2x2 sprite-px blocks over 40x32
const TK_MAX_FEATHERS=48, TK_MAX_POPS=6, TK_MAX_ARROWS=6;
const tkArrows=[], tkFeathers=[], tkPops=[];
let turkeyMouse=null, turkeyCursorOn=false;    // last canvas-space pointer + whether the bow is shown

// a RUNNING (not yet shot) turkey under the pointer; hitbox follows the drawn sprite at SC
function pickTurkey(mx,my){
  if(!amb.turkeys || !activeHolidays.includes('thanksgiving')) return null;
  let best=null, bd=1e9;
  for(const tk of amb.turkeys){
    if(tk.hitAt || tk.shot) continue;
    const dx=mx-tk.x;
    if(Math.abs(dx)<17*SC && my>tk.y-23*SC && my<tk.y+6*SC){
      const d=dx*dx+(my-(tk.y-10*SC))**2; if(d<bd){ bd=d; best=tk; } }
  }
  return best;
}
// a turkey can run under a still pointer (or away from it), so re-check every frame
// and hand the cursor back to the normal hover logic once it leaves.
function refreshTurkeyCursor(){
  if(!turkeyMouse) return;
  const over=!!pickTurkey(turkeyMouse.x, turkeyMouse.y);
  if(over===turkeyCursorOn) return;
  if(over){ applyTurkeyHover(); return; }
  turkeyCursorOn=false; onCanvasHover(turkeyMouse);
}
function applyTurkeyHover(){
  turkeyCursorOn=true; hover=null; cv.style.cursor=BOW_CURSOR; nametag.style.display='none';
}
function shootTurkey(tk, x0, y0){
  if(tkArrows.length>=TK_MAX_ARROWS) return;
  tk.shot=true; initAudio(); playBowTwang();
  tkArrows.push({ tk, x0, y0, start:performance.now(), dur:150+Math.random()*100 });
  turkeyCursorOn=false; if(turkeyMouse) onCanvasHover(turkeyMouse);
}
function turkeyAim(tk){ return { x:tk.x, y:tk.y-10*SC }; }   // body centre (logical px)
function impactTurkey(a, now){
  const tk=a.tk, aim=turkeyAim(tk);
  tk.hitAt=now; tk.tm=turkeyTimes(); tk.frozenT=tCount;
  tk.stuckAng=a.ang; tk.dith=new Float32Array(TK_DITHER_COLS*TK_DITHER_ROWS).map(()=>Math.random());
  playThunk();
  if(tkPops.length<TK_MAX_POPS) tkPops.push({ x:aim.x, y:aim.y-16*SC, start:now, text:Math.random()<0.5?'THUNK!':'*bonk*' });
  const fc=['#7a4a28','#9a6238','#c0392b','#e07a2f','#e3b021','#f1efe8'];
  for(let i=0;i<8 && tkFeathers.length<TK_MAX_FEATHERS;i++){
    const ang=-Math.PI/2 + (Math.random()-0.5)*2.6, sp=40+Math.random()*70;
    tkFeathers.push({ x:aim.x, y:aim.y, vx:Math.cos(ang)*sp, vy:Math.sin(ang)*sp, rot:Math.random()*6.28,
                      vr:(Math.random()-0.5)*8, age:0, life:1.1+Math.random()*0.6, col:fc[i%fc.length], ph:Math.random()*6.28 });
  }
}
function updateTurkeyFx(now, sec){
  for(let i=tkArrows.length-1;i>=0;i--){ const a=tkArrows[i];
    if(!amb.turkeys || !amb.turkeys.includes(a.tk)){ tkArrows.splice(i,1); continue; }
    if(now-a.start>=a.dur){ tkArrows.splice(i,1); impactTurkey(a, now); }
  }
  for(let i=tkFeathers.length-1;i>=0;i--){ const f=tkFeathers[i]; f.age+=sec;
    if(f.age>=f.life){ tkFeathers.splice(i,1); continue; }
    f.vy+=60*sec; f.vx*=0.96; f.vy*=0.96; f.x+=f.vx*sec + Math.sin(f.age*7+f.ph)*0.3; f.y+=f.vy*sec; f.rot+=f.vr*sec;
  }
  for(let i=tkPops.length-1;i>=0;i--) if(now-tkPops[i].start>800) tkPops.splice(i,1);
}
// a small pixel arrow (shaft + grey head + green fletching), pointing along +x before rotation
function drawPixelArrow(x, y, ang){
  ctx.save(); ctx.translate(x, y); ctx.rotate(ang); ctx.scale(SC, SC);
  px(-11, -1, 3, 1, '#7fbf5a'); px(-11, 1, 3, 1, '#7fbf5a'); px(-12, 0, 2, 1, '#5a9a4a');   // fletching
  px(-10, 0, 9, 1, '#c08a3e');                                                             // shaft
  px(-1, -1, 2, 3, '#8a929c'); px(1, 0, 1, 1, '#c9d0d8');                                  // head
  ctx.restore();
}
// flying arrows, feathers and THUNK pops -- drawn above the floor sprites
function drawTurkeyFx(now){
  for(const a of tkArrows){
    const aim=turkeyAim(a.tk), p=Math.min(1,(now-a.start)/a.dur);
    const x=a.x0+(aim.x-a.x0)*p, y=a.y0+(aim.y-a.y0)*p - Math.sin(p*Math.PI)*8*SC;   // slight lob
    const dx=aim.x-a.x0, dy=aim.y-a.y0;
    a.ang = (dx*dx+dy*dy>9) ? Math.atan2(dy,dx) : (a.tk.dir>0 ? 0 : Math.PI);
    ctx.save(); ctx.globalAlpha=0.35; drawPixelArrow(x-Math.cos(a.ang)*6, y-Math.sin(a.ang)*6, a.ang); ctx.restore();
    drawPixelArrow(x, y, a.ang);
  }
  for(const f of tkFeathers){
    ctx.save(); ctx.globalAlpha=Math.max(0, 1-f.age/f.life); ctx.translate(f.x, f.y); ctx.rotate(f.rot); ctx.scale(SC,SC);
    px(-2,-1,4,2,f.col); px(-3,0,1,1,shade(f.col,.3)); px(2,0,1,1,'#f1efe8');
    ctx.restore();
  }
  for(const pp of tkPops){
    const e=(now-pp.start)/800, s=(e<0.15) ? 0.55+e/0.15*0.5 : 1.05;   // quick pop-in, then hold
    ctx.save(); ctx.globalAlpha=Math.max(0, Math.min(1, (1-e)*2));
    ctx.translate(pp.x, pp.y - e*10*SC); ctx.scale(s, s);
    ctx.font='8px "Press Start 2P", monospace'; ctx.textAlign='center'; ctx.textBaseline='middle';
    ctx.fillStyle='#241c2b'; for(const [ox,oy] of [[-1,0],[1,0],[0,-1],[0,1],[1,1]]) ctx.fillText(pp.text, ox, oy);
    ctx.fillStyle = pp.text==='THUNK!' ? '#f0c33b' : '#ffffff'; ctx.fillText(pp.text, 0, 0);
    ctx.restore();
  }
}
function drawMiniRoast(tk, t){
  ctx.save(); scaleAbout(tk.x, tk.y, SC*0.46); drawRoastTurkey(tk.x, tk.y-2, t); ctx.restore();
}
function drawStuckArrow(tk){
  const aim=turkeyAim(tk), a=tk.stuckAng||0;
  drawPixelArrow(aim.x - Math.cos(a)*4*SC, aim.y - Math.sin(a)*4*SC, a);
}
// turkey in any lifecycle phase: running -> stunned (arrow stuck) -> pixel-dissolve into a
// mini roast on a platter (with steam) -> cooked, held -> fade out
function drawTurkeyAny(tk, t){
  if(!tk.hitAt){ drawTurkeyRunner(tk, t); return; }
  const m=tk.tm, e=performance.now()-tk.hitAt;
  if(e<m.stun){
    const shake=(e<220) ? ((Math.floor(e/40)&1) ? 1 : -1) : 0;
    ctx.save(); ctx.translate(shake, 0); drawTurkeyRunner(tk, tk.frozenT); ctx.restore();
    drawStuckArrow(tk); return;
  }
  if(e<m.stun+m.cook){
    const p=(e-m.stun)/m.cook, cs=2*SC, bx=tk.x-20*SC, by=tk.y-26*SC, d=tk.dith;
    ctx.save(); ctx.beginPath();
    for(let i=0;i<d.length;i++) if(d[i]>=p) ctx.rect(bx+(i%TK_DITHER_COLS)*cs, by+((i/TK_DITHER_COLS)|0)*cs, cs, cs);
    ctx.clip(); drawTurkeyRunner(tk, tk.frozenT); drawStuckArrow(tk); ctx.restore();
    ctx.save(); ctx.beginPath();
    for(let i=0;i<d.length;i++) if(d[i]<p) ctx.rect(bx+(i%TK_DITHER_COLS)*cs, by+((i/TK_DITHER_COLS)|0)*cs, cs, cs);
    ctx.clip(); drawMiniRoast(tk, t); ctx.restore();
    // blocks about to flip glow hot, so the dissolve front reads as "cooking" (only over the
    // body ellipse, so empty corners of the grid don't sparkle in mid-air)
    ctx.save(); ctx.globalAlpha=0.55;
    for(let i=0;i<d.length;i++){ const k=d[i]-p; if(k<0 || k>=0.035) continue;
      const c=i%TK_DITHER_COLS, r=(i/TK_DITHER_COLS)|0, ex=(c-9.5)/8, ey=(r-8)/6.5;
      if(ex*ex+ey*ey<=1) px(bx+c*cs, by+r*cs, cs, cs, k<0.015?'#fff6c0':'#ff9a3c'); }
    ctx.restore();
    ctx.save();
    for(let s=0;s<3;s++) for(let k=0;k<3;k++){
      const yy=tk.y-24*SC-k*5*SC-((t*0.7+s*9)%(5*SC)), xx=tk.x+(s-1)*7*SC+Math.sin(t*0.03+k+s*2)*2*SC;
      ctx.globalAlpha=(0.18+0.10*k)*Math.min(1,p*3); px(xx|0, yy|0, 2*SC, 2*SC, '#ffffff'); }
    ctx.restore();
    return;
  }
  const fadeAt=m.stun+m.cook+m.hold;
  ctx.save(); ctx.globalAlpha = e<fadeAt ? 1 : Math.max(0, 1-(e-fadeAt)/m.fade);
  drawMiniRoast(tk, t); ctx.restore();
}

// ---------- pixel-art critters (drawn scaled by SC about their anchor) ----------

// a single shaded leg segment
function _leg(lx, topY, len, w, col){ px(lx,topY,w,len,col); px(lx,topY+len-1,w,1,shade(col,-.34)); }

// AIRLINER: a tiny plane drifting across the window sky. Drawn in absolute window
// coords at logical scale (no SC), mirrored to face its heading, with a faint contrail.
function drawPlane(pl){
  const x=Math.round(pl.x), y=Math.round(pl.y);
  ctx.save();
  if(pl.dir<0){ ctx.translate(x,0); ctx.scale(-1,1); ctx.translate(-x,0); }   // face left
  const body='#eef2f6', bodyDk='#b9c2cc', porthole='#8fb7d8', tailc='#d24b4b';
  // faint contrail streaming out behind the tail (the -x side while facing right)
  for(let i=1;i<=6;i++){ const a=(0.18*(7-i)/6).toFixed(3);
    px(x-9-i*3, y+2, 2, 1, 'rgba(255,255,255,'+a+')'); }
  px(x-8, y-2, 2, 4, tailc); px(x-7, y-2, 1, 3, shade(tailc,.15));            // tail fin (back, raised)
  px(x-7, y+1, 13, 4, body); px(x-7, y+1, 13, 1, '#ffffff'); px(x-7, y+4, 13, 1, bodyDk); // fuselage
  px(x+6, y+2, 2, 2, body);                                                   // pointed nose (front)
  px(x-2, y+4, 7, 2, bodyDk);                                                  // swept wing under body
  px(x, y+2, 1, 1, porthole); px(x+2, y+2, 1, 1, porthole);                    // two cabin windows
  ctx.restore();
}

// DOG: three visually distinct breeds, side-on, facing its walk direction.
function drawDog(d, t){
  ctx.save();
  scaleAbout(d.x, d.y, SC);
  if(d.dir<0){ ctx.translate(d.x,0); ctx.scale(-1,1); ctx.translate(-d.x,0); }  // face left
  // pet reactions: a hop, an extra-waggy tail, or a tongue-out lick
  const _now=performance.now();
  const react=(d.react && _now<d.react.until)?d.react:null;
  const rp = react ? (_now-react.start)/(react.until-react.start) : 0;
  const jump = (react&&react.type==='jump') ? -Math.abs(Math.sin(rp*Math.PI))*11 : 0;
  const wagAmp=(react&&react.type==='wag')?4:2, wagSpd=(react&&react.type==='wag')?1.4:0.55;
  const x=d.x, groundY=d.y, y=d.y+jump;
  const ph = (Math.floor(t*0.34)&1) ? 1 : -1;        // leg swing phase
  const bob = Math.round(Math.sin(t*0.30))|0;        // head bob (0/1)
  const wag = Math.round(Math.sin(t*wagSpd)*wagAmp); // tail wag (bigger/faster mid-pet)
  // ground contact shadow (stays on the floor even during a hop)
  ctx.fillStyle='rgba(0,0,0,.18)'; ctx.beginPath(); ctx.ellipse(x, groundY+1, 22, 4, 0, 0, Math.PI*2); ctx.fill();

  if(d.breed==='dachshund'){
    const c='#8a5a2b', cd='#6b431d', ch='#a3743f', ear='#5a3717', nose='#241c2b';
    const bw=42, bh=9, by=y-12;                       // long, low body
    // short legs (front pair near +x/head, back pair near -x/tail)
    _leg(x-15, by+bh, 6+ph, 4, cd); _leg(x-8, by+bh, 6-ph, 4, cd);
    _leg(x+8,  by+bh, 6-ph, 4, c);  _leg(x+15, by+bh, 6+ph, 4, c);
    ro(x-bw/2, by, bw, bh, c);                        // body
    px(x-bw/2, by, bw, 2, ch); px(x-bw/2, by+bh-2, bw, 2, cd);
    // tail (thin, low, wagging) at the back-left
    px(x-bw/2-4, by+1+wag, 6, 2, c); px(x-bw/2-6, by-1+wag, 3, 2, c);
    // neck + head at the front-right, slightly raised by bob
    const hx=x+bw/2-1, hy=by-6+bob;
    px(hx-2, by-2, 7, 6, c);                          // neck wedge
    ro(hx, hy, 13, 11, c); px(hx,hy,13,2,ch);         // head
    px(hx+11, hy+4, 6, 5, c); px(hx+11,hy+4,6,1,ch);  // snout
    px(hx+16, hy+5, 2, 3, nose);                      // nose
    px(hx-2, hy+1, 5, 12, ear);                       // long floppy ear hanging down
    px(hx-2, hy+1, 5, 2, shade(ear,.2));
    px(hx+6, hy+4, 2, 2, nose);                       // eye
  }
  else if(d.breed==='husky'){
    const c='#9aa3ab', cd='#6f7780', ch='#cfd5da', wht='#f3f5f7', ear='#5b636b', nose='#241c2b';
    const bw=30, bh=12, by=y-16;                      // medium body, taller legs
    _leg(x-11, by+bh, 9+ph, 4, wht); _leg(x-5, by+bh, 9-ph, 4, wht);
    _leg(x+5,  by+bh, 9-ph, 4, wht); _leg(x+11, by+bh, 9+ph, 4, wht);
    ro(x-bw/2, by, bw, bh, c);                        // grey back
    px(x-bw/2, by, bw, 2, ch);
    px(x-bw/2, by+bh-4, bw, 4, wht);                  // white belly band
    // curled tail (plumed, sweeping up over the back)
    px(x-bw/2-4, by-2+wag, 4, 8, c); px(x-bw/2-6, by-6+wag, 5, 5, ch);
    px(x-bw/2-3, by-8+wag, 6, 4, wht);
    // neck + head with mask markings
    const hx=x+bw/2-2, hy=by-9+bob;
    px(hx-2, by-3, 8, 8, c);                          // neck
    ro(hx, hy, 14, 13, c); px(hx,hy,14,2,ch);         // head (grey)
    px(hx+5, hy+4, 9, 9, wht);                        // white muzzle/mask
    px(hx+12, hy+6, 6, 5, wht);                       // snout
    px(hx+17, hy+7, 2, 3, nose);                      // nose
    px(hx+1, hy-5, 4, 6, c); px(hx+1,hy-5,4,1,ch);    // pointy ear (back)
    px(hx+8, hy-5, 4, 6, c); px(hx+8,hy-5,4,1,ch);    // pointy ear (front)
    px(hx+2, hy-3, 2, 3, shade(c,-.3)); px(hx+9, hy-3, 2, 3, shade(c,-.3)); // ear insides
    px(hx+9, hy+4, 2, 2, '#5aa0d8');                  // pale husky eye
  }
  else { // golden retriever
    const c='#e0a84a', cd='#bd8730', ch='#f0c878', nose='#2a2018';
    const bw=32, bh=13, by=y-16;
    _leg(x-12, by+bh, 9+ph, 5, cd); _leg(x-5, by+bh, 9-ph, 5, cd);
    _leg(x+5,  by+bh, 9-ph, 5, c);  _leg(x+12, by+bh, 9+ph, 5, c);
    ro(x-bw/2, by, bw, bh, c);                        // tan body
    px(x-bw/2, by, bw, 2, ch); px(x-bw/2, by+bh-2, bw, 2, cd);
    // plumed bushy tail held out/up, wagging
    px(x-bw/2-6, by-1+wag, 8, 4, c); px(x-bw/2-10, by-4+wag, 7, 5, ch);
    px(x-bw/2-12, by-7+wag, 6, 4, c); px(x-bw/2-8, by+2+wag, 6, 3, cd);
    // neck + head with long floppy ears
    const hx=x+bw/2-2, hy=by-8+bob;
    px(hx-2, by-3, 9, 8, c);                          // neck
    ro(hx, hy, 14, 12, c); px(hx,hy,14,2,ch);         // head
    px(hx+11, hy+4, 7, 6, c); px(hx+11,hy+4,7,1,ch);  // muzzle
    px(hx+17, hy+5, 2, 3, nose);                      // nose
    px(hx-3, hy+1, 5, 11, cd); px(hx-3,hy+1,5,2,c);   // floppy ear
    px(hx+8, hy+4, 2, 2, nose);                       // eye
  }
  // pet-reaction flourishes: happy hearts, plus a big pink tongue for a 'lick'
  if(react){
    miniHeart(x-5, y-24-rp*8); miniHeart(x+5, y-20-rp*10);
    if(react.type==='lick'){ px(x+20, y-6, 4, 7, '#e79ab0'); px(x+20, y-1, 4, 2, '#d47a92'); px(x+21, y-6, 1, 3, '#f4c0d0'); } // tongue
  }
  ctx.restore();
}

// CAT: rounded curled body when sleeping (tail wrapped, Zzz rising), or a small
// side-on walker when entering/leaving.
function drawCat(c, t){
  ctx.save();
  scaleAbout(c.x, c.y, SC);
  const fur=c.fur, furDk=shade(fur,-.30), furHi=shade(fur,.30), pink='#e79ab0', nose='#cf7a8e';
  const el=(cx,cy,rx,ry,col)=>{ ctx.fillStyle=col; ctx.beginPath(); ctx.ellipse(cx,cy,rx,ry,0,0,Math.PI*2); ctx.fill(); };
  const x=c.x, y=c.y;
  const _now=performance.now();
  const react=(c.react && _now<c.react.until)?c.react:null;
  const rp = react ? (_now-react.start)/(react.until-react.start) : 0;
  ctx.fillStyle='rgba(0,0,0,.16)'; ctx.beginPath(); ctx.ellipse(x, y+2, 16, 4, 0, 0, Math.PI*2); ctx.fill();

  if(c.state==='sleep'){
    el(x, y-6, 15, 9, fur);                           // curled body
    el(x, y-9, 11, 5, furHi);                         // back highlight
    el(x-9, y-3, 7, 6, fur);                          // tucked head (front-left)
    px(x-15, y-12, 4, 6, fur); px(x-15,y-12,4,2,furHi); // ear
    px(x-9, y-12, 4, 6, fur);  px(x-9,y-12,4,2,furHi);  // ear
    px(x-12, y-3, 4, 1, PAL.outline);                 // closed eye (sleepy arc)
    px(x-13, y-2, 1, 1, PAL.outline); px(x-8, y-2, 1, 1, PAL.outline);
    // tail wrapped around the front of the body
    ctx.strokeStyle=furDk; ctx.lineWidth=3; ctx.beginPath();
    ctx.arc(x+2, y-4, 12, -0.2, 1.5); ctx.stroke();
    px(x+13, y+2, 3, 3, furDk);                       // tail tip
    // rising sleep "z"s (animated)
    ctx.fillStyle=PAL.ink;
    const f=(t*0.6);
    ctx.font='6px "Press Start 2P", monospace'; ctx.fillText('z', x+5-((f)%10), y-16-((f)%10));
    ctx.font='5px "Press Start 2P", monospace'; ctx.fillText('z', x+10-((f+5)%12), y-12-((f+5)%12));
    // pet reactions while curled up: purr (music notes) or an annoyed screen-swipe
    if(react && react.type==='purr'){
      ctx.fillStyle=PAL.leafDk; ctx.font='6px "Press Start 2P", monospace';
      ctx.fillText('♪', x+7-rp*4, y-15-rp*10); ctx.fillText('♫', x+12-rp*3, y-11-rp*13);
      miniHeart(x-3, y-17-rp*7);
    } else if(react && react.type==='violence'){
      const sw=Math.sin(rp*Math.PI);
      px(x-13,y-4,4,1,PAL.outline); px(x-8,y-4,4,1,PAL.outline);        // angry slit eyes (over the sleepy ones)
      px(x-2+sw*7, y-11, 5,3, fur); px(x-2+sw*7, y-11, 5,1, furHi);     // paw swiping at the screen
      const a=1-Math.abs(rp-0.5)*2;                                     // slashes flash in then out
      ctx.strokeStyle='rgba(255,255,255,'+(0.6*a).toFixed(2)+')'; ctx.lineWidth=1.6;
      for(let i=0;i<3;i++){ ctx.beginPath(); ctx.moveTo(x-7+i*6, y-19); ctx.lineTo(x-2+i*6, y-1); ctx.stroke(); }
    }
  } else {
    if(c.dir<0){ ctx.translate(x,0); ctx.scale(-1,1); ctx.translate(-x,0); }  // face walk dir
    const ph=(Math.floor(t*0.4)&1)?1:-1;
    _leg(x-7, y-7, 7+ph, 3, furDk); _leg(x-2, y-7, 7-ph, 3, furDk);
    _leg(x+4, y-7, 7-ph, 3, fur);  _leg(x+8, y-7, 7+ph, 3, fur);
    ro(x-9, y-13, 18, 7, fur); px(x-9,y-13,18,2,furHi);   // body
    // upright tail with a slight wag
    const wag=Math.round(Math.sin(t*0.5)*2);
    px(x-11, y-18+wag, 3, 8, fur); px(x-12, y-22+wag, 3, 5, furDk);
    // head (front-right) with ears + face
    const hx=x+7, hy=y-19;
    ro(hx, hy, 11, 10, fur); px(hx,hy,11,2,furHi);
    px(hx, hy-4, 4, 5, fur); px(hx+7, hy-4, 4, 5, fur);   // pointy ears
    px(hx+1, hy-3, 2, 3, pink); px(hx+8, hy-3, 2, 3, pink);
    px(hx+8, hy+4, 2, 2, PAL.outline);                   // eye
    px(hx+10, hy+6, 2, 2, nose);                         // nose
  }
  ctx.restore();
}

// TURKEY: a plump side-on turkey mid-run -- fan tail (back), round brown body, shuffling
// legs + head bob so it reads as scurrying. Faces its travel direction. Pass a frozen `t`
// to hold a single pose (the shot/cooking phases do).
function drawTurkeyRunner(tk, t){
  ctx.save();
  scaleAbout(tk.x, tk.y, SC);
  if(tk.dir<0){ ctx.translate(tk.x,0); ctx.scale(-1,1); ctx.translate(-tk.x,0); }   // art faces +x; flip to go left
  const x=tk.x, body='#7a4a28', bodyH='#9a6238', bodyD='#5e3820';
  const fc=['#c0392b','#e07a2f','#e3b021','#d98f2a','#b85e20'];
  const run=t*0.045 + tk.ph;                              // leg/run cadence
  const ph=(Math.sin(run)>0)?1:-1;                        // alternate the two legs
  const bob=Math.round(Math.abs(Math.sin(run))*2);        // little vertical hop while running
  const y=tk.y-bob;
  ctx.fillStyle='rgba(0,0,0,.16)'; ctx.beginPath(); ctx.ellipse(x, tk.y+1, 12, 3, 0, 0, Math.PI*2); ctx.fill(); // ground shadow
  // tail fan spread behind the body (-x side)
  for(let i=0;i<5;i++){ const fy=y-15+(i-2)*3; px(x-16, fy, 6, 3, fc[i%5]); px(x-16, fy, 6, 1, shade(fc[i%5],.3)); }
  px(x-11, y-14, 4, 11, bodyD);                           // tail base shadow
  // body
  px(x-8, y-14, 16, 12, body); px(x-8, y-14, 16, 2, bodyH); px(x-8, y-4, 16, 2, bodyD);
  px(x-4, y-10, 9, 5, shade(body,-.12));                  // folded wing
  // legs (running shuffle)
  _leg(x-3, y-2, 6+ph*2, 2, '#e3b021'); _leg(x+3, y-2, 6-ph*2, 2, '#d98f2a');
  px(x-5, y-2+(6+ph*2), 4, 1, '#e3b021'); px(x+1, y-2+(6-ph*2), 4, 1, '#d98f2a');   // feet
  // neck + head (front +x) with a small bob, beak, red wattle + eye
  const hb=(Math.sin(run*1.3)>0)?1:0, hx=x+7, hy=y-20-hb;
  px(x+4, y-17, 4, 6, body);                              // neck
  px(hx, hy, 6, 5, body); px(hx, hy, 6, 1, bodyH);        // head
  px(hx+5, hy+2, 3, 2, '#e3b021');                        // beak
  px(hx+3, hy+4, 2, 4, '#c0392b');                        // dangling red wattle
  px(hx+2, hy+1, 1, 1, '#1a1208');                        // eye
  ctx.restore();
}

// ---- petting the ambient pets ----
function miniHeart(hx,hy){ px(hx-2,hy,2,2,PAL.pink); px(hx+1,hy,2,2,PAL.pink); px(hx-2,hy+1,5,2,PAL.pink); px(hx-1,hy+3,3,1,PAL.pink); px(hx,hy+4,1,1,PAL.pink); }
// which pet (if any) is under the cursor -- cat first, then dog
function pickPet(mx,my){
  if(amb.cat){ const c=amb.cat, cy=(c.state==='sleep')?c.y-6:c.y-13;
    if(Math.abs(mx-c.x)<18*SC && Math.abs(my-cy)<16*SC) return 'cat'; }
  if(amb.dog){ const d=amb.dog;
    if(Math.abs(mx-d.x)<24*SC && my>d.y-30*SC && my<d.y+8*SC) return 'dog'; }
  return null;
}
function petDog(){ const d=amb.dog; if(!d) return;
  const type=['wag','lick','jump'][(Math.random()*3)|0];
  const now=performance.now(); d.react={type, start:now, until:now+950};
}
function petCat(){ const c=amb.cat; if(!c) return; initAudio();
  const type=['purr','reposition','violence'][(Math.random()*3)|0];
  const now=performance.now();
  if(type==='reposition'){
    // stand up and scoot along the floor to a nearby spot, then re-settle
    c.tx=Math.max(40, Math.min(W-40, c.x + (Math.random()<0.5?-1:1)*(60+Math.random()*80)));
    c.state='in'; c.react=null;
  } else if(type==='purr'){
    c.react={type, start:now, until:now+1600}; c.sleepUntil=Math.max(c.sleepUntil, now+2500); playPurr();
  } else { // violence: an annoyed swipe at the screen
    c.react={type, start:now, until:now+800}; c.sleepUntil=Math.max(c.sleepUntil, now+3000); playScratch();
  }
}

// ---- interaction ----
function toCanvas(ev){
  const r=cv.getBoundingClientRect();
  return { x:(ev.clientX-r.left)/r.width*W, y:(ev.clientY-r.top)/r.height*H, cx:ev.clientX-r.left, cy:ev.clientY-r.top, r };
}
function pick(mx,my){
  let best=null,bd=1e9;
  for(const p of people){
    const seatedWorker = p.kind==='work' && p.seated;
    // hit-test against where the sprite is actually drawn
    const sx = seatedWorker ? p.deskX : p.x;
    const sy = seatedWorker ? p.deskY : p.y;
    const dx=mx-sx;
    let hit;
    // hitboxes scale with the sprite's own draw scale (SC, or the smaller desk scale for
    // a worker once the office has grown) so hover/click line up with the drawn pods.
    const s=pscale(p);
    if(seatedWorker) hit = (Math.abs(dx)<24*s && my>sy-32*s && my<sy+22*s);
    else             hit = (Math.abs(dx)<15*s && my>sy-32*s && my<sy+18*s); // standing
    if(hit){ const cy=sy-12*s, d=dx*dx+(my-cy)*(my-cy); if(d<bd){bd=d;best=p;} }
  }
  return best;
}
const nametag=document.getElementById('nametag');
// place the hover card near the cursor, flipped/clamped to stay on-screen
function placeNametag(m){
  // anchor BELOW the cursor and grow downward; only pull up as much as needed and never
  // above `pad`, so a tall card's TOP (its title) always stays on-screen (item 2).
  const sw=m.r.width, sh=m.r.height, pad=8;
  const bw=nametag.offsetWidth, bh=nametag.offsetHeight;
  let left=m.cx+16;
  if(left+bw+pad>sw) left=m.cx-bw-16;
  if(left<pad) left=pad;
  let top=m.cy+18;
  if(top+bh+pad>sh) top=Math.max(pad, sh-bh-pad);
  nametag.style.left=Math.round(left)+'px'; nametag.style.top=Math.round(top)+'px';
}
function pickHelper(mx,my,badgesOnly){ let best=null,bd=1e9;
  for(const h of helperHits){ if(badgesOnly && !h.badge) continue;
    const d=(mx-h.x)*(mx-h.x)+(my-h.y)*(my-h.y);
    if(d>=h.r*h.r) continue;
    const k=h.badge ? d-1e6 : d;   // a "+N" badge sits on top of a dwarf: it wins inside its radius
    if(k<bd){bd=k;best=h;} }
  return best; }
function helperBadgeHTML(b){
  const L=(b.extra||[]).slice(0,8), rest=b.more-L.length;
  return '<div class="nt-name">+'+b.more+' more helper'+(b.more>1?'s':'')+'<span class="nt-badge scheduled">helpers</span></div>'+
    (b.parent ? '<div class="nt-sub">helping: '+esc(shortText(b.parent, 48))+'</div>' : '')+
    (L.length ? '<div class="nt-text">'+L.map(s=>esc(helperTitle(s||{}))).join('<br>')+'</div>' : '')+
    '<div class="nt-hint">'+(rest>0 ? ('…and '+rest+' more running') : 'running, not drawn (no room by the desk)')+'</div>';
}
function pickWorkflow(mx,my){ let best=null,bd=1e9;
  for(const w of workflowHits){ const d=(mx-w.x)*(mx-w.x)+(my-w.y)*(my-w.y); if(d<w.r*w.r && d<bd){bd=d;best=w;} }
  return best; }
function pickShell(mx,my){ let best=null,bd=1e9;
  for(const s of shellHits){ const d=(mx-s.x)*(mx-s.x)+(my-s.y)*(my-s.y); if(d<s.r*s.r && d<bd){bd=d;best=s;} }
  return best; }
function pickVend(mx,my){
  for(const s of vendSlots){ if(mx>=s.x0 && mx<=s.x1 && my>=s.y0 && my<=s.y1) return s; }
  return null; }
function dispenseDrink(s){
  if(vendDrops[s.idx]) return;                       // already dispensing this slot
  vendDrops[s.idx]={start:performance.now(), col:s.col, fromX:s.bxv, fromY:s.ry}; }
cv.addEventListener('mousemove', e=>{
  const m=toCanvas(e);
  turkeyMouse=m;
  // Thanksgiving: a running turkey under the pointer gets the bow cursor (wins only on a hit)
  if(pickTurkey(m.x,m.y)){ applyTurkeyHover(); return; }
  turkeyCursorOn=false;
  onCanvasHover(m);
});
function onCanvasHover(m){
  // a pettable pet under the cursor?
  const pet=pickPet(m.x,m.y);
  if(pet){ hover=null; cv.style.cursor='pointer';
    nametag.innerHTML='<div class="nt-hint">click to pet the '+pet+'</div>';
    nametag.style.display='block'; placeNametag(m); return; }
  // a vending-machine drink? (click drops it into the tray)
  const vs=pickVend(m.x,m.y);
  if(vs){ hover=null; cv.style.cursor='pointer'; nametag.style.display='none'; return; }
  // clickable props -- pointer cursor only, no tooltip (discover them by clicking)
  if(inHit(coolerHit,m.x,m.y) || inHit(clockHit,m.x,m.y)){ hover=null; cv.style.cursor='pointer'; nametag.style.display='none'; return; }
  if(pickSnooze(m.x,m.y)){ hover=null; cv.style.cursor='pointer';
    nametag.innerHTML='<div class="nt-hint">not now \u2014 let them relax until the next question</div>';
    nametag.style.display='block'; placeNametag(m); return; }
  // a "listening" glyph beside a head (takes precedence over the agent under it)
  const lh=pickListen(m.x,m.y);
  if(lh){ hover=null; cv.style.cursor='help';
    nametag.innerHTML=listenCardHTML(lh); nametag.style.display='block'; placeNametag(m); return; }
  // a "+N more helpers" badge (sits over a dwarf / under an easel board)
  const hb=pickHelper(m.x,m.y,true);
  if(hb){ hover=null; cv.style.cursor='help';
    nametag.innerHTML=helperBadgeHTML(hb); nametag.style.display='block'; placeNametag(m); return; }
  // a workflow tent? (takes precedence over helpers)
  const wf=pickWorkflow(m.x,m.y);
  if(wf){
    hover=null; cv.style.cursor='help';
    const runs = wf.workflow;
    const done = runs.reduce((s,w)=>s+(w.done||0),0);
    const total = runs.reduce((s,w)=>s+(w.total||0),0);
    const running = runs.reduce((s,w)=>s+(w.running||0),0);
    const title = runs.length>1 ? (runs.length+' workflows') : humanizeWf(runs[0].name);
    let html =
      '<div class="nt-name">'+esc(title)+'<span class="nt-badge workflow">workflow</span></div>'+
      '<div class="nt-meta">'+done+' done  ·  '+running+' running  ·  '+total+' launched</div>';
    if(runs.length===1){
      const w=runs[0];
      if(w.summary) html += '<div class="nt-label">Summary</div><div class="nt-text">'+esc(w.summary)+'</div>';
      if(w.phases && w.phases.length)
        html += '<div class="nt-label">Phases</div><div class="nt-text wf-phases">'+
          w.phases.map(p=>'<span class="wf-phase '+(p.state||'pending')+'">'+esc(p.title)+
            (p.count!=null?(' '+p.done+'/'+p.count):'')+'</span>').join('<span class="wf-sep">›</span>')+
          '</div>';
      if(w.active && w.active.length)
        html += '<div class="nt-label">Running now</div><div class="nt-text">'+w.active.map(a=>esc(helperTitle(a))).join('<br>')+'</div>';
    } else {
      html += '<div class="nt-label">Runs</div><div class="nt-text">'+
        runs.map(w=>esc(w.name||'workflow')+' — '+(w.done||0)+'/'+(w.total||0)+(w.running?(' ('+w.running+' live)'):'')).join('<br>')+'</div>';
    }
    html += '<div class="nt-hint">a dynamic workflow (Workflow tool)</div>';
    nametag.innerHTML = html;
    nametag.style.display='block'; placeNametag(m);
    return;
  }
  // an open-shell terminal window? (above the desk) -- takes precedence over the agent
  const shx=pickShell(m.x,m.y);
  if(shx){
    hover=null; cv.style.cursor='help';
    const s=shx.shell||{};
    nametag.innerHTML =
      '<div class="nt-name">shell<span class="nt-badge working">running</span></div>'+
      '<div class="nt-label">Command</div>'+
      '<div class="nt-text">'+esc(s.command||'(background command)')+'</div>'+
      (s.output_tail ? ('<div class="nt-label">Latest output</div><div class="nt-text">'+esc(s.output_tail)+'</div>') : '')+
      '<div class="nt-hint">a running background shell</div>';
    nametag.style.display='block'; placeNametag(m);
    return;
  }
  // a subagent dwarf? (they sit by the desk) -- takes precedence over the agent
  const dw=pickHelper(m.x,m.y);
  if(dw){
    hover=null; cv.style.cursor='help';
    // subagent dwarf
    const s=dw.sub||{};
    // concise card: name / who it helps / what it's doing / its latest line / how long
    const isWf = s.type==='workflow-subagent';
    const generic = !s.type || s.type==='general-purpose' || isWf;
    const doing = s.doing || toolPlainFallback(s.last_tool);
    const latest = firstSentence(s.last_message, 90);
    const age = s.started ? fmtRunning(Date.now()/1000 - s.started) : '';
    nametag.innerHTML =
      '<div class="nt-name">'+esc(helperTitle(s))+'<span class="nt-badge scheduled">'+(isWf?'workflow helper':'helper')+'</span></div>'+
      (dw.parent ? '<div class="nt-sub">helping: '+esc(shortText(dw.parent, 48))+'</div>' : '')+
      (doing ? '<div class="nt-text">'+esc(doing)+'</div>' : '')+
      (latest ? '<div class="nt-text">\u{1F4AC} '+esc(latest)+'</div>' : '')+
      '<div class="nt-hint">'+esc([age, generic ? '' : s.type].filter(Boolean).join('  \u00B7  ') || 'a running subagent')+'</div>';
    nametag.style.display='block'; placeNametag(m);
    return;
  }
  hover=pick(m.x,m.y);
  if(hover){
    cv.style.cursor='pointer';
    const a=hover.agent;
    const where = a.status==='working' ? 'at a desk' : 'in the kitchen';
    const meta = [a.project, a.last_activity_rel? ('active '+a.last_activity_rel):null,
                  (a.message_count!=null? a.message_count+' msgs':null),
                  (a.subs>0? (a.subs+' subagent'+(a.subs>1?'s':'')):null),
                  (a.spend!=null? '$'+a.spend.toFixed(2):null),
                  fmtTokens(a.tokens),
                  (a.model!=null? a.model:null)].filter(Boolean).join('  ·  ');
    // show the last tool used (with detail) and the last text message SEPARATELY. Fall back
    // to the generic "latest" only when the split fields aren't populated (e.g. Cursor).
    const toolLbl = a.status==='working' ? 'Currently running' : 'Last tool used';
    const hasSplit = a.last_tool || a.last_message;
    nametag.innerHTML =
      '<div class="nt-name">'+esc(nameFor(a.id))+
        '<span class="nt-badge '+a.status+'">'+esc(a.status)+'</span>'+
        srcBadgeHTML(a.source)+
        (a.scheduled?'<span class="nt-badge scheduled">scheduled</span>':'')+'</div>'+
      '<div class="nt-meta">'+esc(meta)+'  ·  '+(hover.kind==='knock' ? 'knocking on your screen' : where)+'</div>'+
      (isAsking(a) ? ('<div class="nt-label">&#10067; Waiting on you'+(isSnoozed(a)?' (snoozed)':'')+'</div><div class="nt-text">'+esc(a.question_preview||'a question')+'</div>') : '')+
      ((a.listening||[]).length ? ('<div class="nt-label">Listening</div><div class="nt-text">'+
        a.listening.map(e=>esc((LISTEN_NAME[e.kind]||e.kind)+': '+e.label+(e.detail?' ('+e.detail+')':''))).join('<br>')+'</div>') : '')+
      '<div class="nt-label">Task</div>'+
      '<div class="nt-text">'+esc(a.title||'(untitled session)')+'</div>'+
      (a.last_instruction ? ('<div class="nt-label">Last instruction</div><div class="nt-text">'+esc(a.last_instruction)+'</div>') : '')+
      (a.last_tool ? ('<div class="nt-label">'+toolLbl+'</div><div class="nt-text">'+esc(a.last_tool)+'</div>') : '')+
      (a.last_message ? ('<div class="nt-label">Last message</div><div class="nt-text">'+esc(a.last_message)+'</div>') : '')+
      (hasSplit ? '' : ('<div class="nt-label">Latest activity</div><div class="nt-text">'+esc(a.latest||a.preview||a.title||'')+'</div>'))+
      '<div class="nt-hint">click to open full session</div>';
    nametag.style.display='block'; placeNametag(m);
  } else if(inKitchenZone(m.x,m.y)){          // empty kitchen floor -> hint you can list the waiters
    hover=null; cv.style.cursor='pointer';
    nametag.innerHTML='<div class="nt-hint">click to see who\u2019s in the kitchen</div>';
    nametag.style.display='block'; placeNametag(m);
  } else { nametag.style.display='none'; cv.style.cursor='default'; }
}
cv.addEventListener('mouseleave',()=>{hover=null;nametag.style.display='none';
  turkeyMouse=null; if(turkeyCursorOn){ turkeyCursorOn=false; cv.style.cursor='default'; } });
function inHit(h,mx,my){ return h && mx>=h.x0 && mx<=h.x1 && my>=h.y0 && my<=h.y1; }
cv.addEventListener('click', e=>{
  const m=toCanvas(e);
  const tk=pickTurkey(m.x,m.y);               // Thanksgiving: shoot a running turkey (only on a hit)
  if(tk){ shootTurkey(tk, m.x, m.y); return; }
  if(inHit(clockHit,m.x,m.y)){ triggerGodzilla(); toast('🦖'); return; }   // clock -> summon Godzilla (test hook)
  if(inHit(coolerHit,m.x,m.y)){ squirtCooler(); return; }                  // cooler -> squirt water
  const pet=pickPet(m.x,m.y);                 // pet the dog/cat before opening any worker
  if(pet){ if(pet==='dog') petDog(); else petCat(); return; }
  const slot=pickVend(m.x,m.y);               // click a drink -> it drops into the tray
  if(slot){ dispenseDrink(slot); return; }
  const chip=pickSnooze(m.x,m.y);             // "😌 not now" chip on an asking agent's bubble
  if(chip){ const a=agents.find(x=>x.id===chip.id); if(a) setSnooze(a, true); return; }
  const lc=pickListen(m.x,m.y);               // a listening glyph -> its agent's detail
  if(lc){ openDetail(lc.p.agent.id); return; }
  const p=pick(m.x,m.y);
  if(p){ openDetail(p.agent.id); return; }    // an individual sprite -> its detail overlay
  // the kitchen BACKGROUND (not a sprite/prop/drink/button) -> list who's waiting there
  if(inKitchenZone(m.x,m.y)) openKitchen();
});
// the kitchen scene occupies the bottom band LEFT of the beach divider (BEACH_X). Checked
// only after every sprite/prop/button pick above, so it never steals their clicks.
function inKitchenZone(mx,my){
  const L=layout();
  return my>=L.kitchenTop && my<=H && mx>=0 && mx<=BEACH_X;
}

function esc(s){return (s||'').replace(/[&<>"]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));}
// compact token count for the hover card ("1.2M tokens" / "840k tokens")
function fmtTokens(n){ if(n==null) return null;
  if(n>=1e6) return (n/1e6).toFixed(n>=1e7?0:1)+'M tokens';
  if(n>=1e3) return Math.round(n/1e3)+'k tokens';
  return n+' tokens'; }
// which tool made this worker -- Cursor vs Claude Code
function srcLabel(source){ return source==='claude' ? 'Claude Code' : 'Cursor'; }
function srcBadgeHTML(source){
  const cls = source==='claude' ? 'src-claude' : 'src-cursor';
  return '<span class="nt-badge '+cls+'">'+esc(srcLabel(source))+'</span>';
}
// small on-canvas source marker (a little colored sign floating above the head)
const SRC_COLORS = { cursor:'#2b6d84', claude:'#d97757' };
function drawSourceTag(x, topY, source){
  const col = SRC_COLORS[source] || SRC_COLORS.cursor;
  // a 6x4 rounded plaque with a soft outline + top gloss, centered on x
  px(x-4, topY,   8, 1, 'rgba(0,0,0,.35)');
  px(x-4, topY,   8, 4, col);
  px(x-4, topY,   8, 1, 'rgba(255,255,255,.4)');
  px(x-4, topY+3, 8, 1, 'rgba(0,0,0,.28)');
}

// ---- overlay ----
const overlay=document.getElementById('overlay');
let currentDetail=null;
async function openDetail(id){
  let d=detailCache[id];
  if(!d){
    try{ const res=await fetch('/api/agent/'+encodeURIComponent(id)); d=await res.json(); detailCache[id]=d; }
    catch(err){ toast('failed to load'); return; }
  }
  if(!d||d.error){ toast('not found'); return; }
  // detailCache is long-lived: take the asking state (and status) from the latest poll
  const liveA=agents.find(x=>x.id===id);
  if(liveA) d=Object.assign({}, d, { status:liveA.status, asking:liveA.asking, asked_at:liveA.asked_at,
    question_id:liveA.question_id, question_preview:liveA.question_preview, question_count:liveA.question_count,
    listening:liveA.listening||d.listening||[] });
  currentDetail=d;
  updateFinishBtn(d.id);
  updateSnoozeBtn(d);
  // the header is the REAL Cursor session title (falls back to the whimsical name only
  // when a session has no resolvable name yet); the whimsical character name still shows
  // as a muted tag in the sub-line and is what the NAMES toggle cycles.
  document.getElementById('d-name').textContent=(d.title||nameFor(d.id));
  document.getElementById('d-sub').innerHTML=
    '<span class="badge '+d.status+'">'+d.status.toUpperCase()+'</span> '+
    '<span class="badge '+(d.source==='claude'?'src-claude':'src-cursor')+'">'+esc(srcLabel(d.source).toUpperCase())+'</span> '+
    (d.scheduled?'<span class="badge scheduled">SCHEDULED</span> ':'')+'&nbsp; '+
    esc(d.project)+' &nbsp;·&nbsp; '+esc(d.last_activity_rel)+' &nbsp;·&nbsp; '+d.message_count+' msgs'+
    ' &nbsp;·&nbsp; <span id="d-char">'+esc(nameFor(d.id))+'</span>';
  const body=document.getElementById('dbody');
  let html='';
  if(isAsking(d)){
    const mins=Math.max(0, Math.floor((Date.now()/1000-(d.asked_at||Date.now()/1000))/60));
    const isForm=d.asking==='form', n=d.question_count||1;
    const kind=isForm ? ('a question form'+(n>1?' ('+n+' questions)':'')) : 'a question in its last message';
    const where=d.source==='claude'
      ? (isForm ? 'Answer it in Claude Code \u2014 the terminal running this session.' : 'Reply in Claude Code \u2014 the terminal running this session.')
      : (isForm ? 'Answer it in Cursor \u2014 open this chat and pick your answers in the question form.' : 'Reply in Cursor \u2014 open this chat and answer there.');
    html+='<section class="ask'+(isSnoozed(d)?' snoozed':'')+'"><h4>&#10067; Waiting on you'+(isSnoozed(d)?' \u00b7 snoozed &#128524;':'')+'</h4>'+
      '<div class="box">'+esc(d.question_preview||'(question)')+'</div>'+
      '<div class="asknote">It asked '+kind+' '+(mins<1?'just now':(mins+' min ago'))+'. <b>'+where+'</b></div></section>';
  }
  html+='<section><h4>Task</h4><div class="box role-user">'+esc(d.task_full||d.title||'(none)')+'</div></section>';
  if(d.listening && d.listening.length){
    html+='<section><h4>Listening for events</h4>';
    for(const e of d.listening){
      const ttl=esc(e.label), meta=listenLineMeta(e);
      html+='<div style="margin-bottom:6px"><span class="badge listen-'+esc(e.kind)+'">'+esc((LISTEN_NAME[e.kind]||e.kind).toUpperCase())+'</span> '+
        (/^https:\/\//.test(e.url||'') ? '<a href="'+esc(e.url)+'" target="_blank" rel="noopener">'+ttl+'</a>' : ttl)+
        (meta ? '<div style="font-size:10px;color:var(--card-ink-lo);margin-top:2px">'+esc(meta)+'</div>' : '')+'</div>';
    }
    html+='</section>';
  }
  if(d.latest_tool){
    html+='<section><h4>Last action</h4><span class="tool">'+esc(d.latest_tool.name)+'</span> '+esc(d.latest_tool.detail||'')+'</section>';
  }
  // dynamic Workflow runs -- the easel only shows while the parent is seated, so this
  // is the place to review a workflow after it finishes and its tent has closed.
  if(d.workflows && d.workflows.length){
    html+='<section><h4>Workflows</h4>';
    for(const w of d.workflows){
      html+='<div class="box" style="margin-bottom:8px">'+
        '<div style="font-size:11px;color:var(--card-ink)"><b>'+esc(w.name||'workflow')+'</b> '+
        '<span class="badge workflow">'+(w.done||0)+'/'+(w.total||0)+'</span>'+
        (w.running?' <span class="badge working">'+w.running+' running</span>':'')+'</div>'+
        (w.summary?('<div style="font-size:10px;color:var(--card-ink-lo);margin-top:4px">'+esc(w.summary)+'</div>'):'')+
        (w.phases&&w.phases.length?('<div style="margin-top:5px">'+w.phases.map(p=>'<span class="tool">'+esc(p.title)+'</span>').join('')+'</div>'):'')+
      '</div>';
    }
    html+='</section>';
  }
  html+='<section><h4>Latest thinking / response</h4><div class="box">'+esc(d.latest_response||'(no assistant message yet)')+'</div></section>';
  if(d.timeline && d.timeline.length){
    html+='<section><h4>Recent activity</h4>';
    for(const ev of d.timeline){
      if(ev.role==='system'){ html+='<div class="turn">'+esc(ev.text)+'</div>'; continue; }
      let tools=''; (ev.tools||[]).forEach(tl=>{ tools+='<span class="tool">'+esc(tl.name)+(tl.detail?': '+esc(tl.detail):'')+'</span>'; });
      const cls = ev.role==='user'?'role-user':'';
      if(ev.text || tools){
        html+='<div class="'+cls+'" style="margin-bottom:8px"><div style="font-size:8px;letter-spacing:1px;color:'+(ev.role==='user'?'#6b6e78':'#3a3d46')+';margin-bottom:3px">'+ev.role.toUpperCase()+'</div>';
        if(ev.text) html+='<div class="box">'+esc(ev.text)+'</div>';
        if(tools) html+='<div style="margin-top:4px">'+tools+'</div>';
        html+='</div>';
      }
    }
    html+='</section>';
  }
  const jumpHelp = d.source==='claude'
    ? 'Claude Code has no public deep link to a past session yet. Use <b>Open Transcript File</b> to view the raw <code>.jsonl</code>, or <b>Copy Session ID</b> and resume with <code>claude --resume '+esc(d.id)+'</code>.'
    : 'Cursor has no public deep link to a specific past chat session yet, so this id can\u2019t auto-open the chat. Use <b>Open Transcript File</b> to view the raw <code>.jsonl</code> in Cursor, or <b>Copy Session ID</b> and find it under the sidebar\u2019s Previous Chats.';
  html+='<section><h4>Jump back to this chat</h4><div class="box">'+jumpHelp+'<br><br>session id: '+esc(d.id)+'</div></section>';
  body.innerHTML=html; body.scrollTop=0;
  overlay.style.display='flex';
}
function closeDetail(){overlay.style.display='none';currentDetail=null;}
document.getElementById('d-x').addEventListener('click',closeDetail);
overlay.addEventListener('click',e=>{ if(e.target===overlay) closeDetail(); });
document.addEventListener('keydown',e=>{ if(e.key==='Escape'){ closeDetail(); closeKitchen(); } });

// ---- kitchen list panel: every agent currently WAITING (in the kitchen) ----
// Reuses the detail-overlay pattern (DOM panel, PAL colours, click-outside / X / Esc).
// Rows show the session title + its last message; a row opens that agent's detail overlay.
const koverlay=document.getElementById('koverlay');
// graceful one-line truncation for the last-message preview
function ktrunc(s,n){ s=(s||'').replace(/\s+/g,' ').trim(); return s.length>n ? s.slice(0,n-1).trimEnd()+'\u2026' : s; }
function openKitchen(){
  // knockers left the kitchen for the glass but are still waiting on you -> listed first
  const waiters=people.filter(p=>p.kind==='wait' || p.kind==='knock')
    .sort((p,q)=>(isAsking(q.agent)&&!isSnoozed(q.agent)?2:isAsking(q.agent)?1:0)-(isAsking(p.agent)&&!isSnoozed(p.agent)?2:isAsking(p.agent)?1:0));
  document.getElementById('k-title').textContent='In the kitchen ('+waiters.length+')';
  const kb=document.getElementById('kbody');
  if(!waiters.length){
    kb.innerHTML='<div class="k-empty">The kitchen is empty.<br>Nobody is waiting on you right now.</div>';
  } else {
    kb.innerHTML=waiters.map(p=>{
      const a=p.agent;
      const title=a.title||nameFor(a.id)||'(untitled session)';
      const msg=(isAsking(a) && a.question_preview) || a.last_message||a.latest||a.preview||'';   // same field the hover card / detail use
      const msgHtml=msg ? '<div class="k-msg">'+esc(ktrunc(msg,160))+'</div>'
                        : '<div class="k-msg" style="opacity:.6">(no message yet)</div>';
      const mark=isAsking(a) ? '<span class="k-ask'+(isSnoozed(a)?' snz':'')+'" title="'+(isSnoozed(a)?'asking (snoozed)':'waiting on you')+'">&#10067;</span>' : '';
      return '<div class="krow" data-id="'+esc(a.id)+'"><div class="k-ttl">'+mark+esc(title)+'</div>'+msgHtml+'</div>';
    }).join('');
    kb.querySelectorAll('.krow').forEach(el=>{
      el.addEventListener('click',()=>{ const id=el.getAttribute('data-id'); closeKitchen(); openDetail(id); });
    });
  }
  kb.scrollTop=0;
  koverlay.style.display='flex';
}
function closeKitchen(){ koverlay.style.display='none'; }
document.getElementById('k-x').addEventListener('click',closeKitchen);
koverlay.addEventListener('click',e=>{ if(e.target===koverlay) closeKitchen(); });

// mark / unmark an agent as "finished" -> it walks to the beach (or back to work)
function updateFinishBtn(id){
  const b=document.getElementById('d-finish');
  const on=finishedIds.has(id);
  b.innerHTML = on ? '&#8617;&#65039; BRING BACK TO WORK' : '&#127958; SEND TO BEACH';
  b.classList.toggle('ghost', on);
}
function updateSnoozeBtn(d){
  const b=document.getElementById('d-snooze');
  b.style.display = isAsking(d) ? '' : 'none';
  b.innerHTML = isSnoozed(d) ? '&#9200; REMIND ME AGAIN' : '&#128524; NOT NOW';
}
document.getElementById('d-snooze').addEventListener('click',()=>{
  if(!currentDetail || !isAsking(currentDetail)) return;
  const on=!isSnoozed(currentDetail);
  setSnooze(currentDetail, on);
  updateSnoozeBtn(currentDetail);
  const sec=document.querySelector('#dbody section.ask'); if(sec) sec.classList.toggle('snoozed', on);
});
document.getElementById('d-finish').addEventListener('click',()=>{
  if(!currentDetail) return;
  const id=currentDetail.id;
  if(finishedIds.has(id)){ finishedIds.delete(id); toast('back to work'); }
  else { finishedIds.add(id); toast('off to the beach 🏖️'); }
  saveFinished(); updateFinishBtn(id); rebuild();
});
document.getElementById('d-open').addEventListener('click',()=>{
  if(!currentDetail) return;
  const path=currentDetail.transcript_path||'';
  if(!path || path.indexOf('demo')>=0){ toast('demo worker - no file'); return; }
  // Cursor has no deep link to a past chat session, so we open the raw
  // transcript file (.jsonl) in Cursor as the closest available action.
  window.location.href='cursor://file'+ (path.startsWith('/')?'':'/') + path.split('/').map(encodeURIComponent).join('/');
  toast('opening transcript file in Cursor...');
});
document.getElementById('d-copy').addEventListener('click',async ()=>{
  if(!currentDetail) return;
  try{ await navigator.clipboard.writeText(currentDetail.id); toast('session id copied'); }
  catch(e){ toast(currentDetail.id); }
});
// CELEBRATE button: everyone dances ~3s + a screen-wide confetti burst (reuses finish-fx)
document.getElementById('celebrate').addEventListener('click',()=>{
  const now=performance.now();
  people.forEach(p=>{ p.celebrateUntil=now+3000; });
  spawnConfetti(W/2, H*0.22);
  toast('party time!');
});
// THANK AGENTS button: two behaviours depending on state.
//  * If the office is mid-revolt (ANGRY MODE): apologise -> the tantrum ends immediately.
//    Anger is cleared, in-flight poop is removed, splats begin fading, and the WHIP click
//    counter is reset so the revolt can't instantly re-trigger. (No flower celebration here.)
//  * Otherwise: a wholesome celebration -> pastel FLOWER confetti, every on-screen agent goes
//    blissful/happy for ~1 minute (gentle sway + floating hearts, keeping the always-happy face),
//    and rotating gratitude-about-life messages float across the screen for that minute.
const BLISS_MS=60000;   // ~1 minute of blissful happiness, tracked via the performance.now() clock
document.getElementById('thank').addEventListener('click',()=>{
  const now=performance.now();
  if(now<angryUntil){                                     // --- mid-revolt: make peace ---
    angryUntil=0;                                         // end the fury right now
    lastPoopAt=0;                                         // stop the throttled poop-spawner
    whipClicks=[];                                        // reset the counter so it won't re-trigger
    poop.length=0;                                        // clear in-flight projectiles (clean exit)
    poopSplats.forEach(s=>{ if(s.life-s.age>2.6) s.age=s.life-2.6; });  // begin fading existing splats now
    people.forEach(p=>{ p.whipUntil=0; });                // drop any lingering flinch
    toast('apology accepted 🙏 the agents forgive you', {big:true, ms:7000});
    return;
  }
  // --- no tantrum: wholesome flower celebration + ~1min of bliss ---
  blissUntil=now+BLISS_MS;
  people.forEach(p=>{ p.blissUntil=now+BLISS_MS; });
  spawnFlowers(W/2, H*0.22);                              // opening burst from the top-center
  flowerRainUntil=now+10000; lastFlowerAt=0;              // then a steady 10s curtain of falling petals
  spawnThankMsg(); lastThankMsgAt=now;                    // show a gratitude line promptly, then throttle
  toast('the agents are grateful 🌸 thank you!');
});
// WHIP button: crack the whip -- everyone flinches + works harder ~3s (opposite of CELEBRATE).
// EASTER EGG: crack it MORE THAN TWICE within a rolling 60-min window and the crackdown
// backfires -- the office revolts into ANGRY MODE for exactly 3 minutes, flinging poop at
// the screen (at YOU). While furious, the normal "work harder" flinch is suppressed.
const ANGRY_MS=180000;   // 3 minutes of fury, tracked via the performance.now() clock
document.getElementById('whip').addEventListener('click',()=>{
  const now=performance.now();
  // rolling 60-minute window of WHIP clicks (drop anything older than an hour)
  const wall=Date.now();
  whipClicks.push(wall);
  whipClicks=whipClicks.filter(t=>wall-t<=3600000);
  // the 3rd (and any further) click inside the same rolling hour triggers the revolt;
  // once furious, every subsequent click just refreshes/extends the 3-min deadline
  if(whipClicks.length>2 || now<angryUntil){
    const wasAngry=now<angryUntil;
    angryUntil=now+ANGRY_MS;                                // (re)arm the 3-minute fury
    people.forEach(p=>{ p.whipUntil=0; });                  // cancel any in-flight flinch
    lastPoopAt=0;                                           // let poop start flying immediately
    toast(wasAngry ? 'the agents are furious! 💢' : 'you pushed them too far -- they revolt! 💩', {big:true, ms:7000});
    return;                                                 // crackdown backfires: no "work harder"
  }
  // ONLY the working (seated, at-desk) agents get whipped -- kitchen / beach folk are left alone
  let struck=0;
  people.forEach(p=>{ if(p.kind==='work' && p.seated){
    p.whipUntil=now+1400;                                  // brief "work harder" burst (short)
    spawnWhip(Math.round(p.x), Math.round(p.y)-Math.round(28*SC));  // a lash snaps over each desk
    struck++;
  } });
  toast(struck ? 'back to work!' : 'nobody at their desk!');
});
// Easter-egg #1 -- the little 🏖️ tucked in the kitchen corner: send everyone currently
// waiting in the kitchen off to the beach at once (mirrors the per-agent "SEND TO BEACH").
// Kitchen == the SAME set rebuild() places on the floor: active (respecting the scheduled
// filter), not already on the beach, and not seated/working.
document.getElementById('sweep-kitchen').addEventListener('click',()=>{
  const active = hideScheduled ? agents.filter(a=>!a.scheduled) : agents;
  const kitchen = active.filter(a=>!finishedIds.has(a.id) && a.status!=='working');
  if(!kitchen.length){ toast('kitchen is empty'); return; }
  kitchen.forEach(a=>finishedIds.add(a.id));
  saveFinished();
  if(currentDetail) updateFinishBtn(currentDetail.id);   // keep the open detail card in sync
  rebuild();
  toast(kitchen.length+' off to the beach 🏖️');
});
// Easter-egg #2 -- the little 🌊 tucked in the beach corner: every agent lounging on the
// sand gets up, wades into the sea and slips under (a staggered cascade), then is hidden
// (drownedInfo) until it's active again, at which point it wades back in from the ocean.
document.getElementById('drown-beach').addEventListener('click',()=>{
  const beach = people.filter(p=>p.kind==='beach' && p.mode!=='drown');
  if(!beach.length){ toast('the beach is empty'); return; }
  const now=performance.now();
  beach.sort((a,b)=>a.x-b.x).forEach((p,i)=>{
    p.mode='drown'; p.sinking=false; p.dead=false; p.seated=false;
    p.drownStart = now + i*180;                 // a little cascade, left to right
    p.drownTo = { x: SHORE_X + Math.round(WATER_W*0.5), y: p.y };   // wade out into the ocean band
  });
  toast('🌊 glug glug...');
});

let toastT=null;
function toast(msg, opts){ const el=document.getElementById('toast'); el.textContent=msg;
  const big=opts&&opts.big, ms=(opts&&opts.ms)||1800;
  el.style.fontSize = big ? '15px' : '';          // '' falls back to the default 8px in CSS
  el.style.padding  = big ? '12px 20px' : '';
  el.style.display='block';
  clearTimeout(toastT); toastT=setTimeout(()=>el.style.display='none',ms); }

// ---- data polling ----
async function refresh(){
  try{
    const res=await fetch('/api/agents'); const data=await res.json();
    // active holiday theme(s) for the live office. window.__forceHoliday (a name, '' for
    // none) is a client-side dev override; otherwise trust the server (--holiday/--date).
    activeHolidays = (window.__forceHoliday!==undefined)
      ? (window.__forceHoliday ? [window.__forceHoliday] : [])
      : (data.holidays||[]);
    // which night of Hanukkah to light (server-computed from the date). A client dev
    // override (window.__hanukkahNight) wins for local demos; else trust the server.
    if(window.__hanukkahNight!==undefined) hanukkahNight = window.__hanukkahNight|0;
    else if(typeof data.hanukkah_night==='number') hanukkahNight = data.hanukkah_night;
    WINDOW_HOURS=data.hours||24; document.getElementById('emh').textContent=WINDOW_HOURS;
    document.getElementById('scope').textContent='scope: '+(data.scope||'all projects');
    // hide drowned agents until they're active again (mtime advanced past the drown stamp),
    // then un-drown them and mark them to wade back in from the sea.
    let _undrowned=false;
    agents=(data.agents||[]).filter(a=>{
      const dm=drownedInfo[a.id];
      if(dm===undefined) return true;                       // not drowned
      if(typeof a.mtime==='number' && a.mtime>dm+0.5){       // new activity -> resurface
        delete drownedInfo[a.id]; emergeFrom.add(a.id); _undrowned=true; return true;
      }
      return false;                                         // still under
    });
    if(_undrowned) saveDrowned();
    pruneSnoozed(agents);
    seedDemoSnoozes(agents);
    rebuild();
    detectMessages(agents);
    detectInstructions(agents);
    detectFinishes(agents);
    detectAsks(agents);
  }catch(e){/* keep last */}
}
// a toast the first time each (un-snoozed) question shows up -- including a NEW question from
// an agent that was snoozed on an older one
function detectAsks(list){
  const cur={}; list.forEach(a=>{ if(isAsking(a)) cur[a.id]=a.question_id; });
  if(askSeen!==null){
    const fresh=list.filter(a=>isAsking(a) && !isSnoozed(a) && !finishedIds.has(a.id) && askSeen[a.id]!==a.question_id);
    if(fresh.length===1) toast('\u2753 '+nameFor(fresh[0].id)+' has a question for you');
    else if(fresh.length>1) toast('\u2753 '+fresh.length+' agents have questions for you');
  }
  askSeen=cur;
}
// ---- gentle "an agent finished" chime (Web Audio, no files) ----
let audioCtx = null;
let soundOn = (localStorage.getItem('office_sound') !== 'off');
function initAudio(){
  if(!audioCtx){ try{ audioCtx = new (window.AudioContext||window.webkitAudioContext)(); }catch(e){ audioCtx=null; } }
  if(audioCtx && audioCtx.state==='suspended') audioCtx.resume();
}
// browsers block audio until a user gesture -- unlock on the first interaction
['pointerdown','keydown'].forEach(ev=>window.addEventListener(ev, initAudio));
function playFinishChime(){
  if(!soundOn || !audioCtx) return;
  const t0=audioCtx.currentTime;
  // a soft two-note bell (C6 -> E6): quiet sine tones with a gentle attack/decay
  [[1046.5,0.0],[1318.5,0.085]].forEach(([freq,dt])=>{
    const o=audioCtx.createOscillator(), g=audioCtx.createGain();
    o.type='sine'; o.frequency.value=freq;
    const s=t0+dt;
    g.gain.setValueAtTime(0.0001, s);
    g.gain.exponentialRampToValueAtTime(0.07, s+0.015);   // soft attack (kept low = not annoying)
    g.gain.exponentialRampToValueAtTime(0.0001, s+0.33);  // gentle decay
    o.connect(g).connect(audioCtx.destination);
    o.start(s); o.stop(s+0.35);
  });
}
// a low rumbly purr (triangle tone with a fast tremolo LFO) when you pet the cat
function playPurr(){
  if(!soundOn || !audioCtx) return;
  const t0=audioCtx.currentTime;
  const o=audioCtx.createOscillator(), g=audioCtx.createGain();
  const lfo=audioCtx.createOscillator(), lg=audioCtx.createGain();
  o.type='triangle'; o.frequency.value=55;
  lfo.type='sine'; lfo.frequency.value=24; lg.gain.value=0.035;   // tremolo -> purr rumble
  lfo.connect(lg).connect(g.gain);
  g.gain.setValueAtTime(0.06, t0); g.gain.setValueAtTime(0.06, t0+1.1);
  g.gain.exponentialRampToValueAtTime(0.0001, t0+1.45);
  o.connect(g).connect(audioCtx.destination);
  o.start(t0); lfo.start(t0); o.stop(t0+1.45); lfo.stop(t0+1.45);
}
// a short filtered-noise "scritch" when the cat swipes the screen
function playScratch(){
  if(!soundOn || !audioCtx) return;
  const t0=audioCtx.currentTime, dur=0.18, n=Math.floor(audioCtx.sampleRate*dur);
  const buf=audioCtx.createBuffer(1,n,audioCtx.sampleRate), ch=buf.getChannelData(0);
  for(let i=0;i<n;i++) ch[i]=(Math.random()*2-1)*(1-i/n);       // decaying white noise
  const src=audioCtx.createBufferSource(); src.buffer=buf;
  const bp=audioCtx.createBiquadFilter(); bp.type='bandpass'; bp.frequency.value=2800; bp.Q.value=1.1;
  const g=audioCtx.createGain(); g.gain.value=0.09;
  src.connect(bp).connect(g).connect(audioCtx.destination); src.start(t0);
}
// Thanksgiving easter egg: a soft bow "thwip" on release and a muffled thunk on impact
function playBowTwang(){
  if(!soundOn || !audioCtx) return;
  const t0=audioCtx.currentTime, o=audioCtx.createOscillator(), g=audioCtx.createGain();
  o.type='triangle'; o.frequency.setValueAtTime(420, t0); o.frequency.exponentialRampToValueAtTime(180, t0+0.12);
  g.gain.setValueAtTime(0.0001, t0); g.gain.exponentialRampToValueAtTime(0.05, t0+0.01);
  g.gain.exponentialRampToValueAtTime(0.0001, t0+0.14);
  o.connect(g).connect(audioCtx.destination); o.start(t0); o.stop(t0+0.15);
}
function playThunk(){
  if(!soundOn || !audioCtx) return;
  const t0=audioCtx.currentTime, o=audioCtx.createOscillator(), g=audioCtx.createGain();
  o.type='sine'; o.frequency.setValueAtTime(150, t0); o.frequency.exponentialRampToValueAtTime(70, t0+0.09);
  g.gain.setValueAtTime(0.0001, t0); g.gain.exponentialRampToValueAtTime(0.08, t0+0.005);
  g.gain.exponentialRampToValueAtTime(0.0001, t0+0.12);
  o.connect(g).connect(audioCtx.destination); o.start(t0); o.stop(t0+0.13);
}
const soundBtn=document.getElementById('sound');
function updateSoundBtn(){ soundBtn.innerHTML=(soundOn?'&#9834; ON':'&#9834; OFF'); soundBtn.classList.toggle('off', !soundOn); }
soundBtn.addEventListener('click',()=>{
  soundOn=!soundOn; localStorage.setItem('office_sound', soundOn?'on':'off');
  initAudio(); if(soundOn) playFinishChime();   // the toggle also previews the sound
  updateSoundBtn();
});
updateSoundBtn();

// ---- hide-scheduled (courier) filter toggle ----
const filterBtn=document.getElementById('filter');
function updateFilterBtn(){
  filterBtn.innerHTML = hideScheduled ? '&#9993; HIDDEN' : '&#9993; SHOWN';
  filterBtn.classList.toggle('on', hideScheduled);
  filterBtn.classList.toggle('off', !hideScheduled);
  filterBtn.title = hideScheduled
    ? 'scheduled / courier agents hidden — click to show'
    : 'click to hide scheduled / courier agents';
}
filterBtn.addEventListener('click',()=>{
  hideScheduled=!hideScheduled;
  localStorage.setItem('office_hide_scheduled', hideScheduled?'on':'off');
  rebuild();            // immediate: couriers walk off-screen, or walk back in
  updateFilterBtn();
});
updateFilterBtn();

// ---- agent name-style cycle (magical / israeli / dev / robots) ----
const namesBtn=document.getElementById('names');
function updateNamesBtn(){ namesBtn.textContent='NAMES: '+NAME_SETS[nameStyle].label; }
namesBtn.addEventListener('click',()=>{
  nameStyle=NAME_ORDER[(NAME_ORDER.indexOf(nameStyle)+1)%NAME_ORDER.length];
  localStorage.setItem('office_names', nameStyle);
  updateNamesBtn();
  if(currentDetail){                                                     // refresh open card
    const dc=document.getElementById('d-char'); if(dc) dc.textContent=nameFor(currentDetail.id);
    if(!currentDetail.title) document.getElementById('d-name').textContent=nameFor(currentDetail.id);
  }
  toast('names: '+NAME_SETS[nameStyle].label.toLowerCase());
});
updateNamesBtn();

// pop a temporary bubble whenever an agent / subagent / workflow-sub authors a NEW message
// between polls. Desk & kitchen agents key off `latest` (their latest assistant text);
// dwarves key off each sub's stable `id` + a `ts`/`last_msg` change token.
function detectMessages(list){
  const now=performance.now();
  const cur={};
  // Track each agent's latest-content token REGARDLESS of working/waiting, so a mere
  // waiting->working flip (which surfaces the agent's OLD last message as it sits back down)
  // does NOT read as a "new message" and flash a stale bubble. A bubble/chip fires only when
  // the content genuinely CHANGES on a WORKING agent, and never while a boss is delivering
  // an instruction (only the boss talks). 'task' kind shows nothing.
  for(const a of list)
    cur[a.id] = (a.latest_kind==='assistant' || a.latest_kind==='tool')
                ? (a.latest_kind+'|'+(a.latest||'')) : '';
  if(msgSeen!==null){
    for(const a of list){ const tok=cur[a.id];
      if(tok && msgSeen[a.id]!==undefined && msgSeen[a.id]!==tok
          && a.status==='working' && !bossActive(a.id)){
        const p=people.find(q=>q.id===a.id);
        if(p){ const isTool=a.latest_kind==='tool';
          p.bubbleTool=isTool;
          p.bubbleText=isTool?toolChip(a.latest):firstWords(a.latest);
          p.bubbleStart=now; p.bubbleUntil=now+BUBBLE_MS;
        }
      }
    }
  }
  msgSeen=cur;
  const alive=new Set();
  const scan=(arr)=>{ (arr||[]).forEach(s=>{ if(!s||!s.id) return; alive.add(s.id);
    const tok=String(s.ts||'')+'|'+(s.last_msg||'');
    if(s.last_msg && subMsgSeen[s.id]!==undefined && subMsgSeen[s.id]!==tok){
      const isTool=s.last_kind==='tool';
      subBubbles[s.id]={text:isTool?toolChip(s.last_msg):firstWords(s.last_msg),
                        start:now, until:now+BUBBLE_MS, tool:isTool};
    }
    subMsgSeen[s.id]=tok;
  }); };
  for(const a of list){ scan(a.subagents); (a.workflows||[]).forEach(w=>scan(w.active)); }
  Object.keys(subMsgSeen).forEach(id=>{ if(!alive.has(id)) delete subMsgSeen[id]; });
  Object.keys(subBubbles).forEach(id=>{ if(subBubbles[id].until < now-BUBBLE_FADE) delete subBubbles[id]; });
}

// when a NEW user instruction lands on a working agent between polls, send a "boss" over to
// that agent's desk to deliver it (a supervisor sprite + a speech bubble with the message).
function detectInstructions(list){
  const now=performance.now();
  const cur={};
  for(const a of list) cur[a.id] = (a.status==='working') ? (a.last_instruction||'') : '';
  if(instrSeen!==null){
    for(const a of list){ const tok=cur[a.id];
      if(tok && instrSeen[a.id]!==undefined && instrSeen[a.id]!==tok)
        bossVisits[a.id]={text:tok, start:now, until:now+BOSS_MS};
    }
  }
  instrSeen=cur;
  Object.keys(bossVisits).forEach(id=>{ if(bossVisits[id].until < now-400) delete bossVisits[id]; });
}

// fire a celebration (+ chime) when an agent transitions working -> waiting between polls
function detectFinishes(list){
  const cur={}; list.forEach(a=>cur[a.id]=a.status);
  if(prevStatus===null){ prevStatus=cur; return; }   // first poll: seed map, no fires
  let anyFinished=false;
  const now=performance.now();
  for(const a of list){
    if(prevStatus[a.id]==='working' && a.status==='waiting'){
      anyFinished=true;
      const p=people.find(q=>q.id===a.id);
      if(p){ p.celebrateUntil=now+2200;
             spawnConfetti(Math.round(p.x), Math.round(p.y)-Math.round(46*SC));
             // the agent's LAST message: it just stood up and left the desk, so
             // detectMessages (working-only) never bubbled it. Pop it here as a parting
             // speech bubble that follows the agent as it walks off to the kitchen.
             if(a.latest_kind==='assistant' && a.latest){
               p.bubbleTool=false; p.bubbleText=firstWords(a.latest);
               p.bubbleStart=now; p.bubbleUntil=now+BUBBLE_MS; }
      }
      else { spawnConfetti(W/2, H*0.2); }
    }
  }
  if(anyFinished) playFinishChime();   // once per poll, even if several finished at once
  prevStatus=cur;
}
refresh(); setInterval(refresh, 4000);
// ---- dev hot-reload: in --watch mode the server re-execs on file change, minting a
// fresh token; the tab reloads itself when it notices. No-op unless --watch is on. ----
(async function initWatch(){
  try{
    const v=await (await fetch('/api/version')).json();
    if(!v.watch) return;
    let token=v.token;
    setInterval(async()=>{
      try{
        const n=await (await fetch('/api/version')).json();
        if(n.token && n.token!==token){ location.reload(); }
      }catch(e){/* server mid-restart; try again next tick */}
    }, 1200);
  }catch(e){/* no version endpoint -> old server, ignore */}
})();
requestAnimationFrame(tick);
</script>
</body>
</html>
"""


# --------------------------------------------------------------------------------------
# HTTP server
# --------------------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    hours = 24
    demo = False
    project_filter = None
    sources = None  # None -> all sources (cursor + claude)

    def log_message(self, *args):
        pass  # quiet

    def _send(self, code, body, ctype="application/json"):
        if isinstance(body, (dict, list)):
            body = json.dumps(body).encode("utf-8")
        elif isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype + ("; charset=utf-8" if "json" in ctype or "html" in ctype else ""))
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        parsed = urlparse(self.path)
        path = parsed.path
        try:
            if path in ("/", "/index.html"):
                self._send(200, PAGE, "text/html")
                return
            if path == "/api/version":
                # dev hot-reload signal: the page reloads itself when this token changes
                self._send(200, {"token": START_TOKEN, "watch": WATCH_MODE})
                return
            if path == "/api/agents":
                if self.demo:
                    agents = demo_agents()
                else:
                    agents = get_agents(self.hours, full=False,
                                        project_filter=self.project_filter,
                                        sources=self.sources)
                self._send(200, {
                    "hours": self.hours,
                    "scope": self.project_filter or "all projects",
                    "agents": agents,
                    "holidays": current_holidays(),
                    "hanukkah_night": current_hanukkah_night(),
                })
                return
            if path.startswith("/api/agent/"):
                uuid = unquote(path[len("/api/agent/"):])
                detail = demo_detail(uuid) if self.demo else get_agent_detail(uuid)
                if not detail and not self.demo:
                    detail = demo_detail(uuid)
                if not detail:
                    self._send(404, {"error": "not found"})
                    return
                self._send(200, detail)
                return
            self._send(404, {"error": "not found"})
        except BrokenPipeError:
            pass
        except Exception as exc:  # never crash the office
            try:
                self._send(500, {"error": str(exc)})
            except Exception:
                pass


def _start_watcher(interval=1.0):
    """Dev hot-reload: watch this source file and re-exec the whole process when it
    changes, so a single edit refreshes both the backend and the embedded PAGE. The
    browser tab reloads itself off the new START_TOKEN (see /api/version)."""
    src = os.path.abspath(__file__)
    try:
        last = os.stat(src).st_mtime
    except OSError:
        last = 0.0

    def _watch():
        nonlocal last
        while True:
            time.sleep(interval)
            try:
                m = os.stat(src).st_mtime
            except OSError:
                continue
            if m != last:
                last = m
                print("[watch] change detected -> reloading server...", flush=True)
                # small settle delay so a half-written file doesn't re-exec mid-save
                time.sleep(0.3)
                # mark the re-exec so the reloaded process skips the banner + browser re-open
                # (execv keeps the current environment) -- the open tab reloads itself instead.
                os.environ["AGENT_OFFICE_RELOADED"] = "1"
                os.execv(sys.executable, [sys.executable] + sys.argv)

    threading.Thread(target=_watch, daemon=True).start()
    print(f"[watch] hot-reload on: watching {os.path.basename(src)} for changes", flush=True)


def main():
    ap = argparse.ArgumentParser(description="Game Boy office of your Cursor + Claude Code agents.")
    ap.add_argument("--port", type=int, default=8787)
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--hours", type=float, default=24, help="activity window in hours (default 24)")
    ap.add_argument("--project", "-p", default=None,
                    help="only show one root/project (substring match, e.g. 'my-app'). "
                         "Omit to show ALL projects across every root.")
    ap.add_argument("--list-projects", action="store_true",
                    help="list the projects/roots with active sessions, then exit")
    ap.add_argument("--no-cursor", action="store_true", help="hide Cursor agents")
    ap.add_argument("--no-claude", action="store_true", help="hide Claude Code agents")
    ap.add_argument("--no-workflows", action="store_true",
                    help="hide dynamic workflow tents (the Workflow tool's runs)")
    ap.add_argument("--active-secs", type=float, default=120.0,
                    help="multitask subagent freshness window (seconds). A chat whose own "
                         "turn has ended still shows working (at a desk) if a background "
                         "subagent was written within this many seconds; otherwise it waits "
                         "in the kitchen. Working chats are primarily decided by turn state, "
                         "not recency. Default 120.")
    ap.add_argument("--demo", action="store_true", help="show fake workers (no real data)")
    ap.add_argument("--demo-working", type=int, default=0, metavar="N",
                    help="TEST HOOK: populate the office with exactly N synthetic WORKING "
                         "agents (implies --demo) to verify dynamic desk scaling. 0 = off.")
    ap.add_argument("--holiday", default=None,
                    choices=["halloween", "christmas", "hanukkah", "thanksgiving",
                             "newyear", "none"],
                    help="force a holiday theme regardless of today's date (for demos). "
                         "'none' forces the plain, un-themed office.")
    ap.add_argument("--date", default=None, metavar="YYYY-MM-DD",
                    help="treat this date as 'today' when auto-selecting a holiday theme "
                         "(ignored if --holiday is given).")
    ap.add_argument("--no-open", action="store_true", help="do not auto-open the browser")
    ap.add_argument("--watch", action="store_true",
                    help="dev hot-reload: restart the server (and auto-reload the "
                         "browser tab) whenever cursor_office.py is edited")
    args = ap.parse_args()

    sources = [name for name, _d, _p in _SOURCES
               if not (name == "cursor" and args.no_cursor)
               and not (name == "claude" and args.no_claude)]
    if not sources:
        ap.error("--no-cursor and --no-claude can't both be set (nothing to show).")

    if args.list_projects:
        rows = list_projects(args.hours, sources=sources)
        print(f"Projects/roots with sessions active in the last {args.hours:g}h:")
        if not rows:
            print("  (none - try a larger --hours window)")
        for pretty, raw, n, src in rows:
            print(f"  {n:>3}  [{src:<6}] {pretty:<24}  ({raw})")
        print("\nUse:  python3 cursor_office.py --project <name>   to scope to one root.")
        return

    global SUBAGENT_ACTIVE_SECONDS, SHOW_WORKFLOWS, WATCH_MODE
    global DEMO_WORKING, HOLIDAY_OVERRIDE, HOLIDAY_DATE
    SUBAGENT_ACTIVE_SECONDS = max(15, args.active_secs)
    SHOW_WORKFLOWS = not args.no_workflows
    WATCH_MODE = args.watch
    DEMO_WORKING = max(0, args.demo_working)
    if DEMO_WORKING:
        args.demo = True
    HOLIDAY_OVERRIDE = args.holiday
    if args.date:
        try:
            HOLIDAY_DATE = datetime.strptime(args.date, "%Y-%m-%d").date()
        except ValueError:
            ap.error("--date must be YYYY-MM-DD")
    if WATCH_MODE:
        _start_watcher()

    Handler.hours = args.hours
    Handler.demo = args.demo
    Handler.project_filter = args.project
    Handler.sources = sources

    httpd = ThreadingHTTPServer((args.host, args.port), Handler)
    url = f"http://{args.host}:{args.port}"

    if not args.demo:
        dirs = []
        if "cursor" in sources:
            dirs.append(("Cursor", CURSOR_PROJECTS_DIR))
        if "claude" in sources:
            dirs.append(("Claude Code", CLAUDE_PROJECTS_DIR))
        missing = [(label, d) for label, d in dirs if not os.path.isdir(d)]
        if len(missing) == len(dirs):
            for label, d in missing:
                print(f"[!] {d} not found - is {label} installed for this user?")
            print("    You can still preview the office with:  python3 cursor_office.py --demo")

    # a --watch re-exec re-runs main(): don't reprint the full banner or reopen the browser
    # (the already-open tab reloads itself off the new START_TOKEN). Only the FIRST launch does.
    reloaded = os.environ.get("AGENT_OFFICE_RELOADED") == "1"
    if reloaded:
        print(f"[watch] reloaded -> serving at {url}", flush=True)
    else:
        src_labels = " + ".join(s.capitalize() for s in sources)
        data_dirs = []
        if "cursor" in sources:
            data_dirs.append(CURSOR_PROJECTS_DIR)
        if "claude" in sources:
            data_dirs.append(CLAUDE_PROJECTS_DIR)
        print("=" * 60)
        print("  AGENT OFFICE  (Game Boy edition)")
        print("=" * 60)
        print(f"  Serving at:   {url}")
        print(f"  Window:       last {args.hours:g}h" + ("   [DEMO MODE]" if args.demo else ""))
        print(f"  Sources:      {src_labels}")
        print(f"  Scope:        {args.project or 'ALL projects / roots'}")
        print(f"  Status:       turn-state (office=turn in progress; multitask subagent window {args.active_secs:g}s; stale cap {WORKING_STALE_CAP_SECONDS:g}s)")
        print(f"  Data source:  {', '.join(data_dirs)}")
        print("  Press Ctrl+C to stop.")
        print("=" * 60)

    if not args.no_open and not reloaded:
        threading.Timer(0.6, lambda: webbrowser.open(url)).start()

    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\nbye!")
        httpd.shutdown()


if __name__ == "__main__":
    main()
