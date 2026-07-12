# Agent Office — orientation for a fresh session

A single self-contained Python file, `cursor_office.py`, that serves a Game Boy-style
pixel-art "office" visualizing your local AI coding agents (Cursor + Claude Code). Each
live chat is a little worker: **working** agents sit at a **desk** and type; agents
**waiting** on you stand in the **kitchen**; archived ones lounge on the **beach**.
No dependencies beyond Python 3.8+. Nothing leaves the machine — it binds `127.0.0.1`
and reads your own local transcript files.

## ⚠️ Read this first: there is no auto-reload

`cursor_office.py` builds the **entire** UI (HTML/CSS/JS/canvas) as one big Python string
`PAGE` (starts ~line 1701) and the HTTP handler serves it verbatim. **Editing the file
does nothing to an already-running server.** After any edit you must restart the server
and hard-reload the browser, or run with `--watch` (below). This has burned every past
session — always `ps aux | grep cursor_office` to see what's actually running, and
restart the exact port you're looking at. See memory `serve-from-inmemory-page`.

## Dev loop

```bash
python3 -m py_compile cursor_office.py          # always compile-check after an edit
python3 cursor_office.py --watch --demo --port 9100 --no-open   # dev: hot-reload + fake data
```

- `--watch` — a daemon thread re-`execv`s the process when the file changes, and the open
  browser tab reloads itself via `/api/version` (token = `pid-mtime`). This is the fast
  dev path: edit → save → the tab refreshes on its own. (Added 2026-07-10.)
- `--demo` — fabricated workers incl. one live **Workflow** run, so you can QA visuals
  with no real data. Real workflow easels only appear when a Claude session has a
  genuinely-live `Workflow` run, which is rare — so QA tents on `--demo`.
- `--no-cursor` / `--no-claude` / `--no-workflows`, `--project <substr>`, `--hours N`,
  `--list-projects`, `--active-secs N`. Default port 8787; `./run.sh` is a fixed-port launcher.
- **QA is visual** — use the Chrome browser tools to screenshot/zoom the running office
  and check console for errors. Pixel-art tuning can't be trusted from code alone.

## Architecture map (all in `cursor_office.py`)

**Backend (Python, top of file → ~line 1701):**
- Discovery: `discover_transcripts()` (Cursor) + `discover_claude_transcripts()` (Claude),
  registered in `_SOURCES`. `get_agents()` / `get_agent_detail()` are the API entry points
  the `Handler` serves at `/api/agents` and `/api/agent/<uuid>`.
- Working-vs-waiting: `_is_working(turn_in_progress, eff_mtime, sub_files, wf_latest)` —
  decided by **turn state**, not raw file recency. `_turn_in_progress_claude` returns
  `''`/`'tool'`/`'reply'`; it skips injected user-role lines and treats a trailing
  `[Request interrupted by user…]` (Esc/Ctrl-C) as turn-done, so interrupted chats go to the kitchen.
- Subagents (Task tool): `_subagent_infos` / `_active_sub_count` → helper-dwarf sprites.
- Open background shells (Claude, working desks only): `_open_shells_claude(path)` →
  terminal-window sprites. Running = a `Bash run_in_background` tool_use with no terminal
  `<task-notification>` for its `backgroundTaskId` (mirrors Claude's own "N shells"; blind to
  external `kill`). See memory `open-shells-backend`.
- Dynamic Workflows (Workflow tool): `_discover_workflow_runs` → `_workflow_progress`
  (+ `_workflow_identities`, `_find_workflow_script`/`_parse_workflow_script`, `_phase_states`).
  See memory `workflow-tent-backend` for the on-disk shape and the **stale-gate** (a
  `started`-without-`result` only counts as running if its agent file is fresh within
  `SUBAGENT_ACTIVE_SECONDS`; else 190 dead tents show). Per-phase counts are deliberately
  **not fabricated** — the phase→agent mapping isn't on disk.
- Usage: `_claude_usage()` → token/spend/model in the hover card. `_last_user_instruction()`
  returns the last *real* user message (skips injected/system user-role lines).
- `Handler` (~4643), `_start_watcher` (~4708), `main()` (argparse, ~4740). Demo:
  `demo_agents()`/`demo_detail()`.

**Frontend (the `PAGE` string, ~1701 → ~4640):** vanilla canvas pixel-art.
- Building blocks: `px()` (rect), `ro()` (rounded/outlined rect), `scaleAbout(ax,ay,s)`,
  `shade()`, `hash()`. Logical canvas `W=704,H=576` (11/9, matches `#screen`'s CSS
  aspect-ratio), super-sampled by `SS`.
- Each desk is drawn by `drawDeskPod(x,y,p,t)` **scaled ×1.5 (`SC`) about its own anchor**
  — this matters for geometry (see gotcha below). Sprites: `drawHelper` (subagent dwarf),
  `drawStanding` (kitchen/beach), `drawCourier` (scheduled jobs), `drawWorkflowTent`
  (the whiteboard easel), `drawShellWin` (open-shell terminal), `drawBoss` (supervisor
  escorting a new instruction), `drawDrowning` (a beach agent slipping under — see the
  easter eggs below). `render()`/`tick()` are the frame loop; `refresh()` polls
  `/api/agents` every 4s. `NAME_SETS`/`nameStyle` = the NAMES button (default `israeli`).
- **Bottom-corner emoji easter eggs** (label-less HTML buttons overlaid on `#screen`, faint
  until hover; no tooltip on purpose): `#sweep-kitchen` (🏖️, kitchen/left corner) sends every
  waiting agent to the beach at once; `#drown-beach` (🌊, beach/right corner) makes every beach
  agent wade into the sea and sink (`drawDrowning`), then **hides** them (persisted
  `drownedInfo` = `{id: mtime-at-drown}`) — filtered out of every `refresh()` poll **until the
  agent is active again** (a poll where its `mtime` has advanced past the stamp), at which point
  it un-drowns and **wades back in from the sea**: `emergeFrom` (a transient Set) makes `rebuild`
  spawn it at the far-right water strip (`SEA`) and walk to its desk/kitchen spot instead of the
  usual doorway. Sink progress (`p.sinkT`) is
  computed **once in `tick()`** and read in `render()` — never recompute it from
  `performance.now()` on the draw side; a stale/negative value makes `drawDrowning`'s ripple
  radius negative and **`ctx.ellipse` throws `IndexSizeError`, which kills the rAF loop and
  freezes the ENTIRE office**. `drawDrowning` also clamps `st` to `[0,1]` defensively for the
  same reason. QA gotcha: a **backgrounded/unfocused tab pauses `requestAnimationFrame`**, so
  animations look frozen in automated screenshots even when the code is fine — pump `tick(ts)`
  manually with advancing timestamps (each call renders) or foreground the tab to verify motion.
- Ephemeral change-detection (between 4s polls): `detectMessages` (speech bubbles + tool
  chips — `toolChip()` keeps the file/target, e.g. `EDIT service.py`), `detectInstructions`
  (boss visits, suppress the agent's own bubble while a boss is talking), `detectFinishes`
  (celebrate + a parting bubble as the agent leaves the desk).
- Text wrapping helpers: `wrapTextMid` (word-wrap, breaks inside long tokens) and
  `wrapChars` (char-wrap, packs most text) — both take a trailing `ell` arg (`''` = no
  ellipsis), used by the workflow name and the desk name-plate.

## Visual vocabulary (what the sprites mean)

| Sprite | Meaning |
|---|---|
| Worker at a **desk**, typing | chat whose turn is in progress (working) |
| Worker in the **kitchen** | chat waiting on your reply |
| Worker on the **beach** | you archived it ("send to beach") |
| **Courier** (uniform + envelope) | scheduled/cron/automated agent |
| **Helper dwarf** by a desk | a running Task-tool subagent |
| **Whiteboard easel** (2 wheeled legs) beside a desk | a live dynamic **Workflow** run (name, done/total; its base dwarves = running workflow subagents, each hoverable individually; board hover = phase stepper) |
| Desk **name-plate** | that agent's current task, on a little placard |
| **Terminal windows** above the name-plate (≤3) | that chat's open background shells; hover = command + output tail |
| **Suited "boss"** beside/walking with an agent | delivering a new user instruction (walks the agent in from the kitchen; only the boss shows a bubble) |
| **Dim** desk screen | parent seated only because a background subagent is live (it isn't typing itself) |

## Geometry gotcha (whiteboard / name-plate)

Because each pod is scaled **×1.5 about its own anchor**, a local offset of `d` from the
anchor lands at `anchor + d*1.5` on screen, and the ×1.5 also applies to *vertical*
offsets — so a lower desk's raised whiteboard ends up at the **same screen height** as the
name-plate of the desk above it. The desk grid is 3 columns at logical x = 140 / 352 / 564
(`left=140, right=W-140`, `rowH=128`), canvas 704 wide — the insets were widened from 104 so
the leftmost desk's helper dwarves (which reach ~`anchor−106` local) and the rightmost desk's
easel (which reaches ~`anchor+78` local → `+117px` screen) no longer clip the canvas edge.
The name-plate spans `anchor±28` local (`±42px` screen); the shell terminals sit in a row just
above it; the workflow easel sits to the desk's **right** and must keep its left edge past
`anchor+42px` screen or it butts into the upper desk's name-plate.

## Conventions

- **Persistent knowledge lives in Markdown + the memory system.** Keep in-repo notes and
  the auto-memory (`~/.claude/projects/<enc>/memory/`, index `MEMORY.md`) updated as you
  learn non-obvious things — many future sessions work here with no other context.
  Current memories: `serve-from-inmemory-page`, `workflow-tent-backend`, `open-shells-backend`.
- Single-file on purpose: everything is `cursor_office.py`; keep it self-contained.
- Match the existing pixel-art construction style (`px`/`ro` blocks) when adding sprites.
