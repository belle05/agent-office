#!/usr/bin/env bash
# Fixed launcher for Cursor Office.
# Always starts a clean instance: stops any old server on the port, then runs.
# Usage:
#   ./run.sh                 # default (24h window, opens browser)
#   ./run.sh --hours 48      # pass any cursor_office.py flags through
#   PORT=9000 ./run.sh       # use a different port
set -euo pipefail
cd "$(dirname "$0")"

PORT="${PORT:-8787}"

if lsof -ti "tcp:${PORT}" >/dev/null 2>&1; then
  echo "Stopping existing server on port ${PORT}..."
  lsof -ti "tcp:${PORT}" | xargs kill -9 2>/dev/null || true
  sleep 1
fi

echo "Starting Cursor Office on http://127.0.0.1:${PORT}  (Ctrl+C to stop)"
exec python3 cursor_office.py --port "${PORT}" "$@"
