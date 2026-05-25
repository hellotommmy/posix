#!/usr/bin/env bash
set -euo pipefail

# Watch a tmux pane and re-prompt an idle Codex/Claude Code CLI session.
# For a cross-platform dry-run test, use idle_reprompt.py instead.
# Usage:
#   scripts/backref_idle_watch.sh <tmux-target> [interval-seconds]
#
# Example:
#   scripts/backref_idle_watch.sh backref-agent:0.0 60

TARGET="${1:-}"
INTERVAL="${2:-60}"

if [[ -z "$TARGET" ]]; then
  echo "Usage: $0 <tmux-target> [interval-seconds]" >&2
  exit 2
fi

if ! command -v tmux >/dev/null 2>&1; then
  echo "tmux not found on PATH" >&2
  exit 2
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROMPT_FILE="${BACKREF_PROMPT_FILE:-$SCRIPT_DIR/backref_resume_prompt.txt}"
OUTDIR="${BACKREF_TMUX_LOG_DIR:-$SCRIPT_DIR/../.agent-hunt/tmux}"
SEND_DELAY="${BACKREF_SEND_DELAY:-2}"

mkdir -p "$OUTDIR"

if [[ ! -f "$PROMPT_FILE" ]]; then
  echo "Prompt file not found: $PROMPT_FILE" >&2
  exit 2
fi

last_capture=""

while true; do
  ts="$(date +"%Y%m%d_%H%M%S_%N")"
  current="$OUTDIR/capture_$ts.txt"
  tmux capture-pane -t "$TARGET" -p -S -200 > "$current"

  if [[ -n "$last_capture" ]] && cmp -s "$current" "$last_capture"; then
    prompt="$(tr '\n' ' ' < "$PROMPT_FILE" | sed 's/[[:space:]]*$//')"
    tmux send-keys -t "$TARGET" "$prompt"
    sleep "$SEND_DELAY"
    tmux send-keys -t "$TARGET" Enter
  fi

  last_capture="$current"
  sleep "$INTERVAL"
done
