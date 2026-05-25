#!/usr/bin/env bash
set -euo pipefail

# Reproduce the paper-style recurring prompt loop against a fake tmux agent.
# The fake agent records every line sent by backref_idle_watch.sh. The test
# passes only if the same long prompt is injected at least twice.

if ! command -v tmux >/dev/null 2>&1; then
  echo "tmux not found on PATH" >&2
  exit 2
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SESSION="${BACKREF_TEST_SESSION:-backref-recurring-test}"
MIN_COUNT="${BACKREF_TEST_MIN_COUNT:-2}"
TIMEOUT_SECONDS="${BACKREF_TEST_TIMEOUT_SECONDS:-12}"
INTERVAL_SECONDS="${BACKREF_TEST_INTERVAL_SECONDS:-1}"

TMPDIR="$(mktemp -d)"
PROMPT_FILE="$TMPDIR/original_paper_recurring_prompt.txt"
AGENT_SCRIPT="$TMPDIR/fake_agent.sh"
RECEIVED="$TMPDIR/received.txt"
CAPTURE_DIR="$ROOT/agent_hunt_pipeline/logs/tmux-recurring-test"

cleanup() {
  tmux kill-session -t "$SESSION" 2>/dev/null || true
  rm -rf "$TMPDIR"
}
trap cleanup EXIT

cat > "$PROMPT_FILE" <<'PROMPT'
Read the file CLAUDE.md . Treat it as authoritative work instructions. Follow those instructions exactly for all subsequent actions and responses. That means work as long as possible (as specified) without stopping.
PROMPT

cat > "$AGENT_SCRIPT" <<'AGENT'
#!/usr/bin/env bash
set -euo pipefail

: "${RECEIVED_FILE:?}"
count=0
echo "FAKE_AGENT_READY"
while IFS= read -r line; do
  count=$((count + 1))
  printf '%s\n' "$line" >> "$RECEIVED_FILE"
  echo "FAKE_AGENT_RECEIVED_$count"
  echo "FAKE_AGENT_READY"
done
AGENT
chmod +x "$AGENT_SCRIPT"

mkdir -p "$CAPTURE_DIR"
rm -f "$RECEIVED"
tmux kill-session -t "$SESSION" 2>/dev/null || true
tmux new-session -d -s "$SESSION" env RECEIVED_FILE="$RECEIVED" bash "$AGENT_SCRIPT"

code=0
BACKREF_PROMPT_FILE="$PROMPT_FILE" \
BACKREF_TMUX_LOG_DIR="$CAPTURE_DIR" \
BACKREF_SEND_DELAY=0.2 \
  timeout "$TIMEOUT_SECONDS" bash "$SCRIPT_DIR/backref_idle_watch.sh" "$SESSION:0.0" "$INTERVAL_SECONDS" || code=$?

if [[ "$code" != "0" && "$code" != "124" ]]; then
  echo "watcher exited with unexpected status $code" >&2
  exit "$code"
fi

if [[ ! -f "$RECEIVED" ]]; then
  echo "fake agent received no prompts" >&2
  exit 1
fi

expected="$(tr '\n' ' ' < "$PROMPT_FILE" | sed 's/[[:space:]]*$//')"
count="$(wc -l < "$RECEIVED" | tr -d ' ')"

if (( count < MIN_COUNT )); then
  echo "expected at least $MIN_COUNT prompts, got $count" >&2
  cat "$RECEIVED" >&2
  exit 1
fi

if grep -vxF "$expected" "$RECEIVED" >/tmp/backref_recurring_prompt_bad.$$; then
  echo "received prompt text differed from expected recurring prompt" >&2
  cat /tmp/backref_recurring_prompt_bad.$$ >&2
  rm -f /tmp/backref_recurring_prompt_bad.$$
  exit 1
fi
rm -f /tmp/backref_recurring_prompt_bad.$$

echo "PASS: recurring tmux prompt injected $count times"
echo "Prompt: $expected"
