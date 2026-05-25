#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
CONFIG="${POSIX_LOOP_CONFIG:-$ROOT/loop-config.json}"
STATE_DIR="$ROOT/.cursor/loop-state"
LOG_DIR="$ROOT/agent_hunt_pipeline/logs/cursor-loop"

json_escape() {
  python3 -c 'import json,sys; print(json.dumps(sys.stdin.read())[1:-1])'
}

hook_json() {
  local decision="$1"
  local message="$2"
  printf '{"decision":"%s","followup_message":"%s"}\n' "$decision" "$(printf '%s' "$message" | json_escape)"
}

if [[ ! -f "$CONFIG" ]]; then
  hook_json stop "POSIX loop is not enabled. Copy agent_hunt_pipeline/projects/posix-backref/loop-config.cursor-opus.json to loop-config.json first."
  exit 0
fi

task="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1], encoding="utf-8")).get("task",""))' "$CONFIG")"
if [[ -z "${task// }" ]]; then
  hook_json stop "loop-config.json has no task."
  exit 0
fi

mkdir -p "$STATE_DIR" "$LOG_DIR"
state="$STATE_DIR/state.json"
iteration=1
if [[ -f "$state" ]]; then
  iteration="$(python3 -c 'import json,sys; p=sys.argv[1]; print(json.load(open(p)).get("iteration",0)+1)' "$state" 2>/dev/null || echo 1)"
fi
python3 -c 'import json,sys,datetime; json.dump({"iteration": int(sys.argv[2]), "updated_utc": datetime.datetime.utcnow().isoformat()+"Z", "config": sys.argv[1]}, open(sys.argv[3],"w"), indent=2)' "$CONFIG" "$iteration" "$state"

validation="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1], encoding="utf-8")).get("validation_command",""))' "$CONFIG")"
validation_shell="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1], encoding="utf-8")).get("validation_shell","bash"))' "$CONFIG")"
message=""
if [[ -n "${validation// }" ]]; then
  log="$LOG_DIR/cursor_loop_$(date +%Y%m%d_%H%M%S)_iter${iteration}.log"
  set +e
  if [[ "$validation_shell" == "powershell" ]]; then
    powershell.exe -NoProfile -ExecutionPolicy Bypass -Command "$validation" >"$log" 2>&1
  else
    bash -lc "$validation" >"$log" 2>&1
  fi
  code=$?
  set -e
  output="$(tail -c 12000 "$log")"
  if [[ "$code" -ne 0 ]]; then
    message="Validation failed. Fix this before continuing:
$output"
  else
    message="Validation passed."
  fi
fi

hook_json continue "$message

LOOP ITERATION: $iteration

ONGOING POSIX BACKREF TASK:
$task"
