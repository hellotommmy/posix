#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ISABELLE_BIN="${ISABELLE_BIN:-isabelle}"
ROLE="${ROLE:-admin}"
PILOT_ONLY="${PILOT_ONLY:-0}"

python3 "$ROOT/agent_hunt_pipeline/scripts/backref_no_cheat_guard.py" --root "$ROOT"
python3 "$ROOT/agent_hunt_pipeline/scripts/backref_bounty_guard.py" --file "$ROOT/BACKREF_BOUNTIES.md"
python3 "$ROOT/agent_hunt_pipeline/scripts/backref_role_guard.py" --role "$ROLE"

sessions=()
if [[ "$PILOT_ONLY" != "1" ]]; then
  sessions+=("Posix")
  "$ISABELLE_BIN" build -v -d "$ROOT" Posix
fi

sessions+=("BackRefPilot")
"$ISABELLE_BIN" build -v -d "$ROOT/pilot" BackRefPilot

cert_args=(
  "$ROOT/agent_hunt_pipeline/scripts/write_ci_certificate.py"
  --root "$ROOT"
  --out "$ROOT/agent_hunt_pipeline/certificates/local_ci_certificate.json"
  --ci-name "local-shell"
  --isabelle-version "$("$ISABELLE_BIN" version)"
)
for session in "${sessions[@]}"; do
  cert_args+=(--session "$session")
done
python3 "${cert_args[@]}"
