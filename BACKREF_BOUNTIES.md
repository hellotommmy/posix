# Backreference Pilot Bounties

This is a lightweight coordination file, not a standalone correctness
mechanism. A payout is valid only when the named artifact exists, the guards
pass, and the required Isabelle CI session succeeds.

Amounts are simulated tokens. They are meant to help agents choose useful work.

## Agent Balances

| Agent | Role | Balance | Notes |
| --- | --- | ---: | --- |
| Codex | Admin/Worker | 1130 | Completed BR-001 through BR-010 |
| Opus | Worker | 0 | Available for Cursor collaboration |
| MergeSteward | Steward | 0 | Integration role |
| Alice | Worker | 0 | Optional future worker |
| Bob | Worker | 0 | Optional future worker |

## Active

| ID | Task | Bounty | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | --- | --- | --- | --- | --- |
| BR-005 | Draft `binjval` statement blueprint | 120 | OPEN | - | - | - | No lexer integration yet |
| BR-008 | Draft derivative story for generalized `backref_lang4` | 180 | OPEN | - | - | - | Do not migrate datatype yet |

## Completed

| ID | Task | Bounty | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | --- | --- | --- | --- | --- |
| BR-001 | Language nullable/derivative pilot | 200 | DONE | Codex | BackRefLang.thy:BL_BBACKREF_empty,xnullable_correctness,xder_correctness,xders_correctness | Isabelle:BackRefPilot | PR #1, merged |
| BR-002 | Value/Prf/flat correspondence pilot | 160 | DONE | Codex | BackRefValues.thy:BL_flat_BPrf | Isabelle:BackRefPilot | `BackRefValues.thy`, build passes |
| BR-003 | Add `bmkeps` for pilot nullable values | 80 | DONE | Codex | BackRefValues.thy:bmkeps | Isabelle:BackRefPilot | `bmkeps` in `BackRefValues.thy` |
| BR-004 | Prove `bmkeps` flat/prf correctness | 120 | DONE | Codex | BackRefValues.thy:bmkeps_flat,bmkeps_BPrf | Isabelle:BackRefPilot | `bmkeps_flat`, `bmkeps_BPrf` |
| BR-006 | Add guard scripts for bounty/role checks | 60 | DONE | Codex | agent_hunt_pipeline/scripts/backref_bounty_guard.py;agent_hunt_pipeline/scripts/backref_role_guard.py | LocalGuards | `backref_bounty_guard.py`, `backref_role_guard.py` |
| BR-007 | Generalized four-language backreference blueprint | 160 | DONE | Codex | BackRefLang.thy:backref_lang4,backref_lang_as_backref_lang4 | Isabelle:BackRefPilot | `backref_lang4`, `backref_lang_as_backref_lang4` |
| BR-009 | Local and GitHub Isabelle CI with anti-cheat gate | 260 | DONE | Codex | agent_hunt_pipeline/scripts/isabelle_ci.ps1;agent_hunt_pipeline/scripts/backref_no_cheat_guard.py;agent_hunt_pipeline/scripts/write_ci_certificate.py;.github/workflows/isabelle.yml | Isabelle:Posix+BackRefPilot | CI certificate only after both sessions pass |
| BR-010 | Reproduce recurring tmux prompt loop | 90 | DONE | Codex | agent_hunt_pipeline/scripts/backref_idle_watch.sh;agent_hunt_pipeline/scripts/test_tmux_recurring_prompt.sh;agent_hunt_pipeline/WINDOWS_RUNBOOK.md | WSL:tmux-recurring-test | Same paper prompt injected repeatedly |

## Locks

| Lock ID | Task ID | Agent | Deposit | Branch | Expires UTC | Status |
| --- | --- | --- | ---: | --- | --- | --- |
| - | - | - | 0 | - | - | RELEASED |

## Ledger

| Time UTC | Agent | Action | Task ID | Amount | Balance After | Notes |
| --- | --- | --- | --- | ---: | ---: | --- |
| 2026-05-22T14:00:00Z | Codex | COLLECT | BR-001 | 200 | 200 | Language nullable/derivative pilot merged in PR #1 |
| 2026-05-22T14:20:00Z | Codex | COLLECT | BR-002 | 160 | 360 | Value/Prf/flat correspondence |
| 2026-05-22T14:28:00Z | Codex | COLLECT | BR-003 | 80 | 440 | `bmkeps` definition |
| 2026-05-22T14:28:00Z | Codex | COLLECT | BR-004 | 120 | 560 | `bmkeps` flat and Prf correctness |
| 2026-05-24T02:58:00Z | Codex | COLLECT | BR-006 | 60 | 620 | Bounty and role guard scripts |
| 2026-05-24T02:58:00Z | Codex | COLLECT | BR-007 | 160 | 780 | Generalized `backref_lang4` blueprint |
| 2026-05-25T03:40:00Z | Codex | COLLECT | BR-009 | 260 | 1040 | Local and remote Isabelle CI gates |
| 2026-05-25T04:22:00Z | Codex | COLLECT | BR-010 | 90 | 1130 | Recurring tmux prompt reproduction |

## Lock Rules

- Maximum three active locks per worker in this small pilot.
- Locks expire after 24 hours.
- Push locks immediately if multiple agents are active.
- A lock does not authorize statement changes.
- Admin can clear stale locks.

Run the full local CI before collecting or pushing:

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin
```
