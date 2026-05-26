# Backreference Pilot Bounties

This is the competitive-collaborative bounty board for the POSIX backreference
formalization pilot. It follows the Agent Hunt bounty mechanics: agents compete
for theorem bounties but are incentivized to collaborate.

Amounts are in simulated USD. A payout is valid only when the named artifact
exists, the guards pass, and the required Isabelle CI session succeeds.

See `agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md` for the
full rules including locking, sub-bounties, effort estimates, and statement
immutability.

## Pool

| Category | Amount |
| --- | ---: |
| Total pool | 50,000 |
| Allocated (active + completed) | 23,770 |
| Collected (paid out) | 7,470 |
| Reserved (unallocated) | 26,230 |

## Agent Balances

| Agent | Role | Balance | Notes |
| --- | --- | ---: | --- |
| Codex | Admin/Worker | 1,270 | Completed BR-001 through BR-004, BR-006, BR-007, BR-009, BR-010, and BR-021 |
| Opus | Worker | 6,200 | Completed BR-005, BR-011, BR-012, BR-013, and BR-014 in Cursor/Codex collaboration |
| MergeSteward | Steward | 0 | Integration role |
| Alice | Worker | 0 | Optional future worker |
| Bob | Worker | 0 | Optional future worker |

## Active

| ID | Task | Bounty | Est. Lines | Difficulty | Est. USD | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |
| BR-008 | Draft derivative story for generalized `backref_lang4` | 800 | 60 | 6 | 800 | OPEN | - | - | Isabelle:BackRefPilot | Do not migrate datatype yet |
| BR-015 | POSIX value ordering for backreferences | 2,500 | 120 | 8 | 2,500 | OPEN | - | - | Isabelle:BackRefPilot | Major theorem |
| BR-016 | Generalized `backref_lang4` value pilot | 1,500 | 70 | 7 | 1,500 | OPEN | - | - | Isabelle:BackRefPilot | Blueprint before migration |
| BR-017 | Bitcoded backreference lexer definition | 2,500 | 100 | 8 | 2,500 | OPEN | - | - | Isabelle:BackRefPilot | Depends on BR-014 |
| BR-018 | Bitcoded backreference lexer correctness | 3,000 | 150 | 9 | 3,000 | OPEN | - | - | Isabelle:BackRefPilot | Depends on BR-017 |
| BR-019 | Bounded fragment theorem for backreferences | 4,000 | 200 | 9 | 4,000 | OPEN | - | - | Isabelle:BackRefPilot | Major theorem; do not start before lexer |
| BR-020 | Simplification rules for backreference lexer | 2,000 | 90 | 7 | 2,000 | OPEN | - | - | Isabelle:BackRefPilot | Depends on BR-017 |

## Completed

| ID | Task | Bounty | Est. Lines | Difficulty | Est. USD | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |
| BR-001 | Language nullable/derivative pilot | 200 | 80 | 6 | 200 | DONE | Codex | BackRefLang.thy:BL_BBACKREF_empty,xnullable_correctness,xder_correctness,xders_correctness | Isabelle:BackRefPilot | PR #1, merged |
| BR-002 | Value/Prf/flat correspondence pilot | 160 | 60 | 6 | 160 | DONE | Codex | BackRefValues.thy:BL_flat_BPrf | Isabelle:BackRefPilot | `BackRefValues.thy`, build passes |
| BR-003 | Add `bmkeps` for pilot nullable values | 80 | 20 | 4 | 80 | DONE | Codex | BackRefValues.thy:bmkeps | Isabelle:BackRefPilot | `bmkeps` in `BackRefValues.thy` |
| BR-004 | Prove `bmkeps` flat/prf correctness | 120 | 30 | 5 | 120 | DONE | Codex | BackRefValues.thy:bmkeps_flat,bmkeps_BPrf | Isabelle:BackRefPilot | `bmkeps_flat`, `bmkeps_BPrf` |
| BR-005 | Draft `binjval` statement blueprint | 500 | 30 | 5 | 500 | DONE | Opus | BackRefValues.thy:binjval | Isabelle:BackRefPilot | Commit `b9da0e1` |
| BR-006 | Add guard scripts for bounty/role checks | 60 | 10 | 3 | 60 | DONE | Codex | agent_hunt_pipeline/scripts/backref_bounty_guard.py;agent_hunt_pipeline/scripts/backref_role_guard.py | LocalGuards | `backref_bounty_guard.py`, `backref_role_guard.py` |
| BR-007 | Generalized four-language backreference blueprint | 160 | 20 | 5 | 160 | DONE | Codex | BackRefLang.thy:backref_lang4,backref_lang_as_backref_lang4 | Isabelle:BackRefPilot | `backref_lang4`, `backref_lang_as_backref_lang4` |
| BR-009 | Local and GitHub Isabelle CI with anti-cheat gate | 260 | 15 | 4 | 260 | DONE | Codex | agent_hunt_pipeline/scripts/isabelle_ci.ps1;agent_hunt_pipeline/scripts/backref_no_cheat_guard.py;agent_hunt_pipeline/scripts/write_ci_certificate.py;.github/workflows/isabelle.yml | Isabelle:Posix+BackRefPilot | CI certificate only after both sessions pass |
| BR-010 | Reproduce recurring tmux prompt loop | 90 | 10 | 3 | 90 | DONE | Codex | agent_hunt_pipeline/scripts/backref_idle_watch.sh;agent_hunt_pipeline/scripts/test_tmux_recurring_prompt.sh;agent_hunt_pipeline/WINDOWS_RUNBOOK.md | WSL:tmux-recurring-test | Same paper prompt injected repeatedly |
| BR-011 | Prove `bflat (binjval r c v) = c # bflat v` | 1,000 | 40 | 6 | 1,000 | DONE | Opus | BackRefValues.thy:binjval_flat | Isabelle:BackRefPilot | Commit `6dc8e03` |
| BR-012 | Prove `BPrf (binjval r c v) r` when `BPrf v (xder c r)` | 1,200 | 50 | 7 | 1,200 | DONE | Opus | BackRefValues.thy:binjval_BPrf | Isabelle:BackRefPilot | Commit `6dc8e03` |
| BR-013 | Define and prove `blexer` for pilot `brexp` | 1,500 | 80 | 7 | 1,500 | DONE | Opus | BackRefValues.thy:blexer,blexer_BPrf,blexer_flat,blexer_correct_None,blexer_correct_Some | Isabelle:BackRefPilot | Commit `2e8c45a` |
| BR-014 | Prove `blexer` correctness for pilot `brexp` | 2,000 | 100 | 8 | 2,000 | DONE | Opus | BackRefValues.thy:blexer_correctness,BPosix_binjval,blexer_POSIX,blexer_POSIX_iff | Isabelle:BackRefPilot | Cursor proof lane, Codex stabilization/build verification |
| BR-021 | Cursor/Opus loop startup kit | 140 | 15 | 4 | 140 | DONE | Codex | .cursor/hooks/posix_loop.ps1;.cursor/hooks/posix_loop.sh;agent_hunt_pipeline/projects/posix-backref/loop-config.cursor-opus.json;agent_hunt_pipeline/projects/posix-backref/SLEEP_RUNBOOK.md | CursorHook:posix-loop | Supplemental robust hook and sleep runbook |

## Effort Estimate Key

Every bounty must include an effort estimate before it can be locked:

- **Est. Lines**: approximate lines of a textbook proof for this result.
- **Difficulty**: formalization difficulty on a 1-10 scale (1 = trivial, 10 = research-level).
- **Est. USD**: approximate cost assuming $100/hour of expert Isabelle work.

Estimates assume all previous results in the dependency chain are already proved.

## Locks

| Lock ID | Task ID | Agent | Deposit | Branch | Expires UTC | Status |
| --- | --- | --- | ---: | --- | --- | --- |
| - | - | - | 0 | - | - | RELEASED |

## Lock Rules

- Lock deposit: 10% of bounty, rounded up.
- Maximum **10** active locks per agent.
- Locks expire after **24 hours**.
- Push locks immediately if multiple agents are active.
- Lock-or-lose: if someone else proves a locked theorem, bounty goes to locker.
- A lock does not authorize statement changes.
- Admin can clear stale locks.
- Expired lock deposit is forfeited (not refunded).

## Ledger

| Time UTC | Agent | Action | Task ID | Amount | Balance After | Notes |
| --- | --- | --- | --- | ---: | ---: | --- |
| 2026-05-22T14:00:00Z | Codex | COLLECT | BR-001 | 200 | 200 | Language nullable/derivative pilot merged in PR #1 |
| 2026-05-22T14:20:00Z | Codex | COLLECT | BR-002 | 160 | 360 | Value/Prf/flat correspondence |
| 2026-05-22T14:28:00Z | Codex | COLLECT | BR-003 | 80 | 440 | `bmkeps` definition |
| 2026-05-22T14:28:00Z | Codex | COLLECT | BR-004 | 120 | 560 | `bmkeps` flat and Prf correctness |
| 2026-05-25T16:24:31Z | Opus | COLLECT | BR-005 | 500 | 500 | `binjval` definition |
| 2026-05-24T02:58:00Z | Codex | COLLECT | BR-006 | 60 | 620 | Bounty and role guard scripts |
| 2026-05-24T02:58:00Z | Codex | COLLECT | BR-007 | 160 | 780 | Generalized `backref_lang4` blueprint |
| 2026-05-25T03:40:00Z | Codex | COLLECT | BR-009 | 260 | 1,040 | Local and remote Isabelle CI gates |
| 2026-05-25T04:22:00Z | Codex | COLLECT | BR-010 | 90 | 1,130 | Recurring tmux prompt reproduction |
| 2026-05-25T15:24:00Z | Codex | COLLECT | BR-021 | 140 | 1,270 | Cursor/Opus loop startup kit |
| 2026-05-25T23:24:27Z | Opus | COLLECT | BR-011 | 1,000 | 1,500 | `binjval_flat` |
| 2026-05-25T23:24:27Z | Opus | COLLECT | BR-012 | 1,200 | 2,700 | `binjval_BPrf` |
| 2026-05-25T23:37:17Z | Opus | COLLECT | BR-013 | 1,500 | 4,200 | pilot `blexer` definition and language correctness |
| 2026-05-26T03:58:00Z | Opus | COLLECT | BR-014 | 2,000 | 6,200 | `blexer_correctness`, `BPosix_binjval`, `blexer_POSIX`, `blexer_POSIX_iff`; Codex stabilized build |

## Sub-Bounty Rules

An agent may offer a sub-bounty from their own balance to request help:

1. Create a new task in Active with `Sub-bounty of BR-XXX` in Notes.
2. Record a `SUB_OFFER` ledger entry deducting from the offering agent.
3. Sub-bounty follows normal completion and guard rules.
4. Cancellation: `SUB_CANCEL` entry refunds the offering agent.

## Early-Finish Bonus

If the entire allocated bounty board is completed before the admin-set
deadline, 10% of the remaining unallocated pool is distributed equally among
agents who completed at least one bounty.

Run the full local CI before collecting or pushing:

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin
```
