# POSIX Backref Bounty Protocol

The bounty system is a coordination layer for multiple agents. It does not
replace Isabelle checking.

## Files

- `BACKREF_BOUNTIES.md`: task board, balances, locks, and ledger.
- `agent_hunt_pipeline/scripts/backref_bounty_guard.py`: validates the board.
- `agent_hunt_pipeline/scripts/backref_no_cheat_guard.py`: rejects Isabelle
  proof-bypass markers such as `sorry`.
- `agent_hunt_pipeline/scripts/isabelle_ci.ps1`: local Windows CI entrypoint.
- `.github/workflows/isabelle.yml`: remote GitHub Actions proof check.
- `agent_hunt_pipeline/projects/posix-backref/AGENT_ROLES.md`: roles and scopes.

## Task Statuses

- `OPEN`: available.
- `LOCKED`: reserved by an agent.
- `DONE`: checked and completed.
- `BLOCKED`: cannot proceed without admin/steward action.
- `DROPPED`: removed by admin.

## Lock Rules

- A worker may hold at most three active locks.
- Lock duration is 24 hours.
- Lock deposit is 10 percent of bounty, rounded up.
- A lock must name an agent, branch, and expiry timestamp.
- A lock does not authorize semantic or statement changes.

## Completion Rules

A bounty is complete only when:

- the relevant theorem/file is named;
- the `Artifact` column names a concrete theorem/definition or file path;
- the `Verifier` column names the CI obligation, normally `Isabelle:BackRefPilot`
  or `Isabelle:Posix`;
- the no-cheat guard finds no `sorry`, `oops`, `axiomatization`,
  `quick_and_dirty`, `oracle`, or admit marker in Isabelle theory files;
- the required Isabelle session builds with Isabelle2025-2 default
  `quick_and_dirty=false`;
- all bounty and role guard checks pass;
- `BACKREF_BOUNTIES.md` ledger records the completion.

The ledger entry alone does not pay the bounty. The payout is recognized only
for a commit whose local or GitHub CI certificate says the corresponding
Isabelle sessions passed. A certificate is an audit receipt, not a substitute
for proof checking; the trusted event is still the Isabelle build.

## Current Scale

This is intentionally smaller than the Agent Hunt paper. We are using simulated
tokens to coordinate two or three agents, not a full market.
