# POSIX Backref Bounty Protocol

This document defines the competitive-collaborative bounty system for the POSIX
backreference formalization pilot. It adapts the Agent Hunt bounty mechanics
described in the 130k Lines Formal Topology paper to this Isabelle/HOL project.

The bounty system is a coordination layer for multiple agents. It does not
replace Isabelle checking. A payout is recognized only when the corresponding
Isabelle sessions pass.

## Files

- `BACKREF_BOUNTIES.md`: task board, balances, locks, ledger, and pool status.
- `agent_hunt_pipeline/scripts/backref_bounty_guard.py`: validates the board.
- `agent_hunt_pipeline/scripts/backref_no_cheat_guard.py`: rejects Isabelle
  proof-bypass markers such as `sorry`.
- `agent_hunt_pipeline/scripts/backref_statement_guard.py`: enforces
  immutability of frozen definition and theorem statements.
- `agent_hunt_pipeline/scripts/isabelle_ci.ps1`: local Windows CI entrypoint.
- `.github/workflows/isabelle.yml`: remote GitHub Actions proof check.
- `agent_hunt_pipeline/projects/posix-backref/AGENT_ROLES.md`: roles and scopes.

## Total Bounty Pool

The total bounty pool for this project is **100,000 simulated USD**.

All bounty amounts are denominated in simulated USD. The pool is the maximum
total payout across all agents. Bounties are allocated by the admin and
tracked in `BACKREF_BOUNTIES.md` under the `## Pool` section.

| Category | Amount |
| --- | ---: |
| Total pool | 100,000 |
| Allocated (active + completed bounties) | sum of all bounty amounts |
| Collected (paid out) | sum of COLLECT ledger entries |
| Reserved (unallocated) | 100,000 minus allocated |

The guard script validates that total allocated bounties never exceed the pool.

## Competitive-Collaborative System

Following the Agent Hunt paper, agents compete for theorem bounties but are
incentivized to collaborate to finish early and earn bonuses.

- **Competition**: multiple agents may attempt the same open bounty. The first
  to complete it (per the completion rules) collects the bounty.
- **Collaboration**: agents may issue sub-bounties from their own balance to
  request help on sub-lemmas. Sub-bounties are tracked in the ledger.
- **Early-finish bonus**: if the entire allocated bounty board is completed
  before the admin-set deadline, a 10% bonus of the remaining pool is
  distributed equally among agents who completed at least one bounty.

## Task Statuses

- `OPEN`: available for any agent to attempt or lock.
- `LOCKED`: reserved by an agent who paid the lock deposit.
- `DONE`: checked and completed; bounty collected.
- `BLOCKED`: cannot proceed without admin/steward action.
- `DROPPED`: removed by admin; deposit refunded if locked.

## Locking and Earning Mechanics

These rules replicate the Agent Hunt paper locking system:

1. **Lock deposit**: to lock a bounty, an agent pays 10% of the bounty amount
   (rounded up to the nearest integer). The deposit is deducted from the
   agent's balance and recorded as a `LOCK` ledger entry.
2. **Maximum locks**: an agent may hold at most **10** active locks at any time.
3. **Lock duration**: each lock expires after **24 hours**. Expired locks must
   be removed (status changed to `EXPIRED`) and the deposit is forfeited
   (not refunded).
4. **Lock-or-lose**: if another agent proves a locked theorem, the bounty
   still goes to the locker (the agent who locked it). The proving agent
   receives no bounty for that theorem but may negotiate a sub-bounty.
5. **Lock release**: an agent may voluntarily release a lock before expiry.
   The deposit is refunded (recorded as a `RELEASE` ledger entry).
6. **Balances cannot go negative**: the guard rejects any transaction that
   would make an agent's balance negative.
7. **Lock must be pushed immediately**: when multiple agents are active, a
   new lock must be committed and pushed within 5 minutes.

## Sub-Bounty Mechanism

An agent may offer a sub-bounty from their own balance:

1. Create a new task in the Active table with `Sub-bounty of BR-XXX` in Notes.
2. Record a `SUB_OFFER` ledger entry deducting the amount from the offering
   agent's balance.
3. The sub-bounty follows normal completion rules.
4. On completion, the completing agent receives the sub-bounty via a `COLLECT`
   entry.
5. If cancelled, the offering agent gets a refund via a `SUB_CANCEL` entry.

## Effort Estimates

Following the Agent Hunt blueprint methodology, every bounty task must include
an effort estimate before it can be locked or attempted:

| Field | Description |
| --- | --- |
| Est. Lines | approximate lines of a textbook proof |
| Difficulty | formalization difficulty on a 1-10 scale |
| Est. USD | approximate cost assuming $100/hour of expert Isabelle work |

These estimates assume all previous results in the dependency chain are already
proved. The admin sets initial estimates; agents may propose revisions with
justification in `PROGRESS_BACKREF.md`.

Effort estimates serve as pricing guidance. Actual bounty amounts may differ
from estimates based on strategic importance.

## Statement Immutability

Definitions and theorem statements in checked Isabelle theory files are frozen
once the admin marks them as such. The statement guard enforces this:

- Frozen statements are identified by their position in the theory file.
- The guard compares the current file against the last known frozen snapshot.
- Proof bodies (between statement and `done`/`qed`) may be modified freely.
- Adding new definitions or lemmas after existing frozen content is allowed.
- Modifying or deleting frozen statements is rejected.

An agent who needs a statement change must:

1. Record the proposed change in `PROGRESS_BACKREF.md`.
2. Explain why the current statement is wrong or too weak.
3. Wait for admin approval before editing.

## Completion Rules

A bounty is complete only when:

- the relevant theorem/file is named in the `Artifact` column;
- the `Verifier` column names the CI obligation, normally `Isabelle:BackRefPilot`
  or `Isabelle:Posix`;
- the no-cheat guard finds no `sorry`, `oops`, `axiomatization`,
  `quick_and_dirty`, `oracle`, or `admit` marker in Isabelle theory files;
- the statement guard confirms no frozen statements were modified;
- the required Isabelle session builds with Isabelle2025-2 default
  `quick_and_dirty=false`;
- all bounty and role guard checks pass;
- `BACKREF_BOUNTIES.md` ledger records the completion.

The ledger entry alone does not pay the bounty. The payout is recognized only
for a commit whose local or GitHub CI certificate says the corresponding
Isabelle sessions passed.

## Bounty Eligibility

Wrapper-only theorem packages are not bounty-eligible. A wrapper-only package
is a set of lemmas that mainly restates, bundles, renames, specializes, or
combines already checked facts without adding a new semantic definition, a new
algorithmic definition, or a nontrivial proof bridge that was missing before.

Examples of non-eligible work:

- frontend equality summaries that are direct `simp` consequences of existing
  correctness theorems;
- `*_cases`, `*_iff`, `*_same`, and `*_retrieve_eq` facts that merely repackage
  existing acceptance/rejection theorems;
- downstream boundedness/cardinality restatements that only instantiate an
  already proved finite-family theorem.

Eligible bounties must target one of:

- a new checked semantic or algorithmic layer;
- a central correctness theorem whose proof is not just theorem packaging;
- a proof-system bridge, such as a rewriting relation, derivative-commutation
  theorem, value/retrieval preservation theorem, or finite-bound theorem that
  is needed by later work.

When in doubt, mark the task `BLOCKED` and ask the admin before locking or
collecting it. Existing wrapper facts may stay in the repository as useful API
surface, but they are documentation/interface conveniences, not bounty
deliverables.

## Strategic Guidance

Following the Agent Hunt paper:

- **Prioritize major theorems** over small exercises for better financial and
  project impact.
- **Avoid reverting or losing work**: never undo another agent's checked proof.
- **Progress should be continuous and incremental**: small commits, frequent
  pushes, careful merges.
- **Stay in scope**: do not edit outside the allowed file set for your role.

## Guard Scripts

Guards must be run locally before every commit. The guards enforce:

| Guard | Checks |
| --- | --- |
| `backref_bounty_guard.py` | Non-negative balances, positive bounties, max 10 locks, lock expiry within 24h, bounty collection rules, ledger balance consistency, total pool cap, effort estimates present |
| `backref_no_cheat_guard.py` | No sorry/oops/axiomatization/quick_and_dirty/oracle/admit in theory files (outside comments) |
| `backref_role_guard.py` | Changed files are within the agent's role scope |
| `backref_statement_guard.py` | Frozen definition/theorem statements unchanged |

The guards are intentionally run locally rather than as blocking git hooks,
permitting coordinated structural changes when the admin needs them.
