# Rules for Working on the POSIX Backreference Pilot

These are the authoritative work instructions for coding agents in this
repository. They adapt the publicly described 130k Lines Formal Topology and
Agent Hunt workflows to this Isabelle/HOL POSIX backreference project.

This file is intentionally explicit and somewhat long. It is meant to be read
at the start of every fresh agent session and whenever context has been
compacted.

## Project Identity

- Project: POSIX regex formalization with a backreference pilot.
- Repository: `C:\Users\Chengsong\Documents\AIPV2026Notes\posix`.
- Main remote: `https://github.com/hellotommmy/posix`.
- Isabelle version: `C:\Users\Chengsong\Isabelle2025-2`.
- Current sessions: `Posix` for the inherited development and `BackRefPilot`
  for the backreference pilot.
- Current research phase: value/Prf/flat correspondence for the pilot language.

## Historical Context

- PR #1 added `BackRefLang.thy` and `pilot/ROOT`.
- PR #1 was merged into `origin/main` at merge commit `e207e04`.
- The old branch `codex/backref-pilot` contains the initial language pilot.
- New proof work should start from `origin/main` unless the admin says
  otherwise.
- The next target is controlled carry-over of value evidence, not lexer or
  bounds work.

## Source Documents

Read these before substantial work:

- `agent_hunt_pipeline/projects/posix-backref/SESSION_BRIEF.md`
- `C:\Users\Chengsong\Documents\AIPV2026Notes\backref_agent_hunt_handoff.md`
- `C:\Users\Chengsong\Documents\AIPV2026Notes\backref_agent_hunt_ops_and_prompts.md`
- `agent_hunt_pipeline/references/agent_hunt_rule_search.md`
- `agent_hunt_pipeline/projects/posix-backref/AGENT_ROLES.md`
- `agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md`
- `agent_hunt_pipeline/projects/posix-backref/BRANCHING_AND_RUN_MODE.md`
- `PROGRESS_BACKREF.md`
- `BACKREF_BOUNTIES.md`

## Core Principle

Do not launch into broad formalization. First create a checked statement
blueprint, then extend proofs in small controlled steps.

For this project, the blueprint is the pilot language:

- `BZERO`, `BONE`, `BCH`
- `BSEQ`, `BALT`, `BSTAR`, `BNTIMES`
- `BBACKREF`, `BHALF`, `BRESIDUE`

The backreference constructors are not ordinary regular expression
constructors. Treat them as a separate checked pilot until the core story is
stable.

## Strict Prohibitions

- Do not store or print GitHub PATs or other secrets.
- Do not modify files outside this repository unless the user asks.
- Do not edit `Blexer.thy`, `BlexerSimp.thy`, `FBound.thy`,
  `GeneralRegexBound.thy`, `ClosedForms.thy`, or `ClosedFormsBounds.thy`
  during the value/Prf/flat phase.
- Do not change `BL`, `xnullable`, `xder`, or the meaning of
  `backref_lang` without an explicit admin decision.
- Do not weaken theorem statements to make proofs easy.
- Do not replace real work with axioms or unchecked assumptions.
- Do not leave `sorry` in Isabelle files.
- Do not revert other agents' work.
- Do not use destructive git commands such as `git reset --hard`.

## Allowed Edit Areas

During the current phase, normal worker agents may edit:

- `BackRefValues.thy`
- `pilot/ROOT`
- `PROGRESS_BACKREF.md`
- `BACKREF_BOUNTIES.md`
- small helper files under `agent_hunt_pipeline/scripts/`

Only an admin or merge steward should edit:

- `BackRefLang.thy`
- root `CLAUDE.md`
- this project profile
- `AGENTS.md`
- statement-freeze or governance files

No one should touch old lexer and bounds theories until the value/Prf/flat
pilot is checked.

## Mandatory Start Sequence

At the start of every session:

1. Read this file.
2. Read the handoff and progress files.
3. Run `git fetch --all --prune`.
4. Run `git status --short --branch`.
5. Inspect recent history:

```powershell
git log --oneline --decorate --graph --all -n 20
```

6. Run the relevant Isabelle CI before editing if the planned work depends on
   current proof state.

## Build Commands

Use the local CI wrapper for normal checks:

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin
```

For a quicker pilot-only checkpoint:

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -PilotOnly -Role admin
```

The underlying pilot build uses the bundled Cygwin bash from Isabelle2025-2:

```powershell
C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe -lc 'cd /cygdrive/c/Users/Chengsong/Documents/AIPV2026Notes/posix && /cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle build -v -d pilot BackRefPilot'
```

Successful Isabelle output means the selected sessions are checked. Any error
must be fixed or recorded before claiming progress or collecting bounty.

## Current Checked Facts

`BackRefLang.thy` proves language-level correctness:

- `xnullable_correctness`
- `xder_correctness`
- `xders_correctness`

`BackRefValues.thy` is the value/Prf/flat pilot:

- `bval`
- `bflat`
- `BPrf`
- `BL_flat_BPrf1`
- `BL_flat_BPrf2`
- `BL_flat_BPrf`

The headline value theorem is:

```isabelle
lemma BL_flat_BPrf:
  "BL r = {bflat v | v. BPrf v r}"
```

## Backreference Semantics

The current semantic choice is:

```isabelle
backref_lang A B cs = {x @ y @ rev cs @ x | x y. x \<in> A \<and> y \<in> B}
```

Interpretation:

- `BBACKREF r mid []` accepts `x @ y @ x`.
- `cs` is a reverse accumulator of already consumed capture characters.
- `BHALF mid cs rep` accepts `BL mid ;; {cs}`.
- `BRESIDUE cs rep` accepts `{cs}`.
- `rep` is metadata for reconstruction and is not used semantically yet.

Do not silently change this interpretation.

## Value Semantics

The current value shape is:

- `BBackref v1 v2 cs` flattens to
  `bflat v1 @ bflat v2 @ rev cs @ bflat v1`.
- `BHalf v cs rep` flattens to `bflat v @ cs`.
- `BResidue cs rep` flattens to `cs`.

This is the first checked bridge from language semantics to explicit evidence.
Future lexer work should preserve it or propose an admin-level statement
change.

## Work Strategy

- Make one small checked step at a time.
- Prefer short helper lemmas over large brittle proof scripts.
- Use existing local proof style from `PosixSpec.thy` and `Lexer.thy`.
- Search before adding new concepts.
- Keep helper names descriptive.
- Keep proof statements general enough to be reusable.
- Avoid speculative abstractions.
- When a proof becomes tangled, record the blocker and reduce the target.
- If a statement seems false, stop and write a notice instead of forcing a
  bogus proof.

## Bounty Discipline

This repository uses a competitive-collaborative bounty system adapted from the
Agent Hunt paper (130k Lines Formal Topology). The full protocol is in
`agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md`.

### Total Pool

The total bounty pool is **50,000 simulated USD**. All bounty amounts are
denominated in simulated USD. The pool cap is enforced by the guard script.

### Competitive-Collaborative Rules

- Multiple agents may attempt the same open bounty; the first to complete it
  (per completion rules) collects the bounty.
- Agents may issue sub-bounties from their own balance to request help on
  sub-lemmas.
- If the entire bounty board is completed before the admin-set deadline, a 10%
  bonus of the remaining pool is distributed among agents who completed at
  least one bounty.

### Locking and Earning Mechanics

- **Lock deposit**: 10% of bounty, rounded up. Deducted from agent balance.
- **Maximum locks**: at most **10** active locks per agent.
- **Lock duration**: 24 hours. Expired locks are forfeited (deposit not refunded).
- **Lock-or-lose**: if another agent proves a locked theorem, bounty goes to
  the locker, not the prover.
- **Lock release**: voluntary release before expiry refunds the deposit.
- **Balances cannot go negative**.
- **Push immediately**: locks must be committed and pushed within 5 minutes
  when multiple agents are active.

### Effort Estimates

Every bounty task must include an effort estimate:

1. **Est. Lines**: approximate lines of a textbook proof.
2. **Difficulty**: formalization difficulty on a 1-10 scale.
3. **Est. USD**: approximate cost assuming $100/hour of expert Isabelle work.

These assume all previous results in the dependency chain are proved.

### Task Board

- Open tasks live in `BACKREF_BOUNTIES.md`.
- Claiming a task means locking it (paying the deposit) and recording
  branch/agent.
- Completed tasks must name the theorem or file that checks.
- Bounties have no authority over correctness; only Isabelle checking does.

## Statement Governance and Immutability

Following the Agent Hunt paper, definitions and theorem statements in checked
Isabelle theory files are **frozen** once the admin marks them as such. Agents
cannot change frozen statements to game the system and collect bounties easily.

The statement guard (`backref_statement_guard.py`) enforces immutability:

- Frozen statements are compared against a known snapshot.
- Proof bodies may be modified freely.
- Adding new definitions or lemmas after existing frozen content is allowed.
- Modifying or deleting frozen statements is rejected by the guard.

Statement changes require a note in `PROGRESS_BACKREF.md` with:

- the old statement;
- the proposed new statement;
- why the old statement is wrong or too weak;
- how the change affects downstream work;
- whether Isabelle currently builds.

For major changes, ask the admin before editing.

## Git Discipline

- Fetch before work.
- Commit only checked, coherent changes.
- Pull/rebase before pushing.
- All active agents use the shared branch `codex/backref-values`, unless the
  admin explicitly creates a quarantine branch.
- Use this sync pattern:
  `git pull --rebase --autostash origin codex/backref-values`.
- Do not force-push shared branches unless the admin asks.
- Do not modify another agent's locked theorem or partial proof.

## Merge Steward Rules

The merge steward is allowed to integrate shared-branch work but should not do new proof
research unless needed for a mechanical conflict.

The steward may resolve:

- import list conflicts;
- file ordering conflicts;
- duplicated comments;
- proof script conflicts that preserve statements.

The steward must stop for admin on:

- datatype changes;
- semantic changes to `BL`, `xder`, or `BPrf`;
- theorem statement conflicts;
- conflicts involving old lexer or bounds files.

## Progress Files

Update `PROGRESS_BACKREF.md` after every meaningful checked step.

Include:

- branch;
- commit if available;
- files changed;
- build command;
- build result;
- theorem status;
- next smallest safe step;
- blockers.

If context is getting full, update the progress file before doing anything
else.

## Dependency Awareness

The dependency direction is:

1. `RegLangs.thy`
2. `BackRefLang.thy`
3. `BackRefValues.thy`
4. future mkeps/injval pilot
5. future lexer integration
6. future bitcoded lexer
7. future bounds or bounded-fragment theorems

Do not jump down this chain before the previous layer is checked.

## Agent Roles

Suggested roles for multi-agent work:

- Admin: freezes statements and decides semantic changes.
- Blueprint agent: creates checked definitions and theorem statements.
- Proof worker: proves assigned helper lemmas.
- Merge steward: integrates clean branches and resolves mechanical conflicts.
- Auditor: reviews false statements and proof risks.

For this small pilot, one or two workers plus one steward is enough.

The concrete role assignments live in
`agent_hunt_pipeline/projects/posix-backref/AGENT_ROLES.md`.

## Long-Running CLI Loop

The intended long-running setup is:

```text
Codex or Claude Code CLI
+ tmux
+ agent_hunt_pipeline/scripts/backref_idle_watch.sh
+ CLAUDE.md
+ Isabelle build
+ git
```

The idle watcher should only re-prompt an idle CLI. It must not bypass git,
build, or statement rules.

Use the short prompt in `agent_hunt_pipeline/scripts/backref_resume_prompt.txt`.

## When Resuming

On resume from compacted context or a fresh chat:

1. Read this file.
2. Read `agent_hunt_pipeline/projects/posix-backref/SESSION_BRIEF.md`.
3. Read `PROGRESS_BACKREF.md`.
4. Run git status and fetch.
5. Verify which branch you are on.
6. Build before making proof edits.
7. Continue the smallest safe task.

Do not trust memory alone.

## Quality Bar

A completed proof step must satisfy:

- Isabelle build passes for every session named in the bounty verifier column.
- GitHub Actions or local CI emits a passing CI certificate.
- No `sorry`, `oops`, `axiomatization`, `quick_and_dirty`, `oracle`, or admit
  marker in Isabelle theory files.
- No frozen statement modifications (statement guard passes).
- No unrelated file churn.
- No hidden statement weakening.
- Progress file updated.
- Next task is clear.

## Guard Scripts

All guards must be run locally before every commit:

| Guard | File | Checks |
| --- | --- | --- |
| Bounty guard | `backref_bounty_guard.py` | Non-negative balances, positive bounties, max 10 locks, lock expiry, ledger consistency, pool cap, effort estimates |
| No-cheat guard | `backref_no_cheat_guard.py` | No sorry/oops/axiomatization/quick_and_dirty/oracle/admit outside comments |
| Role guard | `backref_role_guard.py` | Changed files within agent's role scope |
| Statement guard | `backref_statement_guard.py` | Frozen definition/theorem statements unchanged |

Guards are run locally rather than as blocking git hooks, permitting coordinated
structural changes when the admin needs them. After resolving any
inconsistencies, the guards must pass before pushing.

## Stop Conditions

Stop and report if:

- Isabelle build fails and the fix is not local.
- A theorem appears false.
- You need to change semantics.
- You hit a merge conflict in frozen statements.
- You are tempted to edit Blexer or bounds early.
- You see a secret or credential.

## Final Report Format

When ending a session, report:

- branch;
- changed files;
- checked theorem or rule;
- build result;
- remaining task;
- any admin questions.

Keep it short and factual.
