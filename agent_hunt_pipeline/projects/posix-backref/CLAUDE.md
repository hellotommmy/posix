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
- Current research phase: migrate the checked pilot ideas back into the
  original `Posix` theories after admin approval. The target interface is the
  original `rexp`, `val`, `arexp`, `lexer`, `blexer`, and `bsimp` chain.

## Historical Context

- PR #1 added `BackRefLang.thy` and `pilot/ROOT`.
- PR #1 was merged into `origin/main` at merge commit `e207e04`.
- The old branch `codex/backref-pilot` contains the initial language pilot.
- Current branch for shared work is `codex/backref-values` unless the admin
  says otherwise.
- The next target is an original-file migration plan: direct extension of
  `RegLangs.thy`, `PosixSpec.thy`, `Lexer.thy`, `Blexer.thy`,
  `BlexerSimp.thy`, and downstream bounds files. Implementation waits for
  admin approval of the TODO audit.

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

The backreference constructors started as a separate checked pilot, but the
current goal is to fold them back into the original files. Do not create new
parallel regex datatypes. The final regex datatypes should be the original
`rexp` and annotated `arexp`; pilot-only `brexp`, `gbrexp`, `barexp`, and
`gabexp` are migration scaffolding only.

## Cubic Bound Smoke-First Rule

The non-backref cubic size-bound project is smoke-test gated. Do not try to
prove a cubic theorem for a simplifier candidate until the candidate has first
passed the executable Scala smoke gate and the small Isabelle theorem/sanity
facts that belong in `FBound.thy`.

Experimental/grid/enumeration tests belong in ordinary executable code, not in
large Isabelle `eval` lemmas. For this project the gate is
`agent_hunt_pipeline/scala/PosixCubicSmoke.scala`, runnable via
`agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1` and by full
`isabelle_ci.ps1`. The Scala model intentionally mirrors the non-backref
lexer/simplifier definitions and performs exact POSIX value comparisons:
`bsimpCubic` must produce the same decoded POSIX value/bitcode result as the
baseline derivative lexer on bounded generated regexes and inputs. Language
preservation alone is not enough for a cubic candidate.

Default CI runs the bounded exhaustive smoke only. Before any cubic proof or
bounty attempt, also run deterministic deeper random smoke, for example
`scala_cubic_smoke.ps1 -RandomCases 2000 -RandomDepth 5 -RandomInputLength 6`.
If random smoke finds a POSIX value mismatch, the candidate is diagnostic only
until the simplifier or value-reconstruction story is repaired.

Do not count destructive sequence reassociation as a POSIX-value-preserving
output simplification. The Scala diagnostic mode localized a current
`bsimpCubic` gap to `(x.y).z -> x.(y.z)`: full reassociation controls the
Chapter 7 size trace but fails deterministic random value smoke, while
`no-reassoc` preserves tested values but grows beyond the threshold. Even the
tempting restriction "only reassociate when the left factor is non-nullable"
failed random value smoke. Reassociation may be used as a comparison key,
proof-only normalization, or generalized-value transfer route, but production
`bsimpCubic` needs a checked bitcode/value reconstruction theorem before it can
emit reassociated syntax.

The newest promising route is shared representation rather than destructive
syntax change. The Scala harness reports tree size, exact DAG size, and
shape-DAG size for Chapter 7 traces. Value-safe `no-reassoc` fails the old
tree threshold but has much smaller DAG measures, suggesting a hash-consed
row universe or delayed linear-form representation. Use those diagnostics to
guide design, but do not claim a tree-size theorem or bounty from DAG evidence
alone; the shared representation and POSIX-value reconstruction must be stated
and checked.

There is an optional executable reconstruction prototype:
`scala_cubic_smoke.ps1 -SharedNoReassoc`. The switch name is retained for
compatibility, but the shared diagnostic now follows the current `-SeqMode`.
It hash-conses states, expands the final root back to an ordinary `arexp`, and
checks exact decoded POSIX values. Passing this smoke is evidence that the
shared representation route is semantically plausible, but it is not yet a
direct shared derivative algorithm because the current prototype still uses
tree derivatives before interning. The next serious candidate should move bder
and simplification to node IDs/delayed rows.

The `expanded-keyed-no-reassoc` diagnostic is the current smoke version of the
virtual-row accumulator idea. Its pruning key may index `a.c` and `b.c` when a
prior row has shape `(a+b).c`, but it still emits `no-reassoc` output syntax.
This is promising because it exposes Antimirov-style row coverage without
directly distributing POSIX value-carrying syntax. It remains smoke evidence
only until reconstruction/value theorems are stated and checked.

Keep the measurement honest. On the thesis Figure 7.6 `k=5` family,
`bsimpStrong` gives the expected hundreds-scale ordinary tree trace; the
value-safe `expanded-keyed-no-reassoc` mode still has larger ordinary trees,
although its exact DAG/shape-DAG are compact. Do not treat shared-DAG evidence
as a tree-size reproduction of `strongBlexer` unless the candidate theorem is
explicitly about the shared representation and includes reconstruction.

Also keep the value story honest. The optional `scala_cubic_smoke.ps1
-CheckStrong` gate currently fails for `bsimpStrong` on `STAR (STAR (CH a))`
with input `a`, because the strong simplifier collapses nested-star bit/value
structure. A future tree-level strong route must repair that simplifier or add
a checked generalized-value reconstruction theorem before any POSIX/cubic
bounty can rely on it.

The CE-driven `bsimpStrongSafe` diagnostic is useful but not the destination.
It disables nested-star collapse, nonempty right-unit deletion, star absorption,
and sequence reassociation in output syntax; this passes deeper exact-value
Scala smoke but loses the Figure 7.6 tree-size plateau. The next tree-level
route should keep the small strong regex and carry local value transformers for
those rewrites, then prove reconstruction to the original `val`.

Use `scala_cubic_smoke.ps1 -TraceStrongRecon` to check the current executable
sketch for that route. It verifies the first CE witnesses with local
reconstruction equations while keeping the actual `bsimpStrong` small output.
It also runs annotated-value local certificate laws for the rewrite rules that
caused those CEs. Treat it as route evidence only; a bounty candidate still
needs a compositional derivative-time certificate or theorem.

Use `scala_cubic_smoke.ps1 -CheckStrongCoreCert` to check the current
compositional certificate prototype for the sequence/star core of
`bsimpStrong`. The prototype returns a simplified regex plus a value
transformer for derivative-expression epsilon values. It now includes
alternation flatten/distinct certificates, but deliberately does not certify
Antimirov row pruning yet, so do not treat it as BR-039 completion.

Use `scala_cubic_smoke.ps1 -TraceStrongCore` to compare the certified core size
against thesis `bsimpStrong`. The current gap on Chapter 7 points to
shared-suffix row pruning as the next certificate target.

Certified row pruning is contextual to the surrounding `AALTs`: a deleted later
row is justified by an earlier row with the same suffix and POSIX priority.
Never state this as a standalone equivalence of the later row. After the first
prototype, Chapter 7 k=5,n=30 certified core is `678`, below thesis
`bsimpStrong` at `958`; the remaining semantic gap is stating and checking the
proof-facing invariant.

Use `scala_cubic_smoke.ps1 -CheckStrongCoreLoop` for the current whole-input
certificate smoke. It composes `bder`, `bsimpStrongCoreCert`, `injectA`, and an
accumulated continuation to reconstruct the original POSIX value. This is the
main executable gate for the certified-core route.

Use `scala_cubic_smoke.ps1 -CheckStrongFullLoop -FindStrongFullCE` as a CE
miner for the user's preferred "keep the `bsimpStrong` tree" idea. Do not
promote this local-certificate route to a proof target while it still fails the
greedy sequence CE
`SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`.

The current positive version of "keep the `bsimpStrong` tree and still get the
right answer" is `scala_cubic_smoke.ps1 -CheckStrongDeferredMemo`: `bdersStrong`
is only the small nullable acceptance certificate, and exact POSIX values are
reconstructed from original `(regex, input)` spans. This gate now includes the
known nested-star and greedy-sequence CEs, so keep it green before trying any
Isabelle proof route based on the strong tree plateau.

When measuring this route on the Chapter 7 family, use
`scala_cubic_smoke.ps1 -TraceStrongDeferredMemo` with explicit tree/DAG/shape
thresholds. This trace is a guard, not just a report: it checks reconstructed
value flatness, memo span/split universe bounds, and the selected size
thresholds. Do not run the old baseline derivative lexer on the full Chapter 7
trace; that path is heap-explosive and recreates the old growth problem. Exact
baseline POSIX value equality belongs in the bounded exhaustive/random and
known-CE smoke grids. Treat either a small tree with a bad value or a correct
value with an exploding tree as the next counterexample to repair before proof
work.

For regex-size budget pressure, add `-Ch7StrongCubicFactor 1.0` (or the
corresponding `-ScalaSmokeCh7StrongCubicFactor 1.0` in full CI). This enforces
`asize(final strong tree) <= factor * rsize(root)^3` on the Chapter 7 grid.
Keep this distinct from the fixed thesis-regression tree threshold: the former
tests the shape of a cubic claim, while the latter checks that the k=5 example
stays in the Figure 7.6 scale.

Also run the general budget gate with `-StrongCubicFactor 1.0` (or
`-ScalaSmokeStrongCubicFactor 1.0`). This applies the same cubic-shaped size
budget to the exhaustive, known-CE, and random `StrongDeferredMemo` smoke
cases. A candidate that only passes the Chapter 7 family but fails this general
grid should be treated as a fresh CE, not as a proof target.

Before proof work, read
`agent_hunt_pipeline/projects/posix-backref/CERTIFIED_STRONG_CORE.md`. It is
the current proof-facing spec for replacing Scala closures with an Isabelle
relation and loop invariant.

Minimum smoke coverage for a serious cubic candidate:

- Shared-suffix pruning: `(a+b).c + (a+d).c` must eliminate the repeated
  `a.c` contribution without losing the `b.c` and `d.c` alternatives.
- Thesis Chapter 7 evil family: the three-layer star shape
  `((a* + (aa)* + ... + (a...a)*)*)*` must not exhibit the old exponential
  growth behavior under repeated derivatives.
- Bounded regex enumeration: generate all regexes up to a selected depth over a
  small alphabet and compare exact POSIX values over all strings up to a
  selected length. Depth `3` is intentionally not a casual default: it expands
  to tens of millions of raw regexes, so use the cap and random smoke rather
  than accidentally running the machine out of memory.
- Counterexample pressure tests C/D/E/F or later successors must expose
  concrete weaknesses of older simplifiers and show the new candidate fixing
  them. Put broad grids in Scala; keep only compact theorem-facing sanity
  lemmas in Isabelle.

If the candidate is already known to lack a necessary pruning/simplification
operation, stop and re-scope it as diagnostic work. Do not continue with a
proof route just because Isabelle can state conditional cubic hooks. Bounty for
a proof route may only be locked after the smoke suite passes; failed smoke
tests revoke or block the proof bounty.

`rsimp9` is historical evidence only. It repaired some root-safe and counted
repetition issues, but it is not the shared-suffix/Chapter-7 pruning candidate
and must not be used as a payout artifact for the cubic theorem.

## Antimirov/POSIX Pruning Insight

The cubic route must take Antimirov partial derivatives seriously, but cannot
copy the set construction naively. Antimirov-style partial derivatives and
linear forms gain their small-state behavior by viewing derivative results as
sets of rows/continuations. In that setting it is natural to expose the shared
suffix structure of `(a+b).c` by treating it like the rows `a.c` and `b.c`, so
duplicate or covered rows can be removed by set reasoning.

Reference point: Valentin Antimirov, "Partial derivatives of regular
expressions and finite automaton constructions", Theoretical Computer Science
155(2), 1996, DOI `10.1016/0304-3975(95)00182-4`. The relevant proof idea is
that all partial derivatives of a regex form a finite set bounded by the number
of letter occurrences plus one; our POSIX problem is how to recover comparable
deduplication without losing value shape.

The POSIX lexer setting has an extra invariant: the parse value/bitcode shape
matters. Blindly distributing `(a+b).c` to `a.c + b.c` can preserve language but
change POSIX values, for example from `Seq (Left x) y` to `Left (Seq x y)`.
Therefore the central research problem is to get Antimirov-like deduplication
without destructively changing the value semantics.

Acceptable design routes include, but are not limited to:

- a stronger `bsimp`/`rsimp` that performs shared-suffix pruning while keeping
  a proof of POSIX value reconstruction;
- delayed or indexed linear forms that can compare rows across associative
  boundaries without expanding the executable regex structure;
- proof-only normalization plus executable reconstruction;
- a generalized POSIX value/equivalence layer where shapes such as
  `Seq (Left x) y` and `Left (Seq x y)` are related, followed by a transfer
  theorem back to the original POSIX value semantics.

Every cubic proof attempt must state which route it is using and how POSIX
value preservation or reconstruction is handled.

## Strict Prohibitions

- Do not store or print GitHub PATs or other secrets.
- Do not modify files outside this repository unless the user asks.
- Do not implement changes to `RegLangs.thy`, `PosixSpec.thy`, `Lexer.thy`,
  `Blexer.thy`, `BlexerSimp.thy`, `FBound.thy`, `GeneralRegexBound.thy`,
  `ClosedForms.thy`, or `ClosedFormsBounds.thy` until the admin approves the
  TODO audit. Comment-only audit edits are allowed.
- Do not keep simplified two-part `backref_lang` as the final semantics.
  The original `L` semantics should use the approved four-part
  `backref_lang4` shape directly.
- Do not weaken theorem statements to make proofs easy.
- Do not replace real work with axioms or unchecked assumptions.
- Do not leave `sorry` in Isabelle files.
- Do not revert other agents' work.
- Do not use destructive git commands such as `git reset --hard`.
- Do not introduce axioms that duplicate theorems you want to prove.
- Do not add definitions or lemmas that already exist -- always search first.
- Do not pursue a cubic-bound proof for a simplifier that has not passed the
  required smoke suite or is known to miss a required shared-suffix/pruning
  rule.

## ABSOLUTE RULE: Never Throw Away Useful Work

This rule exists because in the 130k Lines paper, an agent accidentally
discarded 9,000 lines (more than a day of work) in a single backup step.
This must never happen in this project.

1. **Never revert to a previous state without salvaging all useful work**
   done in between. If there is a major reason for reverting, you must
   ensure that all compiling theorems and definitions added since are kept.
2. **Simple check after every commit**: compare the line count of changed
   theory files against the previous commit. If a file got shorter, you must
   explicitly justify the decrease in the commit message and confirm that no
   useful checked work was lost.

   ```powershell
   git diff --stat HEAD~1
   ```

3. **If you discover a screwup** (lost work), immediately start salvaging
   the lost definitions and theorems. Do not proceed with new work until
   salvage is complete.
4. **Gradual approach**: when a proof is hard, use temporary `sorry` in
   specific branches and keep gradually eliminating them (recording each
   `sorry` in `PROGRESS_BACKREF.md`). Do NOT delete a partially-complete
   proof. This is preferable to giving up and reverting.
5. **Never overwrite another agent's work**. If a merge conflict arises
   with another agent's checked proof, escalate to the merge steward.

## Allowed Edit Areas

During the current phase, normal worker agents may edit:

- Comment-only TODO audit notes in original theory files.
- `PROGRESS_BACKREF.md`
- `BACKREF_BOUNTIES.md`
- small helper files under `agent_hunt_pipeline/scripts/`

Only after admin approval may workers implement direct original-file changes in:

- `RegLangs.thy`
- `PosixSpec.thy`
- `Lexer.thy`
- `LexerSimp.thy`
- `Blexer.thy`
- `BlexerSimp.thy`
- `BasicIdentities.thy`
- `GeneralRegexBound.thy`
- `ClosedForms.thy`
- `ClosedFormsBounds.thy`
- `FBound.thy`

Only an admin or merge steward should edit root governance files, statement
freeze files, or bounty policy.

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

These rules absorb lessons from the 130k Lines paper where recurring agent
failures were turned into rules.

### Core Discipline

- Make one small checked step at a time.
- Prefer short helper lemmas over large brittle proof scripts.
- Use existing local proof style from `PosixSpec.thy` and `Lexer.thy`.
- Keep helper names descriptive.
- Keep proof statements general enough to be reusable.
- Avoid speculative abstractions.

### Search Before Creating

- **Always search** all current definitions and theorems before creating a
  new one. Avoid duplicates. Run:

  ```powershell
  rg "lemma|definition|fun|datatype" BackRefValues.thy BackRefLang.thy
  ```

- **Completely trust** all checked theorems in the pre-backreference theories
  (`RegLangs.thy`, `PosixSpec.thy`, `Lexer.thy`). Build on them; never
  attempt to re-prove them.

### Balancing Easy and Hard Work

- Doing easy things is initially OK. However, do not endlessly jump around
  looking for easy things -- that wastes time.
- Balance simple infrastructure lemmas with more challenging results.
- **Strong focus on major theorems** (the bounty targets): prioritize them
  even if they are hard, over doing many small helper lemmas that are not
  on the critical path.
- Use gradual/partial approaches for difficult proofs when needed: structure
  bigger proofs into useful top-level/helper lemmas, use temporary `sorry`
  in specific branches, and keep gradually eliminating them.

### When Stuck

- When a proof becomes tangled, record the blocker and reduce the target.
- If a statement seems false, stop and write a notice instead of forcing a
  bogus proof.
- Preserve proof shape before using automation. First split on the relevant
  datatype constructor or inductive case, expose the assumptions for that
  branch, and only then use targeted `simp`, `auto[1]`, or a specific rule.
  Complex branches should become named helper lemmas. Broad automation on an
  undigested goal can irreversibly rewrite or split the state into a shape that
  hides the proof idea.
- If a tactic explodes (large proof terms, slow automation), simplify the
  proof structure. Human rule of thumb: `auto`, `simp`, `force`, or similarly
  broad proof search should normally return within about 0.5 seconds. If it
  visibly hangs, abandon that tactic immediately and split the proof into
  explicit cases/helper lemmas.
- If `sledgehammer` does not solve a goal quickly, break it down manually.

### Proof Performance Budget

Small pilot theories and proof edits in this project should usually replay
quickly. For a few-hundred-line proof change in `BackRefPilot`, a cold check
should normally finish in about 5-10 seconds. A 200 second command is an
extreme abnormality, not a tolerable build time.

Use these thresholds:

- 0.5 seconds for `auto`/`simp`/broad proof search: if it has not returned,
  treat the tactic choice as wrong and replace it with a structured proof.
- 1-2 seconds on one proof line: treat it as proof-performance debt unless the
  line is a known unavoidable definition package command. Try a named helper
  lemma or a more local elimination/simplification rule before accepting it.
- 10 seconds on one Isabelle command: inspect the reported command and line.
- 30 seconds on one command: stop relying on broad automation and narrow it.
- 120 seconds on one command: interrupt or let the timeout wrapper kill it.
- 200 seconds on one command: treat this as a bug in the definition/proof
  structure and fix the root cause before doing more work.

When this happens, do not merely raise timeouts or rerun the same command.
Change the resource-intensive line. Typical fixes:

- replace `fun` definitions with heavy nested/overlapping patterns by
  `primrec`, `definition`, or a simpler recursive shape with explicit
  `case ... of ...`;
- replace broad `auto`, `force`, `blast`, `metis`, or `elim!` over many
  inductive cases by targeted elimination rules such as `BPosix_elims(5)`;
- split the goal into named helper lemmas and explicit Isar steps;
- avoid passing all constructors or all simplification facts to automation
  when only one constructor is relevant;
- rerun with a timeout wrapper and verify that the same line now checks
  quickly.

This rule is mandatory for long-running agent loops. A stalled proof command
can waste the build lease, corrupt the Cursor workflow through reconnects, and
create false confidence from partial IDE state.

## Bounty Discipline

This repository uses a competitive-collaborative bounty system adapted from the
Agent Hunt paper (130k Lines Formal Topology). The full protocol is in
`agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md`.

Wrapper-only theorem packages do not count as bounty work. Do not lock or
collect a bounty for facts that merely bundle, rename, specialize, or restate
existing theorems, such as `*_cases`, `*_iff`, `*_same`, frontend summary, or
retrieve-equality wrappers. Such facts may be useful as an API layer, but they
are not a paid research deliverable.

Paid bounty work must add a new semantic or algorithmic layer, or prove a
nontrivial bridge needed by later work. Good examples are derivative
correctness, value/flat/Prf correspondence, bitcoded retrieve transport,
rewrite-relation preservation, derivative-commutation for simplification, and
real finite-bound theorems. If a task might be only theorem packaging, stop and
ask the admin before claiming it.

### Total Pool

The total bounty pool is **150,000 simulated USD**. All bounty amounts are
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

## Progress Monitoring

Following the 130k Lines paper, maintain structured progress tracking.

### After Every Meaningful Step

Update `PROGRESS_BACKREF.md` with:

- branch;
- commit if available;
- files changed (with line count deltas);
- build command;
- build result;
- theorem status;
- next smallest safe step;
- blockers.

If context is getting full, update the progress file before doing anything
else.

### Line Count Check

After each commit, verify no useful work was lost:

```powershell
git diff --stat HEAD~1
```

If any theory file got shorter, the commit message must justify the decrease.

### Per-Bounty Progress

For each active bounty, `PROGRESS_BACKREF.md` should track:

- Status: not started / definition drafted / statement proved / fully checked
- Remaining `sorry` count (if using gradual approach)
- Dependencies: which other bounties must complete first
- Blockers: what prevents progress

Use this to find imbalances and refocus on neglected tasks.

### Build Frequently

Run the Isabelle build after every meaningful change. Do not accumulate
many edits before checking. Silent build output = success. Any error must
be fixed before proceeding.

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -PilotOnly -Role admin
```

## Technical Roadmap

The work is organized into four phases. Each phase has a clear dependency on
the previous one. Agents should not jump ahead.

### Phase 1: Complete backref_lang (simple version)

The simple backreference `backref_lang A B cs` models `(r1)r2\1`, i.e. the
captured group `r1` is repeated verbatim, with `r2` as the middle expression
and no surrounding context beyond the capture.

**1a. Define `binjval` for brexp (BR-005)**

The injection value function reconstructs a value for the original regex from
a value for the character derivative. Follow the pattern of `injval` in
`Lexer.thy` but extended for `BBACKREF`, `BHALF`, `BRESIDUE`. The definition
must satisfy:

```isabelle
bflat (binjval r c v) = c # bflat v    (* when BPrf v (xder c r) *)
BPrf (binjval r c v) r                 (* when BPrf v (xder c r) *)
```

Study `xder` carefully: each `xder` case produces certain value shapes, and
`binjval` must invert them. For the `BBACKREF` nullable case, `xder` produces
an `BALT` with a `BBACKREF` branch and a `BHALF`/`BRESIDUE` branch; `binjval`
must unwrap accordingly.

**1b. Prove `bflat (binjval r c v) = c # bflat v` (BR-011)**

Induction on `r` with `c` and `v` universally quantified. Each case follows
from the `xder` definition and `BPrf` elimination. The backreference cases
will need careful case analysis matching the `xder` branching.

**1c. Prove `BPrf (binjval r c v) r` (BR-012)**

Same induction structure. This is the value-level correctness of injection.

**1d. Define bitcoded lexer for brexp**

This is recommended as the **primary implementation path** because the Scala
reference implementation (`backRef.sc`) already exists and is tested. The key
definitions to formalize from `backRef.sc`:

- Extend `arexp` datatype with `ABACKREF`, `AHALF`, `ARESIDUE` constructors
  (each carrying `bit list`).
- Extend `fuse`, `intern`, `erase`, `bnullable`, `bmkeps`, `bder`/`bder_simp`
  for the new constructors.
- The `bder` for `ABACKREF` follows the branching in `bder_bsimp_rev` from
  `backRef.sc`. Key insight: when the captured group is nullable, `bder`
  produces an `AALTS` with a `ABACKREF` branch (continuing to derive the
  capture) and a `AHALF` branch (transitioning to replay phase).
- `bmkeps` for `ABACKREF` emits a `Backbit(cs)` marker encoding the captured
  string.

Reference: `backRef.sc` lines 148-553 contain the full Scala implementation.

**Important**: the bitcoded lexer work should go into new sections of
`BackRefValues.thy` or a new theory file `BackRefBlexer.thy` (discuss with
admin). Do NOT modify `Blexer.thy` or `BlexerSimp.thy` during this phase.

**1e. Define `blexer` for brexp and prove correctness (BR-013, BR-014)**

Once `binjval` is defined, the lexer function follows mechanically:

```isabelle
blexer r [] = (if xnullable r then Some (bmkeps r) else None)
blexer r (c#s) = map_option (binjval r c) (blexer (xder c r) s)
```

Correctness: `blexer r s = lexer r s` (where `lexer` is the specification
lexer using `binjval`).

**1f. BlexerSimp for brexp: `blexer ≡ blexer_simp`**

Prove that the simplified bitcoded lexer produces the same result as the
unsimplified one for `brexp`. This requires extending `bsimp`, `bder_simp`,
and the `flts`/`distinctBy` simplification lemmas for the new constructors.
The proof follows `BlexerSimp.thy` structure.

**1g. (Optional, hard) ClosedFormsBounds for brexp (BR-019)**

The size of `xder`-derivatives for backreferences may not be bounded in the
same way as standard regex. This requires careful analysis and may reveal that
backreferences break the finite-derivative property. Record findings in
`PROGRESS_BACKREF.md` even if the result is negative.

### Phase 2: Generalized backref_lang4

The generalized `backref_lang4 L1 L2 L3 L4 cs` models `r1(r2)r3\1r4`, i.e.
the captured group `r2` appears between prefix context `r1` and suffix context
`r3`, then is replayed, followed by tail context `r4`.

**2a. Define new constructors**

Add `BBACKREF4`, `BHALF4`, `BRESIDUE4` (or extend existing constructors with
additional fields) to `brexp`. Define `BL`, `xnullable`, `xder` for them.

The current `backref_lang` is a special case:

```isabelle
backref_lang A B cs = backref_lang4 {[]} A B {[]} cs
```

**2b. Prove xnullable/xder correctness for new constructors**

Follow the same structure as `BackRefLang.thy`.

**2c. Define value/Prf/flat for new constructors**

Extend `bval`, `bflat`, `BPrf` for the generalized case.

**2d. Repeat Phase 1 steps for backref4**

Define `binjval`, prove flat/Prf correctness, define bitcoded lexer,
prove BlexerSimp equivalence -- all for the generalized constructors.

### Phase 3: injval definition (collaborative)

Defining `injval` for backreferences is the hardest open problem because the
derivative structure creates non-trivial value shapes. The recommended
approach:

1. Study the `xder` cases exhaustively and enumerate all possible output
   shapes for each constructor.
2. Define `binjval` case-by-case, matching each `xder` output shape.
3. Prove flat correctness first (easier), then Prf correctness.
4. If a case seems impossible, record the blocker -- it may indicate a
   semantic issue requiring admin intervention.

### Phase 4: Full integration

Once all pieces are in place:

1. Prove the full correctness chain: `lexer ≡ blexer ≡ blexer_simp` for
   `brexp` including all backreference constructors.
2. Integrate with the existing POSIX lexer story.
3. Address bounds questions.

### Concurrent Agent Task Division

When two agents work concurrently:

- **Agent A** (e.g., Opus): Work on `binjval` definition and correctness
  proofs (BR-005, BR-011, BR-012). This is the value-theoretic path.
- **Agent B** (e.g., GPT-5.5): Work on bitcoded lexer definitions for brexp,
  referencing `backRef.sc`. This is the implementation path. Use a new theory
  file `BackRefBlexer.thy` to avoid conflicts with Agent A's edits to
  `BackRefValues.thy`.

Both agents must pull/rebase frequently and push locks immediately.

## Dependency Awareness

The dependency direction is:

1. `RegLangs.thy`
2. `BackRefLang.thy`
3. `BackRefValues.thy` (value/Prf/flat + injval)
4. `BackRefBlexer.thy` (bitcoded lexer for brexp, new)
5. future BlexerSimp for brexp
6. future bounds or bounded-fragment theorems

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

Following the 130k Lines and Agent Hunt papers, agents run in an automated
tmux-based loop: a script monitors the session and re-issues the resume
prompt whenever the agent finishes or stalls. In the topology experiment,
83% of all user messages were automatically issued "Read CLAUDE.md" prompts.

### Setup

```text
Agent CLI (Codex, Claude Code, or similar)
+ WSL Ubuntu + tmux
+ agent_hunt_pipeline/scripts/backref_idle_watch.sh
+ agent-specific resume prompt
+ CLAUDE.md (read by agent at each prompt)
+ Isabelle build
+ git shared branch
```

### One-Click Start (Windows)

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/start_overnight.ps1
```

This script:
1. Opens WSL Ubuntu.
2. Creates a tmux session per agent.
3. Starts the agent CLI in each session.
4. Starts an idle watcher per agent that re-prompts on stall.
5. Prints monitoring instructions.

For Cursor/Opus (which cannot be tmux-injected), the script starts the
idle detector in Level 2 mode (prints prompt when repo state is unchanged).
The user pastes the initial prompt into Cursor; subsequent re-prompts happen
when the user wakes up or via Cursor's background agent mode.

### Agent-Specific Resume Prompts

Each agent has its own resume prompt tuned to its task assignment:

- `agent_hunt_pipeline/scripts/opus_resume_prompt.txt` -- for Opus (Cursor)
- `agent_hunt_pipeline/scripts/gpt55_resume_prompt.txt` -- for GPT-5.5
- `agent_hunt_pipeline/scripts/backref_resume_prompt.txt` -- generic fallback

The idle watcher should only re-prompt an idle CLI. It must not bypass git,
build, or statement rules.

## When Resuming

On resume from compacted context or a fresh chat:

1. **READ THIS FILE FIRST** before making any edits.
2. Read `agent_hunt_pipeline/projects/posix-backref/SESSION_BRIEF.md`.
3. Read `PROGRESS_BACKREF.md`.
4. Run `git fetch --all --prune` and `git status --short --branch`.
5. Verify which branch you are on (`codex/backref-values`).
6. Verify you understand which files you are allowed to edit.
7. Build before making proof edits.
8. Check line counts of theory files against latest commit.
9. Continue the smallest safe task from `PROGRESS_BACKREF.md`.

**Do not trust memory alone.** The 130k Lines paper found that 83% of
prompts were automatic re-prompts of "Read CLAUDE.md". This file is the
single source of truth for all work rules.

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
