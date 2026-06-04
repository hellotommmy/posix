# Next Chat Cubic Handoff, 2026-06-05

This handoff is for a fresh Codex/Cursor/CLI chat taking over the POSIX
non-backref cubic size-bound project. The previous chat should stop after
pushing this file.

## Repository State

- Workspace: `C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`
- Branch: `codex/backref-values`
- Remote branch: `origin/codex/backref-values`
- Preserve these untracked backup files if present:
  - `BackRefLang.thy~`
  - `BackRefLang4Pilot.thy~`
  - `Lexer.thy~`
- Latest pushed state before this handoff was `2df31e3 Clarify open cubic theorem status`.
- This handoff commit may be newer. Start with:

```powershell
cd C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex
git fetch --all --prune
git status --short --branch
git log --oneline -8 --decorate
```

## Truth To Preserve

The final theorem is not proved:

> The final strong simplification / memo-strong route satisfies a cubic bound
> with respect to the original non-backref regex size while preserving POSIX
> values.

Do not claim BR-039, BR-040, or any final cubic bounty until the concrete
original-regex-owned cubic universe is checked in Isabelle and connected to the
actual final strong simplification/memo route.

The current checked theorems are conditional interfaces and handoffs. They are
useful, but they are not the final theorem.

## What Was Just Added

`FBound.thy` now has:

```isabelle
strong_deferred_original_raw_row_norm_later_shared_memo_cubic_interface
```

This packages the final memo/POSIX-facing conclusions under the more realistic
`later_shared` closure premise:

```isabelle
\<And>lrs rrs k.
  RSEQ (RALTS rrs) k \<in> U \<Longrightarrow>
  set (rflts [rsimp7_SEQ_atom
    (rsimp_ALTs (rprune_eq_against lrs rrs)) k]) \<subseteq> U
```

This is deliberately not a final result. It exists so the next proof attempt
does not over-assume `raw_shared_prune_closed U` or the too-naive one-step
active-suffix bridge.

## Main Diagnosis

The promising Scala smoke route and the current Isabelle `bridge_owner` are not
the same object.

In `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`, the good DAG bridge uses:

```scala
strongRowsBridgeRowsId(store, rows) =
  rows.flatMap(reachableIds) ++
  reachableIds(strongRootFromRowsId(store, rows)) ++
  factoredActiveRowsFromRowsId(store, rows)
```

The important extra part is:

```scala
factoredActiveRowsFromRowsId
```

which iteratively adds factor-row witnesses. This is stronger/different from
the current Isabelle `strong_deferred_strong_rows_raw_bridge_owner`.

Therefore, the next serious proof path should formalize a concrete
factor-row/later-shared universe or prove an equivalent closure theorem. Do not
keep trying to prove the final cubic theorem from the old one-step
`bridge_owner` unless you first prove it really covers the iterative factor-row
behavior.

## First Priority For The Next Chat

Construct and prove, in Isabelle, a concrete original-regex-owned universe `U`
for the memo-strong/non-backref route such that:

1. `rerase (intern r) \<in> U`
2. `U` is closed under `rflts`
3. `U` is closed under `rpder_norm_list` followed by `rsimpStrong_raw`
4. `U` is closed under the `later_shared` pruning premise above
5. `finite U`
6. `card U` is cubic or better in `rxsize r`
7. members of `U` have the required size bound so that `card U * M` is cubic
8. the theorem connects to
   `strong_deferred_original_raw_row_norm_later_shared_memo_cubic_interface`

The hard part is 4-7. That is the actual bounty target.

## Do Not Repeat These Failed Routes

- Do not revive `rsimp9` as a cubic candidate.
- Do not claim an emitted-tree `bsimpCubic` route unless POSIX values are
  preserved and thesis Chapter 7 smoke tests are good.
- Do not use broad `auto`, `blast`, or `sledgehammer` lines that run over
  1-2 seconds. Split cases and add helper lemmas.
- Do not put broad smoke-test grids as Isabelle `by eval` lemmas. Run broad
  experiments in Scala.
- Do not create wrappers and call them bounty progress. Wrapper-only work is
  negative value unless it exposes a genuinely missing theorem shape.

## Useful Smoke Commands

Run these before believing any new simplifier or universe route:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 -Route custom -SkipLegacyCubic -CheckStrongRowsBridge -CheckStrongRowsBridgeCh7 -StrongRowsBridgeDag -Depth 2 -InputLength 3 -RandomCases 1000 -RandomDepth 5 -RandomInputLength 6 -Seed 20260602 -Ch7K 8 -Ch7Lengths 4,8,16,32,64 -TimeoutSeconds 180
```

Known positive DAG bridge smoke before this handoff:

- exhaustive depth 2/input length 3: coverage `832/832`, maxRows `3`,
  maxBridgeRows `15`
- random 1000 cases depth 5/input length 6 seed 20260602: coverage `72/72`,
  maxRows `6`, maxBridgeRows `71`
- Chapter 7 k=8 lengths 4,8,16,32,64: coverage `41/41`, maxRows `36`,
  maxBridgeRows `259`

These are evidence only. They do not prove the theorem.

## Required Check Before Commit

After any meaningful Isabelle change:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240
```

Commit only intentional tracked files. Do not commit the `*.thy~` backups.

## Prompt For The New Chat

Paste this into the new chat:

```text
We are working in C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex on branch codex/backref-values. This is the POSIX non-backref cubic size-bound project, now focused on proving the final strong simplification / memo-strong route has a cubic bound w.r.t. original regex size while preserving POSIX values.

First read, in this order:
1. agent_hunt_pipeline/projects/posix-backref/NEXT_CHAT_CUBIC_HANDOFF_2026_06_05.md
2. agent_hunt_pipeline/projects/posix-backref/CLAUDE.md
3. agent_hunt_pipeline/projects/posix-backref/DESIGN_LOG.md
4. PROGRESS_BACKREF.md
5. FBound.thy around strong_deferred_original_raw_row_norm_later_shared_memo_cubic_interface
6. GeneralRegexBound.thy around rsimpStrong_prune_rows_raw_later_shared_subsetI and raw_final_active_suffix_row_dag_universe_rsimpStrong_ALTs_raw_closed_subsetI
7. agent_hunt_pipeline/scala/PosixCubicSmoke.scala around factoredActiveRowsFromRowsId and strongRowsBridgeRowsId

Start with git fetch/status. Preserve untracked backup files BackRefLang.thy~, BackRefLang4Pilot.thy~, and Lexer.thy~.

The final cubic theorem is NOT proved. Do not claim BR-039/BR-040 or final cubic bounty. The promising Scala DAG bridge includes iterative factoredActiveRowsFromRowsId, while Isabelle bridge_owner is not the same object. Your first priority is to formalize or replace it with a concrete original-regex-owned factor-row/later-shared universe U, prove the needed closure/cardinality/member-size bounds, and connect it to strong_deferred_original_raw_row_norm_later_shared_memo_cubic_interface.

Avoid wrappers, rsimp9 revival, broad auto/blast/sledgehammer lines over 1-2 seconds, and Isabelle eval smoke grids. Use Scala for broad smoke. After every meaningful checked checkpoint, run:
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240

Commit and push only intentional tracked files to origin/codex/backref-values.
```

