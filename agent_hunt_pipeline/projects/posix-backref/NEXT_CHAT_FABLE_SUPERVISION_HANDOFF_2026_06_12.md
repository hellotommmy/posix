# Next Chat Handoff: Fable POSIX Cubic Supervision, 2026-06-12

Use this file to start a fresh Codex chat with minimal context.  The job is to
supervise and, when useful, outcompete Fable on the POSIX non-backref cubic
bound proof.  Keep the context small; open long logs only for exact theorem
names or failing line numbers.

## Repository

- Worktree: `C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`
- Branch: `codex/backref-values`
- Remote branch: `origin/codex/backref-values`
- Current latest checked commit before this handoff:
  `bbd9046 Record degree audit and next two square-sum pieces`
- Important recent commits:
  - `bbd9046`: progress note only; degree audit and two proposed next pieces.
  - `fb08f86`: checked bridge from actual opened set ledger to row-square sum.
  - `db1091d`: checked per-row deduplicated opening bound.
  - `ff7f4e4` / `2bd7f88`: checked RONE-pair counterexample to duplicated
    opened-list cubic cost.

At session start run:

```powershell
git status --short --branch
git pull --rebase --autostash origin codex/backref-values
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check
```

Ignore these untracked local scratch files unless the user asks:

```text
agent_hunt_pipeline/projects/posix-backref/fable_partial.md
scratch_dlform_cost_model.py
```

## Build Discipline

Correct commands from the repository root:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check
```

Red `Background shell failed` in Fable is usually an Isabelle proof failure,
not a bad shell command.  After a failure, read the first
`*** Failed to finish proof` block and change one small named proof/lemma before
running another full build.  Do not queue a second build if the first failing
line and goal are unchanged.

Latest known Claude task-output folder:

```text
C:\Users\Chengsong\AppData\Local\Temp\claude\C--Users-Chengsong-Documents-AIPV2026Notes\69d59e71-aa7c-4bf7-86d9-d222b2c0f6b4\tasks
```

Latest known green full build in those outputs:

```text
b6wrwpz7s.output, 2026-06-12 19:17 GMT+8
AntimirovFactoredTransition 100% (82.594s)
Finished Posix (0:01:26 elapsed time)
```

`fb08f86` was separately green at 19:26.  `bbd9046` only changed
`PROGRESS_BACKREF.md`.

## Plain Definitions

- `actual_rows` means
  `rpder_strong_rows_raw c (afactored1 r s)`, the one-step rows produced after
  strong simplification/pruning.
- `row_dlforms q` opens one row `q` and removes duplicate opened rows.
- `row_dlformss rows` opens every row in a list and removes duplicates across
  the whole union.
- `row_dlforms_list_size q` counts duplicates; this is the bad/list quantity.
- `rsize_set U` sums `rsize` over distinct rows in set `U`.
- The live final gate is:

```text
rsize_set (row_dlformss actual_rows) <= 2 * (rsize r + 3)^3
```

## Checked Facts To Use

Duplicated opened-list cost is false:

```text
afactored1_strong_dlform_list_cost_cubic_false
```

Plain meaning: RONE-pair towers make the duplicated opened list grow
exponentially.  Any proof route that tries to bound
`afactored1_strong_dlform_list_cost` polynomially is dead.

Per-row deduplicated opening is checked:

```text
card_row_dlforms_le_rsize
rsize_set_row_dlforms_le_rsize_sq
```

Plain meaning: for any single row, after duplicates are removed, the opened set
has at most `rsize q` members and total size at most `(rsize q)^2`.

Actual-output bridge is checked:

```text
rsize_set_row_dlformss_le_sum_rsize_sq
rsize_set_row_dlformss_rpder_strong_rows_raw_afactored1_le_sum_rsize_sq
```

Plain meaning: the actual deduplicated output set is at most the sum of
`(rsize q)^2` over the actual one-step rows.  This is a safe sufficient bridge,
not the final theorem.

Fable's queued "rsizes deleter chain" is already basically present:

```text
GeneralRegexBound.thy:
  rsizes_rpder_strong_rows_raw_le
  rpder_strong_rows_raw_generated_budget
```

Do not reprove this from scratch.  Instantiate or reuse it only if it directly
unlocks the next square-sum or weighted-split premise.

## Current Mathematical State

The row-square bridge leaves the target:

```text
sum_list (map (%q. rsize q * rsize q) actual_rows)
  <= 2 * (rsize r + 3)^3
```

The naive payment

```text
sum q^2 <= max(q) * sum(q)
```

is useful only if the next step gives enough sharing.  With only current coarse
bounds, it risks becoming quartic, not cubic.  Do not stop at wrappers such as
`sum q^2 <= rsizes rows * rsizes rows`; that loses the important sharing.

The better live route is still the existing weighted split / active-suffix
bucket machinery:

```text
rsize_set_split_rseq_tails_rpder_strong_rows_raw_afactored1_front_open_weighted_plus_active_alt_nodesI
rsize_set_split_rseq_tails_rpder_strong_rows_raw_afactored1_front_weighted_plus_active_alt_nodesI
raw_shared_prune_active_suffix_weighted_rseq_tails_rpder_strong_rows_raw_afactored1_le_pair_budget_list_cost
```

Useful next theorem should either:

1. Bound the actual row-square sum using one-pass strong prune sharing.
2. Bound the step-local active suffix bucket/alt-node budget tightly enough to
   discharge an existing weighted split interface.
3. Prove a direct "square-sum drain" for actual rows that avoids duplicated
   opened-list cost and arbitrary row-list bounds.

## What Not To Do

- Do not work in the parent `AIPV2026Notes` git repository; it is an empty
  parent repo and its giant untracked count is misleading.
- Do not chase `row_dlforms_list_size` or
  `afactored1_strong_dlform_list_cost` as a polynomial target.
- Do not add thin wrappers unless they discharge a named premise of an existing
  interface.
- Do not wait for the other agent unless `codex-proof-workers.ps1 -Action Check`
  shows a live worker or `git status --short` shows tracked edits in the same
  line region.
- Do not use broad `auto`/`blast`/`simp` as a search loop.  If a command is
  visibly slow, split the proof.

## Recommended Opening Message For New Chat

Continue supervising Fable's POSIX cubic-bound work in
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`.  First read
`agent_hunt_pipeline/projects/posix-backref/NEXT_CHAT_FABLE_SUPERVISION_HANDOFF_2026_06_12.md`,
then check `git status --short --branch`, latest commits, latest Claude task
outputs, and proof workers.  If no worker is active and the worktree has no
tracked conflicting WIP, either give Fable a narrow instruction through the
handoff/progress files or prove the next small checked lemma yourself.  Current
live theorem is the cubic set ledger:

```text
rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
  <= 2 * (rsize r + 3)^3
```

Use existing checked facts; avoid duplicated list-cost and arbitrary wrapper
routes.  If Fable's next red background shell repeats the same first failing
goal, intervene with a narrower proof-step instruction.
