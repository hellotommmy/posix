# Fable Cubic Handoff, 2026-06-11

This is the short handoff for trying Claude Fable on the POSIX non-backref
cubic size-bound project.  It is intentionally much shorter than the old chat
logs and the long progress file.  Start here; only open the long files when a
specific theorem name or design question requires it.

## Repository

- Workspace: `C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`
- Branch: `codex/backref-values`
- Isabelle: `C:\Users\Chengsong\Isabelle2025-2`
- Main session: `Posix`
- Checked before this handoff:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\codex-proof-workers.ps1 -Action Check
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\codex-proof-workers.ps1 -Action Check
```

The build passed and there were no matching residual proof-worker processes.

## Task

The target is a cubic bound for the non-backref simplification route, morally:

```text
|bders_simpStrong (intern r) s| <= O(|r|^3)
```

or an equivalent route that preserves the intended lexer/POSIX value behavior.
The user specifically cares about a strong simplifier that handles cases such
as pruning away the final `acd` while still preserving the useful structure of
terms like `(ab+ac)d+(ac+ae)d`, and about keeping `blexer_simp r s` output
equal to `blexer r s`.

Do not treat plain language preservation as enough.  Exact POSIX value output
or a checked reconstruction route matters.

## Important Boundary

The final theorem is not proved.  Do not claim BR-039/BR-040 or a completed
final cubic result.

The useful progress is a set of checked first-stage and conditional
second-stage interfaces.  The next work should be theorem-driven, not wrapper
generation.

## 2026-06-12 Supervisor Update

Fable commit `4e08917` checked
`apder_deep_frontier_linear_card_false`.  This means the deep-frontier version
of route 1 is closed as a dead end:

```text
card (apder_deep_frontier r) <= apder_awidth r + rsize r + 3
```

is false even for legacy `apder_nf` input.  Do not try to prove this premise
again.  The conditional interfaces that assume it are still logically valid,
but they cannot be made unconditional in that form.

Plain-English reading of the counterexample:

- `card S` means "the number of distinct elements in set `S`."
- `RNTIMES X n` means "repeat regex `X` exactly `n` times."
- `RALTS SS` means "choose one alternative from the list `SS`."
- `apder_deep_frontier r` is the proof's broad set of deep derivative row
  forms for root `r`.
- `apder_awidth r + rsize r + 3` was the hoped-for linear budget.
- The checked witness has 49 deep-frontier rows but budget 39, so the universal
  theorem is impossible.

Mechanism: counted repetition creates one continuation for each remaining
repeat count, and each continuation can carry every branch of an alternative.
Some branches have zero `apder_awidth` cost, so the row count grows like
`repeat count * branch count` while the proposed budget only grows roughly
linearly in the repeat count.

## Read First

Read only these regions first:

1. `AntimirovNormalFrontier.thy`
   - `normal_canonical_derivative_frontier_eq_ader_front`
   - `normal_canonical_derivative_main_cubic_bound`
   - `normal_canonical_then_strong_main_cubic_bound`
   - `rpder_strong_dcanon_afactored1_same_front_contract`
   - `rsimpStrong_raw_row_dlforms_cost_not_monotone`
2. `AntimirovFactoredTransition.thy`
   - `row_dlform_canonical_rows`
   - `rsizes_row_dlform_canonical_rows_cubic`
   - `apder_deep_frontier_linear_card_false`
   - `rsize_set_adlform_front_cubic_from_deep_linear_card`
   - `row_dlform_canonical_afactored1_same_dlfront_linear_card_cubic_contract`
   - `afactored1_strong_dlform_universe`
   - `afactored1_strong_dlform_universe_not_frontier_subset`
3. `FBound.thy`
   - `strong_deferred_original_raw_row_norm_later_shared_memo_cubic_interface`
4. `GeneralRegexBound.thy`
   - `rsimpStrong_prune_rows_raw_later_shared_subsetI`
   - `raw_final_active_suffix_row_dag_universe_rsimpStrong_ALTs_raw_closed_subsetI`
5. `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`
   - the factored/active row bridge and row-diff comparison harness.

Use `PROGRESS_BACKREF.md` and
`agent_hunt_pipeline/projects/posix-backref/NEXT_CHAT_CUBIC_HANDOFF_2026_06_05.md`
as searchable references, not as initial context dumps.

## What Is Checked

- The normal Antimirov/factored derivative route keeps whole residuals, not
  atomized pieces.  In particular, examples such as `a(aa)` retain whole
  residuals in the relevant front.
- `normal_canonical_derivative r s` has a checked regex-level cubic bound under
  `legacy_rrexp r` and `apder_nf r`.
- The exact same-front theorem is checked:

```text
rfrontier (normal_canonical_derivative r s) = ader_front r s
```

- The clean route

```text
rsimpStrong_raw (normal_canonical_derivative r s)
```

also has a checked cubic regex-size bound, because `rsimpStrong_raw` preserves
language and does not increase `rsize`.
- This clean route is not yet the final production/memo/POSIX theorem.
- The raw strong-row/dcanon route is reduced to conditional universe bounds,
especially around `afactored1_strong_dlform_universe` and next-row closure.

## Known Dead Ends

Do not restart these loops:

- Do not replace the first stage by `aseq_terms`; it atomizes products too
  aggressively and loses the whole-residual Antimirov structure.
- Do not prove arbitrary global-front closure.  The proof must stay indexed by
  the same derivative front.
- Do not try to finish by raw `rsimpStrong_raw` idempotence; checked
  counterexamples already show this fails.
- Do not prove local `row_dlforms` cost nonincrease for `rsimpStrong_raw`;
  `rsimpStrong_raw_row_dlforms_cost_not_monotone` is a checked counterexample.
- Do not try to discharge the deep-frontier linear cardinality premise
  `card (apder_deep_frontier r) <= apder_awidth r + rsize r + 3`;
  `apder_deep_frontier_linear_card_false` is a checked counterexample.
- Do not add more thin wrappers unless they discharge a named missing premise
  of an existing interface.
- Do not use long `auto`/`blast`/Sledgehammer searches.  Split constructor
  cases into small named lemmas.

## Best Next Attack

The most promising route is one of these, in order:

1. Optionally check the smaller front-specific counterexample suggested in
   `PROGRESS_BACKREF.md` for the premise
   `card (adlform_front r s) <= apder_awidth r + rsize r + 3`.  This is a
   short falsification task only; stop once the counterexample is checked.
2. Prove a sharper cubic bound for the actual step-local universe
   `afactored1_strong_dlform_universe r s c`, using same-front/shared-suffix
   counting rather than arbitrary all-pairs closure.
3. Replace the raw strong-row representation by a checked canonical
   projection via `row_dlform_canonical_rows`, then prove the production route
   computes or soundly refines that projection while preserving POSIX values.

If you attempt a bounded-repetition-free side theorem such as a
`rntimes_free` version of the old deep-frontier linear bound, treat it only as
a fragment/boundary result.  It does not solve the user's target, because the
non-backref fragment includes counted repetition.  Do at most one short proof
repair cycle for such a side theorem; if it fails a build again, abandon it and
return to route 2 or 3.

For each route, first state the exact missing theorem and identify the smallest
checked interface it would unlock.  If the theorem does not unlock one of the
interfaces above, it is probably drift.

## Operating Rules

- Start every session with `git status --short --branch`.
- Keep work on a fresh branch or a clean worktree.
- Prefer one theorem gap per session.
- On Windows, use the repository PowerShell wrappers.  Do not use Bash
  `sleep && tail` polling for background builds; use Claude's TaskOutput/Read
  on the output file instead.
- Proof-search discipline: broad `auto`/`simp`/`blast` should normally return
  in about 0.5s; one Isabelle command should usually finish in 5-10s.  A slow
  command means split the proof, not raise the timeout.
- After a meaningful Isabelle change, run:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\codex-proof-workers.ps1 -Action Check
```

- Record only concise progress notes.  Avoid copying long chat transcripts into
  the repo or prompt context.
