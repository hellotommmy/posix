# Fable Cubic Handoff, 2026-06-11

This is the short handoff for trying Claude Fable on the POSIX non-backref
cubic size-bound project.  It is intentionally much shorter than the old chat
logs and the long progress file.  Start here; only open the long files when a
specific theorem name or design question requires it.

## Urgent Supervisor Update, 2026-06-12 13:24 GMT+8

The ordinary sequence-tail size branch now has a checked weighted-row
reduction.  Read:

```text
2026-06-12 Supervisor: weighted extended-suffix tail bound checked
```

Plain definitions:

- `rsize_set S` means the total syntax size of all regexes in finite set `S`.
- `row_dlforms_list_size q` means the total syntax size of the rows obtained by
  opening one row `q`.
- `rseq_suffixes_ext q` means the extended carrier of right-hand sequence tails
  that can appear after opening `q`.

Checked facts:

```text
rsize_set (rseq_suffixes_ext q)
  <= row_dlforms_list_size q * rsize q

rsize_set (rseq_tails
    (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))))
  <= sum_list (map (%q. row_dlforms_list_size q * rsize q)
       (rpder_strong_rows_raw c (afactored1 r s)))
```

Important correction: for `RSEQ (RALTS ps) k`, the extended carrier now follows
only the opened branches `rsimp7_SEQ_atom p k`.  It no longer charges the root
suffix chain of `RSEQ (RALTS ps) k`, because that chain is not produced by
`row_dlforms` in this case.

Next target: prove the displayed weighted sum is cubic for the actual pruned
strong rows.  Do not add more generic suffix-carrier wrappers unless they
discharge that exact weighted-sum target.

Follow-up checked at 13:32: the weighted-row reduction is now connected to the
actual output gate.  The old coarse gate term
`card(front) * sum_t (H + size(t))` is replaced by
`card(front) * ((H + 1) * weighted_raw_rows)`, where `weighted_raw_rows` is the
displayed sum over `rpder_strong_rows_raw c (afactored1 r s)`.  Use:

```text
rsize_set_split_rseq_tails_rpder_strong_rows_raw_afactored1_front_weighted_plus_active_alt_nodesI
rsize_set_split_rseq_tails_rpder_strong_rows_raw_afactored1_front_weighted_plus_generated_ledgerI
```

This still does not finish cubic; it exposes the remaining exact target.

Follow-up checked at 13:36: `weighted_raw_rows` is factorized as
`rsizes(actual_raw_rows) * sum_list(map row_dlforms_list_size actual_raw_rows)`.
Use:

```text
row_dlforms_list_size_weighted_rpder_strong_rows_raw_afactored1_le_rsizes_times_open_sum
```

The next narrow target is the actual opening-cost total.  Do not assume
`rtail_nf` implies opening cost nonincrease; this is already false in the repo.

Follow-up checked at 13:43: `rseq_suffixes_ext_member_size_le` is green.  This
means every member of the extended suffix carrier has size at most the original
row.  Do not re-prove it; use it as the member-size half if pursuing the card
route for `rseq_suffixes_ext`.

Follow-up checked at 13:47: `rsize_set_rseq_suffixes_ext_le_card_times_rsize`
is green.  The remaining card-route target is now only the cardinality bound.

Follow-up checked at 13:50: `card_rseq_suffixes_ext_le_row_dlforms_list_size`
is green.  The single-row ext carrier is now accounted for.  The remaining
work is cross-row: bound the actual `weighted_raw_rows`/opening-cost ledger for
`rpder_strong_rows_raw c (afactored1 r s)`.

## Urgent Supervisor Update, 2026-06-12 12:43 GMT+8

The actual-output sequence tails are now bridged to the extended suffix
carrier.  Read:

```text
2026-06-12 Supervisor: actual tails bridged to extended suffix carrier
```

New checked facts:

```text
rseq_tails_row_dlformss_rpder_strong_rows_raw_afactored1_subset_suffixes_ext
rsize_set_rseq_tails_row_dlformss_rpder_strong_rows_raw_afactored1_le_suffixes_ext
```

Use this as the next size target:

```text
rsize_set(actual sequence tails)
  <= rsize_set(UN q in actual raw rows. rseq_suffixes_ext q)
```

Do not reopen the `row_dlformss` ownership proof.  The useful work is now a
non-product size account for this union of extended suffix carriers.

## Urgent Supervisor Update, 2026-06-12 12:37 GMT+8

The extended suffix carrier has now been checked.  Do not spend another cycle
re-deriving the single-row ownership statement.

Read the newest `PROGRESS_BACKREF.md` section:

```text
2026-06-12 Supervisor: extended suffix ownership checked
```

New checked facts:

```text
rseq_suffixes_ext
finite_rseq_suffixes_ext
rseq_tails_row_dlforms_subset_rseq_suffixes_ext
```

Plain meaning: opening `row_dlforms q` can create sequence tails that are not
in the ordinary suffix chain of `q`, especially when a branch inside
`RSEQ (RALTS ps) k` is itself a sequence.  `rseq_suffixes_ext q` follows those
opened branches via `rsimp7_SEQ_atom p k`, and the checked theorem says all
sequence tails of `row_dlforms q` are inside that extended carrier.

Next target: size/accounting for this extended carrier or a sharper actual
step carrier derived from it.  The proof must avoid charging the same shared
tail once per branch at every nesting level.  A result that merely places the
carrier in the old list-cost universe is too coarse.

## Urgent Supervisor Update, 2026-06-12 12:29 GMT+8

Current checked source should include the next supervisor/Fable brick:

```text
Fable: suffix-chain toolkit checked
Supervisor: sequence-tail size ledger checked
```

Read the newest `PROGRESS_BACKREF.md` section:

```text
2026-06-12 Supervisor/Fable: sequence-tail size ledger checked
```

Plain definitions for the next proof attempt:

- "actual output" means the rows produced by one strong derivative step,
  opened through the current deep-row form pipeline:
  `row_dlformss (rpder_strong_rows_raw c (afactored1 r s))`.
- "sequence tail" means the right side `t` of a row shaped `RSEQ h t`.
- "suffix chain" means repeatedly taking the right side of `RSEQ h t` until a
  non-sequence expression remains.
- "drain/nesting theorem" means: prove that the actual tails sit in a
  controlled family of such suffix chains, so shared tails are charged once,
  not once per front row.

New checked interfaces:

```text
rsize_set_rseq_tails_le
rsize_set_rseq_tails_rpder_strong_rows_raw_afactored1_le_actual
rsize_set_rseq_tails_rpder_strong_rows_raw_afactored1_le_list_cost
rsize_set_rseq_suffixes_quadratic
```

Use these to attack the remaining source-to-tail drain against the sharper
actual gate.  Do not return to generic owner-DAG cardinality, and do not try to
close the theorem from the global cubic-universe closure; both directions are
known bad or too coarse in this repo.

## Urgent Supervisor Update, 2026-06-12 11:53 GMT+8

Current checked head should include `94ab885` and the next supervisor
checkpoint after it:

```text
Bound nonsequence actual gate by front terms
Split actual gate by nonalt rows
Point Fable at sharper actual gate
nonalt sequence rows are universe/list-cost paid
```

Read the newest `PROGRESS_BACKREF.md` sections:

```text
2026-06-12 Supervisor: replace front-count tail product by actual nonalt rows
2026-06-12 Supervisor: nonalt sequence rows are universe-paid, not closed
```

Important correction to the gate shape: do not keep working against the older
coarse term

```text
front-count * sum(distinct tail weights)
```

unless you explicitly explain why that coarse product is still needed.  The
new checked split is sharper:

```text
actual-output rsize
<= non-sequence rows
 + actual sequence rows with non-RALTS heads
 + active RALTS-head copying cost
```

The first term is already checked cubic:

```text
rsize_set_rnonseq_members_row_dlformss_rpder_strong_rows_raw_afactored1_cubic
```

The second term now has a checked guard:

```text
rsize_set_rseq_tail_nonalt_head_rows_rpder_strong_rows_raw_afactored1_le_list_cost
```

Plain meaning: these rows are inside the one-step strong dlform universe and
are paid by the current generated/list-cost ledger.  This is not the final
cubic theorem, because the generated/list-cost ledger is still too coarse as a
main route.

The next useful theorem should attack one of these directly:

```text
rsize_set (actual sequence rows with non-RALTS heads)
active RALTS-head copying cost
```

Tail-nesting/drain ideas should be stated against this sharper gate, not the
older `front-count * tail-sum` formula.

Coordination rule: if `codex-proof-workers.ps1 -Action Check` says no worker is
running and there are no uncommitted theory edits from another agent, do not
wait for the supervisor.  Work on one of the two gate terms above.  If you
touch a theory, run the wrapper build command shown below and report the exact
failing Isabelle line if it fails.

## Urgent Supervisor Update, 2026-06-12 11:31 GMT+8

Current checked head should include `c82c6a5`:

```text
Expose product cost of ledger fallback
Fragment ledger is cubic: awidth <= rsize without NTIMES
```

After syncing, read the newest `PROGRESS_BACKREF.md` section:
`2026-06-12 Supervisor correction: cubic front total is not yet the end gate`.

New checked gate-level lemmas in `AntimirovFactoredTransition.thy`:

```text
rsize_set_split_rseq_tails_rpder_strong_rows_raw_afactored1_front_sum_plus_active_alt_nodesI
rsize_set_split_rseq_tails_rpder_strong_rows_raw_afactored1_front_sum_plus_generated_ledgerI
```

Simple definitions:

- `actual output` = rows really returned by one strong derivative step:
  `rpder_strong_rows_raw c (afactored1 r s)`.
- `front term` = the left side `h` of a top-level sequence row `RSEQ h t`.
- `tail` = the right side `t` of such a row.
- `active copying cost` = how much repeated work comes from multiple active
  rows sharing the same tail.
- `generated ledger` = `length generated + rsizes generated`, where
  `generated = concat (map (rpder_norm_list c) (afactored1 r s))`.

Plain checked shape:

```text
actual-output rsize
<= non-sequence rows
 + front-count * sum(distinct tail weights)
 + active copying cost
```

The active copying cost currently has this sharp interface:

```text
list_cost * active_alt_node_count * (Suc H + list_cost)
```

and this fallback interface:

```text
list_cost * generated_ledger * (Suc H + list_cost)
```

Do not report this as "only the generated ledger remains".  The fallback is a
product bound.  To finish the cubic theorem, either remove the product by a
non-product accounting argument, or prove a much sharper provenance bound for
`active_alt_node_count` and the distinct-tail/front terms.

Fable's useful checked fragment lemma is:

```text
rsizes_afactored1_rntimes_free_rsize_cubic
```

Plain meaning: on the `rntimes_free` fragment, the current front row list
`afactored1 r s` has cubic total size.  This is real progress, but it does not
make the generated-list route cubic by itself.  The currently checked
generated estimate is still a sum of per-row cubes:

```text
rsizes generated
<= sum over front rows q of 2 * (rsize q + 3)^3
```

A cubic bound on `sum rsize q` alone does not make that sum cubic.  Next work
should attack the three actual-output terms directly:

```text
non-sequence rows
front-count * sum(distinct tail weights)
active copying cost
```

or replace the active product with non-product accounting.

## Urgent Supervisor Update, 2026-06-12 10:46 GMT+8

Current checked remote/head after sync should include:

```text
Relate active suffix tail sum to pair budget
```

After syncing, read the newest `PROGRESS_BACKREF.md` section:
`2026-06-12 Supervisor: active-suffix weighted tails are paid by pair budget`.

New checked bridge in `AntimirovFactoredTransition.thy`:

```text
raw_shared_prune_active_suffix_weighted_rseq_tails_rpder_strong_rows_raw_afactored1_le_pair_budget
raw_shared_prune_active_suffix_weighted_rseq_tails_rpder_strong_rows_raw_afactored1_le_pair_budget_list_cost
raw_shared_prune_active_suffix_pair_budget_card_bucket_bound
afactored1_strong_dlform_universe_active_suffix_pair_budget_list_cost_bucket_boundI
raw_shared_prune_active_suffix_alt_nodes
card_raw_shared_prune_active_suffix_bucket_le_alt_nodes
afactored1_strong_dlform_universe_active_suffix_pair_budget_list_cost_alt_nodes_bound
card_afactored1_strong_dlform_universe_alt_nodes_le_generated
afactored1_strong_dlform_universe_active_suffix_pair_budget_list_cost_generated_bound
raw_shared_prune_active_suffix_weighted_rseq_tails_rpder_strong_rows_raw_afactored1_le_generated_ledger
```

Plain definitions:

- `actual output` = `rpder_strong_rows_raw c (afactored1 r s)`, the rows
  really produced by one strong derivative step.
- `tail t` = the right side of a top-level sequence row `RSEQ h t` after
  opening the actual output with `row_dlformss`.
- `active-suffix bucket(t)` = the step-local rows shaped
  `RSEQ (RALTS rows) t`; these are the rows that copy the same continuation
  `t`.
- `pair_budget(U)` = the sum of `bucket_size(k)^2` over active suffix keys.
  This is the existing same-key sharing budget.

The current checked decomposition leaves this active weighted term:

```text
sum over actual tails t of
  card active_suffix_bucket(t) * (Suc H + rsize t)
```

The new bridge pays it as:

```text
if every actual tail t satisfies Suc H + rsize t <= M
then active weighted term
  <= raw_shared_prune_active_suffix_pair_budget
       (afactored1_strong_dlform_universe r s c) * M
```

Stronger checked instance: for this active weighted term, the size bound is
only needed when `active_suffix_bucket(t)` is nonempty.  Such a `t` is an
active suffix key, and active suffix keys are already bounded by
`afactored1_strong_dlform_list_cost r s c`.  Therefore:

```text
active weighted term
  <= raw_shared_prune_active_suffix_pair_budget
       (afactored1_strong_dlform_universe r s c)
     * (Suc H + afactored1_strong_dlform_list_cost r s c)
```

Latest refinement: the abstract bucket-width target is now reduced to active
`RALTS`-head nodes.  Checked:

```text
pair_budget(afactored1_strong_dlform_universe r s c)
<=
  afactored1_strong_dlform_list_cost r s c
  * card (raw_shared_prune_active_suffix_alt_nodes
      (afactored1_strong_dlform_universe r s c))
```

Important correction: the remaining problem is not merely
`rsize_set (rseq_tails ...)`.  A distinct tail can be copied by several
same-key rows, so multiplicity must be paid by `pair_budget` or by an even
sharper same-key bucket theorem.

Best immediate target:

```text
bound the active RALTS-head count:

card (raw_shared_prune_active_suffix_alt_nodes
        (afactored1_strong_dlform_universe r s c)) <= A
```

Fallback already checked:

```text
A = length generated + rsizes generated
```

where `generated = concat (map (rpder_norm_list c) (afactored1 r s))`.  This
is useful as a ledger bridge, but probably too loose as the final cubic count;
look for a sharper step-local/provenance argument before declaring victory.

Important: this fallback gives a PRODUCT, not a single ledger obligation:

```text
active weighted bucket term
<=
  (afactored1_strong_dlform_list_cost r s c
   * (length generated + rsizes generated))
  * (Suc H + afactored1_strong_dlform_list_cost r s c)
```

So proving `length generated + rsizes generated <= cubic` alone does not close
the theorem.  Either prove a much sharper active-alt-node/provenance bound, or
replace this product accounting with a non-product ledger.

Then the checked interface gives:

```text
raw_shared_prune_active_suffix_pair_budget
  (afactored1_strong_dlform_universe r s c)
<= afactored1_strong_dlform_list_cost r s c * A
```

Do not continue the older "only distinct tail count remains" claim unless it
is restated through this pair-budget bridge.

## Urgent Supervisor Update, 2026-06-12 09:08 GMT+8

After syncing, read the last 250 lines of `PROGRESS_BACKREF.md`.  The latest
checked supervisor change adds an `actual-output dlform` gate in
`AntimirovFactoredTransition.thy`.

Simple definitions:

- `generated universe` = all rows produced before the one-pass strong prune.
- `actual output` = the rows that really remain after
  `rpder_strong_rows_raw c (afactored1 r s)`.
- `dlform set` = the deep-linear pieces obtained by opening those actual rows
  with `row_dlformss`.
- `shared-tail ledger` = a counting proof that charges the same simplified
  continuation/tail once, not once for every payload that mentions it.

The new preferred local gate is:

```text
rsize_set
  (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
  <= 2 * (rsize r + 3)^3
```

Checked equivalence: this gate is exactly the same as bounding the actual
deep-canonical strong rows:

```text
rsizes (rpder_strong_dcanon_rows_raw c (afactored1 r s))
  <= 2 * (rsize r + 3)^3
```

because `rpder_strong_dcanon_rows_raw` is just the duplicate-free list of the
actual output's `row_dlformss`.

If this gate is proved, the checked theorem
`rpder_strong_dcanon_rows_raw_afactored1_actual_dlforms_tight_cubic_contractI`
already gives the canonical rows with the desired language, disjointness,
liveness, paid-size, and cubic `rsizes` conclusions.

There is also a checked bridge from a list-cost target:

```text
sum_list
  (map (%p. row_dlforms_list_size (rsimpStrong_raw p))
    (concat (map (rpder_norm_list c) (afactored1 r s))))
  <= 2 * (rsize r + 3)^3
```

to the actual-output gate, via
`rpder_strong_dcanon_rows_raw_afactored1_actual_dlforms_list_tight_cubic_contractI`.

Do not spend a long cycle proving the explicit `pair_carrier` cubic by raw
product arithmetic.  Containment may be useful, but payloads x tails x
member-size is only a quartic-looking budget unless you add a shared-tail
ledger or another proof that avoids repeated charging.

Checked caveat for the first shared-tail brick:
`row_dlforms_list_size_RSEQ_RALTS_flat_payload_le` is now proved, but only with
explicit flat-payload and tail-cost premises:

```text
all p in ps are rnonseq and nonalt
row_dlforms_list_size k <= rsize k
```

Do not use `rtail_nf k` alone as the tail-cost premise; a tail can itself be a
grouped row and then `row_dlforms_list_size k <= rsize k` is not automatic.
This is now checked as `rtail_nf_not_enough_for_row_dlforms_list_size` with
`k = (a | b).c`.
The leaf case is checked by `row_dlforms_list_size_nonseq_nonalt_le`, and the
flat-tail package is
`row_dlforms_list_size_RSEQ_RALTS_flat_payload_flat_tail_le`.

Second checked caveat: `nested_payload_flat_tail_copy_bound_false` shows that
even a payload `p` with `rtail_nf p` and `nonalt p` is not enough.  The witness
is `p = (a | b).c`, `k = d`, `q = p.d`: the tail `k` is flat, but simplifying
`p.d` opens the inner `(a | b)` and copies the accumulated tail `c.d` into both
branches.  So the simple flat tail-copy formula is valid only for explicitly
flat payloads (`rnonseq` and `nonalt`), or it must be replaced by a recursive
ledger.

Checked bridge for the deduplicated actual-output route:
`rseq_tails_row_dlformss_rpder_strong_rows_raw_afactored1_subset_front` says
that every atom inside every top-level sequence tail `t` from an actual
dlform member `RSEQ h t` is still in
`strong_derivative_front_terms r (s @ [c])`; the matching checked head bridge
is `rseq_heads_row_dlformss_rpder_strong_rows_raw_afactored1_subset_front`.
Use `rseq_tails`/`rseq_heads` for actual dlform parts; `raw_shared_prune_suffix_key`
only sees `RSEQ (RALTS rows) k` buckets and misses ordinary `RSEQ h t`
members.

Checked size split: `rsize_set_split_rseq_tails_bucket_boundI` is the safe
form of the deduplicated accounting.  It does NOT charge each distinct tail
only once.  Since `rsize_set` is syntax size, the same tail repeated under
different heads is counted once per row.  The sound statement keeps a bucket
width `B`: if every sequence head has size at most `H`, and every fixed-tail
bucket `rseq_tail_rows U t` has at most `B` rows, then

```text
rsize_set U <= rsize_set (rnonseq_members U)
  + sum over distinct tails t of B * (Suc H + rsize t)
```

The generic bound `card_rseq_tail_rows_le_rseq_heads` is checked, and the
derived split `rsize_set_split_rseq_tails_head_count_boundI` lets you take
`B = card (rseq_heads U)`.

The nonalt-head half of the bucket bound is also checked as
`card_rseq_tail_nonalt_head_rows_rpder_strong_rows_raw_afactored1_le_front`:
for actual output, fixed-tail rows with a nonalt head inject into
`strong_derivative_front_terms r (s @ [c])`.  The remaining bucket-count work
is the keyed-head/RALTS part.

Update: the keyed-head/RALTS bridge is now checked as
`card_rseq_tail_rows_rpder_strong_rows_raw_afactored1_le_front_plus_active_suffix_bucket`.
It proves that each actual fixed-tail bucket is bounded by:

```text
card strong front carrier
+ card (raw_shared_prune_active_suffix_bucket
    (afactored1_strong_dlform_universe r s c) t)
```

So the next target is specifically to bound that active-suffix bucket term,
not to redo the head/tail split.

Per-tail size split is now checked:
`rsize_set_split_rseq_tails_rpder_strong_rows_raw_afactored1_front_plus_active_suffix_bucketI`.
Use this instead of forcing a single constant bucket bound.  It reduces the
actual deduplicated gate to:

```text
nonseq-member cost
+ sum over distinct tails t of
    (card strong_front + card active_suffix_bucket(t)) * (Suc H + rsize t)
```

where `H` bounds actual sequence-head size.  Remaining work: bound the weighted
active-suffix-bucket/tail sum and the head/tail size terms.

Next high-value concrete target: instantiate this with
`U = row_dlformss (rpder_strong_rows_raw c (afactored1 r s))` and prove a
useful actual-output bound for `card (rseq_heads U)` and the distinct tail
sum.

High-value next moves:

1. prove the actual-output gate directly from one-pass pruning;
2. prove the generated list-cost target using a shared-tail ledger;
3. if working on `pair_carrier`, prove only containment or a sharing lemma,
   not a raw product-size theorem.

## Urgent Supervisor Update, 2026-06-12 08:50 GMT+8

First sync to the current checked remote head:

```powershell
git fetch origin
git pull --ff-only
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check
```

Current checked head:

```text
9e8b091 Refute path-dual as strong carrier
```

The full `Posix` build passed after that proof-changing commit:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
```

Interpretation in simple terms:

- `carrier` means "the set we hope contains all rows produced by the strong
  derivative step."
- `rsize_set U` means "sum of syntax-tree sizes of all distinct rows in `U`."
- `cubic` means bounded by a fixed constant times `(rsize r + 3)^3`.
- `strong simplification exposes rows` means it can delete or simplify a
  prefix/continuation and thereby create a row that is not literally present
  as an old subterm or old frontier row.

Dead direct-carrier routes, all checked:

```text
apder_strong_dlfrontier_not_deep_frontier_subset
apder_strong_dlfrontier_not_insert_RONE_deep_frontier_subset
apder_strong_dlfrontier_not_subterm_deep_frontier_subset
apder_strong_dlfrontier_not_path_dual_frontier_universe_subset
actual_strong_canonical_aseq_payment_false
raw_shared_prune_active_suffix_owner_exponential
```

Do not try to prove any of these as positive containment/counting facts:

```text
apder_strong_dlfrontier r subset apder_deep_frontier r
apder_strong_dlfrontier r subset insert RONE (apder_deep_frontier r)
apder_strong_dlfrontier r subset apder_subterm_deep_frontier r
apder_strong_dlfrontier r subset partial_derivative_path_dual_frontier_universe r
unconditional aseq_terms_size_paid for actual strong canonical rows
generic polynomial/cardinality bound for raw_shared_prune_active_suffix_owner U
```

The current useful target is still this local one-step gate:

```text
rsize_set (afactored1_strong_dlform_universe r s c)
  <= 2 * (rsize r + 3)^3
```

This gate feeds already checked contracts such as
`rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_cubic_contractI`.
Equivalently, build a smaller contextual exposed-row carrier `Uctx` with:

```text
afactored1_strong_dlform_universe r s c subset Uctx
rsize_set Uctx <= O((rsize r + 3)^3)
```

The word "contextual" is important: the carrier must own rows formed by
combining a front payload with a simplified surrounding continuation.  A union
of literal subterms' deep frontiers and the old path-dual universe both miss
the same checked witness:

```text
star = a*
p    = a . star
k    = star | star
r    = (p) . k
x    = a . (star . star)
```

If you need to run Isabelle, use only the repository wrappers above.  Check
the worker slot first.  Do not use `sleep && tail` polling.  Treat background
shell "failed" after a full Isabelle run as a proof failure until the output
says otherwise; the command path itself is known-good.

## Latest Supervisor Note, 2026-06-12

First sync to the current checked branch:

```powershell
git fetch origin
git pull --ff-only
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check
```

After syncing, read this file from the current `origin/codex/backref-values`
tip.  Doc-only handoff commits may appear after the last proof-changing commit.

Current proof-checked theory head:

```text
cd1afcc Check abstract owner closure exponential witness
```

Do not restart from the older `54ddcda` checkpoint.  The current remote branch
already contains both the checked owner-closure exponential witness and this
handoff correction.

Latest checked direction warning:

```text
raw_shared_prune_active_suffix_owner_exponential
raw_shared_prune_active_suffix_owner_filtered_subsets_3
```

Do not spend another session proving that the owner DAG is finite.  That is now
checked.  In simple terms:

- `sizeNregex N` means "old/non-backref regexes whose syntax-tree size is at
  most `N`."
- `owner DAG` means the owner set plus all regex subterms of rows in that owner
  set.
- The new bridge says: if the one-step universe `U` is inside `sizeNregex N`,
  then its owner DAG is also inside `sizeNregex N`, hence finite.
- This is not a cubic count.  `sizeNregex N` is a large finite universe, and
  `card (sizeNregex N)` is not the desired `O(|r|^3)` budget.

Do not try to prove a generic polynomial bound for the abstract owner closure
`raw_shared_prune_active_suffix_owner U`.  The 2026-06-12 Fable construction is
now checked: repeated same-key pruning can generate `2^m - 1` filtered rows
from a seed set of size at most `m + 1`.  Treat generic owner-cardinality as a
dead route unless you first prove a step-local invariant that excludes the
construction.

The next useful proof should therefore be one of these:

1. a step-local invariant showing `afactored1_strong_dlform_universe r s c`
   cannot realize that construction, followed by a sharp same-key bucket
   bound;
2. a replacement of the abstract all-pairs owner closure by the actual
   one-pass accumulated pruning object matching `rsimpStrong_prune_rows_acc_raw`,
   where output count is tied to the input pass rather than to the transitive
   all-pairs closure.

If a proposed theorem only proves finite containment, key size, key projection,
or another wrapper around an already checked fact, it is drift.

For Isabelle on Windows, use the repository PowerShell wrappers.  Do not use
Bash `sleep && tail` polling for background builds.  If a build reaches 100% on
all theories and only then reports `SQLITE_CONSTRAINT_PRIMARYKEY`, that is a
concurrent Isabelle database write collision, not a proof failure.

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
This was last rechecked at `cd1afcc` after the owner-closure exponential witness
landed.

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

## 2026-06-12 Route-2 Supervisor Update

Latest checked checkpoint before this note: `7bdc97c`
(`Add bucket-shaped active closure bounds`) on `codex/backref-values`.

Since `3df1cef`, the route-2 support layer also gained:

- active closure front/key atom preservation;
- active closure key-DAG member-size and `rsize_set` packaging;
- bucket-shaped active closure and key-DAG cardinality interfaces;
- nested-`RNTIMES` raw-tree and ID/DAG smoke probes showing the risk family is
  useful stress evidence but not yet a counterexample to the active
  key-DAG/owner route.

The active route is no longer the route-1 linear frontier premise.  Work on
the step-local universe:

```text
U = afactored1_strong_dlform_universe r s c
```

Plain definitions:

- `U` is the set of row forms produced by one strong derivative step from
  `afactored1 r s`, after taking delayed linear forms.
- An active suffix key is the `k` in a grouped row
  `RSEQ (RALTS rows) k`.
- The active suffix bucket for `k` is the set of rows in `U` with exactly that
  same key `k`.
- The active suffix pair budget is the sum, over keys `k`, of
  `card(bucket k) * card(bucket k)`.  This is deliberately not all heads times
  all tails; only rows sharing the same key are paired.

Checked route-2 handles now include:

```text
raw_shared_prune_active_suffix_keys_iff
raw_shared_prune_active_suffix_bucket_iff

afactored1_strong_dlform_universe_active_suffix_key_aseq_union_subset_same_strong_front
card_afactored1_strong_dlform_universe_active_suffix_keys_le
afactored1_strong_dlform_universe_active_suffix_key_size_le_generated_rsizes
afactored1_strong_dlform_universe_active_suffix_key_size_le_list_cost

afactored1_strong_dlform_universe_active_suffix_pair_budget_le_card_square
afactored1_strong_dlform_universe_active_suffix_closure_member_size_le_generated_rsizes
afactored1_strong_dlform_universe_active_suffix_closure_member_size_le_list_cost
card_afactored1_strong_dlform_universe_active_suffix_closure_generated_boundI
card_afactored1_strong_dlform_universe_active_suffix_closure_list_boundI
card_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_generated_boundI
card_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_list_boundI
card_afactored1_strong_dlform_universe_active_suffix_closure_bucket_generated_boundI
card_afactored1_strong_dlform_universe_active_suffix_closure_bucket_list_boundI
card_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_bucket_generated_boundI
card_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_bucket_list_boundI
```

What this means: active-suffix closure does not make individual rows larger.
It adds rows by pruning pairs of rows that share the same key.  The useful
accounting shape is therefore:

```text
card U + pair_budget(U) * max_row_size
```

and the key-DAG accounting adds one more multiplication by `max_row_size`.

There is now a more targeted checked interface for this shape.  In plain
terms, prove:

```text
card U <= C
number of active suffix keys in U <= S
each active suffix bucket in U has size <= K
each generated/list row-size budget for U is <= M
```

Then Isabelle already gives:

```text
active closure size <= C + S*K*K*M
active closure key-DAG universe size <= (C + S*K*K*M)*M
```

This is the next best route because it preserves the same-key bucket structure
instead of charging every row against every other row.

The next useful theorem should close one of these real gaps:

- a cubic or otherwise strong enough bound for the step-local active suffix
  key count and per-key bucket size of `U`;
- a cubic or otherwise strong enough bound for the step-local `pair_budget(U)`;
- a cubic/list-cost bound strong enough to feed the checked closure lemmas;
- a bridge from `U` into the existing active-suffix owner/DAG machinery in
  `GeneralRegexBound.thy` and `FBound.thy`;
- a precise counterexample showing one of those subclaims is too strong.

Avoid these low-value moves:

- Do not introduce a generic tail-family abstraction unless it immediately
  proves a bound for active-suffix buckets or `pair_budget(U)`.
- Do not multiply "number of heads" by "number of tails" globally.  That loses
  the same-key bucket structure and can overshoot cubic.
- Do not add wrappers that merely restate current-front containment without
  discharging a named premise of a route-2 interface.

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
   - `afactored1_strong_dlform_universe_active_suffix_key_aseq_union_subset_same_strong_front`
   - `afactored1_strong_dlform_universe_active_suffix_closure_key_aseq_union_subset_same_strong_front`
   - `card_afactored1_strong_dlform_universe_active_suffix_closure_generated_boundI`
   - `card_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_generated_boundI`
   - `card_afactored1_strong_dlform_universe_active_suffix_closure_bucket_generated_boundI`
   - `card_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_bucket_generated_boundI`
   - `afactored1_strong_dlform_universe_owner_seq_member_decomp`
   - `afactored1_strong_dlform_universe_owner_seq_nonalt_head_in_front_terms`
   - `afactored1_strong_dlform_universe_owner_active_suffix_key_aseq_union_subset_same_strong_front`
   - `afactored1_strong_dlform_universe_owner_active_suffix_key_size_le_list_cost`
   - `afactored1_strong_dlform_universe_owner_active_suffix_key_dag_subset_owner_dag`
   - `card_afactored1_strong_dlform_universe_owner_active_suffix_key_dag_le_owner_dag`
   - `afactored1_strong_dlform_universe_owner_dag_member_size_le_list_cost`
   - `rsize_set_afactored1_strong_dlform_universe_owner_dag_list_boundI`
   - `afactored1_strong_dlform_universe_active_suffix_closure_key_dag_member_size_le_list_cost`
   - `rsize_set_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_list_boundI`
3. `FBound.thy`
   - `strong_deferred_original_raw_row_norm_later_shared_memo_cubic_interface`
   - `strong_deferred_row_gate_norm_active_suffix_universe_POSIX_contract`
   - `strong_deferred_row_gate_norm_active_suffix_universe_accumulator_POSIX_contract`
4. `GeneralRegexBound.thy`
   - `rsimpStrong_prune_rows_raw_later_shared_subsetI`
   - `raw_shared_prune_active_suffix_keys_iff`
   - `raw_shared_prune_active_suffix_bucket_iff`
   - `raw_shared_prune_active_suffix_pair_budget_bucket_bound`
   - `card_raw_shared_prune_active_suffix_closure_member_pair_budget_card_bound`
   - `raw_final_active_suffix_row_dag_universe_rsimpStrong_ALTs_raw_closed_subsetI`
5. `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`
   - the factored/active row bridge and row-diff comparison harness;
   - `nestedNtimesRisk`, `checkNestedNtimesRiskIdTrace`, and
     `ActiveSuffixIdStats` if investigating the nested-`RNTIMES` risk.

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

## Nested NTIMES Smoke Status

The nested-`RNTIMES` risk note in `PROGRESS_BACKREF.md` is a risk hypothesis,
not a theorem-target obituary.  Use the ID/DAG smoke mode first:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 -Route custom -SkipLegacyCubic -TraceNestedNtimesId -NestedNtimesK 8 -NestedNtimesM 8 -NestedNtimesN 8 -NestedNtimesBranches 8 -NestedNtimesLevels 3 -NestedNtimesLengths '128,256,512' -TimeoutSeconds 120
```

Observed so far: active rows grow along the counted grid, but the active
key-DAG/component/decomposition metrics stay far below `2*(rsize+3)^3` on
tested sizes.  The ID probe crosses the raw-tree OOM point
(`k=m=32, len=1023`) with `activeDecompOver2cubic=0.000453`.  A larger
three-level ID run at `k=m=n=16` printed len 1024 and then timed out before
len 2048, so keep samples small and bounded.  Do not run larger raw tree
traces in the background, and do not re-scope the theorem from this risk note
alone.  If no concrete executable counterexample emerges, return to the
route-2 active key-DAG/owner cardinality proof.

## Best Next Attack

The next session should not continue broad counterexample hunting.  Treat
counterexamples as a tool only when they answer a named theorem subclaim.  The
most useful routes are now:

1. First try to close the new ordinary sequence-tail weighted ledger:

   ```text
   sum_list (map (%q. row_dlforms_list_size q * rsize q)
     (rpder_strong_rows_raw c (afactored1 r s)))
     <= cubic polynomial in rsize r
   ```

   This would finish the ordinary sequence-tail size branch produced by
   `row_dlformss`.  Use the actual raw-row generator; do not prove a generic
   theorem over arbitrary row lists.
2. Prove a sharper bound for the actual step-local active sharing budget by
   bounding
   `raw_shared_prune_active_suffix_alt_nodes
   (afactored1_strong_dlform_universe r s c)`.  The checked interface
   `afactored1_strong_dlform_universe_active_suffix_pair_budget_list_cost_alt_nodes_bound`
   then gives `pair_budget <= list_cost * card(active_alt_nodes)`.  This is
   the concrete form of the old same-key bucket-width target.
3. Use the checked list-cost weighted bridge for the active term:

   ```text
   raw_shared_prune_active_suffix_weighted_rseq_tails_rpder_strong_rows_raw_afactored1_le_pair_budget_list_cost
   ```

   The active weighted bucket term no longer needs a separate all-tail size
   theorem.  Distinct-tail or tail-size work may still help the ordinary
   front/tail summand, but it is not the blocker for the active bucket term.
4. Use the existing owner/DAG machinery only with care.  The owner-set
   `RSEQ h t` decomposition is already packaged; it can still help charge
   nonalt heads to the current strong-front carrier and suffix/key pieces to
   active key accounting.  Owner active-key atoms, key sizes, key-DAG
   projection, owner-DAG member-size, and conditional `rsize_set` bounds are
   packaged.  Finite owner-DAG side conditions are also packaged via
   `sizeNregex`:

   ```text
   raw_shared_prune_active_suffix_owner_dag_sizeNregex_subset
   finite_raw_shared_prune_active_suffix_owner_dag_sizeNregex
   afactored1_strong_dlform_universe_owner_dag_subset_sizeNregex_generatedI
   afactored1_strong_dlform_universe_owner_dag_subset_sizeNregex_listI
   finite_afactored1_strong_dlform_universe_owner_dag_generatedI
   finite_afactored1_strong_dlform_universe_owner_dag_listI
   ```

   This only proves finite containment in a large ambient set.  Do not use
   `card (sizeNregex N)` as a final cubic bound.  Also do not pursue a generic
   cardinality bound for `raw_shared_prune_active_suffix_owner U`: the Fable
   exponential construction note shows that the abstract all-pairs closure is
   likely too large.  Continue this route only by proving a step-local
   invariant that excludes that construction, or by replacing the abstract
   closure with the one-pass accumulated pruning object used by
   `rsimpStrong_prune_rows_acc_raw`.
5. If a proposed step-local subclaim looks false, make the falsification exact
   and executable/checked, then stop.  Do not use the nested-`RNTIMES` smoke
   note as a reason to re-scope the whole theorem unless it becomes a concrete
   counterexample to a named route-2 statement.
6. As a fallback, replace the raw strong-row representation by a checked
   canonical projection via `row_dlform_canonical_rows`, then prove the
   production route computes or soundly refines that projection while
   preserving POSIX values.

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

- Run only one Posix build at a time.  If all theories reach 100% and the
  build then ends with `SQLITE_CONSTRAINT_PRIMARYKEY`, treat it as a concurrent
  Isabelle build database collision, not as a proof failure.  Check workers,
  wait for the other build to finish, and rerun the wrapper.
- Record only concise progress notes.  Avoid copying long chat transcripts into
  the repo or prompt context.
