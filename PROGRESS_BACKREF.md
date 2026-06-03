# POSIX Backreference Progress

Last updated: 2026-06-04 (strong-memo route is default)

## Cubic Route Checkpoint: Shared-Universe POSIX Contract (2026-06-04)

- Added the checked theorem
  `FBound.thy:strong_deferred_original_final_active_shared_row_dag_linear_contract`.
  It connects the shared row-DAG component handoff directly to the memo-strong
  POSIX reconstruction contract.
- New proof obligation shape:
  - `legacy_rexp r`;
  - final-active row count is linear:
    `card (strong_deferred_final_active_suffix_rows r s) <= rxsize r`;
  - one finite shared universe `U` covers both
    `strong_deferred_final_active_suffix_payload_dag_universe r s` and
    `strong_deferred_final_active_suffix_key_dag_universe r s`;
  - `card U <= C * rxsize r`.
- Under those assumptions the theorem yields exact `Some`/`None` POSIX
  correctness, `flat v = s`, legacy preservation for the final raw state and
  row-DAG nodes, pair budget `<= rxsize r * rxsize r`, and
  `card finalRowDag <= (C + 2) * rxsize r`.
- Design meaning: the remaining BR-040 proof can focus on constructing this
  shared root-owned `U`, instead of separately summing payload and key DAG
  components or proving POSIX value preservation again.
- Verification: focused Isabelle `Posix` build passed.
- No BR-039/BR-040 bounty is claimed; this is proof-interface infrastructure.

## Cubic Route Checkpoint: Root-Owned Shared Universe Handoff (2026-06-04)

- Added the general helper
  `GeneralRegexBound.thy:rsubterm_closure_subsetI`.
  If roots are contained in `U` and `U` is closed under `rsubterms`, then the
  full `rsubterm_closure` of those roots is contained in `U`.
- Added the checked theorem
  `FBound.thy:strong_deferred_original_final_active_shared_root_universe_linear_contract`.
  This lowers the shared-universe premise one more step: future work may prove
  coverage only for
  `strong_deferred_final_active_suffix_payload_roots r s` and
  `strong_deferred_final_active_suffix_keys r s`, plus subterm closure of `U`.
  The theorem internally lifts that to payload/key DAG coverage and then
  reuses the shared row-DAG POSIX contract.
- Design meaning: the preferred BR-040 target is now a root-owned finite
  universe `U` satisfying:
  `payload_roots ∪ suffix_keys ⊆ U`,
  `q ∈ U ==> rsubterms q ⊆ U`, and `card U <= C * rxsize r`, plus the final
  active row-count bound. Under those assumptions, exact POSIX reconstruction
  and `finalRowDag <= (C + 2) * rxsize r` follow.
- Verification: focused Isabelle `Posix` build passed.
- No BR-039/BR-040 bounty is claimed; this is still proof-interface
  infrastructure.

## Cubic Route Smoke: Memo-Strong Focus Reconfirmed (2026-06-04)

- Reconfirmed the route decision after inspecting the new derivative-size
  graphs: direct emitted-tree `bsimpCubic` is not the object to prove about.
  The active target is memo strong tree: `bders_simpStrong (intern r) s`
  supplies the nullable recognition gate, while exact POSIX values are
  reconstructed from the original regex through `strong_deferred_span_value`
  and the span/memo table.
- Re-ran the `strong-memo` Scala gate with exact POSIX value checks:
  exhaustive depth `2`/input length `3` (`84,300` regex/input pairs), known
  counterexample grid, and `5,000` deterministic random depth `7`/input `8`
  cases with seed `20260602`. Both `k=5` and `k=8` Chapter 7 traces passed
  with the final-active row-DAG universe gate at factor `3.0`.
- Fresh Chapter 7 memo-strong data to `n=80`:
  - `k=5`, `rsize=46`: strong tree peaks at `958` in this sampled grid,
    strong DAG is `69` at `n=80`, final-active row-DAG universe is `41`,
    and final-active pair budget is `17`.
  - `k=8`, `rsize=97`: strong tree is `3233` at `n=80`, strong DAG is
    `133`, final-active row-DAG universe is `91`, and final-active pair
    budget is `65`.
- Regenerated the focused plot/report at
  `agent_hunt_pipeline/reports/ch7_memo_strong_size_compare/`. The report
  compares `strongMemoTree`, `strongMemoDag`,
  `strongMemoFinalActiveRowDagUniverse`, and
  `strongMemoFinalActivePairBudget` for `k=5,8`, `n=0..80`.
- Proof implication: continue proving the final-active row-DAG/shared-universe
  bound and reuse the existing POSIX contracts
  `strong_deferred_memo_tree_POSIX_correctness` and
  `strong_deferred_original_final_active_single_row_dag_linear_contract`.
  Do not spend effort improving `bsimpCubic` unless a future candidate first
  beats this smoke grid and preserves exact POSIX values.

## Cubic Route Checkpoint: Row-DAG Decomposition Bridge (2026-06-04)

- Accepted the graph evidence that direct `bsimpCubic` tree-size control is
  hopeless as the main theorem route. The active route is memo strong tree:
  use `bsimpStrong` as the nullable recognition tree, reconstruct exact POSIX
  values from the original regex through the span/memo table, and prove the
  size theorem over final-active shared rows.
- Added checked raw row-DAG decomposition infrastructure in
  `GeneralRegexBound.thy`:
  `raw_final_active_suffix_alt_nodes`,
  `raw_final_active_suffix_payload_dag_universe`,
  `raw_final_active_suffix_key_dag_universe`,
  their `rsubterms`/finite facts, and
  `card_raw_final_active_suffix_row_dag_universe_decomp_boundI`.
  This decomposes a final-active `RSEQ (RALTS rows) k` row-DAG into four
  separately countable components: row nodes, the `RALTS` payload nodes,
  payload-member DAG subterms, and suffix-key DAG subterms.
- Lifted the same bridge to `FBound.thy` as
  `strong_deferred_final_active_suffix_*` definitions and
  `card_strong_deferred_final_active_suffix_row_dag_universe_decomp_boundI`.
  Future BR-040 work can now prove bounds for the four components instead of
  falling back to the coarse `rows * maxRowDag` factorization.
- Tightened the decomposition with checked
  `card_raw_final_active_suffix_alt_nodes_le_rows` and
  `card_strong_deferred_final_active_suffix_alt_nodes_le_rows`, plus the
  direct row-count interface
  `card_strong_deferred_final_active_suffix_row_dag_universe_decomp_rows_boundI`:
  it is now enough to bound `2 * rows + payload-DAG + suffix-key-DAG`.
- Split the two DAG components into closure-style accounting interfaces:
  `raw_final_active_suffix_key_dag_universe_eq_rsubterm_closure` and
  `raw_final_active_suffix_payload_dag_universe_eq_rsubterm_closure`, plus
  the lifted `strong_deferred_final_active_suffix_*` versions. The checked
  bounds
  `card_strong_deferred_final_active_suffix_key_dag_universe_boundI` and
  `card_strong_deferred_final_active_suffix_payload_dag_universe_boundI`
  reduce these components to cardinality bounds for keys/payload roots and
  local subterm-size bounds for each member.
- Added the combined checked interface
  `card_strong_deferred_final_active_suffix_row_dag_universe_component_boundI`.
  The remaining proof target can now be stated as five component obligations:
  row count `R`, payload-root count `P`, payload-root DAG bound `PM`, key
  count `K`, and key DAG bound `KM`; together they imply
  `finalRowDag <= 2*R + P*PM + K*KM`.
- Added invariant bridges for the new payload-root component:
  `legacy_raw_final_active_suffix_payload_roots`,
  `row_group_deep_nf_raw_final_active_suffix_payload_roots`,
  `legacy_strong_deferred_final_active_suffix_payload_roots`, and
  `row_group_deep_nf_strong_deferred_final_active_suffix_payload_roots_nonempty`.
  This makes payload roots usable in the same original-owned universe proof
  style as rows and suffix keys.
- Added a shared-universe row-DAG handoff:
  `card_strong_deferred_final_active_suffix_row_dag_universe_shared_component_boundI`.
  If a finite universe `U` covers both payload-DAG and key-DAG components,
  then `finalRowDag <= 2*rows + card U`. This is the hash-consed proof shape
  suggested by the Scala evidence and is sharper than summing payload and key
  DAG components separately.
- Focused Isabelle `Posix` build passed after splitting the proof into
  explicit subterm and suffix-key witnesses; no broad slow automation was
  introduced.
- Re-ran `strong-memo` Scala smoke with exact POSIX value checking on the
  default exhaustive grid (`84,300` regex/input pairs), the known CE grid, and
  `1,000` deterministic random depth-6/input-8 cases with seed `20260602`.
  The factor-`3` final-active row-DAG universe gate still passed; the strongest
  random observation in this run was seed `20260602` case `995`, with
  `rsize=28`, `rowDagUniverse=57`, ratio `2.035714`.
- No BR-039/BR-040 bounty is claimed. This is a proof-bridge checkpoint toward
  the memo-strong POSIX/cubic interface, not the final theorem.

## Cubic Route Smoke: Direct Final-Active Row-DAG Metric (2026-06-04)

- Retired `bsimpCubic` as a theorem candidate after the graphs: its emitted
  tree is the wrong object. The active candidate is now memo strong tree with
  exact POSIX reconstruction from the original regex, and a proof-facing size
  metric over final-active row-DAG subterms.
- Updated the Scala smoke gate to report the direct executable analogue of
  `strong_deferred_final_active_suffix_row_dag_universe`, exposed through
  `-StrongFinalActiveRowDagUniverseFactor` and the
  `strongMemoFinalActiveRowDagUniverse` Chapter 7 metric.
- The local CI entry point now enables this gate by default with factor `3.0`
  and reports the top three final-active observations, so the proof-facing
  metric is checked in ordinary `isabelle_ci.ps1` runs.
- Re-ran exact POSIX value smoke on the default exhaustive grid
  (`84,300` regex/input pairs) and the known counterexample grid with a
  final-active row-DAG universe factor of `2.0`; both passed.
- Chapter 7 long-tail smoke now separates the important metrics:
  - `k=5`, `rsize=46`, `n=4..80`: emitted strong tree ranges from `474` to
    `959`, prefix active row-DAG universe grows up to `320`, but the final
    row-DAG universe stays in `40..44`.
  - `k=8`, `rsize=97`, `n=4..80`: emitted strong tree ranges from `1164` to
    `3245`, prefix active row-DAG universe grows up to `870`, but the final
    row-DAG universe stays in `83..97`.
- Tighter factor-`1.0` and factor-`2.0` row-DAG-universe gates are false.
  The factor-`1.0` shrinker reduces seed `20260602` case `995` to
  `STAR(ALT(CH(b),STAR(CH(b))))` on input `b`, with `rsize=5`, exact POSIX
  values preserved, and final row-DAG universe `7`. The factor-`2.0` shrinker
  reduces the same random case to
  `NTIMES(NTIMES(STAR(ALT(STAR(CH(b)),CH(b))),2),2)` on `bbb`, with
  `rsize=11` and final row-DAG universe `23`. A factor-`3.0` gate passed
  `2,000` random depth-6/input-8 cases plus the k=8 Chapter 7 trace, and the
  finder found no factor-`3.0` CE in `5,000` random cases. So the next proof
  statement should be parameterized by a small constant `K`; current smoke
  evidence points to trying `K=3`, not `K=1` or `K=2`.
- Added checked Isabelle sanity facts for the two minimized row-DAG constant
  counterexamples:
  `FBound.thy:thesis_memo_strong_row_dag_factor1_counterexample` and
  `FBound.thy:thesis_memo_strong_row_dag_factor2_counterexample`. These facts
  make the failed `K=1` and `K=2` targets explicit on the proof side, while
  also checking that both examples satisfy the factor-`3` gate.
- Design meaning: the proof should not try to bound the raw emitted tree or
  the prefix-cumulative active universe. The current BR-040 target is:
  `bders_simpStrong` as the nullable recognition gate, exact POSIX value
  reconstruction via `strong_deferred_span_value`, and a final-only
  row-DAG-universe bound owned by the original regex. No bounty is claimed.

## Cubic Route Checkpoint: Empty Final-Active Budget Bridge (2026-06-04)

- Accepted the graph/smoke evidence: emitted-tree `bsimpCubic` is no longer a
  theorem candidate. Future work should make the memo strong tree route work
  for exact POSIX values, then prove the final-active row-DAG accounting
  theorem.
- Removed an uncommitted attempt to prove a linear raw-tree one-step theorem
  for `asize (bder c (intern r))`; that target is the wrong metric because it
  loses the sharing that makes the memo route plausible.
- Added checked raw and lifted empty-row bridge facts:
  - `GeneralRegexBound.thy:raw_final_active_suffix_row_dag_universe_empty`
  - `GeneralRegexBound.thy:raw_final_active_suffix_row_dag_universe_empty_iff`
  - `GeneralRegexBound.thy:raw_final_active_suffix_keys_empty`
  - `GeneralRegexBound.thy:raw_final_active_suffix_pair_budget_empty`
  - `GeneralRegexBound.thy:raw_final_active_suffix_max_row_dag_empty`
  - `FBound.thy:strong_deferred_final_active_suffix_row_dag_universe_empty`
  - `FBound.thy:strong_deferred_final_active_suffix_row_dag_universe_empty_iff`
  - `FBound.thy:card_strong_deferred_final_active_suffix_row_dag_universe_eq_zero_iff`
  - `FBound.thy:strong_deferred_final_active_suffix_keys_empty`
  - `FBound.thy:strong_deferred_final_active_suffix_pair_budget_empty`
  - `FBound.thy:strong_deferred_final_active_suffix_max_row_dag_empty`
- Added the checked lifted contract
  `FBound.thy:strong_deferred_original_final_active_empty_rows_contract`.
  If a legacy root has no final-active rows after `bders_simpStrong`, the
  memo strong nullable gate still gives exact POSIX `Some`/`None`
  reconstruction and `flat v = s`, while the active key/pair/row-DAG/max
  budgets collapse to zero.
- Design meaning: examples with large whole-final DAG but `finalRows=0` are
  now formally separated from the active metric. The BR-040 target remains:
  exact POSIX reconstruction via `strong_deferred_span_value`, with size
  controlled by final-active row-DAG universe/max-row-DAG facts.
- Verification: focused Isabelle `Posix` build passed. Full local CI passed.
  A follow-up strong-memo Scala smoke with seed `20260602`, `1,000` random
  depth-5/input-6 cases, and Chapter 7 `k=5` lengths through `80` also passed.
  At `k=5,n=80`, the strong tree is `957`, `finalRows=5`,
  `finalMaxRowDag=31`, and `finalPairs=17`. No bounty is claimed.

## Cubic Route Checkpoint: Final Raw DAG Handoff (2026-06-04)

- Added checked metric base facts for the memo-strong final recognition DAG:
  - `FBound.thy:strong_deferred_final_raw_dag_size_empty_le_rxsize`
  - `FBound.thy:strong_deferred_final_raw_dag_size_singleton_le_rxsize_square`
- Refactored the one-character row-DAG theorem to go through the stronger
  final raw DAG metric:
  `strong_deferred_final_raw_dag_size r [c] <= rxsize r * rxsize r`
  implies the existing final-active row-DAG universe bound.
- Added the checked handoff
  `FBound.thy:strong_deferred_original_final_raw_dag_linear_contract`.
  It states the current memo-strong route in Scala/proof terms: for a legacy
  root, a future linear bound on
  `strong_deferred_final_raw_dag_size r s` is enough to get exact POSIX
  `Some`/`None` reconstruction, `flat v = s`, legacy final raw, final rows,
  final pair budget, final row-DAG universe, max row-DAG, and span/split memo
  budgets.
- Design meaning: BR-040 can now be attacked either by proving the final-active
  row-DAG universe bound directly or by proving the whole final memo-DAG bound.
  This is still infrastructure; no bounty is claimed.
- Verification: focused Isabelle `Posix` build passed.
- Follow-up negative smoke: whole final memo-DAG constants are not the primary
  target. Seed `20260607` finds a factor-`3.0` CE:
  `NTIMES(STAR(NTIMES(ALT(CH(a),NTIMES(STAR(CH(b)),2)),3)),2)` on `abbb`,
  with `rsize=15`, `strongDag=48`, ratio `3.2`, exact POSIX values preserved,
  and `finalRows=0`. This means the final raw DAG handoff is useful if a
  larger linear constant is later proven, but the preferred BR-040 target
  remains the final-active row-DAG universe, which ignores inactive final DAG
  structure.

## Cubic Route Checkpoint: One-Step Row-DAG Base Case (2026-06-04)

- Added the checked legacy one-character derivative-size theorem
  `FBound.thy:asize_bder_intern_legacy_le_rxsize_square`:
  for non-backref roots,
  `asize (bder c (intern r)) <= rxsize r * rxsize r`.
  The proof is deliberately split by constructor and uses small named nat
  arithmetic helpers instead of broad nonlinear automation.
- Added the checked final-active row-DAG theorem
  `FBound.thy:card_strong_deferred_final_active_suffix_row_dag_universe_singleton_le_rxsize_square`:
  for legacy roots,
  `card (strong_deferred_final_active_suffix_row_dag_universe r [c]) <=
   rxsize r * rxsize r`.
- Design meaning: the memo-strong proof route now has both `[]` and `[c]`
  checked base evidence for the final-active row-DAG universe. This is still
  not the full BR-040 cubic theorem; the next proof obligation is the general
  path/induction step for arbitrary input while preserving the deferred POSIX
  value reconstruction contract.
- Verification: focused Isabelle `Posix` build passed.
- No bounty is claimed.

## Cubic Route Smoke: Memo Strong Long-Tail Gate (2026-06-04)

- Re-ran the strong-memo smoke route with exact POSIX value comparison,
  final-active budget factors, and Chapter 7 long tails:
  `rowsFactor=1.0`, `pairFactor=1.0`, `memberDagFactor=2.0`,
  `memberShapeDagFactor=2.0`.
- Seed `20260605`, `5,000` random cases at depth `6`, input length `8`,
  passed exact POSIX value preservation. The largest random final-active row
  ratio observed was `5 / 28`; the largest row DAG ratio stayed below `1.0`,
  while raw tree row-size could be larger (`112 / 33`). This is positive
  evidence for proving a DAG/row-universe theorem rather than a raw tree-member
  theorem.
- Chapter 7 long-tail checks:
  `k=5`, `n=80`: strong tree `957`, final rows `5`, final pair budget `17`,
  final max row DAG `31`.
  `k=8`, `n=80`: strong tree `3233`, final rows `9`, final pair budget `65`,
  final max row DAG `61`.
- Design meaning: `bsimpCubic` remains retired. The viable route is still
  memo strong recognition plus exact original-regex POSIX reconstruction, with
  the proof target focused on final-active row-DAG accounting.

## Cubic Route Checkpoint: Empty Row-DAG Base Case (2026-06-04)

- Added the checked base-case theorem
  `FBound.thy:card_strong_deferred_final_active_suffix_row_dag_universe_empty_le_rxsize`.
  It proves the active BR-040 row-DAG universe obligation for empty input with
  constant `K = 1`:
  `card (strong_deferred_final_active_suffix_row_dag_universe r []) <=
   rxsize r`.
- The proof uses the actual memo-strong state, not a wrapper:
  `bders_simpStrong (intern r) [] = intern r`, final row-DAG universe is
  bounded by final raw `rsize`, and `rsize (rerase (intern r)) = rxsize r`.
  This is the base case for a future input-induction proof of the linear
  row-DAG universe bound.
- Verification: focused Isabelle `Posix` build passed.
- No bounty is claimed.

## Cubic Route Checkpoint: Single Row-DAG Linear Handoff (2026-06-04)

- Added the checked theorem
  `FBound.thy:strong_deferred_original_final_active_single_row_dag_linear_contract`.
  It matches the current memo-strong proof target directly: for a legacy root,
  one bound
  `card (strong_deferred_final_active_suffix_row_dag_universe r s) <=
   K * rxsize r`
  yields exact POSIX `Some`/`None` correctness, `flat v = s`, final row count
  `<= K * rxsize r`, pair budget `<= (K * rxsize r)^2`, max row-DAG
  `<= K * rxsize r`, and the existing span/split memo budgets.
- This removes the older need to state a separate final-row bound when the
  proof route constructs a single row-DAG universe. The theorem is still a
  handoff: BR-040 remains open until Isabelle derives the row-DAG universe
  bound from the original non-backref regex structure.
- Verification: focused Isabelle `Posix` build passed.
- No bounty is claimed.

## Cubic Route Checkpoint: Memo-Strong DAG Scout and Final-Active Gate (2026-06-04)

- Added a Scala smoke switch for the whole final memo-strong exact-DAG metric:
  `-FindStrongMemoDagBudgetCE`, with `-StrongMemoDagFactor` and
  `-StrongMemoDagMinRegexSize` exposed by
  `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1`.
- Smoke result: `strongMemoDag <= 4 * rsize` found no CE in `1,000`
  random depth-6/input-8 cases on seed `20260602`, and
  `strongMemoDag <= 3 * rsize` found no CE in `5,000` cases on seed
  `20260603`. However `strongMemoDag <= 2 * rsize` is false: the shrinker
  reduces a CE to `STAR(NTIMES(STAR(CH(b)),2))` on input `bb`, with
  `rsize=6`, `strongDag=13`, and exact POSIX value preservation still true.
  This keeps the whole-final-DAG metric useful as a diagnostic, but too tight
  linear constants should not be the main proof target.
- Re-ran the proof-facing final-active scout on seeds
  `20260602,20260603,20260604`, `5,000` random cases each, depth `6`, input
  length `8`. No CE was found for final rows `<= 1.0 * rsize`, pair budget
  `<= 1.0 * rsize^2`, and exact-DAG/shape-DAG row-member budget
  `<= 2.0 * rsize`. The refreshed report is
  `agent_hunt_pipeline/reports/strong_memo_final_active_scout/summary.md`.
- Refreshed the Chapter 7 derivative-size report for `k=5,8`, `n=0..80`.
  At `n=80`, `strongMemoDag` is `69` for `k=5` and `133` for `k=8`, while
  `strongMemoFinalActiveMaxRowDag` is `31` and `61`, and final rows are `5`
  and `9`. This strengthens the route decision: prove the final-active
  row-DAG universe contract and exact POSIX reconstruction, not an emitted-tree
  `bsimpCubic` theorem.
- No BR-039/BR-040 bounty is claimed. This is smoke and route-selection
  infrastructure only.

## Cubic Route Checkpoint: Final Raw DAG Metric Bridge (2026-06-04)

- Added the Isabelle metric `strong_deferred_final_raw_dag_size`, defined as
  `card (rsubterms (strong_deferred_final_raw r s))`. This is the erased
  proof-side analogue of the Scala `strongMemoDag` measurement and keeps the
  focus on hash-consed/exact-DAG accounting rather than raw emitted-tree size.
- Proved
  `card_strong_deferred_final_active_suffix_row_dag_universe_le_final_raw_dag_size`
  and `strong_deferred_final_raw_dag_bound_to_row_dag_universe_bound`.
  Therefore any future bound on the exact DAG of the full memo-strong final
  recognition tree immediately supplies the row-DAG universe bound needed by
  `strong_deferred_original_final_active_single_row_dag_universe_contract`.
- Refreshed the Chapter 7 derivative-size report for `k=5,8`, `n=0..64`,
  metrics `strongTree,strongMemoTree,strongMemoDag,
  strongMemoFinalActiveMaxRowDag,strongMemoFinalActiveRows`. At `n=64`, the
  report shows:
  `k=5`: `strongMemoDag=72`, `finalMaxRowDag=31`, `finalRows=5`;
  `k=8`: `strongMemoDag=133`, `finalMaxRowDag=61`, `finalRows=9`.
  The report lives in
  `agent_hunt_pipeline/reports/ch7_derivative_size_compare/index.html`.
- Verification: full local CI passed with
  `isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin
  -SessionTimeoutSeconds 300`.
- No BR-039/BR-040 bounty is claimed. The next theorem target is now one of
  two concrete original-size bounds: either bound
  `strong_deferred_final_raw_dag_size r s`, or directly bound
  `strong_deferred_final_active_suffix_row_dag_universe r s`.

## Cubic Route Checkpoint: Memo-Strong Row-DAG Eliminators (2026-06-04)

- Confirmed the route switch requested after the derivative-size graphs:
  emitted-tree `bsimpCubic` is not an active proof target. The active candidate
  is memo strong tree: `bders_simpStrong` is the nullable recognition gate,
  while exact POSIX values are reconstructed from the original regex by
  `strong_deferred_span_value`.
- Ran a stronger executable gate:
  `scala_cubic_smoke.ps1 -Route strong-memo -RandomCases 2000 -RandomDepth 6
  -RandomInputLength 8 -Seed 20260602 -Ch7K 5 -Ch7Lengths
  4,8,12,16,20,24,28,32`. It preserved exact POSIX values on the default
  `84,300` exhaustive regex/input pairs and `2,000` deterministic random
  cases. On the thesis Chapter 7 `k=5` family, the recognition tree stayed in
  the observed range `474..918` for `n=4..32`, while final-active metrics
  stayed tiny: `finalRows` was `4` or `5`, and `finalMaxRowDag` stayed `31`.
- Re-ran the default final-active scout on seeds
  `20260602,20260603,20260604`, `5000` random cases each, depth `6`, input
  length `8`. No CE was found for rows `1.0 * rsize`, pair budget
  `1.0 * rsize^2`, and exact-DAG/shape-DAG row-member budget `2.0 * rsize`.
  The worst exact-DAG ratio remains `1.266667`; raw row-tree size is still
  much larger and remains the wrong metric.
- Added checked structure eliminators
  `GeneralRegexBound.thy:raw_final_active_suffix_row_dag_universeE` and
  `FBound.thy:strong_deferred_final_active_suffix_row_dag_universeE`. These
  expose every row-DAG node as a subterm of some concrete final-active
  `RSEQ (RALTS rows) k`, which is the next proof handle for row coverage and
  original-regex-owned DAG accounting.
- Verification: full local CI passed with
  `isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin
  -SessionTimeoutSeconds 300`, including the default strong-memo Scala gate,
  Isabelle `Posix`, and Isabelle `BackRefPilot`.
- No BR-039/BR-040 bounty is claimed. The remaining theorem is still to prove
  an original-regex-owned bound for
  `strong_deferred_final_active_suffix_row_dag_universe`.

## Cubic Route Checkpoint: Memo-Strong DAG Scout Default (2026-06-04)

- Followed the derivative-size graphs and retired emitted-tree `bsimpCubic` as
  the active route. The current route is memo strong tree: use
  `bders_simpStrong` as the nullable recognition gate, reconstruct exact
  POSIX values from `strong_deferred_span_value`, and account for final-active
  row exact-DAG size rather than raw row tree size.
- Updated `agent_hunt_pipeline/scripts/strong_memo_final_active_scout.ps1` so
  its default budget matches the proof contract: rows `1.0 * rsize`,
  pair-budget `1.0 * rsize^2`, raw member budget disabled, and exact-DAG plus
  shape-DAG member budgets `2.0 * rsize`.
- Re-ran the default scout on seeds `20260602,20260603,20260604`, `5000`
  random cases each, depth `6`, input length `8`. No final-active budget CE
  was found. Worst observed exact-DAG/shape-DAG ratio is `1.266667` on seed
  `20260602` case `4784`; the raw row-tree ratio on the same witness is
  `5.633333`, confirming that raw emitted-tree member size is the wrong
  theorem target.
- Added the Isabelle scalar metric
  `strong_deferred_final_active_suffix_max_row_dag` and the handoff theorem
  `strong_deferred_original_final_active_max_row_dag_metrics_contract`. This
  is the closest proof-side match to Scala's `finalMaxRowDag`: prove
  `card finalRows <= R` and `finalMaxRowDag <= M`, then obtain exact POSIX
  reconstruction, row-DAG universe size `R * M`, pair budget `R * R`, and the
  span/split memo budgets.
- Added the raw/strong bridge from row-DAG universe cardinality to the scalar
  max metric:
  `raw_final_active_suffix_max_row_dag_le_row_dag_universe`,
  `strong_deferred_final_active_suffix_max_row_dag_le_row_dag_universe`, and
  `strong_deferred_original_final_active_row_dag_universe_metrics_contract`.
  Hence proving
  `card (strong_deferred_final_active_suffix_row_dag_universe r s) <= D`
  immediately yields `finalMaxRowDag <= D` plus the POSIX reconstruction
  contract.
- Added fallback bounds
  `raw_final_active_suffix_max_row_dag_le_rsize` and
  `strong_deferred_final_active_suffix_max_row_dag_le_final_asize`, so the new
  scalar metric is wired into the existing final-size fallback facts.
- Added rows-to-row-DAG containment and the single-universe contract
  `strong_deferred_original_final_active_single_row_dag_universe_contract`.
  Since every final-active row is a member of the row-DAG universe, one bound
  `card rowDagUniverse <= D` now controls `finalRows <= D`, pair budget
  `<= D * D`, `finalMaxRowDag <= D`, and exact POSIX reconstruction.
- Added the exact row-DAG decomposition
  `raw_final_active_suffix_row_dag_universe_eq_rsubterm_closure` /
  `strong_deferred_final_active_suffix_row_dag_universe_eq_rsubterm_closure`
  and the cardinality bridge
  `card_strong_deferred_final_active_suffix_row_dag_universe_le_rows_times_max`.
  This states the proof split explicitly:
  `card rowDagUniverse <= card finalRows * finalMaxRowDag`.
- The report is in
  `agent_hunt_pipeline/reports/strong_memo_final_active_scout/summary.md`.
  This is smoke evidence only; BR-040 still requires an Isabelle derivation of
  original-regex-owned bounds for the row count and exact-DAG member size.

## Cubic Route Checkpoint: Row-DAG POSIX Handoff (2026-06-04)

- Continued the memo-strong route after retiring emitted-tree `bsimpCubic`.
- Added a raw finite-universe bridge:
  `raw_final_active_suffix_row_dag_universe_subsetI`,
  `raw_final_active_suffix_row_dag_universe_closed_subsetI`, and
  `card_raw_final_active_suffix_row_dag_universe_boundI`. If a universe `U`
  covers final-active rows and is closed under `rsubterms`, then the whole
  row-DAG universe is contained in `U`.
- Lifted this to the memo-strong final tree as
  `strong_deferred_final_active_suffix_row_dag_universe_subsetI`,
  `strong_deferred_final_active_suffix_row_dag_universe_closed_subsetI`, and
  `card_strong_deferred_final_active_suffix_row_dag_universe_boundI`.
- Added raw row-DAG universe closure facts:
  `legacy_raw_final_active_suffix_row_dag_universe` and
  `row_group_deep_nf_raw_final_active_suffix_row_dag_universe`.
- Lifted those facts to the final memo-strong state as
  `legacy_strong_deferred_final_active_suffix_row_dag_universe` and
  `row_group_deep_nf_strong_deferred_final_active_suffix_row_dag_universe_nonempty`.
- Added `strong_deferred_memo_tree_value_final_active_row_dag_interface`,
  which packages exact POSIX value reconstruction, final-active rows/pairs,
  row-DAG universe fallback bounds, and span/split memo budgets.
- Added the proof handoff
  `strong_deferred_original_final_active_row_dag_linear_contract`: for a
  non-backref regex, if the final-active row count is bounded by `rxsize r`
  and the row-DAG universe is bounded by `K * rxsize r`, then the memo-strong
  nullable gate returns the exact POSIX value and every final-active row has
  exact-DAG size at most `K * rxsize r`.
- Added the more proof-directed handoff
  `strong_deferred_original_final_active_row_dag_finite_universe_contract`.
  It reduces the row-DAG bound to constructing a finite original-size universe
  `U` that covers final-active rows and is closed under `rsubterms`.
- Added the more flexible two-universe handoff
  `strong_deferred_original_final_active_row_dag_two_universe_contract`.
  `RowU` controls final-active row count and therefore pair budget, while
  `DagU` controls exact-DAG nodes via `rsubterms` closure. This avoids forcing
  the hash-consed DAG universe itself to have the same tight cardinality as the
  row universe.
- Added `GeneralRegexBound.thy:rsubterm_closure` with closure/finite/cardinality
  lemmas. Instantiated the two-universe handoff as
  `strong_deferred_original_final_active_row_dag_row_closure_contract`: if
  `RowU` covers final-active rows, has size `R`, and every member has
  exact-DAG size at most `M`, then `rsubterm_closure RowU` is a valid `DagU`,
  the whole row-DAG universe has size at most `R * M`, and each final-active
  row keeps the sharper bound `M`.
- Added the metric-facing handoff
  `strong_deferred_original_final_active_row_metrics_contract`. This
  instantiates `RowU` to the actual final-active row set measured by Scala
  (`finalRows` plus `finalMaxRowDag`) and packages exact POSIX reconstruction,
  row count, pair budget, row-DAG size `R * M`, per-row exact-DAG bound `M`,
  and the span/split memo budgets. It is deliberately not a cubic theorem:
  the remaining proof target is to derive original-regex-owned bounds for
  those final-active row metrics.
- Added `strong_deferred_original_final_active_max_row_dag_metrics_contract`
  as a scalar form of the same handoff: a bound on
  `strong_deferred_final_active_suffix_max_row_dag r s` supplies the per-row
  exact-DAG member premise.
- Verification:
  focused `isabelle build -v -d . Posix` passed.
- This is BR-040 infrastructure. The missing theorem is now concrete: define
  an original-regex-owned `RowU`, prove row coverage, and prove cardinality
  plus exact-DAG member bounds for it.

## Cubic Route Checkpoint: Isabelle Row-DAG Universe (2026-06-04)

- Moved the Scala row-DAG observation into Isabelle as a proof-facing object.
- Added `GeneralRegexBound.thy:raw_final_active_suffix_row_dag_universe`,
  defined as the union of `rsubterms q` over all final-active rows `q`.
  This corresponds to the exact-DAG nodes of final-active rows, not their raw
  tree expansion.
- Checked raw facts:
  `raw_final_active_suffix_row_dag_universe_subset_rsubterms`,
  `card_raw_final_active_suffix_row_dag_universe_le_rsize`,
  `raw_final_active_suffix_row_dag_subterms_subset_universe`,
  `card_raw_final_active_suffix_row_dag_le_universe`, and
  `card_raw_final_active_suffix_row_dag_le_rsize`.
- Lifted the universe to the memo-strong final tree in `FBound.thy` as
  `strong_deferred_final_active_suffix_row_dag_universe`, with final-rsize and
  final-asize bounds plus the key interface
  `card_strong_deferred_final_active_suffix_row_dag_boundI`.
- Design effect: future proof work can now target
  `card (strong_deferred_final_active_suffix_row_dag_universe r s) <= K *
  rxsize r`, then obtain a linear exact-DAG bound for every final-active row.
  This is the Isabelle counterpart of the new Scala `maxRowDag` smoke metric.
- Verification:
  focused `isabelle build -v -d . Posix` passed.
- This remains BR-040 infrastructure. No cubic theorem or bounty is claimed.

## Cubic Route Checkpoint: Final-Active Member DAG Metrics (2026-06-03)

- Continued the route requested by Chengsong: focus on memo/hash-consed strong
  tree with exact POSIX reconstruction, not the retired emitted-tree
  `bsimpCubic`.
- Extended `agent_hunt_pipeline/scala/PosixCubicSmoke.scala` with erased
  `Rexp` exact DAG and shape-DAG size functions, and added final-active row
  member DAG/shape-DAG metrics:
  `maxRowDagSize` and `maxRowShapeDagSize`.
- Extended the smoke wrapper with optional final-active DAG budget gates:
  `-StrongFinalActiveMemberDagFactor` and
  `-StrongFinalActiveMemberShapeDagFactor`. Existing raw tree member-factor
  behavior is unchanged and remains available as negative evidence.
- Extended the Chapter 7 deferred-memo grid script so it can plot
  `strongMemoActiveMaxRowDag`, `strongMemoActiveMaxRowShapeDag`,
  `strongMemoFinalActiveMaxRowDag`, and
  `strongMemoFinalActiveMaxRowShapeDag` by default.
- Smoke results:
  - default strong-memo smoke still passed exact POSIX values on 84,300
    exhaustive cases, the known CE grid, and a small random compile check;
  - a DAG budget scout with rows `1.0`, pair `1.0`, raw member disabled, and
    DAG/shape-DAG member factors `2.0` found no CE in 5,000 deterministic
    random cases at depth `6`, input length `8`, seed `20260602`;
  - the previous raw-tree counterexample remains informative: random case
    `4784` has `rsize=30`, raw final-active max row size `169`, but
    max row DAG and shape-DAG are both `38`.
- Chapter 7 probe:
  `agent_hunt_pipeline/reports/ch7_deferred_memo_dag_probe/` records k=`5`,
  n=`4,8,12`: final-active max row raw tree size is constantly `126`, while
  final-active max row DAG and shape-DAG are constantly `31`.
- Design consequence: the next Isabelle target should be a finite
  hash-consed/indexed final-active member universe and POSIX reconstruction
  bridge. Proving raw row-member tree size linear is explicitly the wrong
  target.
- This is BR-038/BR-039/BR-040 testing infrastructure only. No bounty is
  claimed.

## Cubic Route Checkpoint: Strong-Memo Row Subterm Handles (2026-06-03)

- Continued the memo-strong route and kept emitted-tree `bsimpCubic` retired.
  The live object is still `bders_simpStrong` as the nullable recognition tree,
  with exact POSIX values reconstructed from the original regex span/memo
  table.
- Added raw final-active row member handles in `GeneralRegexBound.thy`:
  `raw_final_active_suffix_row_elem_rsubterms`,
  `raw_final_active_suffix_row_key_rsubterms`,
  `raw_final_active_suffix_row_elem_size_le_rsize`, and
  `raw_final_active_suffix_row_key_size_le_rsize`.
- Lifted them to the memo-strong final tree in `FBound.thy`:
  `strong_deferred_final_active_suffix_row_elem_final_rsubterms`,
  `strong_deferred_final_active_suffix_row_key_final_rsubterms`,
  `strong_deferred_final_active_suffix_row_elem_size_le_final_rsize`,
  `strong_deferred_final_active_suffix_row_key_size_le_final_rsize`,
  `strong_deferred_final_active_suffix_row_elem_size_le_final_asize`, and
  `strong_deferred_final_active_suffix_row_key_size_le_final_asize`.
- Verification so far:
  focused `isabelle build -v -d . Posix` passed; default strong-memo Scala
  smoke passed exact POSIX value comparison on 84,300 exhaustive depth-2/input-3
  cases, the known CE grid, and 2,000 deterministic random cases. On the
  Chapter 7 k=5 grid at lengths `4,8,12,16,20`, strong tree sizes were
  `474,730,771,820,875`.
- Important negative scout result: final-active rows and pair-budget remain
  small, but raw final-active row-member **tree** size is not a credible
  linear metric. `MemberFactor=1` fails on the known CE (`rsize=10`,
  max row size `15`); `MemberFactor=2` fails on a random nested-star case
  (`rsize=26`, max row size `59`); `MemberFactor=3` fails on another random
  case (`rsize=30`, max row size `169`, while the strong DAG is only `42`).
  Therefore the next proof target should be a hash-consed/member-DAG or
  indexed/quotiented final-active universe that preserves POSIX reconstruction,
  not the raw-tree member-size premise.
- This is BR-040 infrastructure and counterexample guidance only. No bounty is
  claimed.

## Cubic Route Checkpoint: Final-Active Row Element Handles (2026-06-03)

- Continued the memo-strong route. The goal is still the cubic non-backref
  bound with exact POSIX values; `bsimpCubic` remains negative evidence rather
  than a proof target.
- Added raw final-active inheritance lemmas in `GeneralRegexBound.thy`:
  `legacy_raw_final_active_suffix_rows`,
  `legacy_raw_final_active_suffix_keys`,
  `legacy_raw_final_active_suffix_bucket`,
  `row_group_deep_nf_raw_final_active_suffix_rows`,
  `row_group_deep_nf_raw_final_active_suffix_keys`,
  `row_group_deep_nf_raw_final_active_suffix_bucket`,
  `row_group_deep_nf_raw_final_active_suffix_row_elem`, and
  `row_group_deep_nf_raw_final_active_suffix_row_key`.
- Lifted those handles to the memo-strong final tree in `FBound.thy`:
  `legacy_strong_deferred_final_raw`,
  `legacy_strong_deferred_final_active_suffix_rows`,
  `legacy_strong_deferred_final_active_suffix_keys`,
  `legacy_strong_deferred_final_active_suffix_bucket`,
  `row_group_deep_nf_strong_deferred_final_active_suffix_bucket_nonempty`,
  `row_group_deep_nf_strong_deferred_final_active_suffix_row_elem_nonempty`,
  and
  `row_group_deep_nf_strong_deferred_final_active_suffix_row_key_nonempty`.
- Design effect: future row/member-size proofs can now start from a concrete
  final-active row `RSEQ (RALTS rows) k` and immediately know that the row
  payload elements and suffix key are legacy/deep-normal. This is a proof
  handle for the final-active size argument, not a wrapper or a payout.
- Verification:
  focused `isabelle build -v -d . Posix` passed.

## Cubic Route Checkpoint: Memo Strong Final-Active NF Bridge (2026-06-03)

- Followed the derivative-size graphs and kept emitted-tree `bsimpCubic`
  retired as a proof target. The active route is memo strong tree:
  `bders_simpStrong` is only the small nullable recognition state, while
  exact POSIX values are reconstructed from the original regex span/memo table.
- Re-ran the stronger `strong-memo` smoke gate:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 -Route strong-memo -RandomCases 2000 -RandomDepth 5 -RandomInputLength 6 -Seed 20260602 -FindStrongFinalActiveBudgetCE -StrongFinalActiveRowsFactor 1.0 -StrongFinalActiveMemberFactor 8.0 -StrongFinalActivePairFactor 1.0 -StrongFinalActiveMinRegexSize 5 -StrongFinalActiveTop 5 -TimeoutSeconds 300`.
  It passed exact POSIX value comparison on the exhaustive depth-2/input-3
  grid, the known CE grid, and 2,000 deterministic random cases. No
  final-active budget CE was found under rows `1.0`, member `8.0`, pair `1.0`.
- Added checked proof bridges:
  `GeneralRegexBound.thy:legacy_rrexp_rsubterms`,
  `GeneralRegexBound.thy:row_group_deep_nf_legacy_rsubterms`,
  `FBound.thy:row_group_deep_nf_strong_deferred_final_raw_nonempty`,
  `FBound.thy:row_group_deep_nf_strong_deferred_final_active_suffix_rows_nonempty`,
  and
  `FBound.thy:row_group_deep_nf_strong_deferred_final_active_suffix_keys_nonempty`.
- Design effect: for legacy non-backref roots and nonempty input, the final
  raw strong recognition tree, every final-active shared-suffix row, and every
  final-active suffix key are now known to be `row_group_deep_nf`. This gives
  the future row-count/member-size proof a normal-form handle directly at the
  `strong_deferred_final_raw` object used by the memo-strong contracts.
- Proof engineering note: the first draft used broad `auto` over `rsubterms`
  and immediately caused 100s proof-search lines. The checked version splits
  constructor cases and handles non-legacy backref constructors by explicit
  contradiction from `legacy_rrexp`.
- Verification:
  - focused `isabelle build -v -d . Posix` passed;
  - full local CI passed:
    `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`.
- This is BR-040 infrastructure only. It does not claim the cubic theorem or
  any bounty payout.

## Cubic Route Checkpoint: Strong `NTIMES` Entry Normalization (2026-06-03)

- Strengthened `bsimpStrong`/`rsimpStrong`/`rsimpStrong_raw` so they recurse
  into `ANTIMES`/`RNTIMES` bodies. This is deliberately conservative: it does
  not collapse `n = 0` repetitions or epsilon bodies into `ONE`, so the strong
  recognition tree keeps the repetition/value framing while eliminating the
  previous unnormalized-body gap.
- Synchronized the Scala smoke model (`PosixCubicSmoke.scala`) with the same
  `ANTIMES` body-recursion rule. The historical counterexample G now records
  the new strong result `ANTIMES [] (AONE []) 3`, while `bsimpCubic` still
  folds the whole repetition to `AONE [Z,Z,Z,S]`.
- Added checked entry-normalization lemmas:
  `row_group_deep_nf_rsimpStrong_raw_legacy`,
  `row_group_deep_nf_rerase_bsimpStrong_legacy`,
  `row_group_deep_nf_rerase_bders_simpStrong_bsimpStrong_start`,
  `row_group_deep_nf_rerase_bders_simpStrong_nonempty`,
  `row_group_deep_nf_rerase_bders_simpStrong_bsimpStrong_intern`, and
  `row_group_deep_nf_rerase_bders_simpStrong_intern_nonempty`.
- Design effect: the memo-strong proof route no longer has to pretend that
  raw `intern r` is already deep-normal. Either start the recognition state at
  `bsimpStrong (intern r)`, or use the nonempty-input theorem for the existing
  derivative loop.
- Verification:
  - full local CI passed:
    `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`;
  - deterministic random `strong-memo` Scala smoke passed:
    `scala_cubic_smoke.ps1 -Route strong-memo -RandomCases 2000 -RandomDepth 5 -RandomInputLength 6`.
- This is still infrastructure for BR-039/BR-040, not a cubic theorem payout.

## Cubic Route Checkpoint: Raw Strong Normal-Form Preservation (2026-06-03)

- Followed the graph evidence and kept emitted-tree `bsimpCubic` retired as a
  proof target. The active route is now the memo strong tree: `bsimpStrong`
  supplies the small nullable recognition state, while exact POSIX values come
  from the original regex span/memo reconstruction.
- Added checked raw preservation lemmas for the strong simplifier:
  `row_group_deep_nf_rsimpStrong_prune_pair_raw`,
  `row_group_deep_nf_rsimpStrong_prune_against_rows_raw`,
  `row_group_deep_nf_rsimpStrong_prune_rows_raw`,
  `row_group_deep_nf_rsimpStrong_ALTs_raw`, and
  `row_group_deep_nf_rsimpStrong_raw` in `GeneralRegexBound.thy`.
- Lifted this through erasure with
  `FBound.thy:row_group_deep_nf_rerase_bsimpStrong`. This is the right proof
  side for `bsimpStrong`, because annotated strong simplification erases to
  `rsimpStrong_raw`, not to the older non-raw simplifier.
- This is proof infrastructure only. It does not prove the cubic theorem and
  claims no BR-039/BR-040 bounty. The next target is a derivative-step
  invariant of the form
  `row_group_deep_nf (rerase r) ==> row_group_deep_nf (rerase (bsimpStrong (bder c r)))`,
  followed by final-active row/member bounds for the memo strong tree.
- Added and checked that derivative-step invariant for the legacy non-backref
  fragment:
  `GeneralRegexBound.thy:row_group_deep_nf_rsimpStrong_raw_rder`,
  `FBound.thy:row_group_deep_nf_rerase_bsimpStrong_bder`, and the loop lift
  `FBound.thy:row_group_deep_nf_rerase_bders_simpStrong`.
- Important limitation: the loop theorem assumes the current annotated state
  already erases to `legacy_rrexp` and `row_group_deep_nf`. Raw `intern r` is
  not claimed to be deep-normal for arbitrary original regex syntax. A future
  entry theorem should either normalize the start state first or state the
  first-step/final-active bound with this precondition explicit.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Checkpoint: Final-Active Proof Contract (2026-06-03)

- Added and checked
  `FBound.thy:strong_deferred_original_final_active_budget_contract_with_member_bound`;
  the older `strong_deferred_original_final_active_budget_contract` remains as
  the special `M = rxsize r` instance.
- Added checked linear-member handoff theorem
  `strong_deferred_original_final_active_linear_member_cubic_contract`. It
  states the next landing zone explicitly: if final-active rows are linear,
  final-active pair-budget is quadratic, and final-active row member-size is
  `<= K * rxsize r`, then the final-active closure is
  `<= rxsize r + K * rxsize r^3`.
- The theorem matches the current Scala final-active scout: for a legacy
  non-backref regex, if the final derivative state satisfies
  `finalActiveRows <= rxsize r`, `finalActivePairBudget <= rxsize r^2`, and
  each final-active row has raw size `<= M`, then the memo strong-tree route
  yields:
  - exact POSIX `Some`/`None` correctness and `flat v = s`;
  - a legacy final raw recognition state;
  - final-active closure size
    `<= rxsize r + rxsize r * rxsize r * M`;
  - the existing quadratic span-state and cubic split-probe memo budgets.
- This is not a wrapper payout and does not prove the cubic theorem. It turns
  the next proof obligation into root-owned final-active size premises. A
  future cubic theorem can instantiate this with `M = K * rxsize r` once a
  checked linear member-size proof is available.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Checkpoint: Strong-Memo Final-Active Scout (2026-06-03)

- Retired `bsimpCubic` as an active proof target after the size graphs: future
  proof effort should focus on the memo strong tree route, where
  `bders_simpStrong` is the small POSIX recognition gate and exact values come
  from original-regex span/memo reconstruction.
- Added final-active budget smoke plumbing to
  `agent_hunt_pipeline/scala/PosixCubicSmoke.scala` and
  `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1`. The new optional gate
  checks `strongMemoFinalActiveRows <= rowsFactor * rsize(r)`,
  `strongMemoFinalActiveMaxRowSize <= memberFactor * rsize(r)`, and
  `strongMemoFinalActivePairBudget <= pairFactor * rsize(r)^2`, while keeping
  the existing exact POSIX value comparison enabled.
- Added `agent_hunt_pipeline/scripts/strong_memo_final_active_scout.ps1`, a
  reproducible multi-seed scout that runs the gate plus a greedy final-active
  counterexample shrinker and writes
  `agent_hunt_pipeline/reports/strong_memo_final_active_scout/summary.md`.
- Current checked scout run:
  `Seeds=20260602,20260603,20260604`, `RandomCases=5000`, `RandomDepth=6`,
  `RandomInputLength=8`, `RowsFactor=1.0`, `MemberFactor=8.0`,
  `PairFactor=1.0`, `MinRegexSize=5`. All three seeds found no final-active
  witness above the linear rows, linear member-size, or quadratic pair-budget.
  The worst reported rows ratio was `0.782609`; the worst member ratio was
  `6.500000`; the worst pair ratio was `0.040000`.
- The rejected `MemberFactor=1.0`, `2.0`, and `4.0` runs are useful negative
  evidence: a known greedy-sequence CE needs `15/10 = 1.5`, Chapter 7
  `k=5,n=4` needs `126/46 ~= 2.74`, and seed `20260602` case `4784` needs
  `195/30 = 6.5`. A separate `k=5,8`, `n=4..32` grid shows the final-active
  max row size plateaus at `126` for `k=5` and `297` for `k=8`.
- Added `agent_hunt_pipeline/scripts/strong_memo_final_active_factor_sweep.ps1`
  to make this comparison reproducible. The current report under
  `agent_hunt_pipeline/reports/strong_memo_final_active_factor_sweep/` sweeps
  member factors `4,6,8` on seeds `20260602,20260603,20260604`, `5000` random
  cases each. It records `4` and `6` as failed by the same `6.5x` witness, and
  `8` as the current smoke-passing candidate.
- A deeper follow-up report under
  `agent_hunt_pipeline/reports/strong_memo_final_active_factor_sweep_deep/`
  sweeps member factors `8,10,12` on seeds
  `20260602,20260603,20260604,20260605,20260606`, `10000` random cases each,
  depth `7`, input length `10`. All three factors pass; the worst member
  ratio observed is `6.809524`. This strengthens smoke evidence for using
  `K = 8` as the next candidate, but it is still not a theorem.
- Added checked structural lemmas for the final-active proof route:
  `raw_final_active_suffix_rows_iff`, `raw_final_active_suffix_keys_iff`, and
  `raw_final_active_suffix_bucket_iff` in `GeneralRegexBound.thy`, with
  lifted `strong_deferred_final_active_suffix_*` versions in `FBound.thy`.
  These reduce final-active row/key/bucket reasoning to concrete
  `RSEQ (RALTS rows) k` subterms of the final strong tree.
- Added checked key/bucket support lemmas for the same route:
  final-active keys and buckets are subsets of final-tree `rsubterms`, with
  card and member-size bounds by the final raw tree size/asize. These are not
  original-size bounds yet; they are proof plumbing for the next step, where
  the final active rows must be related back to the root regex.
- Added checked premise-reduction facts:
  `strong_deferred_final_active_suffix_pair_budget_le_rxsize_square` derives
  the quadratic pair-budget directly from the linear final-active row bound,
  and
  `strong_deferred_original_final_active_rows_linear_member_cubic_contract`
  packages the memo strong-tree POSIX contract with only two remaining
  original-size obligations: final-active row count and final-active row
  member size.
- The Chapter 7 k=5 trace now prints final-active metrics directly. On
  lengths `4,8,12,16,20`, the cumulative active pair-budget grows
  `82,577,901,1226,1601`, but the final-active pair-budget stays `17` and
  final-active rows stay `5`. This is exactly the separation the proof route
  should exploit.
- No bounty is claimed. This is smoke evidence and tooling for BR-039/BR-040;
  the remaining theorem target is still a checked final strong-tree bound, or
  an equivalent indexed/quotiented final-active universe bound preserving
  POSIX values.

## Cubic Route Checkpoint: Strong-Memo Budget Scout (2026-06-03)

- Added `agent_hunt_pipeline/scripts/strong_memo_budget_scout.ps1`, a reusable
  smoke driver for the direct memo strong-tree route. It loops over seeds,
  runs `scala_cubic_smoke.ps1 -Route strong-memo -FindStrongCubicBudgetCE`,
  keeps exact POSIX value smoke enabled, and writes logs plus
  `agent_hunt_pipeline/reports/strong_memo_budget_scout/summary.md`.
- Initial checked scout run:
  `Seeds=20260602,20260603`, `RandomCases=2000`, `RandomDepth=6`,
  `RandomInputLength=8`, `StrongCubicFactor=1.0`,
  `StrongCubicMinRegexSize=5`. Both seeds found no final strong-tree witness
  above `rsize(r)^3`; the report's top global ratio is `0.112000` from the
  bounded exhaustive smoke.
- A separate larger manual run on seed `20260602` with `10000` random cases at
  depth `6`, input length `8`, also found no `rsize(r)^3` budget CE; the worst
  random ratio printed there was `0.143519` for
  `STAR(STAR(NTIMES(STAR(CH(b)),1)))` on `bb`.
- Design result: this strengthens the smoke evidence for the direct
  `bders_simpStrong` final-tree bound, but it is not a theorem. The next proof
  move should still be a root-owned indexed/quotiented universe or a direct
  final strong-tree bound that can explain these observations.

## Cubic Route Checkpoint: Row-List Bridge CE Shrinker (2026-06-03)

- Added an explicit Scala CE finder for the optional row-list/factoring bridge:
  `scala_cubic_smoke.ps1 -FindStrongRowsBridgeCE`. It greedily shrinks random
  final-active coverage failures by input and regex structure.
- The shrinker confirms that the row-list bridge is not the right main route
  yet. After adding local ALT-branch factoring, bounded sequence/ALT expansion,
  and an 8-round factoring closure, the deterministic depth `6`, input length
  `8`, seed `20260602` search still shrinks to:
  `SEQ(SEQ(STAR(SEQ(STAR(ALT(SEQ(CH(a),CH(b)),CH(a))),CH(a))),CH(a)),CH(b))`
  on input `a`.
- A tempting bridge root
  `strongRootFromRows rows = bsimpStrong (AALTs [] rows)` also fails on this
  counterexample: `rowRootEq1 = false`, `rowRootHit = false`. Therefore do not
  try to prove the cubic theorem through exact row-list reconstruction unless a
  new smoke-tested bridge replaces this one.
- Current positive theorem route remains direct memo strong tree:
  `strong_deferred_memo_tree_POSIX_correctness`,
  `strong_deferred_memo_tree_POSIX_flat`, and the row-gated variants are
  already checked in `FBound.thy`. The remaining hard task is a size bound for
  `bders_simpStrong (intern r) s` or an equivalent indexed/quotiented
  representation, not POSIX value correctness from scratch.

## Cubic Route Checkpoint: Row-Gated Memo Smoke (2026-06-03)

- Added checked row-gated POSIX contracts in `FBound.thy`:
  `strong_deferred_row_gate_memo_POSIX_correctness` and
  `strong_deferred_row_gate_memo_POSIX_flat`. These use
  `bpders_strong1_rows (intern r) s` only as the nullable gate; the exact value
  still comes from `strong_deferred_span_value`, so POSIX values are preserved.
- Added Scala smoke support for `bpdersStrong1Rows` and a candidate final-active
  bridge:
  `scala_cubic_smoke.ps1 -CheckStrongRowsBridge
  -RequireStrongRowsBridgeCoverage`.
- Positive smoke:
  exhaustive depth `2`, input length `3` passes on `84,300` regex/input pairs;
  deterministic random depth `5`, input length `6`, `2,000` cases at seed
  `20260602` also passes.
- Negative smoke:
  deterministic random depth `6`, input length `8`, `10,000` cases at seed
  `20260602` still finds a final-active bridge counterexample, so this bridge is
  not yet a theorem candidate. Also, running the row-list bridge on Chapter 7
  long tails can exhaust the Scala heap, so `bpdersStrong1Rows` must not be the
  executable long-tail object.
- Design result: keep `bders_simpStrong` / memo reconstruction as the active
  route. Use row-list/factoring only as a proof abstraction and CE-driven
  diagnostic until the bridge survives stronger smoke.

## Cubic Route Checkpoint: Active-Suffix POSIX Contract (2026-06-03)

- Added the checked theorem
  `FBound.thy:strong_deferred_original_raw_row_norm_active_suffix_memo_POSIX_contract`.
  Under the current active-suffix cubic-universe premises it now packages:
  exact POSIX value correctness for the strong nullable gate plus
  `strong_deferred_span_value`, exact `None` iff no POSIX value exists,
  `flat v = s` for successful reconstruction, the `bpders_strong1_rows`
  row-size bound `<= B`, the raw row-size bound `<= B`, the row nullable gate,
  and the existing span/split memo budgets.
- Regenerated the deferred memo Chapter 7 grid report:
  `agent_hunt_pipeline/scripts/ch7_deferred_memo_grid.ps1 -Ks "5,8,10,12" -MaxN 200 -Step 4`.
  The report lives under
  `agent_hunt_pipeline/reports/ch7_deferred_memo_grid/`.
- Long-tail smoke summary from the CSV:
  - k=5: `strongMemoTree` peaks at `959`, tail n=80/120/160/200 is
    `957/957/957/957`; final active pair-budget stays at `17`.
  - k=8: `strongMemoTree` peaks at `3425`; final active pair-budget stays at
    `65`.
  - k=10: `strongMemoTree` peaks at `5940`; final active pair-budget peaks at
    `101`.
  - k=12: `strongMemoTree` peaks at `9686`; final active pair-budget peaks at
    `145`.
- Design result: `strongMemoTree` and final-active metrics look like the
  viable proof objects. The cumulative active rows/pair-budget still grow with
  n on k=8/10/12, so they remain diagnostic only and must not be used as the
  final cubic proof object.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.
- No BR-039/BR-040 payout is claimed. The remaining hard theorem is still a
  final strong-tree bound or an equivalent indexed/quotiented representation
  bound.

## Cubic Route Checkpoint: Final Active Closure Contract (2026-06-03)

- Added proof-facing final-active closure definitions:
  - `GeneralRegexBound.thy:raw_final_active_suffix_closure`;
  - `FBound.thy:strong_deferred_final_active_suffix_closure`.
- Checked raw cardinality interfaces:
  - `card_raw_final_active_suffix_closure_member_pair_budget_bound`;
  - `card_raw_final_active_suffix_closure_member_pair_budget_card_bound`;
  - `card_raw_final_active_suffix_closure_le_rsize_plus_square_member`;
  - `raw_final_active_suffix_rows_member_size_le_rsize`;
  - `card_raw_final_active_suffix_closure_le_rsize_cubic`.
- Checked lifted strong-memo interfaces:
  - `strong_deferred_final_active_suffix_closure_member_pair_budget_bound`;
  - `strong_deferred_final_active_suffix_closure_member_pair_budget_card_bound`;
  - `strong_deferred_final_active_suffix_closure_le_final_asize_square_member`;
  - `strong_deferred_final_active_suffix_rows_member_size_le_final_asize`;
  - `strong_deferred_final_active_suffix_closure_le_final_asize_cubic`;
  - `strong_deferred_memo_tree_bounded_active_closure_contract`;
  - `strong_deferred_memo_tree_bounded_active_closure_cubic_contract`.
- Design result: final active rows are subterms of the final strong tree, so a
  future final strong-tree bound
  `asize (bders_simpStrong (intern r) s) <= T` now directly yields
  `card (strong_deferred_final_active_suffix_closure r s) <= T + T*T*T`.
  This removes the separate member-size obligation for this final-active
  closure. The remaining hard obligation is the final strong-tree bound itself,
  or an equivalent indexed representation bound with the same POSIX
  reconstruction contract.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.
- No BR-040 payout is claimed. The remaining hard theorem is still the final
  tree or indexed-universe bound itself.

## Cubic Route Checkpoint: Strong-Memo POSIX Contract (2026-06-03)

- Froze `bsimpCubic` as negative evidence after the plots; the current route is
  `bders_simpStrong` as the small nullable gate plus original-regex
  span/memo reconstruction for exact POSIX values.
- Added checked contract lemmas in `FBound.thy`:
  - `strong_deferred_memo_tree_POSIX_correctness`;
  - `strong_deferred_memo_tree_POSIX_flat`;
  - `strong_deferred_memo_tree_bounded_contract`.
- The contract theorem states that if the final strong tree has
  `asize (bders_simpStrong (intern r) s) <= T`, then the same strong-memo
  expression is exactly POSIX-correct, returns `None` exactly when no POSIX
  value exists, has final active rows bounded by `T`, has active pair-budget
  bounded by `T*T`, and keeps the existing span/split memo cubic budgets.
- Updated `agent_hunt_pipeline/scripts/ch7_derivative_size_compare.ps1` so its
  default graph compares only `strongTree` and `strongMemoTree`; `cubicTree`
  is still available as an explicit metric but is no longer the default route.
- Extra smoke:
  - k=5, lengths `4,8,12,16,20,30,40,60,80`: strong memo tree peak `958` on
    this run and exact POSIX values preserved;
  - k=8, lengths `4,8,16,32,48,64,80`: strong memo tree peak `3245` and exact
    POSIX values preserved;
  - deterministic random smoke: `1000` cases at depth `5`, input length `6`,
    seed `20260602`, exact POSIX values preserved.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.
- No BR-039/BR-040 payout is claimed. The remaining hard theorem is the bound
  for the final strong tree or an equivalent indexed final-active universe.

## Cubic Route Checkpoint: Final Active Pair-Budget Square Bound (2026-06-03)

- Added checked active-pair accounting:
  - `raw_shared_prune_active_suffix_pair_budget_eq_pairs`;
  - `raw_shared_prune_active_suffix_pairs_subset_Times`;
  - `raw_shared_prune_active_suffix_pair_budget_le_card_square`.
- Lifted the square bound to final strong trees:
  - `raw_final_active_suffix_pair_budget_le_rows_square`;
  - `raw_final_active_suffix_pair_budget_le_rsize_square`;
  - `strong_deferred_final_active_suffix_pair_budget_le_rows_square`;
  - `strong_deferred_final_active_suffix_pair_budget_le_final_asize_square`.
- Updated `strong_deferred_memo_tree_value_final_active_interface` so it now
  packages exact POSIX reconstruction, final active row count bounded by final
  `asize`, final active pair-budget bounded by final `asize^2`, and the
  existing span/split memo budgets.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.
- This is still infrastructure, not a BR-039/BR-040 payout. The hard remaining
  theorem is the regex-size bound for the final strong tree / final active
  rows themselves.

## Cubic Route Checkpoint: Final Active Strong Tree Bridge (2026-06-03)

- Retired `bsimpCubic` as the active candidate after the derivative-size
  graphs: it is useful negative evidence, not the route to optimize now.
- Added proof-facing final-active definitions for the memo-strong route:
  - `GeneralRegexBound.thy:raw_final_active_suffix_rows`;
  - `GeneralRegexBound.thy:raw_final_active_suffix_keys`;
  - `GeneralRegexBound.thy:raw_final_active_suffix_pair_budget`;
  - `FBound.thy:strong_deferred_final_raw`;
  - `FBound.thy:strong_deferred_final_active_suffix_rows`;
  - `FBound.thy:strong_deferred_final_active_suffix_keys`;
  - `FBound.thy:strong_deferred_final_active_suffix_pair_budget`.
- Checked bridge lemmas now state that final active rows are filtered
  subterms of the final strong tree, hence finite and bounded by the final
  `asize`; the theorem
  `strong_deferred_memo_tree_value_final_active_interface` packages exact
  POSIX reconstruction via `lexer`, the final-active row bound, and the
  existing span/split memo budgets.
- Extra smoke:
  - k=5, lengths `4..80`: strong memo tree peak `959`, under threshold `1000`;
  - k=8, lengths `4..80`: strong memo tree peak `3245`, under threshold `4000`;
  - deterministic random smoke: `1000` cases at depth `5`, input length `6`,
    seed `20260602`, exact POSIX values preserved.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.
- No BR-039/BR-040 payout is claimed. The next hard proof target is a cubic
  bound for final-active rows/pair-budget, or an indexed quotient explaining
  the prefix pool without counting every prefix row separately.

## Cubic Route Checkpoint: Final Active Metrics Added and Stressed (2026-06-03)

- Added Scala smoke metrics for the active suffix rows reachable in only the
  final strong derivative tree:
  - `strongMemoFinalActiveRows`;
  - `strongMemoFinalActiveKeys`;
  - `strongMemoFinalActiveMaxBucket`;
  - `strongMemoFinalActivePairBudget`.
- Regenerated `agent_hunt_pipeline/reports/ch7_deferred_memo_grid/` with
  these final-state metrics.
- The default deferred-memo report command now generates `k=5,8,10,12`,
  `n=0..200`, step `4`.
- Evidence from that grid:
  - `k=5`: final active rows max `5`, final active pair-budget max `17`;
  - `k=8`: final active rows max `9`, final active pair-budget max `65`;
  - `k=10`: final active rows max `11`, final active pair-budget max `101`;
  - `k=12`: final active rows max `13`, final active pair-budget max `145`;
  - all four keep final active keys at max `2`.
- In contrast, the cumulative prefix pool still grows on the same grid:
  `k=12` reaches `513` active rows and active pair-budget `262145` at
  `n=200`.
- Design consequence: the long-tail growth seen in
  `strongMemoActiveRows`/`strongMemoActivePairBudget` belongs to the cumulative
  prefix pool, not to the final derivative tree. The next proof target should
  model final-state active rows, or prove a periodic/indexed quotient for
  prefix accumulation, rather than bounding the raw prefix pool directly.

## Cubic Route Checkpoint: Active Closure Monotonicity (2026-06-03)

- Added monotonicity facts for the memo-strong active shared-prune universe:
  - `raw_shared_prune_active_suffix_keys_mono`;
  - `raw_shared_prune_active_suffix_bucket_mono`;
  - `raw_shared_prune_active_suffix_pairs_mono`;
  - `raw_shared_prune_active_suffix_closure_mono`;
  - `raw_shared_prune_active_suffix_pair_budget_mono`.
- This prepares the concrete root-owned active universe proof for iterative
  closure / least-fixed-point style constructions: if `U <= V`, active rows,
  active closure, and pair-budget all move in the expected direction.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Checkpoint: Deferred-Memo Long-Tail Grid to n=200 (2026-06-03)

- Regenerated `agent_hunt_pipeline/reports/ch7_deferred_memo_grid/` for
  `k=5,8,10,12`, `n=0..200`, step `4`.
- Positive evidence for the main route:
  - `strongMemoTree` stays thesis-like and bounded in this grid;
  - `k=5` maximum is `959`;
  - `k=8` maximum is `3425`;
  - `k=10` maximum is `5940`;
  - `k=12` maximum is `9686`.
- Negative evidence for the naive proof universe:
  - the cumulative/prefix active pool for `k=8` keeps growing through
    `n=200`;
  - `strongMemoActiveRows` reaches `312`;
  - `strongMemoActiveMaxBucket` reaches `311`;
  - `strongMemoActivePairBudget` reaches `96722`.
- Design consequence: memo strong tree is still the right recognition/value
  route, but a naive root-owned universe containing every prefix active row is
  not yet the final cubic proof object. The next proof attempt should use a
  quotient/periodic/indexed row universe, or a final-state/tree invariant that
  does not count all prefixes as distinct states.

## Cubic Route Checkpoint: Active Pair-Budget Bound (2026-06-03)

- Added proof-facing pair-budget accounting in `GeneralRegexBound.thy`:
  - `raw_shared_prune_active_suffix_pair_budget`;
  - `card_raw_shared_prune_active_suffix_pairs_le_pair_budget`;
  - `raw_shared_prune_active_suffix_pair_budget_bucket_bound`;
  - `card_raw_shared_prune_active_suffix_closure_pair_budget_bound`;
  - `card_raw_shared_prune_active_suffix_closure_member_pair_budget_bound`;
  - `card_raw_shared_prune_active_suffix_closure_member_pair_budget_card_bound`.
- This aligns the Isabelle closure accounting with the Scala
  `strongMemoActivePairBudget` metric.
- The active closure cardinality obligation can now be stated as:
  `card (raw_shared_prune_active_suffix_closure U) <= card U + P * M`,
  provided the active pair budget is at most `P` and every universe member has
  size at most `M`.
- Design consequence: the next concrete universe proof can target one
  aggregate pair-budget bound instead of only the coarser
  `S * K * K` active-key/max-bucket bound.
- The fallback theorem `raw_shared_prune_active_suffix_pair_budget_bucket_bound`
  keeps the old key/max-bucket estimate available, while
  `card_raw_shared_prune_active_suffix_closure_member_pair_budget_card_bound`
  gives the proof side the direct `C + P * M` universe-size shape.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Checkpoint: Active-Suffix Metrics Added (2026-06-03)

- Added Scala smoke instrumentation for the active-suffix proof contract:
  - `ActiveSuffixStats`;
  - `activeSuffixStatsForStrongPrefixes`;
  - `strongMemoActiveRows`;
  - `strongMemoActiveKeys`;
  - `strongMemoActiveMaxBucket`;
  - `strongMemoActivePairBudget`.
- Added `agent_hunt_pipeline/scripts/ch7_deferred_memo_grid.ps1`, a dedicated
  reproducibility wrapper for the deferred-memo Chapter 7 plots.
- Regenerated
  `agent_hunt_pipeline/reports/ch7_deferred_memo_grid/index.html` with active
  suffix metrics.
- Evidence from `k=5,8`, `n=0..80` step `2`:
  - active suffix keys stay at `2` for both `k=5` and `k=8` after the first
    nontrivial prefix;
  - `k=5` active max bucket reaches `84` and then plateaus by `n=62`;
  - `k=8` active max bucket reaches `176` at `n=80` and is still growing
    slowly;
  - pair budget is the expected sum-of-bucket-squares metric, reaching `7057`
    for `k=5,n=80` and `30977` for `k=8,n=80`.
- Design consequence: the next Isabelle universe proof should focus on active
  suffix-key count and active bucket-size bounds. The smoke data suggests the
  key count is tiny on the thesis family, while bucket size is the meaningful
  quantity to bound.

## Cubic Route Checkpoint: Active-Suffix Memo Contract (2026-06-03)

- Decision confirmed from the graphs: do not push the emitted-tree
  `bsimpCubic` route. The active theorem route is memo strong tree:
  `bsimpStrong` supplies the small nullable-recognition tree, and POSIX values
  are reconstructed from the original regex by the checked span/memo semantics.
- Added an active shared-prune closure in `GeneralRegexBound.thy`:
  - `raw_shared_prune_active_suffix_keys`;
  - `raw_shared_prune_active_suffix_bucket`;
  - `raw_shared_prune_active_suffix_pairs`;
  - `raw_shared_prune_active_suffix_closure`.
- The active closure only counts real shared-prune rows of shape
  `RSEQ (RALTS rows) k` with the same suffix `k`; it excludes the old broad
  `None` bucket for non-row terms.
- Proved checked bridges and accounting:
  - `raw_shared_prune_closedI_active_suffix_closure_subset`;
  - `card_raw_shared_prune_active_suffix_pairs_bucket_bound`;
  - `card_raw_shared_prune_active_suffix_closure_member_bucket_bound`.
- Added raw-row active interfaces:
  - `rsizes_rpders_strong1_rows_raw_norm_active_suffix_finite_universe_boundI`;
  - `rsizes_rpders_strong1_rows_raw_norm_active_suffix_cubic_universe_boundI`.
- Added `FBound.thy` forwarding interfaces:
  - `asizes_bpders_strong1_rows_raw_norm_active_suffix_cubic_universe_boundI`;
  - `strong_deferred_original_raw_row_norm_active_suffix_memo_cubic_interface`.
- Regenerated the Chapter 7 deferred-memo plots to length `80` for `k=5,8`:
  `agent_hunt_pipeline/reports/ch7_deferred_memo_grid/index.html`.
  Summary: `k=5` strong tree is `474,730,820,875,958,918,957,957` at
  `n=4,8,16,20,30,40,60,80`; `k=8` is
  `1164,1816,2691,2641,2747,2968,3120,3233`. Memo states/probes remain below
  their span/split bounds.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Checkpoint: Pair Output Bound Removed (2026-06-03)

- Added `GeneralRegexBound.thy:rsize_rsimpStrong_prune_pair_raw_le`.
- Added `GeneralRegexBound.thy:card_set_le_rsizes` as a reusable list-size
  counting lemma.
- Proved `card_raw_shared_prune_pair_outputs_le_later_size`: the output of
  one raw prune pair has cardinality at most the size of the later row.
- Proved
  `card_raw_shared_prune_same_suffix_closure_member_bucket_bound`, specializing
  the earlier bucket accounting theorem so the one-pair output bound is
  discharged by the ordinary universe member-size bound.
- The active closure cardinality obligation is now reduced to:
  - number of suffix keys;
  - maximum bucket size per suffix key;
  - ordinary member-size bound for the universe.
  There is no longer a separate same-suffix pair-output size parameter.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Checkpoint: Same-Suffix Bucket Accounting (2026-06-03)

- Added `GeneralRegexBound.thy:raw_shared_prune_same_suffix_pairs` and
  `GeneralRegexBound.thy:raw_shared_prune_suffix_bucket`.
- Proved the same-suffix pair domain decomposes by continuation/suffix bucket:
  `raw_shared_prune_same_suffix_pairs_bucket_union`.
- Added generic cardinality accounting lemmas:
  - `card_raw_shared_prune_same_suffix_pairs_le_sum_buckets`;
  - `card_raw_shared_prune_same_suffix_pairs_bucket_bound`;
  - `card_raw_shared_prune_same_suffix_closure_bound`;
  - `card_raw_shared_prune_same_suffix_closure_bucket_bound`.
- The active cubic accounting obligation is now factored into three concrete
  quantities:
  - number of suffix keys;
  - maximum bucket size per suffix key;
  - maximum output size of one same-suffix prune pair.
- This is not a final cubic theorem, but it is the proof shape needed for a
  concrete root-owned same-suffix/memo universe: once those three quantities
  are bounded polynomially, the existing
  `strong_deferred_original_raw_row_norm_same_suffix_memo_cubic_interface`
  can be instantiated.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Checkpoint: Same-Suffix Memo Interface (2026-06-03)

- Added proof-side bridge lemmas in `GeneralRegexBound.thy`:
  - `raw_shared_prune_same_suffix_closure_subsetI`;
  - `raw_shared_prune_closed_iff_same_suffix_closure_subset`.
- Under the existing singleton-flattening closure premise, the old abstract
  `raw_shared_prune_closed U` obligation is now equivalent to the concrete
  same-suffix closure obligation
  `raw_shared_prune_same_suffix_closure U \<subseteq> U`.
- Added same-suffix row-size interfaces:
  - `rsizes_rpders_strong1_rows_raw_norm_same_suffix_finite_universe_boundI`;
  - `rsizes_rpders_strong1_rows_raw_norm_same_suffix_cubic_universe_boundI`.
- Added corresponding `FBound.thy` interfaces:
  - `asizes_bpders_strong1_rows_raw_norm_same_suffix_cubic_universe_boundI`;
  - `strong_deferred_original_raw_row_norm_same_suffix_cubic_universe_interface`;
  - `strong_deferred_original_raw_row_norm_same_suffix_memo_cubic_interface`.
- This is the current preferred theorem shape for the memo strong tree route.
  A future concrete universe should prove finite/card/member-size/cubic
  accounting plus this same-suffix closure premise, then instantiate the memo
  interface directly.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Decision: Focus Memo Strong Tree (2026-06-03)

- Current decision: do not invest more proof effort in the emitted-tree
  `bsimpCubic` route. The derivative-size comparison graphs show that its
  ordinary tree output is not competitive with the thesis Chapter 7
  `bsimpStrong` baseline on the evil family.
- Main route from here:
  - keep the thesis-strength `bsimpStrong` tree as the recognition object;
  - reconstruct exact POSIX values through original-regex span/memo tables;
  - prove the cubic theorem through a memo/shared representation and a finite
    raw-row universe, not by forcing a new emitted regex tree to be both tiny
    and value-identical.
- Checked today: `GeneralRegexBound.thy` now includes
  `raw_shared_prune_suffix_key` and
  `raw_shared_prune_same_suffix_closure`. This narrows the previous global
  pair closure to same-continuation buckets, matching the shape of the
  same-suffix row-difference operation required by strong pruning.
- The same-suffix closure is finite for finite `U`, extensive, included in the
  broader pair closure, and strong enough to derive `raw_shared_prune_closed U`
  from the local closure premise
  `raw_shared_prune_same_suffix_closure U \<subseteq> U`.
- The old path9/carry9 atom-frontier counterexample witness is now checked to
  be included by the same-suffix closure:
  `raw_shared_prune_bad_result_in_path9_same_suffix_closure` and
  `raw_shared_prune_bad_result_in_carry9_same_suffix_closure`.
- This is still not the final cubic theorem. The next proof obligation is to
  instantiate this same-suffix/memo closure with a concrete root-owned universe
  and prove its cardinality and member-size accounting are cubic.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Checkpoint: Row-Difference Closure Operator (2026-06-03)

- Added `GeneralRegexBound.thy:raw_shared_prune_pair_outputs` and
  `GeneralRegexBound.thy:raw_shared_prune_pair_closure`.
- Checked basic closure facts:
  - `finite_raw_shared_prune_pair_closure`;
  - `raw_shared_prune_pair_closure_extensive`;
  - `raw_shared_prune_pair_outputs_subset_closureI`;
  - `raw_shared_prune_closedI_pair_closure_subset`;
  - `raw_shared_prune_pair_closure_subsetI`.
- Added witness facts
  `raw_shared_prune_bad_result_in_path9_pair_closure` and
  `raw_shared_prune_bad_result_in_carry9_pair_closure`: the old path9/carry9
  universes miss the row-difference result, but one explicit
  same-suffix-pair closure step adds it.
- This is not the final cubic universe. It is a proof-facing prototype of the
  row-difference operation that the final memo/frontier universe must account
  for without exploding into arbitrary emitted-tree subsets.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Checkpoint: Strong Memo POSIX Value Is Now Packaged (2026-06-03)

- Added `FBound.thy:strong_deferred_span_value_THE_lexer` and
  `FBound.thy:strong_deferred_memo_exact_value_budget`.
- This is the checked theorem shape for the current main route:
  `bders_simpStrong (intern r) s` is only the nullable recognition gate; when
  it accepts, the unique `strong_deferred_span_value` extracted from the
  original-regex span/memo table is exactly `lexer r s`.
- Added proof-facing negative guards in `GeneralRegexBound.thy`:
  `path9_atom_frontier_not_raw_shared_prune_closed` and
  `carry9_atom_frontier_not_raw_shared_prune_closed`.
- These guards show that the existing path9/carry9 atom-frontier universes are
  not closed under the raw strong shared-prune operation. The next universe
  must explicitly account for same-suffix ALT row differences; simply wiring
  `StrongDeferredMemo` into those old frontier universes is not enough.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.
- Extended smoke:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 -Route strong-memo -TimeoutSeconds 300 -RandomCases 1000 -RandomDepth 5 -RandomInputLength 6 -Seed 20260602 -Ch7K 5 -Ch7Lengths "4,8,12,16,20,24,28,32,40,48,64,80" -Ch7TreeThreshold 0`
  passed. For the Chapter 7 `k=5` family, strong tree sizes through `n=80`
  were `474,730,771,820,875,918,908,858,918,903,959,957`; deterministic
  random exact-POSIX smoke also passed on `1,000` cases.

## Cubic Route Pivot: StrongDeferredMemo Is The Main Candidate (2026-06-03)

- Promoted the `StrongDeferredMemo` route to the default Scala smoke route:
  - `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1` now defaults to
    `-Route strong-memo`;
  - `agent_hunt_pipeline/scripts/isabelle_ci.ps1` now defaults to
    `-ScalaSmokeRoute strong-memo`.
- Default `strong-memo` route:
  - skips the legacy emitted-tree `bsimpCubic` smoke;
  - checks exact POSIX value preservation for `StrongDeferredMemo`;
  - checks the known counterexample grid;
  - traces the Chapter 7 family with `strongMemoTree` plus memo-state and
    split-probe budgets.
- The old emitted-tree route remains available explicitly with
  `-Route legacy-cubic` or `-ScalaSmokeRoute legacy-cubic`, and both routes can
  be run together with `both`.
- Reason for the pivot:
  - The direct derivative-size graphs show `bsimpCubic` is worse than the
    thesis Chapter 7 baseline by ordinary tree size.
  - `StrongDeferredMemo` keeps the thesis-strength `bsimpStrong` tree while
    reconstructing exact POSIX values through original-regex span/memo tables.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 -TimeoutSeconds 240`
  passed the new default route on `84,300` exhaustive pairs, the known CE grid,
  and the Chapter 7 `k=5` memo trace.

## Cubic Route Checkpoint: Strong Memo Interface Has A Concrete Finite Fallback (2026-06-03)

- Added `GeneralRegexBound.thy:sizeNregex_member_size`,
  `GeneralRegexBound.thy:sizeNregex_member_legacy`, and
  `GeneralRegexBound.thy:rflts_sizeNregex_closed`.
- Added `FBound.thy:strong_deferred_original_sizeNregex_memo_cubic_interface`.
  This specializes the strong deferred memo interface to the concrete finite
  universe `sizeNregex N`, discharging the mechanical `finite`,
  `flat_closed`, `raw_shared_prune_closed`, and member-size assumptions.
- This is not the final cubic theorem and does not claim BR-039/BR-040. It is
  a checked fallback that makes the remaining hard obligation explicit:
  replace the huge `sizeNregex N` universe by a POSIX-safe Antimirov/frontier
  universe whose closure and `card * member-size` bound are genuinely cubic in
  the original regex size.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including default `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.

## Cubic Route Checkpoint: Row Universe And Memo Budget Are Packaged (2026-06-03)

- Added `FBound.thy:strong_deferred_original_raw_row_norm_closed_memo_cubic_interface`.
- This theorem combines the two proof-side halves that were previously
  separate:
  - raw strong-row cubic-universe assumptions imply both annotated row-size and
    raw row-size bounds for `bpders_strong1_rows (intern r) s`;
  - the row nullable gate is equivalent to the unique deferred POSIX value;
  - the unique deferred POSIX value is equivalent to
    `bnullable (bders_simpStrong (intern r) s)`;
  - the `bders_simpStrong` recognition state stays in the legacy fragment;
  - the deferred accept/value span memo table has the quadratic bound, and the
    split-probe table has the cubic bound;
  - the memo/split states remain over legacy subterms for a `legacy_rexp` root.
- This is still a conditional interface, not the final cubic theorem. The open
  obligation is still the real raw/shared universe instantiation: find the
  right finite `U`, prove its closure, and prove the `card U * member-size`
  cubic bound without over-quotienting POSIX values.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including Scala smoke, `Posix`, and `BackRefPilot`.

## Cubic Route Checkpoint: Deferred Memo Budget Is Checked (2026-06-03)

- Added `FBound.thy:strong_deferred_memo_budget` and
  `FBound.thy:strong_deferred_original_memo_budget`.
- The theorem packages the current strong-deferred route in the same shape as
  the Scala memo report:
  - unique deferred POSIX value exists exactly when
    `bnullable (bders_simpStrong (intern r) s)`;
  - `card (rexp_span_states r s) + card (rexp_span_posix_states r s)` is
    bounded by `2 * rxsize r * Suc (length s) * Suc (length s)`;
  - `card (rexp_span_all_split_probes r s)` is bounded by
    `rxsize r * Suc (length s) * Suc (length s) * Suc (length s)`.
- This connects the plotted `strongMemoStates` / `strongMemoSplitProbes`
  intuition to a checked Isabelle interface. It is still not the final cubic
  theorem: the remaining hard part is tying the thesis-strength recognition
  tree/share representation to this bounded reconstruction interface with the
  right POSIX value theorem.
- The `legacy_rexp` variant also records that span states, POSIX value states,
  and split-probe states stay inside legacy subterms when the original regex is
  in the non-backref fragment.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including Scala smoke, `Posix`, and `BackRefPilot`.

## Cubic Diagnostic: Direct k/n Derivative-Size Compare Report (2026-06-03)

- Added a visual side task that plots simplified derivative size as a function
  of both Chapter 7 parameters:
  - `agent_hunt_pipeline/scripts/ch7_derivative_size_compare.ps1`
  - `agent_hunt_pipeline/scripts/plot_ch7_derivative_compare.py`
  - output directory
    `agent_hunt_pipeline/reports/ch7_derivative_size_compare/`
- Default command:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\ch7_derivative_size_compare.ps1`
  generates a CSV, a summary table, and one SVG per `k` for `k=1..8`,
  `n=0..30`.
- The default metrics are overlaid on the same per-`k` plot:
  - `strongTree`: thesis Chapter 7 `bsimpStrong` tree baseline;
  - `strongMemoTree`: deferred-memo route using the same strong nullable gate;
  - `cubicTree`: current emitted `bsimpCubic` tree.
- Current readout from the summary table:
  - k=5, n=30: `strongTree=958`, `strongMemoTree=958`,
    `cubicTree=3245`; current `cubicTree` is `3.387x` the thesis baseline
    at n=30 and reaches max ratio `3.477x` on the grid.
  - k=8, n=30: `strongTree=2747`, `strongMemoTree=2747`,
    `cubicTree=7587`; current `cubicTree` is `2.762x` the thesis baseline
    at n=30.
- Design consequence:
  - This report is now the quickest human-facing answer to "are we at least
    as good as thesis Chapter 7?" The answer for ordinary emitted tree size is
    still no for current `bsimpCubic`; the deferred-memo route preserves the
    thesis-strength tree line because it keeps `bsimpStrong` as the nullable
    recognition state.
  - Future simplifier candidates should refresh this report before theorem
    work or bounty claims.

## Cubic Route Evidence: Thesis-Strong Tree With Deferred POSIX Memo (2026-06-03)

- Extended the Chapter 7 size-grid metrics with the existing
  strong-deferred POSIX reconstruction route:
  - `strongMemoTree`, `strongMemoDag`, `strongMemoShape`;
  - `strongMemoAcceptsStates`, `strongMemoValueStates`, `strongMemoStates`;
  - `strongMemoSplitProbes`, `strongMemoQueries`;
  - `strongMemoSpanBound`, `strongMemoSplitBound`.
- Added the report
  `agent_hunt_pipeline/reports/ch7_deferred_memo_grid/index.html`, generated
  with `k=1..8`, `n=0..30`.
- Key Chapter 7 data:
  - `strongMemoTree` matches the thesis-style `strongTree` line:
    - k=5: `n=30 -> 958`, max `960`;
    - k=8: `n=30 -> 2747`, max `2778`.
  - Memo overhead on this family is modest at `n=30`:
    - k=5: `strongMemoStates=1703`, `strongMemoSplitProbes=6011`;
    - k=8: `strongMemoStates=1703`, `strongMemoSplitProbes=6011`;
    - compared with bounds k=5:
      `strongMemoSpanBound=44206`, `strongMemoSplitBound=1370386`;
    - compared with bounds k=8:
      `strongMemoSpanBound=93217`, `strongMemoSplitBound=2889727`.
- Value evidence:
  - Ran `scala_cubic_smoke.ps1 -SkipLegacyCubic -CheckStrongDeferredMemo
    -Depth 2 -InputLength 3 -RandomCases 500 -RandomDepth 5
    -RandomInputLength 6 -StrongCubicTop 4`.
  - Passed exact POSIX value comparison on `84,300` exhaustive pairs, the
    known CE grid, and 500 deterministic random cases; memo universe bounds
    also passed.
- Design consequence:
  - The most promising tree-level path is currently not the emitted
    `cubicTree` simplifier. It is the thesis-strength `bsimpStrong` nullable
    gate paired with original-regex span/memo POSIX reconstruction.
  - This route keeps the ordinary tree-size behavior closest to thesis
    Chapter 7 while avoiding the known direct `bsimpStrong` value mismatch.
  - It remains a prototype route, not BR-039/BR-040 payout, until the
    reconstruction interface and cubic tree/share theorem are checked in
    Isabelle.

## Cubic Diagnostic: Chapter 7 Size-Grid Side Task (2026-06-03)

- Added a reusable plot pipeline:
  - `agent_hunt_pipeline/scripts/ch7_size_grid.ps1`
  - `agent_hunt_pipeline/scripts/plot_ch7_size_grid.py`
  - output directory `agent_hunt_pipeline/reports/ch7_size_grid/`
- The Scala side now has a CSV-only mode controlled by
  `POSIX_SMOKE_CH7_SIZE_CSV`, so plots use the same executable definitions as
  the smoke suite rather than a second reimplementation.
- Default command:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\ch7_size_grid.ps1`
  generates `k=1..8`, `n=0..30` charts for:
  - `strongTree`: thesis-style `bsimpStrong` ordinary tree size;
  - `cubicTree`: current `bsimpCubic` ordinary tree size under
    `unary-cover-no-reassoc`;
  - `sharedShapeStatePool`: current shared direct-DAG erased shape pool;
  - `langContPruneShapeStatePool`: current language-continuation diagnostic.
- Current Figure-7.6-style result, `k=1..8`, `n=0..30`:
  - `strongTree`, k=5: `n=30 -> 958`, max `960`;
  - `strongTree`, k=8: `n=30 -> 2747`, max `2778`;
  - `cubicTree`, k=5: `n=30 -> 3245`;
  - `cubicTree`, k=8: `n=30 -> 7587`;
  - `sharedShapeStatePool`, k=5/k=8 at `n=30`: `159` / `192`;
  - `langContPruneShapeStatePool`, k=5/k=8 at `n=30`: `52` / `76`.
- Design consequence:
  - By ordinary tree size, the current `bsimpCubic` attempt is not yet as
    strong as the thesis Chapter 7 `bsimpStrong` simplification.
  - The shared metrics are much smaller, but they are a different
    representation-level measure and cannot be presented as a tree-size
    reproduction without a reconstruction theorem.
  - The experimental `langAtomicContPruneShapeStatePool` was kept available
    as an optional metric, but it collapses the all-unary Chapter 7 family too
    aggressively and is currently only a warning example of over-quotienting.
  - No BR-039/BR-040 payout is claimed.

## Cubic Diagnostic: Metric-Only Language-Continuation Long Tail (2026-06-03)

- Added `-SharedPlateauMetricOnly` /
  `-ScalaSmokeSharedPlateauMetricOnly` for long-tail smoke. In this mode the
  plateau runner does not reconstruct the full final `arexp` tree and uses a
  bit-erased diagnostic `DagStore`, so shape/row-universe metrics are not
  killed by irrelevant POSIX bit payload growth. Normal value smoke still uses
  the ordinary bit-preserving store.
- Added `langContPruneShapeStatePool`, a Scala-only diagnostic metric that
  keys continuation coverage by approximate unary language patterns rather
  than by raw continuation syntax.
- Positive but limited evidence:
  - Chapter 7 `k=3`, step `4`, first non-increase at `n=12`, with
    `langContPruneShapeStatePool 16 -> 16`;
  - Chapter 7 `k=5`, step `4`, first non-increase at `n=64`, with
    `81 -> 81`;
  - Chapter 7 `k=8`, step `64`, metric-only first non-increase at `n=960`,
    with `885 -> 885`. The sampled prefix was
    `4,110,174,238,302,366,430,494,558,622,686,750,814,878,885,885`.
- Negative/insufficient evidence:
  - Chapter 7 `k=10`, step `128`, metric-only stayed strictly increasing
    through the last checked point before timeout:
    `n=1664`, `langContPruneShapeStatePool=1731`.
  - Therefore the current language-continuation diagnostic is not yet a
    general constant-universe argument. It is stronger than the earlier
    `shapeStatePool`, `unaryModShapeStatePool`, and
    `contPruneShapeStatePool` diagnostics on `k=8`, but the `k=10` tail says
    the quotient is still too fine or the construction is still not the right
    indexed family.
- Design consequence:
  - The proof-side target is not an ordinary tree simplifier yet. The current
    controlled object is an erased/shared row-universe diagnostic for
    `unary-cover-no-reassoc`; it is only controlled by
    `langContPruneShapeStatePool` after metric-only bit erasure.
  - A real BR-039 candidate still needs either a periodic/indexed
    continuation family with a checked reconstruction theorem, or a stronger
    POSIX-safe simplifier that passes the same long-tail tests without relying
    on diagnostic-only erasure.
  - No BR-039/BR-040 payout is claimed.

## Cubic Candidate Prototype: Long-Tail Plateau Discipline (2026-06-03)

- Tightened the Scala smoke harness so shape-pool metrics use hash-consed
  structural shape IDs instead of recursively materialized string keys. The
  old string representation is now only for small witness display. This keeps
  long-tail tests from failing because the diagnostic key format itself grows
  too large.
- Added `-SharedPlateauProgress` /
  `-ScalaSmokeSharedPlateauProgress`, which prints every sampled long-tail
  point immediately. This makes OOM/timeout runs useful: the last printed
  `long-tail-progress` line is the checked empirical boundary.
- Added the experimental `unary-cover-no-reassoc` smoke mode. It keeps
  no-reassociation output syntax but tries a cheap unary-language coverage
  prune: if an earlier row with the same continuation contains `a*`, later
  all-`a` rows with that continuation are treated as covered. This is only
  Scala smoke and is not a checked Isabelle simplifier.
- Positive but narrow evidence:
  - exact POSIX value smoke passed exhaustive depth `2`/input `3` plus
    deterministic random `1,000` cases at depth `5`/input `6`;
  - Chapter 7 `k=5`, metric `shapeStatePool`, step `4`, with
    `-SharedPlateauRequire`, first stops increasing at `n=124`, with
    `shapeStatePool 337 -> 337`.
- Negative long-tail evidence:
  - Chapter 7 `k=8`, metric `shapeStatePool`, step `4`, stayed strictly
    increasing through `n=500`, ending at `2072`;
  - with progress sampling at step `16`, it was still strictly increasing at
    `n=624`, with `shapeStatePool=2568`, `statePool=201915`, and
    `pool=795128`, then ran out of heap inside `eq1Id/distinctWithIds`.
- Design consequence:
  - `unary-cover-no-reassoc` is a useful counterexample-driven diagnostic, but
    it is not a viable constant-universe candidate. It explains the thesis
    `k=5` plot but fails the larger `k=8` long tail.
  - Future candidates must be tested until the selected long-tail metric first
    fails to strictly increase, or else must report an explicit high-water
    boundary and failure mode. Short `0..30` traces cannot support a constant
    or plateau claim.
  - No BR-039/BR-040 payout is claimed.

## Cubic Diagnostic: Unary Modulo And Shallow Prune Metrics (2026-06-03)

- Added two Scala-only diagnostic metrics to
  `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`:
  - `unaryModShapeStatePool`, which recognizes `a^m . (a^p)*` shapes modulo
    the period `p` for counting purposes;
  - `unaryPruneShapeStatePool`, which traverses a shape universe where simple
    later unary ALT children are skipped when an earlier unary child covers
    their language.
- Results:
  - On Chapter 7 `k=5`, `unaryModShapeStatePool` still first stops increasing
    at `n=124`, with `327 -> 327`.
  - On Chapter 7 `k=8`, `unaryModShapeStatePool` remains strictly increasing
    through `n=624`, ending at `2552`; this barely improves on the ordinary
    `shapeStatePool=2568` at the same boundary.
  - The first `unaryPruneShapeStatePool` traversal is also no better on
    `k=8`: through `n=160` it exactly matches the unary-modulo metric, ending
    at `696`.
- Design consequence:
  - The large `k=8` tail is not explained by missing `m mod p` normalization
    alone.
  - It is also not removed by pruning simple unary ALT children locally.
    The next serious route must reason about row-set/continuation coverage,
    e.g. a prior `(A . c)` branch covering a later `(B . c)` branch when the
    row language of `B` is included in the POSIX-prior row language of `A`.
  - These metrics are counterexample diagnostics only; no bounty is claimed.

## Cubic Diagnostic: Continuation-Aware Row-Set Coverage (2026-06-03)

- Added the Scala-only diagnostic metric `contPruneShapeStatePool`.
  It looks through left-associated sequence branches such as
  `((rows . k1) . k2)`, extracts the unary row block `rows`, and treats the
  branch as having continuation `(k1 . k2)`. Within an ALT, later branches
  with the same continuation are skipped when their unary row-set language is
  covered by the earlier POSIX-prior row-set.
- Positive evidence:
  - On Chapter 7 `k=3`, `contPruneShapeStatePool` first stops increasing at
    `n=12`, with `36 -> 36`.
  - On Chapter 7 `k=5`, it first stops increasing at `n=68`, with
    `269 -> 269`, earlier and smaller than the unary-modulo `n=124` /
    `327 -> 327` result.
- Negative evidence:
  - On Chapter 7 `k=8`, it does not improve the long tail. With step `16`, it
    matches `unaryModShapeStatePool` and remains strictly increasing through
    `n=624`, ending at `2552`; after that the current direct-DAG simplifier
    ran out of heap in the existing `seqCoverRowsId`/prune path.
- Design consequence:
  - Simple same-continuation row-set coverage is real but still too shallow.
    It handles smaller evil roots but not the `k=8` tail.
  - The next candidate should either find a better continuation quotient, or
    move from syntax-shaped continuations to an indexed linear-form/row-family
    representation where the repeated Chapter 7 base continuation is recognized
    independently of the surrounding left-associated syntax.
  - This is still diagnostic evidence only; no BR-039/BR-040 payout is claimed.

## Cubic Candidate Prototype: Direct-DAG Shared Smoke (2026-06-03)

- Added an optional direct-DAG path to `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`.
  Unlike the earlier shared diagnostic, this path performs derivative and
  simplification operations directly on hash-consed node IDs instead of
  expanding the current DAG root back to a tree before every derivative step.
- Added `statePool` reporting to shared traces. This is the union of nodes
  reachable from every prefix derivative root, and is distinct from the raw
  total node pool, which also includes dead temporary nodes produced during a
  direct derivative/simplification step.
- Added `shapeStatePool`, the union of erased/shape keys reachable from every
  prefix derivative root. This is closer to the current proof-side
  `rrexp`/`rsimpStrong_raw` universe than exact annotated `statePool`, because
  exact nodes distinguish bit annotations.
- Added wrapper flags:
  - `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1 -SharedDirectDag`;
  - `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1 -SharedDirectCompareTree`;
  - `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1 -SharedStatePoolCubicFactor`;
  - `agent_hunt_pipeline/scripts/isabelle_ci.ps1 -ScalaSmokeSharedDirectDag`;
  - `agent_hunt_pipeline/scripts/isabelle_ci.ps1 -ScalaSmokeSharedStatePoolCubicFactor`.
- Smoke evidence:
  - Direct `no-reassoc`: exhaustive depth `2`, input length `3`, and random
    `1,000` cases at depth `5`/input `6` preserve exact POSIX values.
  - Direct `expanded-keyed-no-reassoc`: same value smoke also passes.
  - With `-SharedDirectCompareTree`, both `no-reassoc` and
    `expanded-keyed-no-reassoc` pass the same exhaustive/random grid while
    checking every prefix derivative root for exact syntactic equality against
    the existing tree-step reference algorithm.
  - Chapter 7 `k=5`, lengths `0,4,8,12,16,20,24,30` under direct
    `expanded-keyed-no-reassoc`:
    final DAG `18,57,97,130,161,197,227,276`;
    shape DAG `18,43,63,76,87,103,113,132`;
    prefix `statePool` `18,90,187,310,445,598,767,1042`;
    raw total pool `18,242,599,1055,1569,2171,2859,4005`.
    The new `statePool <= 1.0 * rsize(r)^3` gate passes this grid; the worst
    reported ratio is `1042 / 46^3 = 0.010705` at `n=30`.
  - Long-tail Chapter 7 `k=5`, step `4`, metric `shapeStatePool`, under
    direct `expanded-keyed-no-reassoc`: first non-increase appears at `n=124`,
    with `shapeStatePool 523 -> 523` from `n=120` to `n=124`. Exact
    `statePool` still grows there (`7729 -> 8046`), so exact annotated nodes
    are not the right proof-side constant-state measure.
  - Chapter 7 `k=8`, lengths `0,4,8,16,32` under direct
    `expanded-keyed-no-reassoc`:
    final DAG `27,78,130,232,408`;
    shape DAG `27,61,87,125,173`;
    prefix `statePool` `27,120,229,550,1400`;
    raw total pool `27,350,752,1957,5292`.
  - Long-tail Chapter 7 `k=8`, step `4`, metric `shapeStatePool`, under
    direct `expanded-keyed-no-reassoc`: no non-increase by `n=500`.
    The last logged point is `shapeStatePool=3257`, exact `statePool=139153`,
    final DAG `5555`, and shape DAG `1576`. This is negative evidence against
    treating the current direct-DAG/hash-consed reference simplifier as already
    having a fixed finite proof universe for larger evil-family roots.
- Design result:
  - The direct-DAG prototype preserves the value-safe no-reassociation output
    story while moving the smoke harness closer to a real shared-row algorithm.
    The exact tree-step comparison means it is currently a hash-consed
    execution form of the reference simplifier, not a semantically different
    simplifier.
  - The proof-facing universe should target prefix reachable states/rows, not
    the naive total node pool. Dead temporary nodes need either garbage-free
    construction, GC, or a separate implementation accounting theorem.
  - The `statePool`/`shapeStatePool` cubic and plateau gates are
    smoke/prototype guards. They can catch regressions and report high-ratio
    witnesses, but they are not the final root-owned finite-universe theorem.
    The `k=8` long-tail failure means future work still needs a stronger
    quotient, pruning, or row-universe construction.
  - This is smoke evidence and tooling only; no BR-039/BR-040 payout is
    claimed.

## Cubic Candidate Prototype: Concrete Raw Shared-Prune Sanity Universe (2026-06-03)

- Added checked raw shared-prune size/legacy helpers in `GeneralRegexBound.thy`:
  - `rsize_rsimp_ALTs_rprune_eq_against_le`;
  - `rsize_rsimpStrong_raw_shared_prune_result_le`;
  - `legacy_rsimpStrong_raw_shared_prune_result`.
- Added checked theorem `raw_shared_prune_closed_sizeNregex`.
- Design result:
  - The raw shared-prune step is now known to stay inside every legacy
    `sizeNregex N` universe when the later shared row is already inside that
    same universe.
  - This does not prove the desired cubic bound, because `sizeNregex N` is a
    coarse finite-by-size universe rather than a root-owned cubic-cardinality
    universe.
  - It does isolate the next hard problem: construct a much smaller raw/shared
    row universe that inherits the same size/legacy closure pattern while
    satisfying cubic cardinality and member-size bounds.
- Build: focused `Posix` and `BackRefPilot` builds passed after this
  checkpoint.

## Cubic Candidate Prototype: Raw Shared-Prune Closure Predicate (2026-06-03)

- Added `raw_shared_prune_closed` in `GeneralRegexBound.thy`.
- Added checked closure chain using that predicate:
  - `rsimpStrong_prune_pair_raw_closed_subsetI`;
  - `rsimpStrong_prune_rows_raw_closed_subsetI`;
  - `rpder_strong_rows_raw_norm_closed_subsetI`;
  - `rpders_strong_rows_raw_norm_closed_subsetI`;
  - `rsizes_rpders_strong1_rows_raw_norm_closed_cubic_universe_boundI`.
- Added checked annotated/original transfer in `FBound.thy`:
  - `asizes_bpders_strong1_rows_raw_norm_closed_cubic_universe_boundI`;
  - `strong_deferred_original_raw_row_norm_closed_cubic_universe_interface`.
- Design result:
  - The shared-suffix obligation is now weaker and more concrete: instead of
    requiring closure for arbitrary `lrs`, a universe must be closed under raw
    shared pruning only when both
    `RSEQ (RALTS lrs) k` and `RSEQ (RALTS rrs) k` are already represented in
    the universe.
  - This better matches the operational invariant of `rsimpStrong_prune_rows_raw`,
    where earlier rows are accumulated from already-produced rows rather than
    invented from nowhere.
  - The next concrete proof target is to define a finite raw/shared row
    universe satisfying `raw_shared_prune_closed`, `flat_closed`, and the
    `rsimpStrong_raw` norm closure, with cubic card/member bounds.
  - No BR-039 or BR-040 payout is claimed.
- Build: focused `Posix` and `BackRefPilot` builds passed after this
  checkpoint.

## Cubic Candidate Prototype: Raw Strong One-Step Closure Split (2026-06-03)

- Added checked raw one-step subset decomposition in `GeneralRegexBound.thy`:
  - `rsimpStrong_prune_pair_raw_shared_subsetI`;
  - `rsimpStrong_prune_rows_raw_later_shared_subsetI`;
  - `rflts_rpder_strong_list_raw_subsetI`;
  - `rpder_strong_rows_raw_norm_later_shared_subsetI`;
  - `rpders_strong_rows_raw_norm_later_shared_subsetI`;
  - `rsizes_rpders_strong1_rows_raw_norm_later_shared_cubic_universe_boundI`.
- Added checked annotated/original transfer in `FBound.thy`:
  - `asizes_bpders_strong1_rows_raw_norm_later_shared_cubic_universe_boundI`;
  - `strong_deferred_original_raw_row_norm_later_shared_cubic_universe_interface`.
- Design result:
  - The raw one-step closure obligation is no longer a monolithic premise
    over `rpder_strong_rows_raw`.
  - Future universe construction can prove three local obligations:
    `flat_closed` for row flattening, `norm` for
    `rsimpStrong_raw` over `rpder_norm_list`, and `shared` for the raw
    shared-suffix prune result
    `rsimp7_SEQ_atom (rsimp_ALTs (rprune_eq_against lrs rrs)) k`.
  - These local obligations still have to be instantiated by a concrete
    finite raw/shared universe with cubic card/member bounds. No BR-039 or
    BR-040 payout is claimed.
- Build: focused `Posix` and `BackRefPilot` builds passed after this
  checkpoint.

## Cubic Candidate Prototype: Raw Strong Row Universe Interface (2026-06-03)

- Added checked raw-row finite-universe bookkeeping in `GeneralRegexBound.thy`:
  - `distinct_rpder_strong_rows_raw`;
  - `distinct_rpders_strong_rows_raw`;
  - `rpders_strong_rows_raw_subsetI`;
  - `length_rpders_strong1_rows_raw_finite_universe_boundI`;
  - `rsizes_rpders_strong1_rows_raw_finite_universe_boundI`;
  - `rsizes_rpders_strong1_rows_raw_cubic_universe_boundI`.
- Added checked annotated transfer interfaces in `FBound.thy`:
  - `asizes_bpders_strong1_rows_raw_cubic_universe_boundI`;
  - `strong_deferred_original_raw_row_cubic_universe_interface`.
- Design result:
  - Future cubic work can now state the hard closure obligation purely on the
    raw erased skeleton:
    `set xs \<subseteq> U \<Longrightarrow> set (rpder_strong_rows_raw c xs) \<subseteq> U`.
  - The checked bridge then transfers the resulting raw `rsizes` bound back to
    the annotated `bpders_strong1_rows (intern r) s` size bound, preserves the
    exact `map rerase` equality, and keeps the nullable-row iff unique deferred
    POSIX value gate.
  - This narrows the next missing theorem to constructing a finite raw/shared
    row universe with cubic card/member bounds. It does not itself prove that
    universe exists and does not pay BR-039 or BR-040.
- Build: focused `Posix` and `BackRefPilot` builds passed after this
  checkpoint.

## Cubic Candidate Prototype: Raw Strong Skeleton Bridge (2026-06-03)

- Added a raw skeleton mirror of the annotated strong simplifier in
  `GeneralRegexBound.thy`:
  - `rsimpStrong_prune_pair_raw`;
  - `rsimpStrong_prune_rows_raw`;
  - `rsimpStrong_ALTs_raw`;
  - `rsimpStrong_raw`;
  - `rpder_strong_list_raw`, `rpder_strong_rows_raw`, and the iterated row
    entry points.
- This raw layer deliberately mirrors the annotated delayed-normalization
  shape instead of the earlier normalized `rsimpStrong_prune_pair`. It is a
  proof-facing carrier for row-universe/reconstruction work, not a new
  production simplifier.
- Checked language preservation:
  - `RL_rsimpStrong_raw`;
  - row-pruning preservation lemmas for the raw strong row layer.
- Added exact erasure bridges in `FBound.thy`:
  - `rerase_bsimpStrong_raw`;
  - `map_rerase_bpder_strong_list_raw`;
  - `map_rerase_bpder_strong_rows_raw`;
  - `map_rerase_bpders_strong1_rows_raw`.
- Design result:
  - The previous exact-erasure shortcut was false for the normalized skeleton,
    but exact erasure is recoverable by making the skeleton carry the same
    delayed row-normalization shape as the annotated algorithm.
  - Future cubic/shared-row proofs can target the raw erased row universe, then
    connect back to annotated `bsimpStrong` through these checked bridges.
  - This is infrastructure only. It does not prove a cubic theorem and does
    not pay BR-039 or BR-040.
- Build: focused `Posix` and `BackRefPilot` builds passed after this
  checkpoint.

## Cubic Candidate Prototype: Strong Prune Exact-Erasure CE (2026-06-03)

- Added checked counterexample
  `rerase_bsimpStrong_prune_pair_not_exact` in `FBound.thy`.
- The counterexample rules out the tempting bridge
  `rerase (bsimpStrong_prune_pair earlier later) =
   rsimpStrong_prune_pair (rerase earlier) (rerase later)`.
- Reason:
  - the annotated `bsimpStrong_prune_pair` preserves bit/value-carrying syntax
    and leaves some list normalization to the outer `distinctWith/flts` layer;
  - the erased skeleton `rsimpStrong_prune_pair` normalizes the pruned
    alternative row internally with `rdistinct/rflts`.
  A later row with duplicate residual alternatives therefore erases to a
  different syntax shape, even though the language/coverage story remains the
  intended one.
- Design result:
  - Do not try to transfer cubic row bounds by a naive exact syntactic
    `map rerase` commutation theorem for `bsimpStrong_prune_pair` or
    `bpder_strong_rows`.
  - Future progress should use the existing language/coverage subset
    interfaces, or define an explicit normalized/shared-row representation
    with a checked reconstruction theorem.
- Build: focused `Posix` and `BackRefPilot` builds passed after this
  checkpoint.

## Cubic Candidate Prototype: Original Row Cubic Interface (2026-06-03)

- Added checked theorem
  `strong_deferred_original_row_cubic_universe_interface` in `FBound.thy`.
- The theorem packages the current proof-facing shape of the strong-row route:
  under `legacy_rexp r`, if a finite erased row universe contains
  `rerase (intern r)`, is closed by one `bpder_strong_rows` step, has a
  cardinality bound, and has a per-member size bound, then
  `bpders_strong1_rows (intern r) s` is bounded by the advertised product
  budget.
- The same interface keeps the semantic gate attached to exact POSIX value
  reconstruction:
  nullable strong row existence is equivalent to unique
  `strong_deferred_span_value r s`.
- It also exposes the size alignment
  `rsize (rerase (intern r)) = rxsize r` and
  `asize (intern r) = rxsize r`, so future regex-size cubic statements can
  start from the original `rexp`.
- This remains infrastructure. The missing hard theorem is still the actual
  finite row universe/closure construction with cubic card/member bounds.
  No BR-039/BR-040 bounty is claimed.
- Build: focused `Posix` and `BackRefPilot` builds passed after this
  checkpoint.

## Cubic Candidate Prototype: Strong Row Gate Bridge (2026-06-03)

- Added checked row-nullability bridge lemmas in `FBound.thy`:
  - `bnullable_iff_RL_rerase_empty`;
  - `bex_bnullable_iff_RLS_map_rerase_empty`;
  - `bpders_strong1_rows_nullable_iff_bders_simpStrong`;
  - `bpders_strong1_rows_intern_nullable_iff_bders_simpStrong`;
  - `strong_deferred_original_row_gate`.
- Design result:
  - The Antimirov-style strong row pipeline
    `bpders_strong1_rows (intern r) s` is now connected to the current
    strong-deferred acceptance/value story: under `legacy_rexp r`, it has a
    nullable row exactly when the deferred original-root POSIX value exists
    uniquely.
  - This narrows the remaining cubic proof obligation: future row-universe
    bounds can reason about the row set, while exact POSIX values still come
    from the original span reconstruction table.
- Added size bridge lemmas:
  - `asize_intern`;
  - `rsize_rerase_intern`.
  These state that interning an original `rexp` preserves the original
  `rxsize` exactly at both annotated and erased skeleton levels.
- This is still proof infrastructure. It does not prove a regex-size cubic
  bound and does not pay BR-039/BR-040.
- Build: focused `Posix` and `BackRefPilot` builds passed after this checkpoint.

## Cubic Candidate Prototype: Original Span Fragment Closure (2026-06-03)

- Added checked fragment-closure lemmas in `FBound.thy`:
  - `legacy_rexp_subterms`;
  - `legacy_rexp_span_states`;
  - `legacy_rexp_span_split_probes`;
  - `legacy_rexp_span_all_split_probes`;
  - `legacy_rexp_span_posix`;
  - `legacy_rexp_span_posix_states`.
- Strengthened `strong_deferred_original_legacy_budget`: under
  `legacy_rexp r`, every regex state appearing in the deferred POSIX value
  table and split-probe table is itself `legacy_rexp`.
- Design result:
  - The strong-deferred route now has a checked pure-non-backref state-space
    invariant for the reconstruction tables, not only for the initial regex
    and final strong derivative gate.
  - This is useful for future regex-size cubic statements because the span
    universe cannot silently introduce `BACKREF4`, `HALF`, or `RESIDUE` states
    while reconstructing exact POSIX values.
  - This remains proof infrastructure, not a final cubic theorem or payout.
- Proof-performance note:
  - The first version used a broad constructor-case simplification and caused
    a 300s CI timeout in the impossible `BACKREF4` branch. The checked proof
    now splits constructors and uses only the relevant contradiction premise.
- Build: focused `Posix` and `BackRefPilot` builds passed after this checkpoint.

## Cubic Candidate Prototype: Original Fragment Bridge (2026-06-03)

- Added `legacy_rexp` in `RegLangs.thy`, a direct predicate on the original
  `rexp` datatype that accepts the legacy/non-backref constructors and rejects
  `BACKREF4`, `HALF`, and `RESIDUE`.
- Added proof-facing bridge lemmas in `FBound.thy`:
  - `legacy_rerase_intern`;
  - `legacy_rexp_rerase_bders_simpStrong_intern`;
  - `strong_deferred_original_legacy_budget`.
- Design result:
  - The current strong-deferred route can now start from the user-facing
    original regex premise `legacy_rexp r`, rather than only from the erased
    bounds skeleton premise `legacy_rrexp (rerase a)`.
  - `bders_simpStrong (intern r) s` is checked to remain in the
    legacy/non-backref bounds fragment under that premise, while the existing
    deferred reconstruction budget facts remain available at the same entry
    point.
  - This is infrastructure for the cubic route, not a POSIX/bitcode
    preservation theorem and not a bounty payout.
- Build: focused `Posix` and `BackRefPilot` builds passed after this checkpoint.

## Cubic Candidate Prototype: Checked Strong-Deferred Reconstruction Package (2026-06-03)

- Added proof-facing `FBound.thy` lemmas around the current positive route:
  - `strong_deferred_span_value_nullable`;
  - `strong_deferred_span_value_root_entry`;
  - `finite_strong_deferred_span_values`;
  - `card_strong_deferred_span_values_le_1`;
  - `strong_deferred_span_value_ex1_iff`;
  - `strong_deferred_reconstruction_budget`.
- The package states the intended division of labor in checked Isabelle form:
  `bders_simpStrong (intern r) s` is the nullable acceptance gate, while the
  exact POSIX value lives as the unique root value in `rexp_span_posix r s`.
  The value table and split-probe table keep their existing quadratic/cubic in
  input-length table bounds:
  `rxsize r * (|s|+1)^2` and `rxsize r * (|s|+1)^3`.
- This is not the final regex-size cubic theorem for the derivative state.
  It is a reusable proof interface for the current route: small strong tree
  for recognition, bounded original-root span table for exact POSIX value
  reconstruction.
- Focused `Posix` and `BackRefPilot` builds passed after this checkpoint.

## Cubic Candidate Prototype: Distinct-Regex Frontier Reporting (2026-06-03)

- Extended `-StrongCubicTop` reporting to print both:
  - the raw top-N observed size-pressure samples; and
  - a distinct-regex top-N frontier that keeps only the strongest input for
    each regex structure.
- This matters because exhaustive and known-CE grids often produce several
  high-ratio inputs for the same regex. Without structural deduplication, the
  report can hide the next useful C/D/E/F counterexample family behind repeated
  input variants.
- Sanity check: with top `4`, depth `2`/input `3`, the raw frontier was filled
  by repeated `NTIMES(STAR(CH _),2)` inputs, while the distinct frontier also
  exposed `STAR(NTIMES(CH _),2)`.
- This is still diagnostic only. It improves the counterexample search loop;
  it does not prove a cubic theorem and does not pay BR-039/BR-040.

## Cubic Candidate Prototype: Top-N Strong Cubic Frontier (2026-06-03)

- Added `-StrongCubicTop` / `-ScalaSmokeStrongCubicTop`, defaulting to `1`.
- The `StrongDeferredMemo` smoke grids can now report the top-N observed
  `asize(final bsimpStrong tree) / rsize(regex)^3` pressure points instead of
  only the single worst case. This keeps the CEGAR loop from overfitting to
  one accidental tiny witness.
- The report is intentionally diagnostic-only: ordinary budget checks still
  run on every generated regex/input pair, while the top-N list is only for
  steering the next counterexample analysis.
- Sanity checks:
  - depth `2`, input `3`, random `20` cases, top `3` passed and reported
    multiple frontier witnesses;
  - Chapter 7 `k=5`, lengths `0,4,8,12,16,20,24,30`, top `3`, tree
    threshold `1000`, cubic factor `1.0` passed and kept the expected
    `n=30` strong tree size `958`.

## Cubic Candidate Prototype: Configurable Strong Cubic Frontier Size (2026-06-03)

- Added `-StrongCubicMinRegexSize` /
  `-ScalaSmokeStrongCubicMinRegexSize`.
- The parameter controls which regexes are reported in worst-frontier
  summaries and which regexes are eligible for `-FindStrongCubicBudgetCE`.
  Budget checks in ordinary smoke still cover every regex.
- The CE finder now also preserves this minimum during greedy regex shrinking,
  so a search for larger structural witnesses does not collapse back to
  `ZERO`/`ONE`-scale examples.
- Sanity checks:
  - with factor `0.03`, min rsize `5`, seed `20260602`, the finder reports a
    shrunk rsize-6 witness
    `STAR(ALT(SEQ(CH b, CH b), CH b))` on input `b`;
  - with the same factor and min rsize `10`, no witness is found in `1,000`
    random depth-6/input-7 cases.
- This makes the CE loop more useful for asymptotic research: small-regex
  constant artifacts can be filtered out without weakening the real budget
  checks.

## Cubic Candidate Prototype: Strong Cubic Budget CE Finder (2026-06-03)

- Added optional `-FindStrongCubicBudgetCE` /
  `-ScalaSmokeFindStrongCubicBudgetCE`.
- Given a positive `-StrongCubicFactor`, the finder searches random
  `(regex, input)` pairs for
  `asize(final bsimpStrong tree) > factor * rsize(regex)^3`.
- When a hit is found, it prints the witness before and after greedy shrinking.
  The shrinker uses a visited `(regex,input)` set, because same-size rewrites
  such as alternation child replacement can otherwise cycle.
- Sanity check: with deliberately tight factor `0.03`, seed `20260602`, the
  finder reports a witness at random case `13` and shrinks it to a three-node
  alternation. This is expected: too-small constants can be refuted by small
  regexes before the asymptotic frontier becomes interesting.
- This is a CE-mining tool, not a proof claim or a default CI gate.

## Cubic Candidate Prototype: Strong Cubic Worst-Witness Reporting (2026-06-03)

- Added worst-witness summaries to the `StrongDeferredMemo` smoke grids.
  Budget checks still cover all regexes, but the summary ignores tiny
  `rsize < 5` observations so `ZERO`/`ONE` do not dominate the report.
- Each exhaustive, known-CE, random, and Chapter 7 trace now reports the
  largest observed ratio `asize(final bsimpStrong tree) / rsize(regex)^3`.
- Representative checked observations with factor `1.0`:
  - exhaustive depth `2` / input `3`: worst ratio `0.112`, witness
    `NTIMES(STAR(CH a), 2)` on `aa`, tree `14`, rsize `5`;
  - known CE grid: worst ratio `0.029`, witness
    `SEQ(STAR(ALT(STAR b, SEQ b a)), STAR a)` on `bb`, tree `29`, rsize
    `10`;
  - random depth `6` / input `7` / seed `20260602`: worst ratio `0.040`,
    witness `ALT(SEQ(ZERO, ONE), ZERO)` on empty input in the `1,000`-case
    run;
  - Chapter 7 k=5 length 30: ratio `0.009842`;
  - Chapter 7 k=8 length 32: ratio `0.003154`.
- This makes the counterexample loop more actionable: the smoke no longer only
  says pass/fail, it identifies the current size-pressure frontier to shrink or
  generalize if the cubic budget is tightened later.

## Cubic Candidate Prototype: Global Strong-Deferred Cubic Smoke (2026-06-03)

- Added `-StrongCubicFactor` / `-ScalaSmokeStrongCubicFactor` for the
  `StrongDeferredMemo` exhaustive, known-CE, and random smoke grids.
- When enabled, every checked `(regex, input)` pair must satisfy
  `asize(final bsimpStrong tree) <= factor * rsize(regex)^3`, in addition to
  exact POSIX value equality and the memo span/split universe bounds.
- This is deliberately CE-oriented: if an ordinary generated regex, rather
  than just the Chapter 7 family, violates the cubic-shaped budget, the smoke
  now reports the concrete regex/input witness.
- Checked smoke:
  - depth `2`, input length `3`: `84,300` exhaustive pairs pass with factor
    `1.0`;
  - known CE grid: `15` cases pass with factor `1.0`;
  - deterministic random depth `6`, input length `7`, seed `20260602`:
    `1,000` cases pass with factor `1.0`;
  - the Chapter 7 `k=5` and `k=8` traces also pass with
    `-Ch7StrongCubicFactor 1.0`.
- This still does not prove the cubic theorem. It upgrades the smoke gate so
  the counterexample-driven loop can reject a candidate for size-budget failure
  on general generated regexes, not only on hand-picked evil families.

## Cubic Candidate Prototype: Regex-Size Cubic Budget Smoke (2026-06-03)

- Added an optional `StrongDeferredMemo` Chapter 7 budget
  `-Ch7StrongCubicFactor` / `-ScalaSmokeCh7StrongCubicFactor`.
- When enabled, the traced `bsimpStrong` recognition tree must satisfy
  `asize <= factor * rsize(root)^3`, in addition to the existing fixed
  thesis-example threshold, reconstructed-value flatness, and memo
  span/split universe checks.
- This separates two useful guards:
  - fixed small thresholds such as `1000` for the thesis Figure 7.6 `k=5`
    regression;
  - a regex-size cubic-shaped budget for larger `k` grids.
- Checked smoke:
  - `k=5`, lengths `0,4,8,12,16,20,24,30`, factor `1.0`:
    `rsize=46`, cubic bound `97336`, max strong tree `958`;
  - `k=8`, lengths `0,4,8,16,32`, factor `1.0`:
    `rsize=97`, cubic bound `912673`, max strong tree `2879`.
- This is still smoke evidence, not a proof. Its purpose is to make the
  counterexample loop more honest: future candidates can be rejected either by
  POSIX value failure or by violating a regex-size polynomial budget.

## Cubic Candidate Prototype: Strong Deferred Ch7 Guard (2026-06-03)

- Tightened the Scala CEGAR pipeline for the user's preferred route: keep the
  thesis `bsimpStrong` tree as the small recognition state, but recover the
  exact POSIX value through the original-root span/memo table.
- `-TraceStrongDeferredMemo` is no longer just a printer. On the Chapter 7
  evil family it now:
  - checks that `StrongDeferredMemo` reconstructs a defined value whose
    `flat` is the traced input;
  - enforces optional strong-tree, DAG, and shape-DAG thresholds;
  - checks the memo span/split universe bound for every traced input length.
- A first version compared against the old baseline derivative lexer on the
  full Chapter 7 trace. That immediately ran out of heap because the baseline
  route is exactly the explosive behavior under study. Therefore exact
  baseline value comparison remains in the bounded exhaustive/random/known-CE
  smoke grids, while the large Ch7 trace uses the span/memo spec plus flatness
  and universe checks.
- This means a future algorithm tweak can only survive the smoke gate if it
  keeps the small `bsimpStrong`-style tree and preserves the exact POSIX
  value. Local certificate routes that fail greedy-boundary CEs remain useful
  as counterexample miners, not as bounty targets.
- This is a smoke-discipline checkpoint, not a cubic-bound proof claim.

## Cubic Candidate Prototype: Checked Span Value-Table Bound (2026-06-03)

- Added a key projection `rexp_span_posix_key` from full value entries
  `(q, i, j, v)` to memo keys `(q, i, j)`.
- Proved POSIX value determinism for every span-table key:
  `rexp_span_posix_value_unique`.
- Proved the key projection is injective over `rexp_span_posix` and has image
  exactly `rexp_span_posix_states`:
  `inj_on_rexp_span_posix_key` and `rexp_span_posix_key_image`.
- Added `finite_rexp_span_posix` and `card_rexp_span_posix_bound`, showing the
  full value table has the same quadratic state bound as the value-erased
  table:
  `rxsize r * Suc (length s) * Suc (length s)`.
- Meaning: the deferred span/memo reconstruction route now has a checked
  value-table size bound, not merely a state-key bound. This matches the Scala
  `valueStates` accounting discipline.
- Focused `Posix` build passed after this checkpoint.

## Cubic Candidate Prototype: Deferred Span Value Interface (2026-06-03)

- Added `strong_deferred_span_value` in `FBound.thy`, the proof-facing
  Isabelle analogue of the Scala `strongDeferredMemoValue` route:
  the final `bders_simpStrong (intern r) s` state is used only as the nullable
  gate, and the exact value is the unique root entry in `rexp_span_posix r s`.
- Checked bridges:
  - `strong_deferred_span_value_iff_Posix`;
  - `strong_deferred_span_value_iff_lexer`;
  - `strong_deferred_span_value_defined_iff`;
  - `strong_deferred_span_value_unique`;
  - `strong_deferred_span_value_flat`.
- Meaning: the current positive route is no longer just a Scala convention or
  prose plan. It has a named Isabelle relation equivalent to the original
  POSIX/lexer semantics, while retaining `bsimpStrong` as the small acceptance
  certificate.
- Focused `Posix` build passed after this checkpoint.

## Cubic Candidate Prototype: Checked Span Flat/Index Boundary (2026-06-03)

- Added cheap checked facts in `FBound.thy` for original-root POSIX span
  entries:
  - `rexp_span_posix_flat_eq`;
  - `rexp_span_posix_flat_length`;
  - `rexp_span_posix_empty_flat_index_eq`;
  - `rexp_span_posix_nonempty_flat_index_lt`.
- Meaning: every span value carries exactly the slice it claims to parse; an
  empty flat value must be an empty interval, and a nonempty flat value must
  consume a nonempty interval. These are small but useful boundary facts for
  the deferred span/memo route, especially around STAR/NTIMES split
  reconstruction.
- Tried to add direct STAR/NTIMES nonempty inversion lemmas, but both the
  generic `Posix_elims(6/7)` route and specialized generated
  `inductive_cases` route produced long-running commands. Those lemmas were
  deliberately not kept. Future STAR/NTIMES extraction should use bespoke,
  structured helper facts rather than generated eliminators.
- Focused `Posix` build passed after this checkpoint.

## Cubic Candidate Prototype: StrongFull Known-CE Guard (2026-06-03)

- Added a Scala smoke gate `-CheckStrongFullKnownCE` for the minimal
  greedy-boundary CE:
  `SEQ(STAR(ALT(STAR(CH b), SEQ(CH b, CH a))), STAR(CH a))` on `bba`.
- The guard intentionally checks both sides of the CEGAR story:
  - `StrongFullCert` still fails this case, so local final-state
    reconstruction is not accidentally treated as the proof target;
  - `StrongDeferredMemo` matches the baseline POSIX value on the same case;
  - the strong/full tree size remains `13`, confirming that the issue is
    value-boundary reconstruction, not recognition-state size.
- Wired the guard into `scala_cubic_smoke.ps1` and `isabelle_ci.ps1` as
  `-CheckStrongFullKnownCE` / `-ScalaSmokeCheckStrongFullKnownCE`.
- This is a route guard, not a bounty claim.

## Cubic Candidate Prototype: Countdown-Aware Span Inversion (2026-06-03)

- Fixed an important proof-interface gap in the original-root span universe:
  `NTIMES q (Suc n)` reconstruction needs the tail state `NTIMES q n`, but
  plain syntactic subterms do not contain countdown variants.
- Updated `FBound.thy` so `rexp_subterms (NTIMES r n)` contains all
  `NTIMES r k` for `k <= n`, and changed `rxsize (NTIMES r n)` to include
  the `Suc n` countdown budget. The cardinality bound
  `card_rexp_subterms_le_rxsize` remains checked.
- Added `rexp_subterms_NTIMES_countdown`, making the countdown closure explicit
  for later memo proofs.
- Added `rslice_prefix_split` in `GeneralRegexBound.thy`, which turns an
  equality `rslice s i j = s1 @ s2` into the concrete split index
  `k = i + length s1`.
- Added original POSIX span inversion rules for left/right alternatives and
  sequences:
  `rexp_span_posix_ALT1E`, `rexp_span_posix_ALT2E`, and
  `rexp_span_posix_SEQE`.
- Attempted STAR/NTIMES inversion with broad elimination was deliberately not
  kept because it triggered long proof search. Future work should add those
  using explicit structured cases, not `auto elim!`.
- Focused `Posix` build passed after this checkpoint.

## Cubic Candidate Prototype: Strong Tree with CE-Driven Span Values (2026-06-03)

- Re-ran the user-requested route: keep the `bsimpStrong` tree as the small
  acceptance state, but recover exact POSIX values through original-root span
  reconstruction instead of direct final-state decoding.
- Negative CE for local certificates remains stable and useful:
  `SEQ(STAR(ALT(STAR(CH b), SEQ(CH b, CH a))), STAR(CH a))` on `bba`.
  `StrongFullCert` keeps the exact small tree (`13` nodes after shrinking),
  but assigns the final `a` to the right star; POSIX greediness assigns
  `bba` to the left star and leaves the right star empty.
- Positive smoke for the span/memo route:
  - exhaustive depth `2`, input length `3`: `84,300` pairs pass;
  - known CE grid: `15` cases pass;
  - deterministic random depth `7`, input length `8`, seed `20260602`:
    `10,000` cases pass;
  - Chapter 7 `k=5`, lengths `0,4,8,12,16,20,24,30` keeps the
    `bsimpStrong` tree sequence
    `46,474,730,771,820,875,918,958`.
- Design conclusion: the CEGAR loop should keep mining local-certificate CEs,
  but the proof target should be a span-indexed POSIX reconstruction relation.
  The small strong derivative tree is the nullable gate; the root-span table is
  where longest-left split information lives.

## Cubic Candidate Prototype: Checked Original Split Probes (2026-06-03)

- Added original-`rexp` split-probe universes in `FBound.thy`:
  - `rexp_span_split_probes` and `card_rexp_span_split_probes_bound`;
  - `rexp_span_all_split_probes` and
    `card_rexp_span_all_split_probes_bound`.
- Added one-directional POSIX constructor rules for original span values:
  - `rexp_span_posix_ONE_emptyI`;
  - `rexp_span_posix_CHI`;
  - `rexp_span_posix_ALT1I` and `rexp_span_posix_ALT2I`;
  - `rexp_span_posix_SEQI`;
  - `rexp_span_posix_STAR_emptyI` and `rexp_span_posix_STAR_stepI`;
  - `rexp_span_posix_NTIMES_zero_emptyI` and
    `rexp_span_posix_NTIMES_SucI`.
- Meaning: the proof-facing span table now has bounded split probes and
  constructor-introduction rules matching the Scala memo algorithm's
  left-priority alternatives and longest-left sequence/star/countdown splits.
- Focused `Posix` build passed after this checkpoint.

## Cubic Candidate Prototype: Checked Root Span POSIX Bridge (2026-06-03)

- Added an original-`rexp` span reconstruction interface in `FBound.thy`:
  - `rxsize`, a payload-insensitive structural size for original regexes;
  - `rexp_subterms` and `card_rexp_subterms_le_rxsize`;
  - `rexp_span_states` and `card_rexp_span_states_bound`;
  - `rexp_span_posix`, whose entries are `(subregex, i, j, value)` with
    `rslice s i j` carrying the original `Posix` value;
  - `rexp_span_posix_states`, the value-erased query-state projection, with
    `card_rexp_span_posix_states_bound`.
- Added the key bridge from the strong acceptance certificate to original
  span reconstruction:
  - `bnullable_bders_simpStrong_intern_iff_rexp_span_posix_root`;
  - `bnullable_bders_simpStrong_intern_unique_rexp_span_posix_root`.
- Meaning: a nullable final `bders_simpStrong (intern r) s` now authorizes a
  unique root entry in the original POSIX span table. This is still not a
  cubic theorem, but it turns the Scala `strongDeferredMemoValue` route into a
  checked proof interface.
- Focused `Posix` build passed after this checkpoint.

## Cubic Candidate Prototype: Strong Tree Plus Span Reconstruction (2026-06-03)

- Added an explicit Scala known-CE grid to `-CheckStrongDeferredMemo`.
  It now checks the examples that broke direct/final-state decoding:
  - `STAR(STAR(CH a))` on small `a`-strings;
  - `SEQ(STAR(ALT(STAR(CH b), SEQ(CH b, CH a))), STAR(CH a))` on
    `bba` and neighboring inputs;
  - the nested nullable sequence/star family.
- Latest smoke checkpoint:
  - exhaustive depth `2`, input length `3`: `84,300` pairs pass;
  - known CE grid: `15` cases pass;
  - deterministic random depth `7`, input length `8`, seed `20260602`:
    `5,000` cases pass;
  - Chapter 7 `k=5`, lengths `0,4,8,12,16,20,24,30` keeps the
    `bsimpStrong` tree plateau, ending at strong tree `958`.
- Design conclusion:
  - the user's requested path is viable if "small tree" means the strong
    derivative state remains the acceptance certificate;
  - exact POSIX values should be reconstructed from original `(regex, input)`
    spans, not decoded directly from the final simplified regex;
  - `StrongFullCert` remains a counterexample miner for local certificate
    ideas, but its `bba` greedy-sequence CE shows that local
    `Val => Option[Val]` transformers do not carry enough split history.

## Cubic Candidate Prototype: More Checked Span Constructor Rules (2026-06-03)

- Extended the checked table-construction algebra in `GeneralRegexBound.thy`:
  - `rspan_accepts_RALTSI`;
  - `rspan_accepts_RONE_emptyI`;
  - `rspan_accepts_RSTAR_stepI`;
  - `rspan_accepts_RNTIMES_zeroI`;
  - `rspan_accepts_RNTIMES_SucI`.
- These are still infrastructure, not a payout: they let future memo/value
  reconstruction proofs build accepted span-table entries for alternatives,
  empty/unit cases, nonempty stars, and counted repetitions.
- Focused `Posix` build passed after this checkpoint.

## Cubic Candidate Prototype: Checked Span Reconstruction Algebra (2026-06-02)

- Added checked slice and span lemmas in `GeneralRegexBound.thy`:
  - `rslice_0_length`;
  - `rslice_same`;
  - `length_rslice`;
  - `rslice_append`;
  - `rspan_accepts_iff`;
  - `rspan_accepts_root_iff`.
- Added checked reconstruction-introduction facts:
  - `rspan_all_split_probes_iff`;
  - `rspan_accepts_RSEQI`, showing that if a legal split has left/right
    accepted slices, then the whole `RSEQ` span is accepted;
  - `rspan_accepts_RSTAR_emptyI`, the empty-star span case.
- This starts the correctness side of the span/memo route: the table bounds
  already exist, and now the basic string-slice algebra needed to prove
  dynamic-programming reconstruction has checked entry points.
- Focused `Posix` build passed after this checkpoint.

## Cubic Candidate Prototype: Checked Span Memo Tables (2026-06-02)

- Extended the checked span-reconstruction interface in `GeneralRegexBound.thy`:
  - `rslice s i j = take (j - i) (drop i s)`;
  - `rspan_accepts r s`, the specification of memoized acceptance states:
    `(subregex, i, j)` where the slice `s[i,j)` is in the subregex language;
  - `rspan_all_split_probes r s`, the specification of all legal split probes
    `(subregex, i, k, j)` with `i <= k <= j <= length s`.
- Added checked subset and cardinality facts:
  - `rspan_accepts_subset_rspan_states`;
  - `card_rspan_accepts_bound`;
  - `rspan_all_split_probes_subset`;
  - `card_rspan_all_split_probes_bound`.
- This moves the memo route one step beyond a raw universe: a future
  reconstruction algorithm can now target these checked table specifications
  directly, then inherit the state/split bounds. The left-greedy CE for
  `StrongFullCert` is exactly the kind of behavior this original-regex
  span-table route is meant to handle.
- Focused `Posix` build passed after this checkpoint.

## Cubic Candidate Prototype: Checked Span Reconstruction Universe (2026-06-02)

- Added checked Isabelle definitions in `GeneralRegexBound.thy`:
  - `rspan_states r s`, the finite universe of reconstruction states
    `(subregex, i, j)`;
  - `rspan_split_probes r s`, the finite universe of split probes
    `(subregex, i, k, j)`.
- Added checked cardinality bounds:
  - `card_rspan_states_bound`:
    `card (rspan_states r s) <= rsize r * (|s|+1)^2`;
  - `card_subset_rspan_states_bound`, for any concrete memo table subset;
  - `card_rspan_split_probes_bound`:
    `card (rspan_split_probes r s) <= rsize r * (|s|+1)^3`;
  - `card_subset_rspan_split_probes_bound`, for any concrete split-probe set.
- This is the first Isabelle-facing version of the Scala memo reconstruction
  accounting. It does not prove POSIX reconstruction correctness yet. Its role
  is to make the deferred/memo route proof-shaped: future reconstruction
  relations can prove their memo states are subsets of these universes and
  inherit polynomial input-span bounds while the strong derivative state keeps
  the regex-size bound.
- Focused `Posix` build passed after this checkpoint.

## Cubic Candidate Prototype: Full Strong Tree With Certificates (2026-06-02)

- Added experimental Scala route `StrongFullCert`:
  - it keeps the small `bsimpStrong`-style output tree as the recognition
    state;
  - each simplification step carries a reconstruction function from values of
    the simplified state back to values of the pre-simplification derivative;
  - wrapper switches: `-CheckStrongFullLoop`, `-FindStrongFullCE`,
    `-TraceStrongFullLoop`, and `-TraceStrongFullKnown`.
- Positive smoke:
  - exhaustive depth `2`, input length `3` passes (`84,300` regex/input pairs);
  - deterministic random depth `6`, input length `7`, seed `20260602`, passes
    `10,000` cases;
  - Chapter 7 `k=5`, lengths `0,4,8,12,16,20,24,30`, keeps the thesis-scale
    tree plateau with max full-certificate state `721` and final sizes
    `46,438,618,612,612,632,579,678`.
- CE-driven repair:
  - depth `6` exposed a small trailing-unit order CE:
    `STAR(STAR(ALT(SEQ(b,ONE), SEQ(SEQ(STAR(a),a),ONE))))` on `abbab`;
  - replacing broad atom-level reparsing by explicit value transformers for
    right-unit deletion, left-unit deletion, sequence reassociation, and star
    absorption repairs that CE and the larger hard random witness.
- Current blocker:
  - deterministic random depth `7`, input length `8`, seed `20260602`, case
    `622` shrinks to
    `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`;
  - the exact POSIX value lets the left star consume `bba`, while the current
    full certificate reconstructs `bb` for the left star and gives the final
    `a` to the right `STAR(a)`;
  - this is a left-greedy sequence boundary problem, so `StrongFullCert` is not
    a bounty candidate yet.
- Design conclusion:
  - the user-suggested CE loop is working and should remain in the pipeline;
  - a pure local `Val => Option[Val]` transformer may still be too weak for
    future derivatives across nullable/greedy sequence boundaries;
  - the most robust theorem route remains: full `bdersStrong` as the small
    acceptance certificate, plus a proof-facing span/memo POSIX reconstruction
    relation for the original regex/input.

## Cubic Candidate Prototype: Deferred Strong Reconstruction Route (2026-06-02)

- Added Scala smoke route `strongDeferredValue` and wrapper switch
  `-CheckStrongDeferred`.
- Added Scala smoke route `strongDeferredMemoValue` and wrapper switch
  `-CheckStrongDeferredMemo`.
- Definition idea:
  - run the full thesis-style `bdersStrong` derivative loop as the small
    recognition state;
  - if the final strong derivative is nullable, reconstruct the exact POSIX
    value from the original regex/input rather than decoding ordinary values
    from the simplified derivative state;
  - the new memo prototype `posixMemoValue` performs that reconstruction by
    dynamic programming over `(regex, start, end)` spans, using left-priority
    alternatives and longest-left splits for `SEQ`, `STAR`, and `NTIMES`.
- This is deliberately a research route, not a bounty claim and not yet a
  cubic theorem. It represents a generalized/deferred-value semantics: the
  small derivative state proves acceptance and keeps the cubic-size route alive;
  the exact POSIX value is recovered by a separate reconstruction theorem over
  the original regex and consumed flat string.
- Smoke evidence:
  - exact POSIX values pass exhaustive depth `2`, input length `3`
    (`84,300` regex/input pairs);
  - deterministic random smoke passes `50,000` cases at depth `7`, input
    length `8`, seed `20260602`;
  - memoized deferred reconstruction passes exhaustive depth `2`, input length
    `3`, and `10,000` deterministic random cases at depth `6`, input length
    `7`, seed `20260602`;
  - `-TraceStrongDeferredMemo` now reports the reconstruction table size.
    `-CheckStrongDeferredMemo` also checks the conservative reconstruction
    universe bounds:
    accepts/value states `<= rsize(r) * (|s| + 1)^2`, and split probes
    `<= rsize(r) * (|s| + 1)^3`.
    Chapter 7 k=5, lengths `0,4,8,12,16,20,24,30`:
    strong tree `46,474,730,771,820,875,918,958`;
    memo accepts states `0,56,158,308,506,752,1046,1577`;
    memo value states `1,22,38,54,70,86,102,126`;
    split probes `0,57,225,569,1153,2041,3297,6011`;
    at n=30 the span bound is `44206` and split bound is `1370386`.
    Chapter 7 k=8, lengths `0,4,8,16,32,48`:
    strong tree `97,1164,1816,2691,2879,2963`;
    memo accepts states `0,56,158,506,1778,3818`;
    memo value states `1,22,38,70,134,198`;
    split probes `0,57,225,1153,7169,22145`;
    at n=48 the span bound is `232897` and split bound is `11411953`.
  - the hand CE grid from the nullable-star failures remains checked.
- Size evidence from the full `bsimpStrong` state is back to the thesis-scale
  plateau:
  - Chapter 7 `k=5`, lengths `0,4,8,12,16,20,24,30`:
    `46,474,730,771,820,875,918,958`.
  - Chapter 7 `k=8`, lengths `0,4,8,16,32,48`:
    `97,1164,1816,2691,2879,2963`.
- Next proof question:
  - Define a proof-facing deferred reconstruction relation. This relation
    should not pretend that simplified ordinary values are POSIX values; it
    should say that a nullable strong derivative plus the consumed string
    authorizes reconstruction of the original POSIX value.
- Checked Isabelle bridge now available in `FBound.thy`:
  - `bnullable_bders_simpStrong_iff_Ders`;
  - `bnullable_bders_simpStrong_iff_member`.
  These state that the full thesis-style `bders_simpStrong` final state has
  correct acceptance behavior even though its ordinary decoded values are not
  generally POSIX values for the original regex.
- The bridge now also connects directly to original POSIX values and the
  production lexer:
  - `bnullable_bders_simpStrong_intern_iff_Posix`;
  - `bnullable_bders_simpStrong_intern_iff_lexer_defined`;
  - `bnullable_bders_simpStrong_intern_obtain_lexer`;
  - `bnullable_bders_simpStrong_intern_unique_Posix`.
  This is the current proof-facing meaning of deferred reconstruction:
  `bders_simpStrong` is a small acceptance certificate; when it accepts,
  the original `lexer r s` supplies the unique POSIX value. A future cubic
  runtime must replace that fallback by an efficient reconstruction relation,
  but the semantic target is now checked.
- New proof target suggested by the memo trace:
  - define the reconstruction universe as span-indexed states
    `(subregex, i, j)`;
  - prove that POSIX reconstruction only queries this universe, with split
    probes bounded by a polynomial in input length times the relevant regex
    frontier;
  - then combine it with the checked `bders_simpStrong` acceptance bridge and
    the separate strong-state size argument.
- Added CE-driven Scala gate `-FindStrongDirectCE` for the unsafe direct decode
  route. It finds and greedily shrinks counterexamples before any proof attempt.
  Current minimal CE:
  - regex `STAR(STAR(CH(b)))`;
  - input `b`;
  - baseline POSIX value is nested `Stars`, while direct `strongValue` is
    `None` because the small final state's epsilon bits no longer decode as
    the original nested-star POSIX value.

## Cubic Candidate Prototype: CE-Driven Strong-Core Reassessment (2026-06-02)

- Added Scala smoke switches for the current counterexample-driven loop:
  `-FindStrongCoreCE`, `-FindRawInjectCE`, `-CheckStrongCoreHand`, and
  `-SkipLegacyCubic`. These isolate the candidate route from the known-bad
  legacy `bsimpCubic full` random gate.
- Positive diagnostic:
  - Raw derivative injection without simplification found no counterexample in
    `1,000` deterministic random cases at depth `7`, input length `8`, seed
    `20260602`. This points away from `injectA` as the first culprit.
- Counterexamples found for the exact-value strong-core loop:
  - `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba` shows that local
    reconstruction around strong simplification can move the final `a` across
    a star boundary.
  - `STAR(STAR(ALT(SEQ(STAR(a), ONE), b)))` on `bab` shows that deleting a
    right unit after a nullable expression is not derivative-state safe under
    nested star: the simplified loop can lose the final `b`.
  - A later random CE involving `NTIMES(ONE,3)`, `STAR(STAR(ZERO))`, and
    nullable alternatives shows that side conditions for nullable units/stars
    are still insufficient as a full exact-value algorithm.
- Experimental repair:
  - `bsimpStrongCoreShape` now uses a POSIX-core sequence helper with side
    conditions: right-unit deletion requires a non-nullable left side,
    left-unit deletion requires a non-nullable right side, reassociation
    requires a non-nullable left factor, and star absorption/nested-star
    collapse require a non-nullable repeated body.
  - The hand CE grid now passes (`44` cases), but broader random smoke still
    finds failures. This is not bounty-complete.
- Size impact:
  - With pruning restored and the side conditions enabled, Chapter 7 `k=5`
    selected lengths `0,4,8,12,16,20,24,30` give
    `46,901,2241,2988,3305,3317,3443,3674`.
  - Chapter 7 `k=8` selected lengths `0,4,8,16,32` give
    `97,2209,5789,12145,18473`.
  - Disabling AALTs pruning/dedup entirely caused an OOM on the k=5 trace, so
    pruning remains essential. The next route must be smarter/certified
    pruning or generalized POSIX values, not simply weakening all strong
    rewrites.
- Current conclusion:
  - A plain `Val => Val` reconstruction layered over ordinary derivatives is
    too weak for the full nullable-star/nullable-alternative fragment.
  - The promising research direction is either a generalized value relation
    that treats equivalent star/sequence segmentations as reconstructible, or a
    row-pruning certificate that records enough payload/history to avoid
    deleting future POSIX choices while keeping the Chapter 7 tree plateau.

## Cubic Candidate Prototype: CE-Driven Strong Value Safety (2026-06-02)

- Added Scala-only diagnostic `bsimpStrongSafe`, with wrapper switches
  `-CheckStrongSafe` and `-TraceStrongSafe`. This is not a bounty artifact; it
  is the first counterexample-driven attempt to keep as much of the thesis
  strong simplifier as possible while preserving exact POSIX values.
- CE-driven repairs found so far:
  - `STAR (STAR (CH a))` on `a` shows nested-star collapse loses the outer
    `Stars` value. Safe variant keeps nested stars and preserves empty-star
    `S` bits.
  - `SEQ (STAR (CH a)) (STAR ZERO)` on `a` shows right `AONE bs` may carry
    value bits. Safe variant drops the right unit only when it is `AONE []`.
  - `SEQ (STAR (CH a)) (STAR (CH a))` on `a` shows star absorption
    `r* . r* -> r*` loses the second-star value. Safe variant disables this
    output rewrite.
  - A depth-3 random counterexample showed left-nested reassociation
    `(x.y).z -> x.(y.z)` reorders prefix bits. Safe variant disables this
    output rewrite too.
- Smoke evidence after those repairs: exact POSIX value preservation passes
  exhaustive depth `2`, input length `3` (`84,300` pairs), deterministic random
  depth `4`, input length `5` (`5,000` cases), and deterministic random depth
  `5`, input length `6` (`2,000` cases), seed `20260602`.
- Size evidence: `bsimpStrongSafe` no longer preserves the thesis Figure 7.6
  tree plateau. On `k=5`, lengths `0..30`, selected tree sizes
  `0,4,8,12,16,20,24,30` are `46,880,2192,2961,3449,3927,4486,5133`.
  This is exact-value safe but worse than both thesis `bsimpStrong`
  (`46,474,730,771,820,875,918,958`) and the current
  `expanded-keyed-no-reassoc` (`46,662,1334,1841,2264,2816,3150,3849`).
- Design conclusion: if we want to keep the `bsimpStrong` tree-size behavior
  and still return correct POSIX values, weakening output rewrites is the wrong
  endpoint. The next serious route is a transformer/reconstruction layer for
  the three value-unsafe strong rewrites: nested-star collapse, star absorption,
  and sequence reassociation. Those rewrites may remain in the small regex only
  if the lexer carries enough evidence to map decoded simplified values back to
  the original `val` shape.
- Added optional sketch smoke `scala_cubic_smoke.ps1 -TraceStrongRecon`. It
  keeps the actual `bsimpStrong` final regex and tests local value
  reconstruction sketches on the first CE family:
  - nested-star collapse: `Stars vs` reconstructs to
    `Stars [Stars vs]` for the nonempty derivative case;
  - star absorption/right nullable unit: `Stars vs` reconstructs to
    `Seq (Stars vs) (Stars [])`;
  - sequence reassociation: `Seq x (Seq y z)` reconstructs to
    `Seq (Seq x y) z`.
  The smoke passes on the current CE witnesses while `bsimpStrong` keeps the
  thesis-sized final regexes, e.g. each small CE has final strong tree size `2`.
  This is positive route evidence, not a completed algorithm: the remaining
  work is to make these local transformers compositional across derivative
  steps.
- Strengthened the sketch with an annotated-value decoder `decodeAValue` and
  local certificate-law smoke. The new checks compare the original annotated
  expression and the rewritten annotated expression over input grids, then apply
  the proposed transformer to the rewritten POSIX value. Passing laws so far:
  nested-star collapse and star absorption for bodies `a`, `aa`, and `a+b`;
  star-zero collapse; right-`AONE` deletion with carried bits; and sequence
  reassociation. This moves the route from isolated CE repair toward reusable
  local certificates.
- Current Figure 7.6 sanity with the certificate-law smoke enabled keeps the
  thesis small-tree trace for `bsimpStrong` on `k=5` selected lengths
  `0,4,8,12,16,20,24,30`: `46,474,730,771,820,875,918,958`.
  The local laws are not yet composed through a full derivative loop, so this
  remains route evidence rather than BR-039 completion.
- Added `StrongCoreCert`, a first compositional Scala certificate prototype for
  the sequence/star core of `bsimpStrong`. It returns a simplified annotated
  regex together with a value transformer from the simplified epsilon value
  back to the pre-simplification epsilon value. This currently certifies
  sequence reassociation, right-unit deletion, star-zero collapse, nested-star
  collapse, and star absorption, while alternation flattening/pruning remains a
  deliberately separate next target.
- Added `decodeAEpsValue`, because derivative-expression certificate checks
  must decode nullable epsilon values, not ordinary input-carrying annotated
  values. This fixed two useful CE diagnostics where non-nullable `ACHAR []`
  branches could otherwise steal an epsilon bitstream.
- Smoke evidence for `StrongCoreCert`: exhaustive depth `2`, input length `3`
  checks `84,300` derivative expressions; deterministic random smoke with
  `expanded-keyed-no-reassoc`, depth `5`, input length `6`, seed `20260602`,
  checks `2,000` random derivative expressions. Both pass. This is still not a
  full lexer-level certificate, because derivative through an already-certified
  simplified state and certified Antimirov row pruning remain open.
- Added certified alternation flatten/distinct support inside
  `StrongCoreCert`. Flattened rows now carry their original outer/inner
  alternative index, and `distinctWith` keeps row certificates for surviving
  rows so the original ALT value wrapper can be reconstructed even when deleted
  rows shift the output index.
- Added `scala_cubic_smoke.ps1 -TraceStrongCore`. Current Chapter 7 k=5
  comparison at lengths `0,4,8,12,16,20,24,30`:
  - thesis `bsimpStrong`: `46,474,730,771,820,875,918,958`;
  - certified `bsimpStrongCore`: `46,420,718,1012,1308,1600,1898,2342`;
  - current `bsimpCubic full`: `46,413,725,800,800,820,816,900`.
  This pinpoints the next missing certificate layer: shared-suffix /
  Antimirov-style row pruning, not sequence/star simplification.
- Added the first certified shared-suffix row pruning prototype. The rule is
  deliberately contextual: deleting a later row is justified by an earlier
  outer-ALT row with the same suffix, so the deleted later branch is not locally
  value-equivalent; the earlier row handles the POSIX choice. Surviving pruned
  rows carry transformers back to their original later-row value.
- Smoke evidence for certified row pruning:
  - `-TraceStrongRecon -CheckStrongCoreCert` passes `84,300` exhaustive
    derivative expressions.
  - `expanded-keyed-no-reassoc -CheckStrongCoreCert` with `3,000` random
    depth-5/input-6 expressions, seed `20260602`, passes.
  - Chapter 7 k=5 selected lengths `0,4,8,12,16,20,24,30` for certified
    `bsimpStrongCore` are now `46,438,618,612,612,632,579,678`, down from
    `46,420,718,1012,1308,1600,1898,2342`. This is the first certified route
    that beats the thesis Figure 7.6 tree trace on this smoke.
- Remaining gap before proof/bounty work: state the proof-facing invariant for
  certified row pruning and for composing `bder`, simplification, `injectA`,
  and reconstruction across the whole lexer run.
- Added the first derivative-loop certificate smoke for certified
  `bsimpStrongCore`. The loop maintains a continuation from the current
  simplified derivative state's value back to the original POSIX value. At each
  character it composes:
  1. `bder` on the current simplified state;
  2. `bsimpStrongCoreCert` for that derivative;
  3. `injectA`, the executable derivative-value reconstruction for annotated
     regexes;
  4. the previous continuation.
- Loop smoke evidence:
  - exhaustive depth `2`, input length `3`: `84,300` regex/input pairs match
    `baselineValue`;
  - deterministic random with `expanded-keyed-no-reassoc`, depth `5`, input
    length `6`, seed `20260602`: `3,000` cases match `baselineValue`.
  This is the first Scala evidence that the small certified core can preserve
  exact POSIX values across a whole lexer run, not just for one simplification
  step. It remains a prototype until the corresponding invariant is stated and
  checked in Isabelle.
- Added `agent_hunt_pipeline/projects/posix-backref/CERTIFIED_STRONG_CORE.md`,
  the proof-facing spec for the certificate route. It records the intended
  Isabelle relation `cert_recon`, the loop invariant shape, the certificate
  constructors, and the current smoke commands.
- Added `-TraceStrongCoreLoop`, a loop-size diagnostic. On the Chapter 7 k=5
  family, `maxCore` stabilizes at `721` by input length `12`, while final sizes
  stay below `678` through length `30`. This is the current evidence that the
  proof should bound every certified loop state, not just the final regex.

## Cubic Candidate Prototype: Shared State plus Virtual Expanded Keys (2026-06-02)

- Added an optional Scala hash-consed annotated-regex store. It interns
  annotated nodes, runs each derivative/simplifier step in the selected
  `POSIX_SMOKE_SEQ_MODE`, reconstructs an ordinary `arexp` at the final root,
  and compares decoded POSIX values against the baseline lexer. The wrapper
  switch is still named `scala_cubic_smoke.ps1 -SharedNoReassoc` for
  compatibility, but the shared diagnostic now follows the current `-SeqMode`.
  This is executable reconstruction evidence, not an Isabelle proof.
- Added diagnostic sequence mode `expanded-keyed-no-reassoc`, the smoke version
  of the accumulator idea: comparison/pruning keys virtually expose rows such
  as `a.c` and `b.c` from `(a+b).c`, but the emitted regex remains
  `no-reassoc` shaped. Thus the index can compare Antimirov-style row
  contributions without destructively distributing POSIX value-carrying syntax.
- Checked smoke evidence for `expanded-keyed-no-reassoc`:
  - Exhaustive depth `2`, input length `3`: exact POSIX value preservation on
    `84,300` regex/input pairs.
  - Deterministic random smoke: `2,000` cases at random depth `5`, input length
    `6`, seed `20260602`, preserves exact POSIX values.
  - Chapter 7 `k=8`, lengths `4,8,16,32`:
    tree `1616,3226,6178,10218`;
    final exact DAG `78,130,232,408`;
    shape DAG `61,87,125,173`;
    shared cumulative pool `120,229,550,1400`.
  - Longer Chapter 7 `k=8`, lengths `32,64,128`:
    tree `10218,18274,34581`;
    final exact DAG `408,760,1465`;
    shape DAG `173,269,462`;
    shared cumulative pool `1400,3855,11810`.
- Comparison with plain `no-reassoc` on Chapter 7 `k=8`, lengths `32,64,128`:
  tree `18643,30258,48077`; exact DAG `547,980,1721`;
  shape DAG `312,489,718`; shared pool `1312,3593,11170`. Interpretation:
  virtual expanded keys improve final pruning and DAG/shape size, while
  hash-consing tracks the shared-state accounting; the virtual key mode can
  create a slightly larger cumulative pool while producing a smaller final
  root.
- Thesis Figure 7.6 comparison for `k=5`, lengths `0..30`: the Scala
  `-TraceStrong` diagnostic now mirrors Isabelle `bders_simpStrong` closely
  (`n=16` gives tree size `820`, matching the existing Isabelle facts `<825`
  and not `<812`). Its tree trace rises and then oscillates in the hundreds:
  `0,4,8,12,16,20,24,30 -> 46,474,730,771,820,875,918,958`. By contrast, the
  value-safe `expanded-keyed-no-reassoc` ordinary tree trace is larger:
  `46,662,1334,1841,2264,2816,3150,3849`, while its exact DAG/shape-DAG at
  `n=30` are only `276/132`. Thus the current value-safe route has not
  reproduced the thesis tree-size plateau; it has reproduced a shareable-state
  plateau.
- Added optional `-CheckStrong` smoke for the thesis-style `bsimpStrong` loop.
  It intentionally stays off by default and currently fails exact POSIX value
  preservation immediately on `STAR (STAR (CH a))` with input `a`: the baseline
  decodes `Stars [Stars [Char a]]`, while `bsimpStrong` collapses to a final
  `ASTAR [Z] (ACHAR [] a)` whose epsilon bits `[Z,S]` do not decode against
  the original nested-star regex. This confirms that the tree-level strong
  plateau is language/size evidence only unless we either disable that
  value-destroying collapse or add a checked generalized-value reconstruction
  theorem.
- Design interpretation: these two ideas are complementary. Hash-consing is a
  representation/counting mechanism; virtual expanded keys are a pruning/index
  mechanism. The next serious design should define derivatives directly over a
  hash-consed row universe or delayed linear forms, record virtual row keys for
  coverage, and prove reconstruction to ordinary POSIX values before any bounty
  or cubic theorem claim.

## Cubic Candidate Diagnostic: Value-Safe DAG/Shared-Row Route (2026-06-02)

- Extended the Scala smoke harness with exact DAG and shape-DAG size
  diagnostics for Chapter 7 traces. The wrapper now exposes
  `-Ch7K`, `-Ch7Lengths`, `-Ch7TreeThreshold`, `-Ch7DagThreshold`, and
  `-Ch7ShapeThreshold`. Default CI still uses the old tree threshold.
- Key evidence: the value-safe `no-reassoc` mode passes deterministic random
  POSIX value smoke (`-RandomCases 2000 -RandomDepth 5 -RandomInputLength 6`)
  but fails the tree-size Chapter 7 threshold. However, its repeated structure
  is highly shareable:
  - `k=5`, lengths `4,8,16,32,64`:
    tree `880,2057,3281,5325,8342`;
    exact DAG `65,124,206,348,575`;
    shape DAG `51,90,132,194,278`.
  - `k=8`, lengths `4,8,16,32`:
    tree `2188,5728,11699,18643`;
    exact DAG `86,166,317,547`;
    shape DAG `69,123,210,312`.
- This gives a concrete next route that preserves POSIX values without
  destructive `ASEQ` reassociation: represent derivative states as a shared
  DAG/hash-consed row universe or delayed linear forms. The tree term still
  grows too much, so this is not a completed tree-size bound, but it supports
  an Antimirov-style finite-row accounting route where repeated continuations
  are shared rather than reassociated into the executable syntax.
- Current recommended next step: prototype a row-universe/DAG representation
  that keeps `no-reassoc`-style value behavior, proves or tests a reconstruction
  path back to ordinary POSIX values, and measures the number of distinct
  annotated nodes/rows as the candidate size metric before attempting Isabelle
  proofs.

## Cubic Candidate Diagnostic: ASEQ Reassociation Hazard (2026-06-02)

- Added a diagnostic `POSIX_SMOKE_SEQ_MODE`/`-SeqMode` switch to the Scala
  smoke harness. Default remains `full`, so normal CI still checks the current
  production candidate; alternative modes are for localization only.
- The deterministic random smoke localizes the known value bug to destructive
  sequence reassociation in `bsimpCubic_ASEQ_atom`. With seed `20260602` and
  `-RandomCases 2000 -RandomDepth 5 -RandomInputLength 6`:
  `no-reassoc`, `zeros-only`, and the experimental `keyed-no-reassoc` mode
  preserve exact POSIX values on the tested random cases, while `full` still
  fails at random case `99`.
- Size tells the other half of the story: `no-reassoc` preserves values but
  the Chapter 7 trace grows to `4->880, 8->2057, 12->2643, 16->3281,
  20->3804`; `keyed-no-reassoc` still fails the threshold at `n=8` with
  `asize=2157`. Thus comparison-only keys are not yet enough to recover the
  desired pruning strength.
- A tempting compromise, `reassoc-nonnullable-left`, also fails exact POSIX
  random smoke (seed `20260602`, case `370`). The design lesson is now
  explicit: ordinary `(x.y).z -> x.(y.z)` reassociation cannot be used as a
  value-preserving output rewrite unless a separate bitcode/value transfer or
  generalized POSIX-value reconstruction theorem is supplied.
- Next viable route: keep destructive associativity out of executable output,
  but introduce a richer row/continuation identity, delayed linear-form index,
  or reconstruction layer strong enough to expose Chapter 7 shared suffixes.
  The current diagnostic modes are evidence for design, not bounty artifacts.

## Cubic Candidate Diagnostic: Random Smoke Value Gap (2026-06-02)

- Extended `agent_hunt_pipeline/scala/PosixCubicSmoke.scala` with an explicit
  exhaustive-generation cap and optional deterministic random smoke. Default
  CI keeps random smoke off; proof/bounty attempts should run it manually, e.g.
  `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1 -RandomCases 2000
  -RandomDepth 5 -RandomInputLength 6`.
- Exhaustive depth `3` over the current two-character grammar is not practical
  as a casual gate: the harness reports about `63,191,284` raw regexes before
  deduplication and fails clearly instead of exhausting heap.
- Random smoke with seed `20260602` found a real value-preservation gap at case
  `99`: regex
  `STAR (ALT ONE (STAR (STAR (STAR (STAR (STAR (CH a)))))))` on input `aaa`.
  The baseline derivative lexer decodes a nested right-branch star value, while
  `bders_simpCubic` produces a nullable final state whose bits do not decode
  against the original regex.
- Design consequence: the current `bsimpCubic` remains useful as a
  language/size/smoke prototype, but it is not yet a production POSIX-value
  preserving cubic candidate. BR-039/BR-040 must remain open until a
  value-aware row identity, reconstruction theorem, or generalized POSIX value
  transfer fixes this class of examples.

## Cubic Candidate Checkpoint: Scala-Gated bsimpCubic Smoke (2026-06-02)

- Moved broad Chapter 7 grid/enumeration smoke tests out of Isabelle and into
  `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`, with wrapper
  `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1`. Full
  `agent_hunt_pipeline/scripts/isabelle_ci.ps1` now runs this Scala gate before
  full Isabelle sessions unless `-PilotOnly` or `-SkipScalaSmoke` is used.
- The Scala gate enumerates bounded non-backref regexes and input strings, then
  compares exact decoded POSIX values for the baseline derivative lexer versus
  `bders_simpCubic`. Default evidence: `84300` regex/input pairs checked at
  depth `2`, input length `3`.
- Scala smoke caught and forced value-preserving repairs: `ANTIMES _ _ 0` and
  empty-star collapses now keep the terminating `S` bit, nested-star collapse
  is not used, and sequence-level star absorption is rejected by the concrete
  counterexample `SEQ (STAR a) (STAR a)` on input `a`.
- Added generalized covered-continuation pruning to `bsimpCubic`: earlier rows
  such as `p.k` or `(p+q).k` cover later rows such as `(p+r).k` without
  destructively distributing the executable regex. The Scala Chapter 7 `k=5`
  trace is now `4->413, 8->725, 12->800, 16->800, 20->820`.
- Isabelle side remains proof-facing: `FBound.thy` checks compact smoke facts
  and erased-language bridges `L_bsimpCubic`, `RL_rerase_bsimpCubic`, and
  `RL_rerase_bders_simpCubic`. This is support for the candidate, not a final
  cubic theorem and not a bounty payout.
- Build evidence: focused Isabelle `Posix` build PASS via bundled Cygwin bash.

## Cubic Bound Guidance Update: Smoke Before Proof (2026-06-02)

- Added a hard rule to the project instructions: cubic-bound proof routes are
  forbidden until the proposed simplifier has passed checked smoke tests for
  shared-suffix pruning and the thesis Chapter 7 three-layer-star family. A
  simplifier with a known missing pruning rule is diagnostic work only, not a
  proof/bounty target.
- Recorded the Antimirov/POSIX design tension. Antimirov partial derivatives
  gain their small-state behavior by using sets/linear forms that can expose
  and deduplicate rows such as the `a.c` overlap in `(a+b).c + (a+d).c`.
  POSIX value semantics cannot blindly distribute `(a+b).c` into `a.c+b.c`,
  because this changes value shape (`Seq (Left x) y` versus
  `Left (Seq x y)`). Future cubic candidates must provide pruning without
  destructive value loss, or introduce a generalized POSIX-value equivalence
  with a transfer theorem back to the original semantics.

## Cubic Bound Checkpoint: Smoke-First Route Reset (2026-06-02)

- Revoked the old proof-first `rsimp9` bounty route in `BACKREF_BOUNTIES.md`.
  `BR-036` and the old root-safe transfer `BR-037` are retired and cannot pay
  out. Historical lemmas may remain as technical evidence, but `rsimp9` is no
  longer a candidate simplifier or proof target.
- Added new smoke-gated bounties: `BR-038` for a checked counterexample/smoke
  suite, `BR-039` for a new simplifier candidate that passes that suite, and
  `BR-040` for proof interfaces only after the suite passes.
- Added new candidate definitions `rsimpCubic`/`rders_simpCubic` and
  `bsimpCubic`/`bders_simpCubic`. The candidate uses strong shared-suffix row
  pruning for alternatives and has its own recursive counted-repetition
  normalization; it is not an `rsimp9` wrapper.
- Added the first smoke suite in `FBound.thy`: A checks
  `(a+b)c + (a+d)c`; B checks the thesis Chapter 7 three-star family; C-F are
  small checked counterexamples where current `bsimp` misses shared-suffix or
  coverage pruning and `bsimpCubic` shrinks the state.

## Cubic Bound Route Correction: Strong-Row Route Is The Target (2026-06-02)

- The Chapter 7 evil family is the three-star shape
  `STAR (STAR (ALTs [a*, (aa)*, ...]))`, represented here by
  `thesis_ch7_evil`. This family is designed to defeat simplifiers that only
  flatten alternatives, remove exact duplicates, or normalize repetition
  tails. A route based only on `rsimp9`/`bsimp9` should therefore not be treated
  as the final cubic-bound candidate.
- The required missing operation is shared-suffix row pruning, e.g. reducing
  `(a + b).c + (a + d).c` to `(a + b).c + d.c`. In this repository that
  operation is implemented in the proof-level `rsimpStrong` route and the
  executable annotated `bsimpStrong` route.
- Existing checked evidence for this route includes
  `thesis_ch7_rsimpStrong_ALTs_prunes_overlap`,
  `thesis_ch7_rsimpStrong_ALTs_overlap_smaller`,
  `thesis_ch7_bsimpStrong_prunes_overlap`,
  `thesis_ch7_evil5_bders_simpStrong_lt_simp8_size_16`, and
  `thesis_ch7_evil5_bders_simpStrong_size_16_under_825`.
- Hence the cubic-bound payout target must be a smoke-tested strong pruning
  route. `rsimp9` is historical scaffolding only and should not be used as a
  candidate or payout artifact.

## Cubic Bound Research Checkpoint: Path9 Tight-Budget Root-Linear Hooks (2026-06-02)

- Added checked tight-member-budget constructor hooks in
  `GeneralRegexBound.thy`:
  `rpath9_tight_member_budget_RALTS_child_root_linearI`,
  `rpath9_tight_member_budget_RSEQ_left_tail_root_linearI`,
  `rpath9_tight_member_budget_RSTAR_tail_root_linearI`, and
  `rpath9_tight_member_budget_RNTIMES_tail_root_linearI`.
- Added the character-alternative specialization
  `rpath9_tight_member_budget_RALTS_RCHARs_tail_le`,
  `rpath9_tight_member_budget_RALTS_RCHARs_root_linear`,
  `rpath9_tight_member_budget_RSTAR_RALTS_RCHARs_root_linear`, and
  `rpath9_tight_member_budget_RNTIMES_RALTS_RCHARs_root_linear`. This gives
  the member-size side a checked analogue of the already-checked one-step
  closure slices for `RALTS` of characters.
- Important design note: `rsimp9` is not the Chapter-7 shared-suffix pruning
  simplifier. It repairs the root-safe/tail-normalization and counted
  repetition route; examples like `(a+b)c + (a+d)c` need the stronger
  `rsimpStrong`/`bsimpStrong` shared-suffix row-prune path. The final cubic
  candidate should therefore promote the strong simplifier route, not claim
  that plain `rsimp9` has that pruning power.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.

## Cubic Bound Research Checkpoint: Path9 Carried-Tail Closure Hooks (2026-06-02)

- Added checked carried-tail universe helpers in `GeneralRegexBound.thy`:
  `rder_path_continuations_acc_RSEQ_rpath9_universeI`,
  `rder_path_continuations_acc_RSTAR_rpath9_universeI`,
  `rder_path_continuations_acc_RNTIMES_rpath9_universeI`,
  `rpath9_atom_frontiers_seq_left_tail_universe`,
  `rpath9_atom_frontiers_star_body_tail_universe`, and
  `rpath9_atom_frontiers_ntimes_body_tail_universe`.
- Added row-level one-step closure splitters:
  `rpder_norm9_path9_atom_frontier_step_RSEQ_left_tailI`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_tailI`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_tailI`. These compose the
  existing `rpder_norm9` constructor splitters with path9 carried-tail
  accumulator obligations, so future `RSEQ`/`RSTAR`/nonzero-`RNTIMES` cases can
  prove the local accumulator invariant and immediately land in the root
  `partial_derivative_path9_atom_frontier_universe`.
- This is progress toward the BR-036 one-step closure proof, not a bounty
  claim. The remaining hard step is still the root-owned induction that proves
  those local carried-tail accumulator obligations for the full non-backref
  fragment, plus the matching linear member-size premise.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.

## Strong-Row Cubic Interface (2026-06-02)

- Added the checked expression-level bridge for the proof-level strong row
  route:
  `row_group_deep_nf_rpd_der_strong`,
  `row_group_deep_nf_rpd_der_strong_rsimp9`,
  `row_group_nf_rpd_der_strong`,
  `row_group_nf_rpd_der_strong_rsimp9`, and
  `rsize_rpd_der_strong_cubic`. These connect the row-list shape invariant
  and the existing one-step cubic size budget to `rpd_der_strong` itself.
  This is support plumbing only, not a BR-036 payout: the remaining hard
  theorem is still root-owned closure/cardinality for repeated strong rows.
- Added the annotated one-step size counterpart in `FBound.thy`:
  `asizes_bpder_norm_list_cubic` and `asize_bp_der_strong_cubic`.
  These transfer the existing proof-level normalized-row cubic one-step
  budget through `rerase` and show that `bp_der_strong` inherits that
  immediate size bound on the non-backref fragment. This does not prove a
  repeated cubic bound for `bpders_strong_rows`; it is the annotated bridge
  needed before the future root-owned universe closure theorem can be used in
  the executable layer.
- Added the checked no-go
  `bsimpStrong_prune_pair_exact_rerase_counterexample`. It records that the
  executable pair prune does not syntactically erase to the proof-level
  `rsimpStrong_prune_pair` on all inputs: duplicate later alternatives can be
  normalized away at different layers. Future transfer proofs should use the
  checked semantic bridge `RL_rerase_bsimpStrong_prune_pair_with_earlier` and
  row-contextual accounting facts, not an exact `rerase` equation.
- Added the annotated local closure splitters
  `map_rerase_flts_bpder_strong_list_subsetI`,
  `map_rerase_flts_concat_map_bpder_strong_list_subsetI`,
  `map_rerase_bpder_strong_rows_local_subsetI`, and
  `map_rerase_bpder_strong_rows_norm_prune_subsetI`. These factor executable
  `bpder_strong_rows` closure into the same two local obligations as the
  proof-level route: normalized member closure after `bsimpStrong`, and
  preservation by the shared-suffix row-prune pass. This avoids relying on the
  checked-false exact erasure equation for `bsimpStrong_prune_pair`.
- Added the honest executable later-shared closure bridge for that same route:
  `map_rerase_bsimpStrong_prune_pair_later_shared_subsetI`,
  `map_rerase_bsimpStrong_prune_rows_later_shared_subsetI`,
  `map_rerase_bpder_strong_rows_norm_later_shared_subsetI`,
  `map_rerase_bpders_strong_rows_norm_later_shared_subsetI`,
  `asizes_bpders_strong_rows_norm_later_shared_finite_universe_boundI`, and
  `asizes_bpders_strong_rows_norm_later_shared_cubic_universe_boundI`. The
  shared premise is stated at the executable syntax produced by
  `bsimpStrong_prune_pair`, then projected through `rerase`; it deliberately
  does not pretend that executable pruning syntactically equals the
  proof-level `rsimpStrong_prune_pair`.
- Added and checked the conditional finite-universe interface for the
  proof-level strong row pipeline:
  `rpders_strong_rows_subsetI`, `rpders_strong1_rows_subsetI`,
  `rsizes_distinct_finite_universe_bound`,
  `rsizes_rpders_strong_rows_finite_universe_boundI`,
  `rsizes_rpders_strong1_rows_finite_universe_boundI`,
  `rsizes_rpders_strong_rows_cubic_universe_boundI`, and
  `rsizes_rpders_strong1_rows_cubic_universe_boundI`.
- The key design point is that the closure premise is row-list based:
  `set xs <= U ==> set (rpder_strong_rows c xs) <= U`. This is necessary
  because `rsimpStrong_prune_rows` performs cross-row pruning after all
  one-step rows are collected; a per-expression closure premise would hide
  exactly the interaction the Chapter-7 simplifier is meant to exploit.
- This is only a checked interface, not a bounty claim for the cubic theorem.
  The next proof task remains instantiating the finite universe and one-step
  closure, especially the carried-continuation cases for `RSEQ`, `RSTAR`, and
  nonzero `RNTIMES`.
- Added checked local closure splitters for the proof-level strong row step:
  `rflts_rpder_strong_list_subsetI`,
  `rflts_concat_map_rpder_strong_list_subsetI`,
  `rpder_strong_rows_local_subsetI`, and
  `rpder_strong_rows_norm_prune_subsetI`. These reduce the strong one-step
  closure premise to two local obligations: each normalized partial derivative
  member must stay in the chosen universe after `rsimpStrong` and flattening,
  and the shared-suffix row-prune pass must preserve that universe.
- Further factored the row-prune obligation with
  `rsimpStrong_prune_pair_shared_subsetI`,
  `rsimpStrong_prune_against_rows_pair_subsetI`,
  `rsimpStrong_prune_rows_acc_pair_subsetI`,
  `rsimpStrong_prune_rows_pair_subsetI`, and
  `rsimpStrong_prune_rows_shared_subsetI`. The remaining prune-side proof can
  now focus exactly on the Chapter-7 shared-suffix result
  `rsimp7_SEQ_atom (rsimp_ALTs (...rprune_eq_against...)) k`, rather than on
  the surrounding row scanner.
- Added the direct composed strong-row closure/cubic hooks
  `rpder_strong_rows_norm_shared_subsetI`,
  `rpders_strong_rows_norm_shared_subsetI`,
  `rsizes_rpders_strong_rows_norm_shared_finite_universe_boundI`, and
  `rsizes_rpders_strong_rows_norm_shared_cubic_universe_boundI`. These package
  the remaining proof-level target as three explicit universe obligations:
  flat closure of `U`, closure of normalized derivative members after
  `rsimpStrong`, and closure of the isolated shared-suffix prune result.
- Added row-normal variants that discharge the flat-closure obligation from
  either `nonalt q` plus `q != RZERO` style row facts or the existing
  `row_nf` predicate:
  `rflts_singleton_nonalt_nonzero_subsetI`,
  `rflts_singleton_row_nf_subsetI`,
  `rpders_strong_rows_norm_shared_flat_rows_subsetI`,
  `rpders_strong_rows_norm_shared_row_nf_subsetI`, and the matching finite/
  cubic bound hooks. This makes the next concrete universe instantiation
  cleaner: maintain row normal form, then focus only on normalized derivative
  closure and shared-suffix prune closure.
- Strengthened that row-normal layer with the checked helper
  `row_nf_rsimp7_SEQ_atom` and the singleton bridge
  `row_nf_rflts_singleton`. The same checkpoint also records the obstruction
  `strong_shared_prune_result_can_leave_row_nf`: shared-suffix pruning can
  produce a row of shape `RSEQ (RALTS [...]) k`, so a future concrete universe
  cannot consist only of strict `row_nf` rows unless the prune result is
  separately collapsed or the universe explicitly admits grouped left
  alternatives.
- Added the first checked grouped-row normal form for that enlarged route:
  `row_group_nf`. It admits ordinary row-normal rows, normalized alternatives,
  and grouped-left sequence rows, while remaining closed under singleton
  flattening, `rsimp_ALTs` normalization, and `rsimp4/rsimp7` sequence atoms.
  The key local theorem is `row_group_nf_shared_prune_result`, which shows the
  isolated Chapter-7 shared-suffix prune result is grouped-row normal whenever
  the later row alternatives and suffix are grouped-row normal. This is not a
  finite-universe proof yet; it is the checked shape invariant the finite
  root-owned universe should refine.
- Proved that the proof-level stronger simplifier preserves this grouped-row
  shape. The checked chain
  `row_group_nf_rsimpStrong_prune_pair`,
  `row_group_nf_rsimpStrong_prune_against_rows`,
  `row_group_nf_rsimpStrong_prune_rows`,
  `row_group_nf_rsimpStrong_ALTs`, and `row_group_nf_rsimpStrong` shows the
  Chapter-7 prune scanner and recursive `rsimpStrong` do not leave the
  enlarged normal-form class. This narrows the remaining concrete-universe
  work to proving that normalized derivative members enter a finite
  root-owned subset of this shape class.
- Added the checked deep version of that shape invariant:
  `row_group_deep_nf`. The shallow predicate `row_group_nf` is not enough for
  derivative iteration because it deliberately treats `RSTAR r` and
  `RNTIMES r n` as row-shaped without remembering that their bodies can be
  exposed by `rpder_list`. The new checked chain
  `row_group_deep_nf_rsimp4_SEQ_atom`,
  `row_group_deep_nf_rsimp7_SEQ_atom`,
  `row_group_deep_nf_rsimpStrong`,
  `row_group_deep_nf_rpder_list`,
  `row_group_deep_nf_rpder_norm_list`,
  `row_group_deep_nf_rpder_strong_list`,
  `row_group_deep_nf_rpder_strong_rows`, and
  `row_group_deep_nf_rpders_strong_rows` proves that the strong row derivative
  iteration preserves the recursive grouped invariant. The exported
  `row_group_nf_rpders_strong_rows` corollary recovers the shallow grouped-row
  shape for every reached row. This is still a shape invariant, not the final
  finite universe or cubic bound.
- Connected the deep grouped invariant to the existing root-safe normalizer:
  `row_group_deep_nf_rsimp9` proves every `rsimp9 r` is deep-grouped, including
  recursively normalized `RNTIMES` bodies. The entry lemmas
  `row_group_deep_nf_rpders_strong1_rows_rsimp9` and
  `row_group_nf_rpders_strong1_rows_rsimp9` now say that the strong-row
  iteration started from `rsimp9 r` stays in the deep invariant and therefore
  has grouped-row shape. This closes the initial-shape gap left by the previous
  checkpoint; the remaining work is still a finite root-owned universe with
  cubic cardinality/member-size bounds.
- Localized the Chapter-7 shared-prune closure interface. The new checked
  lemmas `rsimpStrong_prune_pair_later_shared_subsetI`,
  `rsimpStrong_prune_rows_later_shared_subsetI`,
  `rpder_strong_rows_norm_later_shared_subsetI`,
  `rpders_strong_rows_norm_later_shared_subsetI`, and the matching finite/
  cubic hooks replace the previous unconditional shared premise by the weaker
  obligation that the later row `RSEQ (RALTS rrs) k` already belongs to the
  candidate universe `U`. This is closer to a root-owned finite-universe proof:
  a concrete universe only has to close shared-suffix deletion for rows it can
  actually contain, not for arbitrary `lrs rrs k`. Still no final cubic theorem
  or bounty claim.
- Added checked full-cover prune facts for both the proof-level and executable
  strong simplifiers. In `GeneralRegexBound.thy`,
  `rprune_eq_against_subset_empty` and `rsimpStrong_prune_pair_full_cover`
  prove that a later row whose alternatives are all already covered collapses
  to `RZERO`, and `rsimpStrong_ALTs_full_cover_shared_suffix` records that a
  two-row shared-suffix alternative then keeps only the earlier row. In
  `BlexerSimp.thy`, `prune_eq1_against_all_covered_empty` and
  `bsimpStrong_prune_pair_full_cover` check the same mechanism for annotated
  `arexp` rows up to `eq1`. This is the precise Chapter-7 deletion atom needed
  for future row-count/size accounting; it is still not a general cubic bound.
- Lifted the executable full-cover fact from pair pruning to the actual
  alternative simplifier surface. `bsimpStrong_AALTs_full_cover_shared_suffix`
  proves that `bsimpStrong_AALTs` on two shared-suffix rows fuses only the
  earlier row when the later alternatives are all covered up to `eq1`, and
  `bsimpStrong_AALTs_full_cover_shared_suffix_Nil` records the top-level
  `[]`-bit specialization used by `bp_der_strong`. This makes the Chapter-7
  deletion mechanism available at the same surface where executable row
  derivatives call it.
- Added row-output versions of the full-cover deletion fact. The proof-level
  lemmas `rflts_rsimpStrong_prune_rows_full_cover_shared_suffix` and
  `rdistinct_rflts_rsimpStrong_prune_rows_full_cover_shared_suffix` show that
  after row pruning, flattening, and duplicate removal, a covered two-row
  shared-suffix list contains only the earlier row. The executable counterparts
  `flts_bsimpStrong_prune_rows_full_cover_shared_suffix` and
  `distinctWith_flts_bsimpStrong_prune_rows_full_cover_shared_suffix` do the
  same for `arexp` using `eq1_member`. These facts are closer to
  `rpder_strong_rows`/`bpder_strong_rows`, whose definitions inspect the
  flattened pruned row list directly.
- Connected that deletion atom to the actual derivative-row surfaces. The
  checked lemmas `rpder_strong_rows_shared_suffix` and
  `bpder_strong_rows_shared_suffix` say that if the raw one-step derivative
  rows flatten to two shared-suffix rows, then the real strong-row derivative
  output is exactly the earlier row plus the later row with already-covered
  alternatives removed and normalized. The full-cover specializations
  `rpder_strong_rows_full_cover_shared_suffix` and
  `bpder_strong_rows_full_cover_shared_suffix` say that if the later row is
  fully covered by the earlier row, the real output is exactly the earlier
  row. This is a small but important accounting bridge: future row-count
  bounds can cite the executable/proof pipeline itself, rather than only the
  internal prune helper.
- Added direct size-accounting views of the same bridge:
  `rsizes_rpder_strong_rows_full_cover_shared_suffix` and
  `asizes_bpder_strong_rows_full_cover_shared_suffix`. These are deliberately
  narrow facts for the Chapter-7 overlap atom: they turn full-cover deletion
  into a one-row `rsizes`/`asizes` equation without unfolding the whole
  derivative-row pipeline in later bound proofs.
- Added partial-overlap size-accounting lemmas for the same surface:
  `rsize_rsimpStrong_shared_prune_result_le`,
  `rsizes_rpder_strong_rows_shared_suffix_le`,
  `asize_bsimpStrong_shared_prune_result_le`, and
  `asizes_bpder_strong_rows_shared_suffix_le`. These facts bound the actual
  strong-row derivative output by the earlier shared-suffix row plus the later
  row after `rprune_eq_against`/`prune_eq1_against`. This is the accounting
  form needed for the thesis Chapter-7 family, where the second row is often
  partially rather than fully covered.
- Added strict versions for genuine overlap:
  `rsizes_rprune_eq_against_lt`,
  `rsizes_rpder_strong_rows_shared_suffix_lt`,
  `asizes_prune_eq1_against_lt`, and
  `asizes_bpder_strong_rows_shared_suffix_lt`. These prove that if the later
  shared-suffix row contains at least one covered alternative, the actual
  strong-row derivative output is strictly smaller than keeping both raw rows.
  This is a general theorem-level version of the Chapter-7 overlap-prune
  intuition, not just an `eval` regression.
- Added semantic erasure bridges around the executable strong simplifier:
  `RL_rerase_bsimpStrong_rsimpStrong`,
  `RL_rerase_bders_simpStrong_rders_simpStrong`,
  `eq1_member_rerase`, `map_rerase_prune_eq1_against`, and
  `RL_rerase_bsimpStrong_prune_pair_with_earlier`. The attempted exact
  erasure equation for `bsimpStrong_prune_pair` is too strong for the current
  definitions: executable `bsimp_AALTs` erases to `rsimp_ALTs pruned`, while
  the proof-level strong pair normalizes with `rdistinct (rflts pruned)` first.
  Use the checked language bridge in row-scanner contexts instead of forcing
  syntactic equality.
- Added the first row-count accounting layer for the Chapter-7 prune route.
  The proof-level lemmas `length_rdistinct_le`,
  `length_rprune_eq_against_le`, `length_rprune_eq_against_lt`,
  `length_rpder_strong_rows_full_cover_shared_suffix`, and
  `length_rpder_strong_rows_shared_suffix_le` show that duplicate removal and
  shared-suffix pruning do not increase candidate rows, with strict prune
  shrinkage when a covered alternative is actually present. The executable
  counterparts are `length_distinctWith_le`, `length_prune_eq1_against_le`,
  `length_prune_eq1_against_lt`,
  `length_bpder_strong_rows_full_cover_shared_suffix`, and
  `length_bpder_strong_rows_shared_suffix_le`. These are deliberately narrow
  accounting facts, not a final cubic bound.
- Added the next row-scanner accounting layer. The checked facts
  `length_rsimpStrong_prune_rows_acc` and `length_rsimpStrong_prune_rows`
  show that the proof-level strong prune scanner itself emits exactly one
  row per input row before flattening/duplicate-removal; the analogous
  executable facts are `length_bsimpStrong_prune_rows_acc` and
  `length_bsimpStrong_prune_rows`. The general derivative-row bounds
  `length_rpder_strong_rows_le_pruned` and
  `length_bpder_strong_rows_le_pruned` then expose the exact place where row
  count can only shrink: final flattening and duplicate/subsumption removal.
  This keeps the future cubic argument focused on the finite candidate
  universe and on Chapter-7 shared-suffix deletion, rather than on the
  scanner recursion.
- Added direct candidate-count hooks for future finite-universe instantiations.
  On the proof side, `length_rpders_strong_rows_finite_universe_boundI`,
  `length_rpders_strong1_rows_finite_universe_boundI`,
  `length_rpders_strong_rows_card_boundI`, and
  `length_rpders_strong1_rows_card_boundI` show that once a finite
  root-owned universe is closed under the strong-row step, the number of
  reachable rows is bounded by `card U`. The annotated counterparts
  `length_bpders_strong_rows_finite_universe_boundI`,
  `length_bpders_strong1_rows_finite_universe_boundI`,
  `length_bpders_strong_rows_card_boundI`, and
  `length_bpders_strong1_rows_card_boundI` prove the same fact through
  `rerase`. This separates the cardinality half of the cubic argument from
  the member-size half already handled by the `rsizes`/`asizes` hooks.
- Checked a design no-go for reusing the old cubic
  `partial_derivative_universe` as the strong-row closure target:
  `rsimpStrong_prune_pair_leaves_partial_derivative_universe`. The witness has
  two shared-suffix rows whose later left alternative list is partially
  covered; pruning produces a new grouped-left row
  `RSEQ (RALTS [b,c]) z` that is neither a root subterm nor an allowed
  `RSEQ p k` with `p` from the old subterm set. This confirms that the next
  viable finite universe must explicitly account for pruned grouped
  alternatives or use a different potential/accounting argument; simply
  pointing the strong-row hooks at `partial_derivative_universe` is false.
- Exposed the primitive strict-decrease theorem behind that potential route:
  `rsize_rsimpStrong_prune_pair_shared_suffix_lt` and the executable
  counterpart `asize_bsimpStrong_prune_pair_shared_suffix_lt`. These say that
  whenever a previous shared-suffix row covers at least one alternative of a
  later row, the pair prune strictly shrinks the later row itself. The earlier
  strict derivative-row facts can now be derived or reused at a higher level,
  while future scanner/potential proofs can cite the primitive pair theorem
  directly.
- Lifted that strict decrease one step into the row scanner. The checked
  `rsize_rsimpStrong_prune_against_rows_head_shared_suffix_lt` and
  `asize_bsimpStrong_prune_against_rows_head_shared_suffix_lt` prove that if
  the current head of the seen list is a shared-suffix row covering at least
  one alternative of the row being scanned, then the whole
  `*_prune_against_rows` pass is strictly smaller than the original row; the
  remaining seen rows can only decrease size further. The deliberately narrow
  "head" statement avoids the false-looking shortcut that any matching row
  anywhere in `seen` is enough without tracking how earlier seen rows have
  already rewritten the later row.
- Added the two-row scanner strict-decrease surface:
  `rsizes_rsimpStrong_prune_rows_two_shared_suffix_lt` and
  `asizes_bsimpStrong_prune_rows_two_shared_suffix_lt`. These lift the
  helper-level head theorem to the actual `*_prune_rows` scanner on
  `[earlier, later]`, proving that the total row-size budget strictly shrinks
  when the second row shares the suffix and has any alternative covered by the
  first. This is the direct row-scanner potential fact needed before trying to
  generalize strict shrinkage to longer row lists.
- Lifted the same strict-decrease fact to the actual alternative simplifier
  surface. The new bridge lemmas `rsize_rsimpStrong_ALTs_le_pruned` and
  `asize_bsimpStrong_AALTs_le_pruned` expose the size bound after the
  `*_prune_rows` pass but before the final alternative constructor cap. The
  checked theorems `rsize_rsimpStrong_ALTs_two_shared_suffix_lt` and
  `asize_bsimpStrong_AALTs_two_shared_suffix_lt` then show that a two-row
  shared-suffix overlap strictly shrinks the proof-level `rsimpStrong_ALTs`
  and executable `bsimpStrong_AALTs` surfaces themselves. This connects the
  Chapter-7 potential decrease to the actual stronger simplifier entry point.
- Added the checked direct no-go corollary
  `current_path_frontier_universe_not_closed_under_rsimp4_derivative`. This
  packages the existing middle-alternative witness into the statement that
  old `partial_derivative_path_frontier_universe` is not closed under
  `rfrontier (rsimp4 (rder a root))`. Future closure work should not target
  that universe directly; use the later `path9`, `carry9`, or strong-row route.

## Annotated Strong-Row Cubic Interface (2026-06-02)

- Added and checked the annotated counterpart of the finite-universe
  bookkeeping layer for the executable strong-row pipeline:
  `distinct_map_rerase_bpder_strong_rows`,
  `distinct_map_rerase_bpders_strong_rows`,
  `map_rerase_bpders_strong_rows_subsetI`,
  `asizes_rsizes_rerase`,
  `asizes_distinct_rerase_finite_universe_bound`,
  `asizes_bpders_strong_rows_finite_universe_boundI`, and
  `asizes_bpders_strong1_rows_finite_universe_boundI`.
- Added checked one-step size-control facts for the executable annotated
  route: `asizes_bpder_strong_list_le`,
  `asizes_concat_map_bpder_strong_list_le`,
  `asizes_bpder_strong_rows_le`, `asize_bp_der_strong_le_asizes`, and
  `asize_bp_der_strong_le_rows`.
- Added checked annotated cubic-accounting hooks:
  `asizes_bpders_strong_rows_cubic_universe_boundI`,
  `asizes_bpders_strong1_rows_cubic_universe_boundI`,
  `asize_bp_der_strong_finite_universe_boundI`, and
  `asize_bp_der_strong_cubic_universe_boundI`.
- Design result: future annotated bounds can now reuse the same row-list
  finite-universe discipline as the proof-level `rrexp` pipeline, but with
  an explicit `rerase` bridge. The closure premise is still intentionally
  conditional:
  `set (map rerase ars) <= U ==> set (map rerase (bpder_strong_rows c ars)) <= U`.
  This is not the final cubic theorem and no bounty is claimed.

## Path9 Raw-Tail Bridge (2026-06-01)

- Added and checked `rpath9_tail`, a compact helper that turns a raw
  continuation spine into the normalized tail shape carried by
  `rpath9_atom_frontier_acc`.
- Checked the first linear member-size bridge:
  `rsize_rpath9_tail_le`, `rfrontier_rpath9_tail_member_size_le`,
  `rfrontier_rsimp7_SEQ_atom_rsimp9_rpath9_tail_member_size_le`, and
  `rfrontier_rpath9_tail_RSEQ_member_size_le`. These facts say the normalized
  tail and its frontier members remain bounded by the raw continuation size,
  so the remaining BR-036 member-size proof can reason about raw continuation
  structure instead of repeatedly unfolding the normalized accumulator.
- Added the generic frontier helper
  `rfrontier_rsimp7_SEQ_atom_rsimp9_member_size_le` and the `RCHAR` raw-tail
  base cases
  `rpath9_atom_frontier_acc_RCHAR_rpath9_tail_member_size_le` and
  `rpath9_atom_frontier_acc_RCHAR_rpath9_tail_RSEQ_member_size_le`. These are
  the base leaves for the next carried-continuation induction.
- Added checked raw-tail handoff lemmas for carried constructors:
  `rpath9_atom_frontier_acc_RSEQ_rpath9_tail_member_sizeI`,
  `rpath9_atom_frontier_acc_RSTAR_rpath9_tail_member_sizeI`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_rpath9_tail_member_sizeI`. These
  expose the recursive obligations using `rpath9_tail (RSEQ ... k)` instead
  of the expanded `rsimp7_SEQ_atom (rsimp9 ...) (rpath9_tail k)` form.
- Added checked top-level member-size interfaces
  `rpath9_atom_frontiers_RSEQ_member_size_rpath9_tailI`,
  `rpath9_atom_frontiers_RSTAR_member_size_rpath9_tailI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_size_rpath9_tailI`. These let
  the outer `rpath9_atom_frontiers` cases consume the raw-tail obligations
  directly, rather than asking later proofs to re-expand the top-level
  `RONE` continuation.
- Added `rpath9_tail_prefix_continuation_bound_counterexample`, which shows
  that a continuation-only member-size budget is too strong for long prefixes:
  consuming the first atom of `a.(b.c)` under a carried `d` tail can expose
  `b.(c.d)`, larger than the carried `d.1` continuation. The follow-up
  parent-budget interfaces
  `rpath9_atom_frontiers_RSEQ_member_size_rpath9_tail_parentI`,
  `rpath9_atom_frontiers_RSTAR_member_size_rpath9_tail_parentI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_size_rpath9_tail_parentI`
  are now checked and should be the route for the remaining linear
  member-size proof.
- Added checked route-blocking counterexamples
  `path9_frontiers_not_subset_norm9_frontier_universe` and
  `path9_frontiers_not_subset_original_frontier_universe`. These rule out two
  tempting shortcuts: embedding `rpath9_atom_frontiers r` directly into the
  old frontier universe of either `rsimp9 r` or the original `r`. The remaining
  route must use the dedicated path9 universe/member-size accounting.
- Added the recursive path9 member-size budget
  `rpath9_member_budget`/`rpath9_member_budget_list` and checked
  `rpath9_atom_frontier_acc_rpath9_tail_member_budget` plus
  `rpath9_atom_frontiers_member_budget`. This gives a controlled induction
  target matching the `rpath9_atom_frontier_acc` recursion, instead of trying
  to prove the final linear bound in one monolithic pass.
- Checked `rpath9_member_budget_nested_star_not_linear`, which shows that the
  raw budget is still too coarse for the final linear bound: nested stars make
  it count an unnormalized carried tail. Added the tighter budget layer
  `rpath9_tight_member_budget`/`rpath9_tight_member_budget_list`, the checked
  soundness theorem
  `rpath9_atom_frontier_acc_rpath9_tail_tight_member_budget`, the top-level
  interface `rpath9_atom_frontiers_tight_member_budget`, and the sanity fact
  `rpath9_tight_member_budget_nested_star_linear_sanity`.
- Checked `rpath9_tight_member_budget_le_member_budget` and its list helper,
  proving the tight layer is a monotone strengthening of the raw budget rather
  than a different over-approximation. The witness
  `rpath9_tight_member_budget_nested_star_less_raw` also confirms the tight
  layer strictly improves the exact nested-star case where the raw budget
  exceeded the intended linear bound. Next step: prove the
  top-level estimate
  `rpath9_tight_member_budget r RONE <= Suc (rsize r + rsize r)`, or a
  slightly larger linear bound with an updated cubic constant.
- Added the checked bridge from that remaining budget inequality to the
  existing path9 cubic hook:
  `rpath9_atom_frontiers_tight_member_budget_linearI`,
  `partial_derivative_path9_atom_frontier_universe_member_size_tight_budgetI`,
  and `rsizes_rpders_norm19_rows_rsimp9_path9_tight_budget_cubicI`. This
  reduces the remaining cubic member-size premise to the single tight-budget
  estimate plus the already-separate one-step closure premise.
- Added the local tail-size bridge
  `rpath9_tail_RSEQ_size_le`, and checked the first tight-budget constructor
  interfaces:
  `rpath9_tight_member_budget_list_boundI`,
  `rpath9_tight_member_budget_RALTS_boundI`,
  `rpath9_tight_member_budget_RSEQ_boundI`,
  `rpath9_tight_member_budget_RSTAR_boundI`, and
  `rpath9_tight_member_budget_RNTIMES_nonzero_boundI`. These do not close
  BR-036 by themselves; they record the right proof shape after scratch
  testing showed that both a bare top-level induction and an arbitrary
  continuation linear invariant are too coarse for `RSTAR`. The remaining
  proof should use a root-owned/carried-continuation invariant and discharge
  these constructor obligations locally.
- Added the first path9 one-step self interfaces:
  `rpder_norm9_path9_atom_frontier_step_RALTS_selfI` closes the alternative
  case directly from child self-closure, and
  `rpder_norm9_path9_atom_frontier_step_RSEQ_selfI` packages the nullable
  right-child lift into the parent universe. The `RSEQ` theorem now leaves
  only the genuinely hard left-continuation bridge as an explicit premise:
  rows produced from `rder_path_continuations_acc c r1
  (rsimp4_SEQ_atom r2 RONE)` must be lifted into the current path9 universe.
- Added the first checked left-continuation bridge slice for that `RSEQ`
  blocker. The helper `rder_path_continuations_acc_RCHAR_left_path9_stable`
  proves the `RCHAR`-left bridge whenever the right continuation is already
  norm-tail stable:
  `rsimp9 (rsimp4_SEQ_atom r2 RONE) = rsimp9 r2` and
  `rsimp4_SEQ_atom (rsimp9 r2) RONE = rsimp9 r2`. The checked constructor
  leaves `rder_path_continuations_acc_RCHAR_left_path9_RZERO/RONE/RCHAR/
  RSTAR/RNTIMES` close the obvious stable right-tail cases. This is progress
  only, not a BR-036 payout claim; the remaining hard work is to prove the
  stability interface for `RALTS` and nested `RSEQ` without a slow global
  `auto`.
- Added the first reusable norm-tail stability helper layer:
  `rsimp4_SEQ_atom_RONE_stable_rsimp7_SEQ_atom`,
  `rsimp4_SEQ_atom_RONE_stable_rsimp_ALTs`, and
  `rsimp4_SEQ_atom_RONE_stable_rdistinct`. These facts are deliberately
  local and constructor-guided; they avoid the slow global associativity proof
  shape seen in scratch, and are intended to close the remaining `RALTS` and
  nested-sequence right-tail stability cases for the `RSEQ` bridge.
- Added the checked carried-continuation splitter layer
  `rflts_singleton_rsimp9_frontier`,
  `rder_path_continuations_acc_RCHAR_frontierI`,
  `rder_path_continuations_acc_RALTS_carriedI`,
  `rder_path_continuations_acc_RSEQ_carriedI`,
  `rder_path_continuations_acc_RSTAR_carriedI`, and
  `rder_path_continuations_acc_RNTIMES_carriedI`. These are intentionally
  universe-parametric: later path9 closure proofs can decompose the derivative
  path structurally and discharge the actual target universe locally, instead
  of unfolding the whole derivative and simplifier at once.
- Added the checked raw-to-path9 `RCHAR` tail bridge:
  `rder_path_continuations_acc_RCHAR_path9_tail` and
  `rder_path_continuations_acc_RCHAR_raw_left_path9`. These show that a raw
  `rsimp4` continuation emitted at a character leaf, after `rsimp9` and
  flattening, lands in the normalized `rsimp7_SEQ_atom (rsimp9 k) RONE` tail
  used by `rpath9_atom_frontier_acc`, and therefore in the corresponding
  `RSEQ (RCHAR _) k` parent universe. This is the base case needed for a
  future carried-continuation set induction. A direct nested-`RSEQ` attempt
  exposed that the continuation target cannot be compressed to a single
  frontier: recursive simplification can expose child frontier members, so the
  next theorem needs a carried set/accumulator statement.
- Added the first rpath9-tail carried splitter package:
  `rsimp7_SEQ_atom_rsimp9_RONE`, `rpath9_tail_rsimp9`,
  `rtail_nf_rpath9_tail`,
  `rder_path_continuations_acc_RCHAR_rpath9_tail`,
  `rder_path_continuations_acc_RALTS_rpath9_tailI`,
  `rder_path_continuations_acc_RSEQ_rpath9_tailI`,
  `rder_path_continuations_acc_RSTAR_rpath9_tailI`, and
  `rder_path_continuations_acc_RNTIMES_rpath9_tailI`. This aligns the
  derivative-side carried splitters with the existing path9 member-budget
  recursion: `RSEQ`, `RSTAR`, and nonzero `RNTIMES` now expose recursive
  obligations under `rpath9_tail (RSEQ ... k)`, exactly like the size-accounting
  layer. A scratch attempt at a global `rsimp7_SEQ_atom` associativity lemma
  was rejected because it immediately produced large nested-sequence goals; the
  next proof should introduce a small relation between the derivative
  continuation `rsimp4_SEQ_atom ... k` and the path-side raw spine
  `RSEQ ... k`, rather than forcing syntactic associativity.
- Added the first checked one-step path9 leaves over that layer:
  `rder_path_continuations_acc_RCHAR_root_path9_stable` plus the `RSTAR` and
  `RNTIMES` root leaves, the stable package
  `rpder_norm9_path9_atom_frontier_step_RSEQ_RCHAR_stable` with
  `RZERO`/`RONE`/`RCHAR`/`RSTAR`/`RNTIMES` right-tail instances, and the
  character-body base cases
  `rpder_norm9_path9_atom_frontier_step_RSTAR_RCHAR` and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_RCHAR`. The counted case uses
  the path9 frontier of the predecessor count directly, not a false
  universe-subset shortcut between different counts.
- Added and checked the RALTS-of-characters left bridge for the same stable
  right-tail lane: `rpath9_atom_frontiers_seq_alt_left_subset`,
  `rpath9_atom_frontiers_seq_alt_left_universe`,
  `rder_path_continuations_acc_RALTS_RCHARs_left_path9_stable`, and
  `rpder_norm9_path9_atom_frontier_step_RSEQ_RALTS_RCHARs_stable` with
  `RZERO`/`RONE`/`RCHAR`/`RSTAR`/`RNTIMES` right-tail instances. This packages
  a useful one-step closure case for character alternatives under `RSEQ`;
  general `RALTS` and nested-`RSEQ` carried tails remain open.
- Added the matching checked body bridges for `RSTAR` and nonzero-count
  `RNTIMES` over character alternatives:
  `rder_path_continuations_acc_RALTS_RCHARs_root_path9_RSTAR`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_RALTS_RCHARs`,
  `rder_path_continuations_acc_RALTS_RCHARs_root_path9_RNTIMES`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_RALTS_RCHARs`. The counted
  proof keeps the zero-predecessor branch separate because it contributes
  `RONE` directly to the universe, not through the body frontier.
- Connected the character-alternative bridge to the actual normalized
  alternative output used by `rsimp9`: the checked
  `rpder_norm9_path9_atom_frontier_step_RSEQ_rsimp_ALTs_RCHARs_stable`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_rsimp_ALTs_RCHARs`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_rsimp_ALTs_RCHARs` split the
  `rsimp_ALTs` result into empty, singleton, and genuine-`RALTS` cases. This
  removes a small but recurring proof gap between normalized alternatives and
  the raw `RALTS` bridge lemmas.
- Added the next bridge to the literal `rsimp9 (RALTS rs)` output. The helper
  lemmas `rflts_RCHARs_eq`, `RCHARs_rflts`, `RCHARs_rflts_map_rsimp9`,
  `RCHARs_rdistinct`, and `RCHARs_rdistinct_rflts_map_rsimp9` show that a
  character-only alternative list remains character-only after
  `map rsimp9`, `rflts`, and `rdistinct`. The checked closure packages
  `rpder_norm9_path9_atom_frontier_step_RSEQ_rsimp9_RALTS_RCHARs_stable`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_rsimp9_RALTS_RCHARs`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_rsimp9_RALTS_RCHARs` now apply
  directly to `rsimp9 (RALTS rs)` in the character-alternative case.
- Added checked normalized-tail RSEQ bridges:
  `rder_path_continuations_acc_RCHAR_left_path9_rsimp9`,
  `rder_path_continuations_acc_RCHAR_alt_left_path9_rsimp9`,
  `rder_path_continuations_acc_RALTS_RCHARs_left_path9_rsimp9`,
  `rpder_norm9_path9_atom_frontier_step_RSEQ_RCHAR_rsimp9`,
  `rpder_norm9_path9_atom_frontier_step_RSEQ_RALTS_RCHARs_rsimp9`,
  `rpder_norm9_path9_atom_frontier_step_RSEQ_rsimp_ALTs_RCHARs_rsimp9`, and
  `rpder_norm9_path9_atom_frontier_step_RSEQ_rsimp9_RALTS_RCHARs_rsimp9`.
  These instantiate the new `rsimp9` right-tail stability invariant for
  arbitrary normalized right tails `rsimp9 r2`, replacing the older
  constructor-by-constructor RZERO/RONE/RCHAR/RSTAR/RNTIMES packages in this
  character-left lane.
- Build: full local CI PASS with no certificate via
  `powershell -NoProfile -ExecutionPolicy Bypass -File
  agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -NoCertificate
  -Role admin -SessionTimeoutSeconds 240`.
- Next smallest safe step: generalize the carried-left closure beyond
  character-only alternatives, especially the nested `RSEQ` left branch, using
  the normalized-tail bridges rather than adding more right-tail constructor
  cases.
- Build: direct Isabelle `Posix` build passed after removing stale CLI Isabelle
  build processes that were holding resources from earlier runs.

## Cubic Row-Universe Checkpoint (2026-05-31)

- Added and checked the new root-safe simplifier layer `rsimp8`/`bsimp8`.
  This is the next cubic-size design after discovering that eager `rsimp7`
  can increase the root size by distributing `(a + b) · (c + d)` into a
  product row. `rsimp8` keeps star cleanup and prefix-star absorption, but
  uses only the atom-level sequence simplifier at roots.
- Checked artifacts for this layer include `RL_rsimp8`, `RL_rders_simp8`,
  `bsimp8_rerase`, `rders_simp8_size`, `RL_rerase_bders_simp8`,
  `rsize_rsimp8_le`, and
  `rsizes_rpders_norm17_rows_rsimp8_live_row_cubicI`. This gives a conditional
  cubic interface whose bound is w.r.t. the original `rsize r`, not the
  possibly inflated `rsize (rsimp7 r)`.
- Added `rsimp7_can_increase_root_size`, a checked obstruction showing that
  full `rsimp7` is not safe as the root normalizer for an original-regex-size
  cubic theorem.
- Added `rsimp8_live_row_universe_not_closed`, a checked obstruction showing
  that the first root-safe interface is still too narrow: for
  `(((1+a).a))*`, a normalized derivative row contains
  `((a+(a.a)))*`, which is outside
  `partial_derivative_live_row_universe (rsimp8 r)`. The next invariant must
  include controlled normalized star images, or the root simplifier must
  normalize nullable-left sequence bodies without allowing the general
  `(a+b)·(c+d)` size blow-up.
- Added and checked the next row driver `norm18`: `rpder_norm8_list`,
  `rpder_norm8_rows`, `rpders_norm18_rows`, and the language facts
  `RLS_rpders_norm18_rows`/`RL_rders_pder_norm8`. Unlike `norm17`, this row
  driver applies `rsimp8` at each step instead of full `rsimp7`.
- Added the conditional cubic hook
  `rsizes_rpders_norm18_rows_rsimp8_live_row_cubicI`. The remaining theorem is
  now the cleaner closure premise
  `set (rflts (rpder_norm8_list c q)) \<subseteq>
  partial_derivative_live_row_universe (rsimp8 r)`.
- Added `norm18_closes_rsimp8_live_row_obstruction`, confirming that the
  concrete `(((1+a).a))*` obstruction for `norm17` is repaired by `norm18`.
- Added and checked first closure-infrastructure lemmas for BR-036:
  named live-row universe introduction lemmas, a non-alt `RALTS` child
  monotonicity lemma, the `RZERO`/`RONE`/`RCHAR` one-step closure base cases
  for `rpder_norm8_list`, and the conditional `RALTS` row-composition lemma
  `rpder_norm8_live_row_step_RALTSI`, followed by
  `rpder_norm8_live_row_step_RALTS_selfI` for normalized non-alt children.
  Added checked structural splitters
  `rpder_norm8_live_row_step_RSEQI`,
  `rpder_norm8_live_row_step_RSTARI`, and
  `rpder_norm8_live_row_step_RNTIMESI`; these isolate carried-continuation
  obligations from nullable-right obligations without unfolding the whole
  row derivative in later proofs.
  Added checked normal-form support
  `good_rsimp7_SEQ_atom`, `good_rsimp8`,
  `good_rpder_norm8_list`, and `good_rflts_rpder_norm8_list`, so later
  carried-continuation proofs can treat flattened norm18 rows as good/non-alt.
  Added the bridge lemmas
  `rflts_singleton_good_live_row_universe`,
  `rflts_singleton_rsimp8_live_row_universe`, and
  `rflts_map_rsimp8_live_row_subsetI`: flattened `rsimp8` rows are now
  discharged through the row's own live-row universe, reducing future
  closure obligations to per-raw-continuation universe inclusion facts.
  Also added `rpder_norm8_live_row_step_rsimp_ALTsI` for the
  length-sensitive `rsimp_ALTs` wrapper case. When proving around this area,
  explicitly save the outer list-shape equation before entering an inner
  `cases`; otherwise the useful `rsimp_ALTs rs = RALTS rs` fact can be lost.
  Added checked path-continuation reduction lemmas
  `rflts_map_rsimp8_rpder_list_path_subsetI`,
  `rflts_map_rsimp8_rpder_list_norm_tail_subsetI`,
  `rpder_norm8_live_row_step_RSEQ_pathI`,
  `rpder_norm8_live_row_step_RSTAR_pathI`, and
  `rpder_norm8_live_row_step_RNTIMES_pathI`. These turn carried branches into
  explicit `rder_path_continuations_acc` inclusion obligations, avoiding
  repeated unfolding of `rpder_list` and `rpder_norm8_list`.
  Added the weaker direct-frontier variants
  `rflts_map_rsimp8_direct_subsetI`,
  `rflts_map_rsimp8_rpder_list_path_direct_subsetI`,
  `rflts_map_rsimp8_rpder_list_norm_tail_direct_subsetI`, and
  `rpder_norm8_live_row_step_RSEQ_path_directI`/`RSTAR_path_directI`/
  `RNTIMES_path_directI`. These avoid the too-strong requirement
  `partial_derivative_live_row_universe (rsimp8 p) \<subseteq> U`; future closure
  attempts may instead prove only the actually produced frontier
  `set (rflts [rsimp8 p]) \<subseteq> U`.
  Important failed shortcut: do not assume `rsimp4_SEQ_atom r RONE = r`.
  It is false in the presence of the zero/one simplifications and
  reassociation that make `rsimp4_SEQ_atom` useful; a raw path-continuation
  transitivity proof based on that equation was rejected and removed.
  Added the checked counterexample
  `rsimp8_rsimp4_SEQ_atom_RONE_counterexample`, showing that even the
  tempting normalized equality
  `rsimp8 (rsimp4_SEQ_atom r RONE) = rsimp8 r` is false. The failing shape is
  `((b . b*) . b*)`: pre-normalizing with `rsimp4_SEQ_atom _ RONE` exposes an
  inner `b* . b*` absorption that direct root-safe `rsimp8` does not see.
  Future closure work should use a normalized-tail invariant or a weaker
  direct membership statement, not an equality shortcut.
  Added the checked counterexample
  `rsimp8_live_row_universe_RNTIMES_not_closed`, refuting the plain norm18
  live-row closure target for `RNTIMES`. The expression
  `(((0 + 1) + b)*){1}` reaches a carried continuation whose emitted
  `rsimp8` frontier contains `(1 + b)* . (((0 + 1) + b)*){0}`, outside the
  live-row universe of the root because `rsimp8` does not recurse under the
  repetition body. BR-036 now needs a refined normalized-tail/repetition-body
  invariant, or a revised root-safe simplifier design for `RNTIMES`, before
  the final closure theorem can be true.
  Added the positive sanity check
  `norm18_live_row_NTIMES_body_normalized_sanity`: the same counted-repetition
  tail shape closes when the repeated body is already the normalized star form
  emitted by the frontier. This favors a conservative `RNTIMES` repair:
  normalize repetition bodies/tails without reintroducing full root row-product
  expansion.
  Added and checked the proof-level prototype `rsimp9`, which is `rsimp8`
  plus recursive `RNTIMES` body normalization, safe `0^n`/`1^n` collapse,
  and the semantic zero-count collapse `RNTIMES r 0 = RONE`.
  Checked artifacts include `legacy_rsimp9`, `RL_rsimp9`,
  `rsize_rsimp9_le`, `rpder_norm9_list`, `rpd_der_norm9`,
  `rpder_norm9_rows`, their one-step language/legacy facts, and
  `norm19_closes_RNTIMES_countdown_sanity`. The checked
  `norm19_RNTIMES_body_normalization_obstruction_persists` shows the simple
  countdown case is fixed but complex body normalization can still escape the
  current live-row universe. This does not yet claim BR-036; it identifies a
  checked conservative redesign candidate for the next `bsimp` migration.
  Added the checked norm19 row-driver runway:
  `rders_pder_norm9`, `rpders_norm9_set`, `rpders_norm19`,
  `rpders_norm9_rows`, `rpders_norm19_rows`, finite/distinct facts,
  `RLS_rpders_norm19`, `RLS_rpders_norm19_rows`,
  `RL_rders_pder_norm9`, the generic
  `rpders_norm19_rows_rflts_subsetI`, and the conditional cubic hooks
  `rsizes_rpders_norm19_rows_rsimp9_live_row_cubicI` and
  `rsizes_rpders_norm19_rows_rsimp9_path_cubicI`. The latter keeps the same
  cubic bound while allowing the full `partial_derivative_path_universe`.
  The checked `norm19_RNTIMES_body_normalization_obstruction_in_path_universe`
  shows why this is the more plausible next invariant: the known complex
  `RNTIMES` body-normalization witness escapes live-row but lands in the
  path universe of the normalized root.
  Added the checked `rpder_norm9` one-step closure infrastructure:
  `good_rsimp9`, `good_rpder_norm9_list`,
  `rflts_singleton_rsimp9_live_row_universe`,
  `rflts_map_rsimp9_live_row_subsetI`,
  `rflts_map_rsimp9_direct_subsetI`,
  `rpder_norm9_live_row_step_RZERO/RONE/RCHAR/RALTSI`,
  `RSEQI`, `RSTARI`, `RNTIMESI`, and the path/direct variants for
  `RSEQ`, `RSTAR`, and `RNTIMES`. The hard theorem is now reduced to proving
  the carried-continuation premises for the `rsimp9` normalized root.
  Added the corresponding path-universe helper layer:
  `rflts_singleton_rsimp9_path_universe`,
  `rflts_map_rsimp9_path_subsetI`,
  `rflts_map_rsimp9_rpder_list_path_universe_subsetI`,
  `rflts_map_rsimp9_rpder_list_norm_tail_path_universe_subsetI`, and
  `partial_derivative_path_universe_alt_child_mono` plus
  `rpder_norm9_path_universe_step_RZERO/RONE/RCHAR/RALTS/rsimp_ALTs` and
  `RSEQ/RSTAR/RNTIMES_pathI`. These are the preferred splitters for the next
  BR-036 attempt because they target the checked cubic path-universe hook
  directly.
  Important correction: full one-step closure for every state in
  `partial_derivative_path_universe (rsimp9 r)` is checked-false. The lemma
  `norm19_path_universe_RNTIMES_subterm_not_closed` gives a small counted-tail
  counterexample where the original root contains `(a){2}.b`, the bare subterm
  `(a){2}` is in the path universe, and one derivative emits bare `(a){1}`,
  which is not in the root path universe. The next invariant must therefore be
  a reachable-row/path-carried subuniverse or a countdown-aware extension, not
  arbitrary full path-universe closure.
  Reusing the existing countdown-aware `partial_derivative_frontier_universe`
  is now checked as the next runway: `norm19_frontier_universe_repairs_RNTIMES_subterm_countdown`
  shows the counted-tail counterexample lands there, and
  `rsizes_rpders_norm19_rows_frontier_universe_cubic`,
  `rsizes_rpders_norm19_rows_frontier_universe_cubicI`, and
  `rsizes_rpders_norm19_rows_rsimp9_frontier_cubicI` give a conditional cubic
  hook for `norm19`. The next concrete proof target is the one-step closure
  premise for `partial_derivative_frontier_universe (rsimp9 r)`, preferably
  via constructor splitters rather than unfolding `rpder_norm9_list`.
  Added the first checked frontier splitter layer:
  `rflts_singleton_rsimp9_frontier_universe`,
  `rflts_map_rsimp9_frontier_subsetI`,
  `partial_derivative_frontier_universe_alt_child_mono`, and
  `rpder_norm9_frontier_universe_step_RZERO/RONE/RCHAR/RALTS/rsimp_ALTs`.
  Added the carried-constructor frontier layer:
  `rflts_map_rsimp9_rpder_list_frontier_subsetI`,
  `rflts_map_rsimp9_rpder_list_norm_tail_frontier_subsetI`, and
  `rpder_norm9_frontier_universe_step_RSEQ/RSTAR/RNTIMES_pathI`. These cover
  the same structured continuation interface as the path-universe lemmas, but
  target the countdown-aware frontier universe.
  Added `norm19_frontier_universe_repairs_left_nested_seq_counterexample`:
  the old `frontier_universe_not_closed_under_rpder_norm_list` witness
  `((a*).b).d` is normalized by `rsimp9` to `a*.(b.d)`, and its `a`
  derivative stays inside `partial_derivative_frontier_universe`. This is
  evidence that the frontier route is repairing the known associativity leak,
  not merely adding a larger universe.
  Added `norm19_frontier_universe_repairs_nested_star_counterexample`:
  the older `RSTAR (RSTAR a)` cubic-universe obstruction is normalized to
  `RSTAR a`, and the normalized `a` derivative remains inside the same
  frontier universe.
  Added explicit checked regression lemmas for the thesis cubic-bound examples:
  `thesis_cubic_evil3_aaa_norm19_rows_cubic` checks the concrete Chapter 6
  evil shape `(a* + (aa)* + (aaa)*)*` after reading `aaa`. The smaller
  `thesis_cubic_small_alt3_aaa_norm19_rows_cubic` remains only as a cheap
  non-starred sanity contrast. The
  `thesis_cubic_ntimes_countdown_norm9_no_zero_counter` and
  `thesis_cubic_ntimes_countdown_norm19_rows_cubic` check the counted
  `(a){3}` countdown shape. These are sanity tests for the route, not a
  BR-036 payout.
  The Chapter 7 stronger simplification/pruning route is not yet implemented
  as a real simplifier; it remains the main design gap if `rsimp9/path9`
  accounting is too weak.
  Added checked FBound regression facts for that exact Chapter 7 gap:
  `thesis_ch7_evil5_bders_simp_size_16` shows the production-style
  `bders_simp` state for `((a* + (aa)* + ... + (aaaaa)*)*)*` already reaches
  size `14876` after `a^16`, while `thesis_ch7_evil5_bders_simp8_size_16`
  records that root-safe `bsimp8` is much smaller (`1308`) but still not the
  non-invasive prune rule. The row-list route has the corresponding checked
  `thesis_ch7_evil5_bpders_norm17_row_size_16 = 645`. The overlap-prune
  lemmas `thesis_ch7_bsimp_misses_overlap_prune`,
  `thesis_ch7_overlap_pruned_smaller`, and
  `thesis_ch7_overlap_pruned_same_language` pin down the missing rule:
  current `bsimp` cannot prune the shared component in the
  `(a + b + d).c + (a + c + e).c` shape, even though the pruned erasure has the
  same language and smaller annotated size.
  Added the first executable `bsimpStrong` prototype in `BlexerSimp.thy`.
  It scans flattened alternative rows left-to-right and, for later rows of
  the form `(X + Y).k` with the same continuation as an earlier
  `(X + Z).k`, removes from the later left alternative the entries already
  covered by the earlier row. The generic support lemma
  `L_prune_eq1_against_AALTs` checks the erasure-language basis of this
  deletion. The regression facts `thesis_ch7_bsimpStrong_prunes_overlap`,
  `thesis_ch7_bsimpStrong_overlap_smaller`, and
  `thesis_ch7_bsimpStrong_overlap_same_language` show that this prototype
  performs the Chapter 7 overlap prune on `(a + b + d).c + (a + c + e).c`.
  The first full-family size regression is also checked:
  `thesis_ch7_evil5_bders_simpStrong_lt_simp8_size_16` and
  `thesis_ch7_evil5_bders_simpStrong_size_16_under_825` show that on
  `((a* + (aa)* + ... + (aaaaa)*)*)*` after `a^16`, `bders_simpStrong`
  is below `825`, and
  `thesis_ch7_evil5_bders_simpStrong_size_16_not_under_812` gives a checked
  lower-bound sanity check. It improves over `bsimp8 = 1308` and vastly over old
  `bders_simp = 14876`, but still not matching the row-list route (`645`).
  Added the checked erasure-language theorem `L_bsimpStrong`. This upgrades
  the prototype from example-only evidence to a general language-preserving
  annotated simplifier at the erased-language level. It is deliberately not a
  BR-037 payout claim yet: POSIX/bitcode preservation and a general cubic
  theorem are still open.
  This is still not a BR-036 payout: production use needs a POSIX/bitcode
  preservation theorem and a general cubic proof.
  Added the dual-frontier cubic hook:
  `quadratic_plus_linear_padding_bound`,
  `quadratic_plus_linear_times_linear_cubic_bound`, and
  `rsizes_distinct_path_dual_frontier_universe_cubicI`. This checked theorem
  says any distinct row list inside the dual frontier universe is cubic once
  two remaining local obligations are proved: the combined full/atom frontier
  set is quadratic, and each dual-universe member has linear size.
  Added `current_dual_frontier_universe_member_size_not_linear`, a checked
  counterexample to the second premise for the current dual universe: a
  left-nested chain with five binary suffix alternatives produces a member of
  `partial_derivative_path_dual_frontier_universe` whose size exceeds
  `Suc (rsize r + rsize r)`. Do not pursue the full dual-frontier hook as-is;
  switch to an atom-only or smaller reachable-row universe.
  Added `current_path_atom_frontier_universe_member_size_not_linear`, showing
  that the old atom-only universe is also too broad when it uses
  `rsimp4 r2` inside sequence continuations: a right-nested binary suffix chain
  is expanded before being placed in the atom frontier. The next viable route
  should be norm9-specific, using root-safe `rsimp9`/`rsimp7_SEQ_atom`
  continuations rather than the older `rsimp4` continuation collector.
  Added that norm9-specific scaffold as `rpath9_atom_frontier_acc`,
  `rpath9_atom_frontiers`, and
  `partial_derivative_path9_atom_frontier_universe`, with checked finite
  support. The sanity lemma `path9_atom_frontier_avoids_old_atom_explosion`
  shows the previous right-nested binary suffix witness no longer enters the
  new universe, so the next proof target is card/member-size accounting plus
  one-step closure for this smaller invariant.
  Added the first accounting interface for this smaller invariant:
  `partial_derivative_path9_atom_frontier_universe_card_le`,
  `partial_derivative_path9_atom_frontier_universe_member_size_boundI`,
  `partial_derivative_path9_atom_frontier_universe_member_size_linearI`, and
  `rsizes_distinct_path9_atom_frontier_universe_cubicI`. This reduces the
  cubic row-size target to two local facts about `rpath9_atom_frontiers`:
  quadratic cardinality and linear member size.
  Added the first path9 closure plumbing:
  `rsubterms_rsimp_ALTs_member`, `set_rflts_singleton_map_member`,
  `rflts_singleton_rsimp9_path9_atom_frontier`,
  `rflts_map_rsimp9_path9_atom_subsetI`,
  `rflts_rsimp9_alt_child_path9_atom_subset`, and the base
  `rpder_norm9_path9_atom_frontier_step_RZERO/RONE/RCHAR` lemmas. A first
  attempt used broad `blast` and hit the performance warning; the final checked
  version is split into explicit membership/subset steps.
  Extended the path9 `RALTS` plumbing with
  `set_rflts_map_member_exists`, `set_rflts_map_memberE`,
  `rflts_map_rsimp9_alt_path9_atom_subset`,
  `rflts_map_rsimp9_rsimp_ALTs_path9_atom_subset`,
  `rpath9_atom_frontiers_alt_child_subset`,
  `rpath9_atom_frontiers_alt_child_universe`,
  `rpder_norm9_path9_atom_frontier_step_RALTS_parentI`, and
  `rpder_norm9_path9_atom_frontier_step_rsimp_ALTs_parentI`. These deliberately
  avoid the false-looking full child-universe monotonicity and only transport
  flattened rows/frontier atoms into the parent target.
  Added carried-frontier parent inclusions for sequence, star, and counted
  repetition:
  `rpath9_atom_frontiers_universe`,
  `rpath9_atom_frontiers_seq_left_subset`,
  `rpath9_atom_frontiers_seq_left_universe`,
  `rpath9_atom_frontiers_seq_right_subset`,
  `rpath9_atom_frontiers_seq_right_universe`,
  `rpath9_atom_frontiers_star_body_subset`,
  `rpath9_atom_frontiers_star_body_universe`,
  `rpath9_atom_frontiers_ntimes_body_subset`, and
  `rpath9_atom_frontiers_ntimes_body_universe`. These are the checked parent
  membership facts needed before turning `RSEQ/RSTAR/RNTIMES` derivative
  splitters into path9 closure lemmas.
  Added the parent-target derivative splitters
  `rpder_norm9_path9_atom_frontier_step_RSEQ_parentI`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_parentI`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_parentI`. They instantiate the
  existing `rpder_norm9_live_row_step_*` splitters with the exact path9 parent
  universe, leaving only the carried branch subset obligations for the next
  proof layer.
  Added the direct carried-continuation variants
  `rpder_norm9_path9_atom_frontier_step_RSEQ_directI`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_directI`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_directI`. These reduce the
  remaining carried branches to singleton obligations of the form
  `set (rflts [rsimp9 p]) <= parent_universe`, avoiding a repeat of the full
  `map`/`rflts` proof state in each constructor.
  Added the checked nullable right-branch lift for sequence:
  `rnullable_rsimp9`,
  `rsubterms_rsimp4_SEQ_atom_nullable_right_subset`,
  `rsubterms_rsimp7_SEQ_atom_nullable_right_subset`,
  `rsubterms_rsimp9_RSEQ_right_nullable_universe`,
  `partial_derivative_path9_atom_frontier_universe_RSEQ_right_nullable_subset`,
  and `rpder_norm9_path9_atom_frontier_step_RSEQ_parent_childI`. This removes
  the `RSEQ` nullable-right child-to-parent universe obligation from the next
  closure layer; the remaining hard part is the carried left/body branch.
  Added the checked normalized-alternative child lifts
  `partial_derivative_path9_atom_frontier_universe_RALTS_flat_child_subset`,
  `rsubterms_nonalt_flattened_subterms`,
  `rsubterms_rsimp9_alt_child_nonalt_path9_atom_subset`,
  `partial_derivative_path9_atom_frontier_universe_RALTS_nonalt_child_member`,
  `rpder_norm9_path9_atom_frontier_step_RALTS_childI`, and
  `rpder_norm9_path9_atom_frontier_step_rsimp_ALTs_childI`. The key point is
  that a full child-universe lift for nested `RALTS` is too strong after
  flattening; the checked version lifts the flattened rows and the nonalt
  derivative rows actually produced by `rpder_norm9_list`.
  Added the first direct quadratic-card accounting split for
  `rpath9_atom_frontiers`: `plus2_square_plus_plus3_square_le`,
  `sum_list_rsize_plus2_square_le_rsizes_plus3_square`,
  `card_rpath9_atom_frontier_acc_list_le`,
  `card_rpath9_atom_frontiers_RALTS_le`, and
  `card_rpath9_atom_frontiers_RALTS_quadraticI`. The `RALTS` case of the
  target `card (rpath9_atom_frontiers r) <= (rsize r + 2)^2` can now be
  discharged from the child quadratic hypotheses.
  Added the matching checked member-size split
  `rpath9_atom_frontiers_RALTS_member_sizeI`, so the `RALTS` case of
  `q in rpath9_atom_frontiers r ==> rsize q <= Suc (rsize r + rsize r)` also
  reduces to child hypotheses.
  Added checked path9 accounting base cases for `RZERO`, `RONE`, `RCHAR`, and
  zero-count `RNTIMES`: `card_rpath9_atom_frontiers_RZERO_quadratic`,
  `card_rpath9_atom_frontiers_RONE_quadratic`,
  `card_rpath9_atom_frontiers_RCHAR_quadratic`,
  `rpath9_atom_frontiers_RZERO_member_size`,
  `rpath9_atom_frontiers_RONE_member_size`,
  `rpath9_atom_frontiers_RCHAR_member_size`,
  `card_rpath9_atom_frontiers_RNTIMES_zero_quadratic`, and
  `rpath9_atom_frontiers_RNTIMES_zero_member_size`.
  Added checked helper facts for the next `RSEQ`/`RSTAR`/`RNTIMES` accounting
  layer: `rfrontier_member_size_le_rsize`,
  `card_rfrontier_rsimp7_SEQ_atom_le`, and
  `rfrontier_rsimp7_SEQ_atom_member_size_le`. These bound the frontier
  cardinality and member size of root-safe carried continuations without
  reopening the row-driver definitions.
  Added the first constructor splitters for path9 frontier accounting:
  `card_rpath9_atom_frontiers_RSEQ_le`,
  `card_rpath9_atom_frontiers_RSTAR_le`,
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_le`,
  `rpath9_atom_frontiers_RSEQ_member_sizeI`,
  `rpath9_atom_frontiers_RSTAR_member_sizeI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_sizeI`. These do not claim
  the full quadratic/linear facts yet; they isolate the remaining carried
  continuation branch from the already-handled child/root cases.
  Added the conditional quadratic constructor layer:
  `seq_component_product_plus_child_square_le`,
  `component_product_le_square`,
  `card_rpath9_atom_frontiers_RSEQ_quadraticI`,
  `card_rpath9_atom_frontiers_RSTAR_quadraticI`, and
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_quadraticI`. The remaining
  cardinality work for these constructors is now the product-shaped carried
  collector bound
  `card (rpath9_atom_frontier_acc body carried_k) <=
   rsize body * (rsize parent + 2)`, rather than the full parent frontier
  inequality.
  Added checked tail-normalization support for that carried product route:
  `rsize_rsimp4_SEQ_atom_RONE_le`,
  `rsize_rsimp7_SEQ_atom_RONE_le`,
  `rsize_rsimp7_SEQ_atom_rsimp9_RONE_le`,
  `card_rfrontier_rsimp7_SEQ_atom_RONE_le`,
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RONE_le`,
  `rfrontier_rsimp7_SEQ_atom_RONE_member_size_le`, and
  `rfrontier_rsimp7_SEQ_atom_rsimp9_RONE_member_size_le`. These facts record
  the important nuance that `rsimp7_SEQ_atom r RONE` need not equal `r`, but
  it does not increase size and its frontier is still controlled by the
  original tail size.
  Added checked base facts for the carried collector itself:
  `card_rpath9_atom_frontier_acc_RZERO_product`,
  `card_rpath9_atom_frontier_acc_RONE_product`,
  `card_rpath9_atom_frontier_acc_RCHAR_le`,
  `rpath9_atom_frontier_acc_RCHAR_member_size_le`,
  `card_rpath9_atom_frontier_acc_RCHAR_rsimp9_RONE_product`, and
  `rpath9_atom_frontier_acc_RCHAR_rsimp9_RONE_member_size`. These close the
  zero/one/char base cases for a future induction over
  `rpath9_atom_frontier_acc`.
  Added checked carried-collector constructor splitters:
  `sum_list_map_rsize_mult_right`,
  `card_rpath9_atom_frontier_acc_RALTS_productI`,
  `rpath9_atom_frontier_acc_RALTS_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RSEQ_le`,
  `rpath9_atom_frontier_acc_RSEQ_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RSTAR_le`,
  `rpath9_atom_frontier_acc_RSTAR_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_le`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_member_sizeI`. These isolate the
  future product-bound induction cases without monolithic proof search.
  Added checked product-introduction lemmas for the remaining accumulator
  constructors: `card_rpath9_atom_frontier_acc_RSEQ_productI`,
  `card_rpath9_atom_frontier_acc_RSTAR_productI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_productI`,
  `card_rpath9_atom_frontier_acc_RBACKREF4_productI`,
  `rpath9_atom_frontier_acc_RBACKREF4_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RHALF_productI`,
  `rpath9_atom_frontier_acc_RHALF_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RRESIDUE_product`, and
  `rpath9_atom_frontier_acc_RRESIDUE_member_size`. The arithmetic steps use
  explicit `algebra_simps`, after a first CI run showed plain `simp` leaves
  residual natural-number product goals.
  Added checked normalized nested-tail budget facts:
  `rsize_rsimp7_SEQ_atom_rsimp9_nested_RONE_le`,
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_nested_RONE_le`, and
  `rfrontier_rsimp7_SEQ_atom_rsimp9_nested_RONE_member_size_le`. A direct
  syntactic associativity lemma for `rsimp7_SEQ_atom` was rejected as too
  strong; the useful invariant is budget control for the nested normalized
  carried tail.
  Added checked `RCHAR` accumulator instances for that nested-tail budget:
  `card_rpath9_atom_frontier_acc_RCHAR_rsimp9_nested_RONE_product` and
  `rpath9_atom_frontier_acc_RCHAR_rsimp9_nested_RONE_member_size`. These close
  the character-leaf case that appears when the carried continuation has one
  extra normalized sequence layer.
  Added checked `RSEQ` normalized-tail handoff lemmas:
  `card_rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_productI` and
  `rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_member_sizeI`. These split
  `acc (RSEQ r1 r2) (rsimp9 k . 1)` into a left nested-tail obligation for
  `r2 . k` and a right ordinary-tail obligation for `k`.
  Added checked `RSTAR`/`RNTIMES` normalized-tail handoff lemmas:
  `card_rpath9_atom_frontier_acc_RSTAR_rsimp9_RONE_productI`,
  `rpath9_atom_frontier_acc_RSTAR_rsimp9_RONE_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_productI`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_member_sizeI`.
  These expose the body obligation with the extra normalized carried tail.
  Added budget-compatible variants:
  `card_rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_balanced_productI`,
  `rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_balanced_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_outer_productI`,
  and `rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_outer_member_sizeI`.
  These are closer to the future induction because they keep the right child
  and countdown parent on the same `RSEQ ... k` budget scale.
  Added the checked top-level path9 frontier cardinality bound:
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RSTAR_le`,
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RNTIMES_le`,
  `sum_list_rsize_times_rsize_plus_le`, `seq_frontier_acc_card_arith`,
  `card_rpath9_atom_frontier_acc_le_size_frontier`, and
  `card_rpath9_atom_frontiers_quadratic`. This replaces the remaining
  card-accounting TODO with a direct accumulator induction. Also added relaxed
  `RSEQ`/`RSTAR`/`RNTIMES` top-level quadratic interfaces with
  `RSEQ parent RONE` budgets for later handoff-based proofs.
  Added cubic handoff interfaces that bake in the checked cardinality theorem:
  `rsizes_distinct_path9_atom_frontier_universe_cubic_member_sizeI`,
  `rsizes_rpders_norm19_rows_path9_atom_frontier_universe_cubic`, and
  `rsizes_rpders_norm19_rows_rsimp9_path9_atom_frontier_cubicI`. The remaining
  assumptions are exactly the next proof obligations: path9 linear member-size
  and one-step `rpder_norm9_list` closure.
  Full local CI passed for `Posix` and `BackRefPilot`.
  A too-broad attempted `rsimp8` idempotence proof was
  discarded after hitting the timeout/performance rule; do not resurrect it
  without splitting `rsimp_ALTs`/`rdistinct`/`rflts` helper facts first.
- Added and checked the stronger `rsimp7`/`bsimp7` simplifier layer for the
  25k new-definition bounty. It extends `rsimp6` with prefix star absorption
  `r* · (r* · k) = r* · k`, the repeated-row shape that appears once
  Antimirov rows carry a continuation.
- The checked artifacts include `RL_rsimp7`, `rders_simp7`,
  `rpder_norm7_list`, `rpd_der_norm7`, `rpder_norm7_rows`,
  `rpders_norm17_rows`, `RLS_rpders_norm17_rows`, and
  `RL_rders_pder_norm7`.
- Added the `norm17` conditional cubic interfaces:
  `rpders_norm17_rows_subterms_subsetI`,
  `rpders_norm17_rows_rflts_subsetI`,
  `rsizes_rpders_norm17_rows_cubic_universe_cubicI`, and
  `rsizes_rpders_norm17_rows_live_path_universe_cubicI'`.
- The annotated mirror includes `bsimp7`, `bpder_norm7_list`,
  `bp_der_norm7`, `bpder_norm7_rows`, `bders_pder_norm7`, and
  `bpders_norm17_rows`, with erasure/language transfer facts
  `bsimp7_rerase`, `bp_der_norm7_rerase`, `rpders_norm17_rows_rerase`, and
  `RL_rerase_bders_pder_norm7`.
- BR-032 is now marked DONE. The final repeated-row cubic closure theorem is
  still open under BR-033/BR-034.
- Added `partial_derivative_live_row_universe` and the checked lemma
  `live_path_universe_misses_flattened_alt_row`. This refutes the too-narrow
  rflts/live-path target: for `a · (b + c)`, the `a` step flattens the row to
  `b` and `c`, while `partial_derivative_live_path_universe` contains only the
  whole continuation `b + c`. The next BR-033 invariant must therefore close
  Antimirov frontier rows of live continuations, not only continuation terms.
- Strengthened that correction with checked bridge lemmas:
  `rfrontier_path_continuation_subset_path_universe`,
  `partial_derivative_live_row_universe_subset_path`,
  `rsizes_distinct_live_row_universe_cubic`, and
  `rsizes_rpders_norm17_rows_live_row_universe_cubicI'`. Thus the corrected
  live-row target still inherits the existing cubic path-universe accounting;
  the remaining BR-033 proof is the live-row one-step closure premise.
- Added `raw_live_row_universe_not_closed_under_norm7`, confirming that the
  final closure theorem should start from the normalized root `rsimp7 r` (or an
  equivalent normalized-image universe). The raw root `((0 + a)*)` reaches
  `a*`, which is not in its raw live-row universe but is in the live-row
  universe of `rsimp7 ((0 + a)*)`.
- Checked commits continue on `codex/backref-values`; older hash notes below
  are historical breadcrumbs rather than the current head.
- Follow-up checked prototype through `462fd39` and the next local checkpoint:
  `rsimp6` adds star absorption on top of the normalized Antimirov row
  pipeline. `rpder_norm6_list`, `rpd_der_norm6`, `rpder_norm6_rows`, and
  `rpders_norm16_rows` are now defined in `GeneralRegexBound.thy` with
  legacy preservation, distinctness, and language-correctness lemmas. This is
  still a proof-level prototype, not yet the final annotated `bsimp`
  replacement.
- Added `rsimp6_collapses_cubic_counterexample_row`, showing the new
  normalizer directly collapses the previously checked `(a*)*` repeated-row
  obstruction (`a* · ((a*)* · a*)`) to `a*`. This does not close the global
  cubic theorem yet, but it gives a checked reason to pursue star absorption as
  the next simplifier design.
- Mirrored the prototype into the annotated layer with `bsimp6`,
  `bpder_norm6_list`, `bp_der_norm6`, `bpder_norm6_rows`,
  `bders_pder_norm6`, and `bpders_norm16_rows`. `FBound.thy` now proves the
  erasure transfer lemmas, including `bsimp6_rerase`,
  `bp_der_norm6_rerase`, `rders_pder_norm6_size`,
  `rpders_norm16_rows_rerase`, and `RL_rerase_bders_pder_norm6`.
- The annotated prototype is deliberately not wired into the production
  `blexer_simp` yet: star absorption erasure correctness is checked, but
  value/bitcode preservation still needs a separate theorem before replacing
  the thesis-style simplifier.
- Added `reachable_norm6_row_can_leave_current_cubic_universe`. This checked
  counterexample shows that the current universe is too syntactic for
  `rsimp6`: from `((0 + a)*)`, one normalized row step reaches `a*`, which is
  language-equivalent but not a member of the old root's
  `partial_derivative_cubic_universe`. The closure target must therefore use a
  pre-normalized root or a normalized-image universe.
- Added the checked conditional route for the pre-normalized root:
  `rpders_norm16_rows_subterms_subsetI`,
  `rsizes_rpders_norm16_rows_cubic_universe_cubicI`, and
  `rsizes_rpders_norm16_rows_normalized_root_cubicI`. The remaining theorem is
  not the all-universe premise directly, because that premise is too strong.
- Added `normalized_root_universe_not_all_q_closed_under_norm6`, showing even
  a normalized root universe is not closed for every member `q`: for
  `((b · b)*)`, the continuation `((b · b)*) · b` is in the universe, but its
  `b`-row exposes `b · (((b · b)*) · b)` outside it. The final proof needs a
  reachable-row invariant or a refined universe, not plain all-member closure.
- Strengthened `rsimp6`/`bsimp6` with `0* = 1` and `1* = 1`; added the
  language facts `Star_empty` and `Star_one`.
- Strengthened `rsimp6_SEQ`/`bsimp6_ASEQ` again so star absorption is applied
  inside each distributed sequence product via `rsimp6_SEQ_atom` and
  `bsimp6_ASEQ_atom`. This fixes the case where `(b* + a) · b*` generated an
  internal `b* · b*` product that the previous top-level-only rule missed.
- Added `partial_derivative_live_path_universe r =
  {0, 1, r} \<union> rpath_continuations r`, plus
  `rsizes_distinct_live_path_universe_cubic` and
  `rsizes_rpders_norm16_rows_live_path_universe_cubicI`. This gives a smaller
  cubic target (`2 * (rsize r + 3)^3`) once the live-path one-step closure for
  `rpder_norm6_list` is proved.
- Added the sharper rflts-based closure interface
  `rpders_norm16_rows_rflts_subsetI` and
  `rsizes_rpders_norm16_rows_live_path_universe_cubicI'`. This replaces the
  earlier over-strong subterm-closure premise: live-path universes track rows
  and carried continuations, so they need closure under `rflts` of generated
  rows, not closure under every syntactic subterm.
- Added helper lemmas for the current combined cubic universe:
  `partial_derivative_path_universe_subset_cubic`,
  `partial_derivative_frontier_universe_subset_cubic`,
  `set_rdistinct_subset`, and `set_rflts_good_subset_rfrontiers`.
- Added `set_rflts_subset_rsubterms_list` and
  `rpder_norm_rows_single_path_subterms_subset`. This proves that one
  normalized Antimirov row step is supported by subterms of the path universe,
  rather than an arbitrary regex-size universe.
- Added `rsubterms_subterm_subset_frontier`,
  `rsubterms_linear_continuation_subset`, and
  `rsubterms_frontier_universe_member_subset`. These close the quadratic
  frontier universe under subterms, which is needed whenever `rflts` exposes
  children of a normalized row.
- Current hard gap: prove repeated `rpders_norm1_rows` stay inside the original
  `partial_derivative_cubic_universe r`, or refine the row normalizer so this
  invariant is direct. The numeric cubic accounting is checked; the remaining
  problem is closure/invariance, not arithmetic.
- Local CI passed after each checkpoint with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix`, and Isabelle `BackRefPilot`.

## Antimirov Partial-Derivative Checkpoint (2026-05-31)

- Added a checked proof-only Antimirov layer in `GeneralRegexBound.thy`:
  `rpder`, `rpder_set`, `rpders`, and `rpders1`.
- `rpder` is deliberately restricted by theorem assumptions to the legacy
  non-backref fragment. The backreference constructors return `{}` in the
  raw definition, and the semantic/cardinality theorems require
  `legacy_rrexp`, so no false boundedness claim is made for payload-carrying
  states.
- Proved the core one-step facts:
  - `finite_rpder`
  - `legacy_rpder`
  - `card_rpder_le_rsize`
  - `RLS_rpder`
  - `RLS_rpder_rder`
- Proved the word-level driver facts:
  - `finite_rpder_set`
  - `finite_rpders`
  - `legacy_rpder_set`
  - `legacy_rpders`
  - `RLS_rpder_set`
  - `Ders_Cons`
  - `RLS_rpders`
  - `RLS_rpders1`
- Design consequence: the cubic-bound route can now use a checked
  partial-derivative automaton as the reference model. The next `bsimp`
  redesign should aim to erase to an ordered/list implementation of this
  partial-derivative set, rather than expanding all sequence alternatives
  by a global `rsimp5` row product.
- Proof-performance note: the first drafts exposed exactly the bad pattern
  Chengsong warned about. Broad `auto`/`blast` on the `legacy_rpder` sequence
  and backreference cases caused 20-40 second proof commands and session
  timeouts. The checked version splits membership cases explicitly and keeps
  `Posix.GeneralRegexBound` replay around 18 seconds.
- Local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (about 27 seconds elapsed), and Isabelle `BackRefPilot`
  (about 3 seconds elapsed).
- Follow-up executable checkpoint:
  - Added `rpder_list`, an ordered/list implementation of `rpder`, with
    `set_rpder_list`.
  - Proved `length_rpder_list_le_rsize` for the legacy non-backref fragment,
    giving the executable one-step partial-derivative list the same linear
    size-count discipline as the set model.
  - Added `rpd_der`, which packages `rpder_list` through the existing
    `rsimp_ALTs`/`rdistinct`/`rflts` normalization.
  - Added `rsize_rpd_der_le_rsizes_rpder_list`, the first size-accounting
    hook for the executable pipeline: normalizing a partial-derivative list
    into a regex state costs at most one constructor over the list's total
    structural size.
  - Added `rders_pder` and proved `legacy_rpd_der`, `legacy_rders_pder`,
    `RL_rpd_der`, and `RL_rders_pder`.
  - Design consequence: the next annotated `bsimp` candidate should mirror
    this list-producing derivative pipeline and then prove an erasure bridge,
    instead of treating `rsimp5`'s global row product as the final algorithm.
  - Local CI again passed with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (about 26 seconds elapsed), and Isabelle `BackRefPilot`
    (about 3 seconds elapsed).
- Annotated pipeline checkpoint:
  - Added `bpder_list`, `bp_der`, and `bders_pder` in `BlexerSimp.thy`.
    This is the annotated counterpart of the executable partial-derivative
    pipeline. It preserves bit-prefix structure rather than being a mere
    wrapper: `AALTs bs` fuses `bs` into each produced row, `ASEQ bs r1 r2`
    carries `bs` through left rows, and the nullable right branch fuses
    `bs` followed by `bmkeps r1`.
  - Added `rerase_bpder_list`, `bp_der_rerase`, and `rders_pder_size` in
    `FBound.thy`, proving the annotated pipeline erases to
    `rpder_list`/`rpd_der`/`rders_pder`.
  - Added `legacy_rerase_bders_pder` and `RL_rerase_bders_pder`, so for the
    legacy non-backref fragment the annotated candidate has the same semantic
    derivative language as `Ders`.
  - Proof-performance note: the bridge proof was kept modular with explicit
    list-map lemmas (`rerase_concat_map_bpder_list`,
    `map_rsimp4_SEQ_atom_rerase_cong`) instead of a broad `simp_all` that
    left map-congruence subgoals unresolved.
  - Local CI passed with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (about 27 seconds elapsed), and Isabelle `BackRefPilot`
    (about 3 seconds elapsed).

## Partial-Derivative Size Transfer Checkpoint (2026-05-31)

- Added `asize_bp_der_rpd_der` and `asize_bders_pder_rders_pder` in
  `FBound.thy`. These facts make the annotated partial-derivative candidate
  size-exact with the proof-level `rpd_der`/`rders_pder` pipeline after
  erasure.
- Added `aders_pder_finiteness`, the direct finite-size transfer hook for any
  future checked bound on `rders_pder`. This is intentionally a transfer hook,
  not a bounty claim for the final cubic theorem.
- Added a reusable cubic accounting lemma in `GeneralRegexBound.thy`:
  `rsizes_distinct_path_universe_cubic`. If a normalized derivative row list
  is distinct and contained in `partial_derivative_path_universe r`, its total
  structural size is bounded by `2 * (rsize r + 3) ^ 3`.
- Design consequence: the remaining hard theorem is now sharply separated.
  The numeric side of the cubic argument is checked; the open research work is
  the closure side, namely proving that the chosen stronger simplifier keeps
  derivative rows inside a universe with the same linear-cardinality and
  quadratic-member-size discipline.
- Local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (about 26 seconds elapsed), and Isabelle `BackRefPilot`
  (about 3 seconds elapsed).
- Follow-up checked candidate-simplifier transfer:
  - Added `RL_rders_simp5` in `GeneralRegexBound.thy`, proving the word-level
    language correctness of the stronger row-product simplifier loop.
  - Added `asize_bders_simp5_rders_simp5`, `RL_rerase_bders_simp5`, and
    `aders_simp5_finiteness` in `FBound.thy`, connecting the annotated
    `bders_simp5` candidate back to proof-level semantics and size bounds.
  - This makes `bsimp5` a real checked candidate for BR-032/BR-034 work, while
    still not claiming the final cubic theorem until closure into the chosen
    universe is proved.
  - Local CI passed with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (about 26 seconds elapsed), and Isabelle `BackRefPilot`
    (about 3 seconds elapsed).
- First `rsimp5` closure layer:
  - Added dual-universe one-step closure for `rsimp5 (rder c r)` on
    `RZERO`, `RONE`, `RCHAR`, and `RALTS`.
  - The `RALTS` proof mirrors the Antimirov row discipline: normalize mapped
    branch derivatives, extract the branch row with
    `rfrontier_normalize_memberE`, then transport through the alternative
    child monotonicity lemma for `partial_derivative_path_dual_frontier_universe`.
  - This leaves the real continuation cases (`RSEQ`, `RSTAR`, `RNTIMES`) as
    the next isolated closure target.
  - Local CI passed with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (about 27 seconds elapsed), and Isabelle `BackRefPilot`
    (about 3 seconds elapsed).
- Checked design counterexample for over-eager row products:
  - Added lemmas showing that `rsimp5` distributes a right alternative suffix
    in `(a b) (c+d)` into rows `b c` and `b d`.
  - Added
    `current_dual_frontier_universe_misses_right_alt_suffix_distribution`,
    proving that the current dual frontier universe does not contain one of
    those rows for a distinct-character witness.
  - Design consequence: the fully eager `rsimp5` row-product is semantically
    correct, but it is probably too aggressive to be the final cubic
    simplifier as-is. The next candidate should use the Antimirov frontier
    discipline more selectively, or the universe must be redesigned with a
    checked non-exponential accounting argument before any bounty claim.
  - Local CI passed with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (about 27 seconds elapsed), and Isabelle `BackRefPilot`
    (about 3 seconds elapsed).
- Positive Antimirov-list closure step:
  - Added `rpder_list_path_continuations_acc_subset`, a carried-continuation
    theorem showing that the executable partial-derivative rows, after the
    local `rsimp4_SEQ_atom` continuation normalization, are contained in the
    derivative path-continuation collector.
  - Added `rpder_list_path_universe_subset`: for legacy/non-backref regexes,
    `map (\<lambda>p. rsimp4_SEQ_atom p RONE) (rpder_list c r)` is contained in
    `partial_derivative_path_universe r`.
  - Important proof-shape lesson: `rsimp4_SEQ_atom p RONE` is not globally
    identical to `p` for sequence-shaped rows, because the continuation
    normalizer may still remove zero/one structure or reassociate. The theorem
    therefore states closure for the normalized row list, which is the object
    relevant to the size-bound pipeline.
  - Added `rsizes_rpder_list_RONE_cubic`, proving that one executable
    partial-derivative step has cubic total row size after this local
    continuation normalization, for the legacy/non-backref fragment.
  - This is the positive replacement for the over-eager `rsimp5` direction:
    keep Antimirov rows as rows, normalize local continuations, and account
    for the row list directly instead of expanding every right alternative
    suffix into a full Cartesian product.
  - Local CI passed with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (about 26 seconds elapsed), and Isabelle `BackRefPilot`
    (about 3 seconds elapsed).
- Normalized partial-derivative pipeline:
  - Added explicit proof-level definitions `rpder_norm_list`, `rpd_der_norm`,
    and `rders_pder_norm`.
  - Proved `legacy_rpd_der_norm`, `legacy_rders_pder_norm`,
    `RL_rpd_der_norm`, and `RL_rders_pder_norm`. The local row normalization
    uses `rsimp4_SEQ_atom p RONE`, and `RL_rsimp4_SEQ_atom_RONE` proves this
    preserves row language.
  - Proved `rsize_rpd_der_norm_cubic`: one normalized partial-derivative step
    is bounded by `Suc (2 * (rsize r + 3) ^ 3)` for the legacy/non-backref
    fragment.
  - Design consequence: the likely final algorithm should mirror
    `rpd_der_norm` in the annotated layer, rather than use the raw
    `bp_der` or the over-eager `bsimp5` row-product loop as the final cubic
    simplifier.
  - Local CI passed with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (about 26 seconds elapsed), and Isabelle `BackRefPilot`
    (about 3 seconds elapsed).
- Annotated normalized partial-derivative pipeline:
  - Added `bpder_norm_list`, `bp_der_norm`, and `bders_pder_norm` in
    `BlexerSimp.thy`. This mirrors `rpder_norm_list` by locally normalizing
    each annotated partial-derivative row with `bsimp4_ASEQ_atom [] p (AONE [])`.
  - Added `rerase_bpder_norm_list`, `bp_der_norm_rerase`,
    `rders_pder_norm_size`, `RL_rerase_bders_pder_norm`, and exact annotated
    size-transfer lemmas in `FBound.thy`.
  - Added `asize_bp_der_norm_cubic`: one annotated normalized
    partial-derivative step inherits the checked cubic one-step bound from
    `rpd_der_norm` under the legacy/non-backref erasure invariant.
  - The `rerase_bpder_norm_list` proof uses the existing map-congruence lemma
    explicitly; a blind `simp` did not push `map rerase` through the local row
    normalizer.
  - Local CI passed with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (about 26 seconds elapsed), and Isabelle `BackRefPilot`
    (about 3 seconds elapsed).

## Cubic Size-Bound Research Kickoff (2026-05-31)

- Branch: `codex/backref-values` at `89b40aa` before this kickoff note.
  Remote `origin/codex/backref-values` was already up to date with the checked
  reachable `BACKREF4` `cs` counterexample.
- Current dirty files before this note were this progress log plus local backup
  files `BackRefLang.thy~`, `BackRefLang4Pilot.thy~`, and `Lexer.thy~`. The
  backup files remain intentionally untracked and should not be committed.
- New research target from Chengsong: investigate how to reduce the size bound
  to cubic in the regex size for the non-backref fragment. Backreferences are
  explicitly excluded from the bounded fragment. The likely direction is a
  stronger, redesigned `bsimp` inspired by Antimirov partial derivatives and
  Chengsong's thesis final chapter, with a new 50k bounty pool and 25k reserved
  for the new simplifier definition.
- Important constraint: the new bound work must not weaken the checked
  backreference correctness path. Any new simplifier should have a clearly
  delimited non-backref fragment theorem first, then connect back to the
  current original files only through proved preservation lemmas.
- Checked first implementation checkpoint:
  - Added new bounty tasks `BR-031` through `BR-034` and raised the project
    pool to 100k simulated USD. `BR-032` reserves 25k for the new simplifier
    definition.
  - Added proof-only `rsimp3`/`rders_simp3` in `BasicIdentities.thy`.
    `rsimp3` keeps zero/one simplification, alternative flattening, and
    duplicate removal, and adds the Antimirov-style step that distributes a
    sequence over a left `RALTS` frontier. It intentionally does not distribute
    over right `RALTS`, because that would move right-side alternative choice
    bits before the left value in the annotated lexer.
  - Proved `RL_rsimp3`, the semantic preservation theorem for `rsimp3`.
  - Added annotated `bsimp3`/`bders_simp3` in `BlexerSimp.thy`, mirroring the
    left-frontier distribution while preserving right-hand choice-bit order.
  - Added `bsimp3_rerase` and `rders_simp3_size` in `FBound.thy`, establishing
    the transfer bridge from annotated states back to proof-only `rrexp`.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: define a non-backref partial-derivative universe whose
  elements are generated from original subterms and continuation contexts, then
  prove a cubic cardinality bound for that universe and show `rders_simp3`
  stays inside it.
- Checked second implementation checkpoint:
  - Added `rsubterms`, `rcontinuations`, and
    `partial_derivative_universe` in `GeneralRegexBound.thy`.
  - Proved `partial_derivative_universe_card_cubic`:
    `card (partial_derivative_universe r) <= (rsize r + 3)^3`.
    This is the first finite-universe replacement for the older
    `sizeNregex`-style counting argument; it is still an overapproximation,
    not yet the final closure theorem for `rders_simp3`.
  - Kept the proof granular: explicit `card_Un3_le`, `card_Un4_le`, image
    cardinality, and cubic padding lemmas. No long-running `auto`/`fun`
    proof search was introduced.
  - Local CI passed for both `Posix` and `BackRefPilot` after this checkpoint.
- Next research target: prove membership/closure, first for one derivative
  step and then for `rders_simp3`, showing that every generated frontier atom
  stays in `partial_derivative_universe r` for the non-backref fragment.
- Checked third implementation checkpoint:
  - Added `rlinear_continuations`, which keeps only syntactically reachable
    continuation contexts: sequence suffixes, star loop contexts, and bounded
    `RNTIMES r k` counters from the original `RNTIMES r n` node.
  - Proved `card_rlinear_continuations_le_rsize`, replacing the deliberately
    broad global-counter continuation set with a linear one.
  - Added `partial_derivative_frontier_universe` and proved
    `partial_derivative_frontier_universe_card_quadratic`:
    `card (partial_derivative_frontier_universe r) <= (rsize r + 2)^2`.
    This is the stronger cubic-size route: a quadratic number of frontier
    atoms times a linear atom-size bound, instead of the earlier cubic
    cardinality overapproximation.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: prove every element of the quadratic frontier universe
  has size at most linear in `rsize r`, then prove `rsimp3`/`rders_simp3`
  frontier membership for the non-backref fragment.
- Checked fourth implementation checkpoint:
  - Proved `rsubterms_member_size_le_rsize` and
    `rlinear_continuations_member_size_le_rsize`.
  - Proved `partial_derivative_frontier_universe_member_size_linear`:
    any atom in the quadratic frontier universe has structural size at most
    `Suc (rsize r + rsize r)`.
  - Corrected `partial_derivative_frontier_universe` to include reachable
    continuations themselves, not only `RSEQ p k` pairs. This is necessary
    because `rsimp3_SEQ_atom RONE k` simplifies directly to `k`.
    The cardinality theorem remains quadratic.
  - This establishes the two numeric ingredients for a cubic result:
    quadratic many frontier atoms, each of linear size. The remaining proof
    obligation is semantic/closure-shaped: show the actual `rsimp3` derivative
    frontier is a subset of this universe for the non-backref fragment.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: define a small `rfrontier`/normal-form extractor and
  prove closure lemmas for `rsimp3_SEQ`, then lift to one derivative step.
- Checked fifth implementation checkpoint:
  - Added proof-only `rsimp4`/`rders_simp4` in `BasicIdentities.thy`.
    `rsimp4` extends `rsimp3` by reassociating left-nested sequences:
    `SEQ (SEQ p k1) k2` is simplified recursively into a head-plus-continuation
    shape. This is the structural move needed for a cubic Antimirov-style
    frontier proof; without it, closure wants nested continuation towers.
  - Proved `RL_rsimp4`, the language preservation theorem.
  - The first draft used overlapping catch-all equations for `rsimp4_SEQ_atom`;
    that produced awkward split goals. The checked version uses explicit
    constructor equations, following the project rule that slow or strange
    proof states should be removed at the definition/proof-shape level.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: port `rsimp4` to annotated `bsimp4`, prove the
  `rerase` bridge, then use the quadratic frontier universe for closure.
- Checked sixth implementation checkpoint:
  - Added annotated `bsimp4`/`bders_simp4` in `BlexerSimp.thy`.
    The reassociation clause mirrors `rsimp4`: an `ASEQ` on the left is
    recursively converted into a head-plus-continuation shape while keeping
    bit prefixes in the corresponding annotated nodes.
  - Added `bsimp4_rerase` and `rders_simp4_size` in `FBound.thy`, proving
    that the annotated simplifier erases to `rsimp4`.
  - One subtle proof repair: `rerase_bsimp4_ASEQ` needs `rerase_fuse`
    explicitly, because the `AONE` case simplifies to `fuse (bs @ bs2) r2`
    while `rsimp4` sees only `rerase r2`.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: prove `rsimp4` frontier closure into
  `partial_derivative_frontier_universe`, then state the first actual cubic
  non-backref `rders_simp4` size theorem.
- Checked seventh implementation checkpoint:
  - Added recursive `rfrontier`/`rfrontiers` in `GeneralRegexBound.thy`.
    `RALTS` frontiers are now recursive, so nested alternatives are treated
    like Antimirov frontier sets rather than opaque syntax nodes.
  - Proved normalization lemmas for `rsimp_ALTs`, `rflts`, and `rdistinct`:
    if input frontiers are inside a set `U`, the normalized frontier remains
    inside `U`.
  - Added `rseq_sources` and `rfrontier_rsimp4_SEQ_subset`. This isolates the
    next closure obligation: to prove `rsimp4_SEQ` stays in a universe, it is
    enough to prove the row atoms `rsimp4_SEQ_atom x r2` stay there for each
    source `x` actually sequenced.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: prove row-atom closure for the quadratic frontier
  universe, or refine the continuation universe if the proof exposes a missing
  syntactic continuation shape.
- Checked eighth implementation checkpoint:
  - Added membership API lemmas for `partial_derivative_frontier_universe`:
    direct membership for `RZERO`, `RONE`, subterms, continuations, and
    `RSEQ p k` pairs.
  - Added `rnonseq` and proved
    `rfrontier_rsimp4_SEQ_atom_nonseq_subset`: if `p` is a non-`RSEQ`
    subterm, `k` is a reachable continuation, and `rfrontier k` is already in
    the universe, then the frontier of `rsimp4_SEQ_atom p k` stays in the
    quadratic frontier universe.
  - The proof exposed a useful design invariant: continuations cannot merely
    be members of the universe; their own frontiers must also be closed.
    This is now an explicit premise for the row-atom lemma instead of being
    hidden under automation.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: prove `rfrontier k` closure for all
  `k \<in> rlinear_continuations r`, then use it to discharge the row closure
  premise for derivative continuations.
- Checked ninth implementation checkpoint:
  - Proved `rfrontier_subset_rsubterms`/`rfrontiers_subset_rsubterms` by
    mutual induction over the recursive frontier view.
  - Proved `rsubterms_trans` and `rfrontier_subterm_subset`, so the frontier
    of any subterm of the original expression is directly inside
    `partial_derivative_frontier_universe`.
  - This is a small but important proof-throughput improvement: future closure
    cases can reduce subterm-frontier obligations without unfolding the whole
    universe each time.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Checked tenth implementation checkpoint:
  - Added `self_rsubterm`, `rlinear_continuations_subterm_subset`, and
    `partial_derivative_frontier_universe_subterm_mono`.
  - Proved `rfrontier_linear_continuation_subset`: every reachable
    continuation has its recursive frontier inside the parent quadratic
    frontier universe.
  - This discharges the extra continuation-frontier premise discovered by
    `rfrontier_rsimp4_SEQ_atom_nonseq_subset`, and makes the next target
    cleaner: row closure can now rely only on `p \<in> rsubterms r`,
    `k \<in> rlinear_continuations r`, and `rnonseq p`.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Checked eleventh implementation checkpoint:
  - Added `rfrontier_rsimp4_SEQ_atom_nonseq_subset'`, discharging the
    explicit continuation-frontier premise via
    `rfrontier_linear_continuation_subset`.
  - Added `rfrontier_rsimp4_SEQ_nonseq_sources_subset`: if all actual
    `rsimp4_SEQ` sources are non-`RSEQ` subterms and the right operand is a
    reachable continuation, the whole simplified sequence frontier is inside
    `partial_derivative_frontier_universe`.
  - This gives a compact target for the derivative closure induction: prove
    that the sources produced by one `rder`/`rsimp4` step are non-sequence
    subterms of the original and that the carried suffix is in
    `rlinear_continuations`.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Checked twelfth implementation checkpoint:
  - Added two small diagnostic lemmas showing that the current
    `rlinear_continuations` universe is too weak for nested sequencing.
    In the example `RSEQ (RSEQ (RSTAR (RCHAR a)) (RCHAR b)) (RCHAR c)`,
    the simple local-continuation set does not contain the composed suffix
    `RSEQ (RCHAR b) (RCHAR c)`.
  - The corresponding checked derivative lemma shows why this is a real
    closure issue rather than a proof accident: after differentiating by
    `a` and applying `rsimp4`, the frontier contains
    `RSEQ (RSTAR (RCHAR a)) (RSEQ (RCHAR b) (RCHAR c))`.
  - Design consequence: the next universe should use composed continuation
    contexts, not just immediate sequence suffixes. This matches the
    Antimirov/continuation view: frontier atoms are heads paired with the
    continuation accumulated along the path.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: define composed continuation contexts, prove their
  finite/cardinality and linear member-size bounds for the non-backref
  fragment, then replace `partial_derivative_frontier_universe` with this
  stronger checked universe.
- Checked thirteenth implementation checkpoint:
  - Added `rpath_continuations_acc`/`rpath_continuations`, a path-sensitive
    continuation universe. Unlike `rlinear_continuations`, this accumulates
    composed suffixes along the syntax path, so nested sequences such as
    `((a*) b) c` are represented by the actual continuation carried to each
    character position.
  - Proved `card_rpath_continuations_acc_le_rsize` and
    `card_rpath_continuations_le_rsize`: the number of path continuations is
    linear in the original regex size.
  - Proved `rpath_continuations_member_size_quadratic`: each carried
    continuation has size at most `1 + (rsize r + 2)^2` at top level. This is
    intentionally looser than the local linear-continuation bound, because
    nested star/sequence contexts can duplicate ancestor syntax along a path.
  - Added `partial_derivative_path_universe` with checked linear cardinality
    and quadratic member-size bounds. This is the new cubic route:
    linear many path atoms, each at most quadratic size.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: prove that one `rsimp4 (rder c r)` frontier is a subset
  of `partial_derivative_path_universe r` for `legacy_rrexp r`, then lift from
  one step to `rders_simp4`.
- Checked fourteenth implementation checkpoint:
  - Strengthened the `rsimp4` sequence atom with right-unit simplification:
    `rsimp4_SEQ_atom p RONE` now returns `p` for non-sequence atoms. The
    annotated `bsimp4_ASEQ_atom` mirrors this on `AONE`, and the existing
    `rerase` bridge remains checked.
  - This change is not cosmetic. Without right-unit elimination, top-level
    path continuations acquire artificial trailing `RONE` syntax, while the
    actual normalized derivative does not. The new rule aligns the path
    universe with the derivative shape and reduces residual size.
  - Added `partial_derivative_path_universe_*` membership lemmas and the
    checked nested-sequence sanity lemma
    `rsimp4_derivative_needs_path_continuation`.
  - Added `rder_path_continuations_acc` and proved
    `rder_path_continuations_universe_subset`, a modular overapproximation of
    one-symbol derivative positions. This isolates the next proof target:
    show that the `rsimp4 (rder c r)` frontier is contained in this
    path-derivative overapproximation.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: connect `rfrontier (rsimp4 (rder c r))` to
  `rder_path_continuations c r` for the legacy/non-backref fragment.
- Checked fifteenth implementation checkpoint:
  - Added a checked counterexample showing that the path-continuation universe
    is still not strong enough for full one-step `rsimp4` closure.
  - Example: for `RSEQ (RCHAR a) (RSEQ (RALTS [RCHAR b, RCHAR c]) (RCHAR d))`,
    differentiating by `a` and simplifying produces frontier atom
    `RSEQ (RCHAR b) (RCHAR d)`.
  - That atom is not in the current `partial_derivative_path_universe`.
    Reason: the current path universe records the carried suffix, while
    `rsimp4` also distributes a suffix whose left side is an alternative.
  - Design consequence: the final cubic universe should not be just
    path continuations. It must include the Antimirov frontier of simplified
    carried suffixes, still with a linear/quadratic accounting discipline.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: replace `rpath_continuations` with a frontier-aware
  path universe whose suffix component is `rfrontier (rsimp4 suffix)`, then
  reprove the linear-count/quadratic-size accounting.
- Checked sixteenth implementation checkpoint:
  - Added `rpath_frontier_acc`/`rpath_frontiers` and
    `partial_derivative_path_frontier_universe`.
  - This candidate records `rfrontier (rsimp4 carried_suffix)` at character
    positions, rather than only the carried suffix syntax. It therefore covers
    both classes of counterexample discovered so far.
  - Checked sanity lemmas:
    `left_nested_atom_in_path_frontier_universe` and
    `distributed_suffix_atom_in_path_frontier_universe`.
  - Added finite-frontier lemmas for `rfrontier`/`rfrontiers`, needed by the
    new universe.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: prove linear/quadratic accounting for
  `partial_derivative_path_frontier_universe`, then use it as the target for
  one-step `rsimp4 (rder c r)` closure.
- Checked seventeenth implementation checkpoint:
  - Proved `card_rfrontier_le_rsize` and `card_rfrontiers_le_rsizes`.
    This establishes that taking the recursive Antimirov-style frontier of a
    single syntax tree does not introduce more atoms than the tree size.
  - This is the first accounting lemma needed for the frontier-aware path
    universe: the remaining issue is bounding the size/cardinality of
    `rsimp4`-normalized carried suffixes.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Checked eighteenth implementation checkpoint:
  - Tightened the path-frontier universe definition at character leaves:
    `rpath_frontier_acc (RCHAR c) k` now records
    `rfrontier (rsimp4_SEQ RONE k)` rather than running a fresh full `rsimp4 k`.
  - Design reason: the carried continuation should be exposed through the same
    sequence normalizer used by `rsimp4_SEQ`. This lines up the `RCHAR`
    derivative case with the universe directly and avoids hiding an expensive
    full simplifier call inside the universe collector.
  - Added `rfrontier_rsimp4_SEQ_RONE_subset` and
    `card_rfrontier_rsimp4_SEQ_RONE_le`, showing that exposing an empty-left
    sequence continuation does not increase frontier cardinality.
  - Added `card_rfrontier_rsimp4_SEQ_atom_le`: appending a carried
    continuation to a single sequence atom increases exposed frontier count by
    at most the size of that atom. The only nontrivial branch is
    `RALTS ... RONE`, discharged with `card_rfrontiers_le_rsizes`.
  - Added `card_rfrontier_normalize_le_rfrontiers`,
    `card_rfrontiers_concat_rsimp4_seq_rows_le`, and
    `card_rfrontier_rsimp4_SEQ_le`. The last lemma gives a checked coarse
    product bound:
    `card (rfrontier (rsimp4_SEQ r k)) <=
    rsize r * Suc (card (rfrontier k))`.
    This is not the final cubic theorem, but it is a reusable accounting
    interface for one layer of Antimirov-style sequence distribution.
  - Added `rfrontier_rsimp4_SEQ_atom_member_size_quadratic`, a local size
    bound for frontier atoms exposed by a single sequence atom with a carried
    continuation:
    `q in rfrontier (rsimp4_SEQ_atom r k) ==> rsize q <=
    rsize k + (rsize r + 2)^2`.
    The proof deliberately splits `RONE`, `RSEQ`, and `RALTS ... RONE`
    instead of relying on broad automation.
  - Lifted that local estimate through normalization with
    `rfrontier_normalize_memberE`,
    `rfrontiers_concat_rsimp4_seq_rows_memberE`,
    `rfrontier_rsimp4_SEQ_single_member_size_quadratic`, and
    `rfrontier_rsimp4_SEQ_member_size_quadratic`.
  - Performance note: an intermediate version using broad `blast` timed out the
    full `Posix` build at 240 seconds. It was replaced by explicit
    one-step instantiation of the member-size lemma; the checked build then
    returned to normal timing.
  - Added `partial_derivative_path_frontier_universe_card_le`, reducing the
    remaining cubic accounting problem to bounding `rpath_frontiers`.
  - Started one-step derivative closure for the new path-frontier universe:
    base constructors `RZERO`, `RONE`, `RCHAR`, plus a compositional
    `RALTS` rule. The `RALTS` rule uses the Antimirov-style shape directly:
    normalize the mapped branch derivatives, extract a normalized frontier
    member, then transport it through
    `partial_derivative_path_frontier_universe_alt_child_mono`.
  - Added carried-continuation base closure lemmas for
    `rsimp4_SEQ (rsimp4 (rder c r)) k` on `RZERO`, `RONE`, and `RCHAR`.
    These are the base cases needed before attacking `RSEQ`, `RSTAR`, and
    `RNTIMES` with a generalized continuation theorem.
  - Added frontier-normalization equality facts:
    `rfrontiers_member_iff`, `rfrontiers_rdistinct_empty`,
    `rfrontiers_rflts`, `rfrontier_rsimp_ALTs_eq`, and
    `rfrontier_normalize_eq`. This upgrades earlier one-way normalization
    subset reasoning into set equality for frontiers.
  - Added `rfrontier_rsimp4_SEQ_memberE`, an eliminator that turns a member of
    `rfrontier (rsimp4_SEQ r k)` into a concrete sequence source `x` with
    `q in rfrontier (rsimp4_SEQ_atom x k)`. This is intended as the entry
    point for the upcoming `RSEQ` carried-closure proof.
  - Added `rsimp4_SEQ_atom_assoc`, a checked syntactic associativity lemma for
    sequence atoms:
    `rsimp4_SEQ_atom (rsimp4_SEQ_atom r1 r2) k =
    rsimp4_SEQ_atom r1 (rsimp4_SEQ_atom r2 k)`.
    This gives the local reassociation needed by the future `RSEQ` proof; the
    remaining hard part is lifting it through full `rsimp4_SEQ` where
    alternatives may distribute.
  - Added `rfrontier_rsimp4_SEQ_atom_source_subset`, the converse visibility
    direction for sequence sources: a source row's atom frontier is contained
    in the full `rsimp4_SEQ` frontier. Together with
    `rfrontier_rsimp4_SEQ_memberE`, this gives a controlled way to move between
    whole-frontier and row-frontier goals without broad search.
  - Added `rfrontier_rsimp4_SEQ_nonalt_eq_atom` and
    `rfrontier_rsimp4_SEQ_rsimp_ALTs_nonalt_subset`. These isolate the next
    invariant needed for full `RALTS`/`RSEQ` closure: normalized alternative
    rows must be `nonalt`, after which sequence-frontier normalization can be
    pushed through using row-wise subset proofs.
  - Failed path, intentionally not kept: trying to use the existing
    `nonnested` predicate as that invariant is too weak, because
    `nonnested (RSEQ a b)` is definitionally `True` and therefore does not
    constrain nested alternatives inside `a` or `b`. The next invariant should
    be `good`-style or a new sequence-normal-form predicate, not plain
    `nonnested`.
  - Added `good_rsimp4_SEQ_atom`: under `good-or-zero` inputs, the atom-level
    sequence normalizer preserves `good-or-zero`. This is the first checked
    replacement for the weak `nonnested` path and recursively constrains
    sequence structure via the existing `good` predicate.
  - Lifted that invariant to full `rsimp4_SEQ` with two small bridge lemmas:
    normalized/flattened alternative lists preserve `good-or-zero`, and
    concatenated `rsimp4_seq_row`s inherit the atom-level invariant. This gives
    later closure proofs a checked syntactic normal-form hook.
  - Added `good_rsimp4`: the whole `rsimp4` simplifier now has a checked
    `good-or-zero` output invariant. This packages the sequence and alternative
    cases for later derivative-closure proofs.
  - Added frontier-row bridge lemmas for `good` expressions and proved the
    carried `RALTS` closure:
    `rfrontier_rsimp4_SEQ_rder_RALTS_path_acc`. A normalized derivative row now
    traces back to an original alternative child before entering the parent
    path-frontier accumulator.
  - Found and checked a real design counterexample for the `RSEQ` closure path:
    current `rsimp4` can keep a middle alternative opaque after a non-empty
    head (`b ((c+d) e)` shape), while the current path-frontier universe records
    the fully distributed continuation instead. This is a simplifier/universe
    design issue, not a tactic issue.
  - Added `rsimp5`/`rders_simp5` prototype in `BasicIdentities.thy`. Its
    sequence normalizer converts both sides to alternative rows and takes a
    row-product, using `rsimp4_SEQ_atom` for zero/one and sequence reassociation.
    Checked sanity lemmas show the middle-alternative counterexample now yields
    both distributed rows `b (c e)` and `b (d e)`.
  - Proved `RL_rsimp5_SEQ` and `RL_rsimp5`. The proof factors through
    `rsimp5_alt_rows` and `rsimp5_seq_products`, so the row-product definition
    is now language-preserving.
  - Proved `good_rsimp5_SEQ` and `good_rsimp5`: the row-product simplifier also
    preserves the `good-or-zero` normal-form invariant.
  - Proved `legacy_rsimp5_SEQ`, `legacy_rsimp5`, and `legacy_rders_simp5`.
    The candidate cubic simplifier therefore preserves the non-backref fragment
    required by the theorem statement.
  - Added checked row-product length bounds: product row count is exactly the
    product of the two row-list lengths, and the two `rsimp5_alt_rows` lengths
    are bounded by the corresponding regex sizes. This is the first local
    multiplicative counting lemma for the cubic argument.
  - Important invariant note: `good` is still too weak for the final frontier
    cardinality proof, because a `good` sequence can contain an internal
    `RALTS`. The next proof layer should introduce a row-level alt-free/sequence
    normal-form predicate before claiming that each product row has frontier
    cardinality at most one.
  - Added checked `row_nf` predicate for product rows. Proved
    `row_nf_rsimp4_SEQ_atom`, `row_nf_rsimp5_seq_products`, and the conditional
    local bound
    `card_rfrontier_rsimp5_SEQ_le_size_product_if_row_nf`. The remaining local
    gap is now precise: show `rsimp5` outputs have `row_nf` alternative rows.
  - Closed that local gap with `rows_nf`: normalization through `rflts`,
    `rdistinct`, and `rsimp_ALTs` preserves row normal form; hence
    `rows_nf_rsimp5` holds. This yields the unconditional local frontier bound
    `card_rfrontier_rsimp5_SEQ_le_size_product` for simplified operands.
  - Added the bridge from rows to frontiers:
    `card_rfrontier_rows_nf_le_alt_rows` and
    `card_rfrontier_rsimp5_le_alt_rows`. Also checked that a binary-alternative
    sequence has four row-product alternatives under `rsimp5`. The helper
    `rfrontier_alt_rows_eq` is intentionally not a global simp rule; briefly
    marking it `[simp]` made unrelated proof lines run for tens of seconds.
  - Added an alternate atom-continuation universe:
    `rpath_atom_frontier_acc` and
    `partial_derivative_path_atom_frontier_universe`. This uses
    `rsimp4_SEQ_atom (rsimp4 r2) k` at sequence nodes, avoiding eager full
    row-product expansion. Checked sanity lemmas show it contains both the old
    distributed suffix example and the previously missed middle-alternative
    opaque row.
  - Added annotated `bsimp5`/`bders_simp5` in `BlexerSimp.thy` and proved the
    erasure bridge in `FBound.thy`: `bsimp5_rerase` and `rders_simp5_size`.
    This gives the cubic prototype a checked path from `arexp` back to the
    proof-level `rsimp5` skeleton.
  - Started replacing the old path-frontier proof interface with the
    atom-continuation universe. Added the card skeleton
    `partial_derivative_path_atom_frontier_universe_card_le`, alternative-child
    monotonicity, top-level RZERO/RONE/RCHAR/RALTS derivative closure, and
    carried RZERO/RONE/RCHAR/RALTS closure lemmas.
  - Added `rpath_dual_frontiers` and
    `partial_derivative_path_dual_frontier_universe`, the union of full
    continuation frontiers and atom-continuation frontiers. This is the current
    best candidate universe: full continuations cover distributed suffix rows,
    while atom continuations cover opaque middle-alternative rows. Checked both
    examples and added the dual card skeleton.
  - Lifted the old/atom proof interfaces into a real dual accumulator
    `rpath_dual_frontier_acc`. Added subset bridges, dual universe inclusion
    lemmas, and dual RZERO/RONE/RCHAR/RALTS closure lemmas for both top-level
    derivatives and carried derivatives.
  - Local CI passed for both `Posix` and `BackRefPilot`.

## Worker B Original Bitcoded/Simplifier Checkpoint (2026-05-27)

- Branch: `codex/backref-values` at `d8f84f7`; `git fetch --all --prune`
  found no newer remote core-constructor work. The worktree had only the two
  untracked backup files `BackRefLang.thy~` and `BackRefLang4Pilot.thy~`
  before this checkpoint.
- Scope respected: only `Blexer.thy` and `PROGRESS_BACKREF.md` were changed
  by Worker B.
  `RegLangs.thy`, `PosixSpec.thy`, `Lexer.thy`, and `LexerSimp.thy` were read
  only.
- Initial core blocker: before the concurrent edit, original `RegLangs.thy`
  still had only
  `ZERO/ONE/CH/SEQ/ALT/STAR/NTIMES`, and original `PosixSpec.thy` still has
  only `Void/Char/Seq/Right/Left/Stars`. Therefore the BR-027/BR-028
  constructor cases for `BACKREF4/HALF/RESIDUE`, the corresponding original
  value constructors, and the `injval`/`mkeps` bridge are not yet available.
  Worker B did not fake wrappers or introduce `bbit`, `barexp`, `gabexp`, or
  any new `BackRef*` wrapper files.
- Checked original-file scaffold added:
  - `Blexer.thy:erase_AALTs_ignore_bits [simp]`, mirroring the pilot
    `berase_BAALTs_ignore_bits` fact directly in the original `arexp` layer.
    This is a non-conflicting helper for future retrieve/derivative proofs
    where `AALTs` bit prefixes must not affect erasure.
- Precise BR-027 port sections to apply once Worker A lands the original core
  constructors:
  - Extend original `bit` with `Backbit string` unless admin chooses a
    different in-band string encoding.
  - Extend original `arexp` with annotated cases matching the frozen core
    arities: `ABACKREF4` for `BACKREF4`, `AHALF` for `HALF`, and `ARESIDUE`
    for `RESIDUE`. Use only these original constructors.
  - Port the pilot `BackRefGBlexer.gaintern/gabder/gretrieve` shape into
    original `intern/bder/retrieve`, and port the simple
    `BackRefBlexer.bbder_residue` shape into original `bder` for `RESIDUE`.
  - Preserve the original theorem names and interfaces:
    `erase_bder`, `retrieve_code`, `bmkeps_retrieve`, `bder_retrieve`,
    `MAIN_decode`, and `blexer_correctness`.
- Precise BR-028 port sections queued after BR-027 parses:
  - Add `eq1`, `flts`, `bsimp_ASEQ`, `bsimp_AALTs`, and `bsimp` cases for the
    new annotated constructors without replacing the aggressive rewrite route.
  - Extend `rrewrite/srewrite` only with constructor context rules and any
    approved semantics-preserving backreference simplifications.
  - Repair, in order, `rewrites_to_bsimp`, `rewrite_preserves_bder`,
    `central`, `main_blexer_simp`, and `blexersimp_correctness`.
- BR-029/BR-030 blocker: `BasicIdentities.thy`, `ClosedForms.thy`,
  `ClosedFormsBounds.thy`, `FBound.thy`, and `GeneralRegexBound.thy` still
  depend on the pre-migration `rrexp` skeleton. Their TODOs require admin/core
  approval on whether to migrate the closed-form chain to `rexp` or
  temporarily extend `rrexp`; Worker B made no speculative datatype edit.
- Build before the concurrent core edit:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin`
  passed after the scaffold with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:04
  elapsed), and local CI certificate generation. Baseline before the edit also
  passed with cached `Posix`/`BackRefPilot`.
- Final build after a concurrent `RegLangs.thy` core-constructor edit appeared
  in the worktree failed before Worker B-owned files were replayed. Failure:
  Isabelle could not prove termination of `RegLangs.thy:der` for the
  `BACKREF4` tail call
  `der c (SEQ r3 (SEQ (RESIDUE (rev cs) (rev cs)) r4))`. `RegLangs.thy` is
  outside Worker B's write scope, so this checkpoint stops with that blocker
  instead of editing the core layer.

## Original-File Migration Audit (2026-05-27)

- Admin direction: stop growing `BackRef*` wrapper files as bounty targets.
  Future bounty should only count direct extensions of the original `rexp`,
  `val`, `arexp`, `lexer`, `blexer`, `bsimp`, and bounds theorem chain.
- Round status: two subagents completed two read-only audit rounds:
  - semantic/value lane: `RegLangs.thy`, `PosixSpec.thy`, `Lexer.thy`,
    `LexerSimp.thy`
  - bitcoded/bounds lane: `Blexer.thy`, `BlexerSimp.thy`,
    `BasicIdentities.thy`, `GeneralRegexBound.thy`, `ClosedForms.thy`,
    `ClosedFormsBounds.thy`, `FBound.thy`
- Comment-only TODOs were added to original files. They mark which
  datatype/function/theorem families need definition augmentation, proof
  constructor cases, deletion/migration, or admin approval.
- New low-value active bounty: BR-023 `Original-file migration TODO audit`
  for admin review. No payout collected yet.
- Admin approval is required before implementation for the exact `rexp`
  constructor shape, value constructors/flattening, POSIX priority rule,
  bit-code representation, and whether bounds-only `rrexp` is removed or
  temporarily retained.
- Proof-performance rule remains mandatory: any Isabelle command running around
  10 seconds must be split or narrowed; a 200 second `fun`/proof command is a
  bug to fix, not a normal build delay.

## Current Branch

- Branch: `codex/backref-values`
- Base: `origin/main`
- PR #1 status: merged into `origin/main` at `e207e04`

## Build

Checked command:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin
```

Latest result:

- PASS on 2026-05-27 (abbypan) with no-cheat guard after adding simple lexer
  derivative-prefix API (`blexer_xders_*` family) to `BackRefValues.thy`.
  New checked lemmas mirror the existing `gblexer_gxders_*` family from
  `BackRefLang4Values.thy`, filling the asymmetry between simple and
  generalized lexer APIs. New facts:
  `blexer_xders_defined_BL_iff`,
  `blexer_xders_None_BL_iff`,
  `blexer_xders_Some_BL`,
  `xders_BPrf_BL_iff`,
  `blexer_xders_defined_BPrf_iff`,
  `blexer_xders_None_BPrf_iff`,
  `blexer_xders_Some_BPrf`,
  `blexer_xders_BPrf_obtains`,
  `blexer_xders_BL_obtains`,
  `blexer_xders_BL_cases`,
  `blexer_xders_BPrf_cases`,
  `blexer_xders_defined_POSIX_iff`,
  `blexer_xders_Some_POSIX`,
  `blexer_xders_None_POSIX_iff`,
  `blexer_xders_POSIX_obtains`,
  `blexer_xders_POSIX_cases`.
  The simple side now has POSIX-specific derivative-prefix lemmas that the
  generalized side does not yet have. Files changed:
  `BackRefValues.thy` (+170 lines), `PROGRESS_BACKREF.md`.

- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding individual left-quotient finite/card
  wrappers in the bounded-fragment blueprint. New checked facts in
  `BackRefBoundedBlueprint.thy` package `BL_bound`/`GBL_bound` results for
  single `Ders` quotients, derivative residual quotients, and the ordinary
  `BBACKREF` plus generalized `GBACKREF4` constructor instances, including
  `BL_bound_left_quotient_finite`,
  `GBL_bound_left_quotient_finite`,
  `BL_bound_left_quotient_card_bound`,
  `GBL_bound_left_quotient_card_bound`,
  `BL_bound_xders_left_quotient_finite`,
  `GBL_bound_gxders_left_quotient_finite`,
  `BL_bound_BBACKREF_left_quotient_finite`,
  `GBL_bound_GBACKREF4_left_quotient_finite`,
  `BL_bound_residual_left_quotient_finite`,
  `GBL_bound_residual_left_quotient_finite`,
  `BL_bound_BBACKREF_residual_left_quotient_card_bound`, and
  `GBL_bound_GBACKREF4_residual_left_quotient_card_bound`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+226) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 4.298 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 4.277 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:35 elapsed), cached Isabelle
  `BackRefPilot` (0:03 elapsed), and local CI certificate generation;
  explicit statement guard PASS. After fast-forwarding to remote commit
  `82e2ca7`, the autostash conflict was limited to the `PROGRESS_BACKREF.md`
  title/order and both progress entries plus theory changes were preserved.
  Final post-sync full local CI passed with no-cheat guard, bounty guard,
  admin role guard, cached Isabelle `Posix` (0:04 elapsed), cached Isabelle
  `BackRefPilot` (0:05 elapsed), and local CI certificate generation;
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding ordinary and generalized bitcoded
  frontend derivative-prefix residual-evidence wrappers. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_xders_BPrf_retrieve_iff`,
  `bblexer_frontends_xders_defined_BPrf_iff`,
  `bblexer_frontends_xders_None_BPrf_iff`,
  `bblexer_frontends_xders_Some_BPrf`,
  `bblexer_frontends_xders_BPrf_cases`,
  `gbblexer_frontends_gxders_GPrf_retrieve_iff`,
  `gbblexer_frontends_gxders_defined_GPrf_iff`,
  `gbblexer_frontends_gxders_None_GPrf_iff`,
  `gbblexer_frontends_gxders_Some_GPrf`, and
  `gbblexer_frontends_gxders_GPrf_cases`, packaging all three bitcoded
  frontend variants after a consumed derivative prefix `p` against explicit
  residual `BPrf`/`GPrf` evidence for `xders r p` / `gxders r p`. Files
  changed before this progress note: `BackRefBitcodedSummary.thy` (+168) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.905 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 1.019 seconds. Pre-progress full local CI passed with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix` (0:04 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed), and local CI certificate generation. After
  fast-forwarding to concurrent remote commit `abcd83e`, the autostash
  conflict was limited to the `BackRefBitcodedSummary.thy` generalized
  derivative-prefix insertion point and the `PROGRESS_BACKREF.md` title; both
  the remote `*_same_iff` wrappers and this residual-evidence wrapper set were
  preserved. Post-sync pilot-only local CI passed with `BackRefPilot` (0:18
  elapsed), with `BackRefBitcodedSummary` replaying in about 0.970 seconds.
  After rebasing over concurrent remote commit `645b9ec`, the conflict was
  limited to `PROGRESS_BACKREF.md` title/order and both progress entries plus
  theory changes were preserved. Final post-rebase full local CI passed with
  no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`, Isabelle
  `BackRefPilot`, and local CI certificate generation; explicit statement
  guard PASS. Next smallest safe step: stop until the admin opens a new
  bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS after adding ordinary and generalized
  derivative-prefix final retrieve correctness wrappers. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_xders_final_retrieve_correctness` and
  `gbblexer_frontends_gxders_final_retrieve_correctness`, packaging all three
  bitcoded frontend variants after a consumed derivative prefix `p` so any
  accepted output is the normalized residual final-retrieve output for
  `xders r (p @ s)` / `gxders r (p @ s)` and carries the corresponding
  `bmkeps`/`gmkeps` empty residual evidence. Files changed before this
  progress note: `BackRefBitcodedSummary.thy` (+44) and `PROGRESS_BACKREF.md`.
  Baseline pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.865 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 1.150 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:36 elapsed), cached Isabelle `BackRefPilot` (0:03 elapsed), and
  local CI certificate generation; explicit statement guard PASS. Final
  after-progress full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:37 elapsed), Isabelle `BackRefPilot` (0:18
  elapsed), `BackRefBitcodedSummary` replaying in about 0.988 seconds, and
  local CI certificate generation. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding ordinary and generalized bitcoded
  frontend derivative-prefix wrappers. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_xders_defined_BL_iff`,
  `bblexer_frontends_xders_None_BL_iff`,
  `bblexer_frontends_xders_Some_BL`,
  `bblexer_frontends_xders_BL_cases`,
  `bblexer_frontends_xders_final_cases`,
  `gbblexer_frontends_gxders_defined_GBL_iff`,
  `gbblexer_frontends_gxders_None_GBL_iff`,
  `gbblexer_frontends_gxders_Some_GBL`,
  `gbblexer_frontends_gxders_GBL_cases`, and
  `gbblexer_frontends_gxders_final_cases`, packaging all three bitcoded
  frontend variants after a consumed derivative prefix `p` against
  `p @ s` membership in the original ordinary/generalized language and the
  normalized residual final-retrieve output. Files changed before this
  progress note: `BackRefBitcodedSummary.thy` (+182) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.721 seconds. An initial post-edit proof attempt failed only for the
  bundled `Some` membership wrappers because `auto` did not extract the
  existential-defined equivalence strongly enough; the proof was narrowed to
  explicit per-frontend `blast` steps. Post-fix pilot-only local CI passed
  with `BackRefPilot` (0:18 elapsed), with `BackRefBitcodedSummary` replaying
  in about 2.025 seconds. Full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:34 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed, cached), and local CI certificate generation.
  After fast-forwarding to concurrent remote commit `57c8cdb`, the autostash
  conflict was limited to `PROGRESS_BACKREF.md` title/order and both progress
  entries plus theory changes were preserved. Final post-rebase full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:36 elapsed), Isabelle `BackRefPilot` (0:18 elapsed),
  `BackRefBitcodedSummary` replaying in about 0.930 seconds, and local CI
  certificate generation; explicit statement guard PASS. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only similarly
  direct downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS before rebasing over remote commit
  `97668d6`; during the rebase the broader remote derivative-prefix wrapper
  facts were preserved and the non-duplicated checked additions kept from this
  step are `bblexer_frontends_xders_same_iff` and
  `gbblexer_frontends_gxders_same_iff` in `BackRefBitcodedSummary.thy`.
  These package the three bitcoded frontend variants run on `xders r p` /
  `gxders r p` as rejecting together or accepting with one shared bit output
  exactly when `p @ s \<notin> BL r` / `p @ s \<notin> GBL r` or
  `p @ s \<in> BL r` / `p @ s \<in> GBL r`. Files changed before this
  progress note: `BackRefBitcodedSummary.thy` and `PROGRESS_BACKREF.md`.
  Next smallest safe step: stop until the admin opens a new bounty/phase, or
  add only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS after adding derivative-prefix `GPrf`
  packaging facts for the standalone generalized value lexer. New checked
  facts in `BackRefLang4Values.thy` are `gxders_GPrf_GBL_iff`,
  `gblexer_gxders_defined_GPrf_iff`,
  `gblexer_gxders_None_GPrf_iff`, `gblexer_gxders_Some_GPrf`,
  `gblexer_gxders_GPrf_obtains`, and
  `gblexer_gxders_GPrf_cases`, relating `gblexer (gxders r p) s`
  directly to explicit `GPrf` evidence for `gxders r p` and to
  `p @ s \<in> GBL r`. Files changed before this progress note:
  `BackRefLang4Values.thy` (+68) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefLang4Values` replaying in about 1.872 seconds. The first post-edit
  proof of `gxders_GPrf_GBL_iff` was too broad: simplification left two
  evidence-existence forms, and the next version still needed equality
  orientation normalization. It was replaced with an explicit chain through
  `s \<in> GBL (gxders r p)` plus a localized `auto` step. Post-fix pilot-only
  local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefLang4Values` replaying in about 2.061 seconds. Initial full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix`, Isabelle `BackRefPilot`, and local CI certificate generation;
  explicit statement guard PASS. After rebasing over concurrent remote commit
  `792a41d`, the progress conflict was limited to the title/order and both
  entries plus theory changes were preserved. Final post-rebase full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix`, Isabelle `BackRefPilot`, and local CI certificate generation;
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding ordinary and generalized bitcoded
  frontend final retrieve evidence wrappers. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_final_retrieve_correctness` and
  `gbblexer_frontends_final_retrieve_correctness`, packaging that any accepted
  result from any of the three bitcoded frontend variants is the normalized
  final derivative retrieve output and carries the corresponding
  `bmkeps`/`gmkeps` residual proof plus empty flat witness. Files changed
  before this progress note: `BackRefBitcodedSummary.thy` (+40) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.781 seconds. An initial proof attempt for the wrappers failed
  because the residual epsilon evidence did not follow from the normalized
  membership rewrite alone; the proof was narrowed to reuse the already
  checked per-frontend retrieve correctness lemmas. Post-fix pilot-only local
  CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.682 seconds. Full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:35 elapsed), Isabelle `BackRefPilot` (0:17 elapsed),
  `BackRefBitcodedSummary` replaying in about 0.720 seconds, and local CI
  certificate generation; explicit statement guard PASS. Sync note:
  `git pull --rebase --autostash origin codex/backref-values` fast-forwarded
  to `1dfb775`; the autostash conflicted only in `PROGRESS_BACKREF.md`, and
  both progress entries plus theory changes were preserved. Final post-sync
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:17 elapsed),
  `BackRefBitcodedSummary` replaying in about 1.716 seconds, and local CI
  certificate generation; explicit statement guard PASS. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only similarly
  direct downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after preserving the uncommitted generalized
  value-lexer case wrappers across the fast-forward to remote commit
  `3eb3be6` and adding derivative-prefix packaging facts for the standalone
  generalized value lexer. New checked facts in `BackRefLang4Values.thy` are
  `gblexer_gxders_defined_GBL_iff`, `gblexer_gxders_None_GBL_iff`,
  `gblexer_gxders_Some_GBL`, `gblexer_gxders_GBL_obtains`, and
  `gblexer_gxders_GBL_cases`, relating `gblexer (gxders r p) s` directly to
  `p @ s \<in> GBL r`. Files changed before this progress note:
  `BackRefLang4Values.thy` (+90 total since `3eb3be6`, including +47 in this
  step) and `PROGRESS_BACKREF.md`. Sync note: `git pull --rebase --autostash
  origin codex/backref-values` fast-forwarded to `3eb3be6`; the autostash
  conflicted only in `PROGRESS_BACKREF.md`, and both progress entries plus
  theory changes were preserved. Baseline post-sync pilot-only local CI passed
  with `BackRefPilot` (0:19 elapsed), with `BackRefLang4Values` replaying in
  about 2.084 seconds. An initial post-edit pilot check exposed an overly broad
  proof for `gblexer_gxders_GBL_obtains`; it was replaced by an explicit
  `s \<in> GBL (gxders r p)` step through `gxders_correctness`. Post-fix
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefLang4Values` replaying in about 2.174 seconds. Final full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:37 elapsed), Isabelle `BackRefPilot` (0:03 elapsed, cached), and local CI
  certificate generation; an explicit statement guard check also passed. After
  rebasing over concurrent remote commit `9a2d375`, the progress conflict was
  limited to title/order and both entries were preserved. Post-rebase
  pilot-only local CI passed with `BackRefPilot` (0:18 elapsed), with
  `BackRefLang4Values` replaying in about 2.690 seconds. Final post-rebase
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and local CI certificate generation; explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS after adding ordinary and generalized
  bitcoded frontend case wrappers keyed by the value lexer result. New checked
  facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_blexer_cases` and
  `gbblexer_frontends_gblexer_cases`, packaging that a failed
  `blexer`/`gblexer` run makes all three bitcoded frontend variants reject,
  while a successful value run gives the same retrieved bit output for all
  three frontend variants. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+38) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:18 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.631 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:18 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.784 seconds. Pre-progress
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:04 elapsed,
  cached), and local CI certificate generation; explicit statement guard PASS.
  Final
  after-progress full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:03
  elapsed), and local CI certificate generation; explicit statement guard
  PASS. Next smallest safe step: stop until the admin opens a new
  bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after preserving the uncommitted bitcoded frontend
  output equality wrappers across the fast-forward to remote commit `1ad2a3e`
  and adding ordinary/generalized frontend output uniqueness wrappers. New
  checked facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_output_unique` and
  `gbblexer_frontends_output_unique`, packaging that any two successful
  bitcoded frontend variants report the same bit output. Files changed before
  this progress note: `BackRefBitcodedSummary.thy` (+18 in this step, +42
  total uncommitted since `1ad2a3e`) and `PROGRESS_BACKREF.md`. Sync note:
  `git pull --rebase --autostash origin codex/backref-values` fast-forwarded
  to `1ad2a3e`; the autostash conflicted only in the progress title, and both
  progress entries plus theory changes were preserved. Baseline post-sync
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.637 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.719 seconds. Full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:35 elapsed), Isabelle `BackRefPilot` (0:03 elapsed, cached), and local CI
  certificate generation; explicit statement guard PASS. After rebasing over
  concurrent remote commit `b23b16a`, the progress conflict was limited to the
  title/order and all progress entries were preserved. Post-rebase pilot-only
  local CI passed with `BackRefPilot` (0:18 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.626 seconds. Final post-rebase
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and
  local CI certificate generation; explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding bitcoded frontend output equality
  wrappers for ordinary and generalized value evidence. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_blexer_retrieve_eq`,
  `bblexer_frontends_POSIX_retrieve_eq`, and
  `gbblexer_frontends_gblexer_retrieve_eq`, packaging that any reported bit
  output from the three frontend variants is the retrieve output for the
  known `blexer`/POSIX/`gblexer` value. Files changed before this progress
  note: `BackRefBitcodedSummary.thy` (+24) and `PROGRESS_BACKREF.md`.
  Baseline pilot-only local CI passed with `BackRefPilot` (0:16 elapsed),
  with `BackRefBitcodedSummary` replaying in about 0.545 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.582 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:34 elapsed), Isabelle `BackRefPilot` (0:03 elapsed, cached), and
  local CI certificate generation; explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding direct generalized value-lexer accept/reject case
  wrappers. New checked facts in `BackRefLang4Values.thy` are
  `gblexer_defined_GBL_iff`, `gblexer_None_GBL_iff`,
  `gblexer_GBL_cases`, and `gblexer_GPrf_cases`, packaging the standalone
  generalized value lexer against `GBL` membership and explicit `GPrf`
  evidence without changing `gbrexp`, `GBL`, `gxder`, `GPrf`, or production
  lexer files. Files changed before this progress note:
  `BackRefLang4Values.thy` (+43) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:18 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefLang4Values` replaying in about 1.980 seconds. Pre-progress full
  local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:04 elapsed,
  cached), and local CI certificate generation. Final after-progress full
  local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation; a subsequent explicit statement guard
  check also passed. Next smallest safe step: stop until the admin opens a new
  bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding generalized value-lexer evidence packaging facts.
  New checked facts in `BackRefLang4Values.thy` are `gblexer_Some_GBL`,
  `gblexer_GBL_obtains`, `gblexer_defined_GPrf_iff`, and
  `gblexer_None_GPrf_iff`, aligning the standalone generalized value lexer
  with the ordinary value and bitcoded wrapper style without changing
  `gbrexp`, `GBL`, `gxder`, or `GPrf`. Files changed before this progress
  note: `BackRefLang4Values.thy` (+35) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). An initial
  post-edit pilot check exposed one overly implicit option-case proof in
  `gblexer_None_GPrf_iff`; the proof was replaced by an explicit
  `None`-versus-`Some` equivalence. Post-fix pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefLang4Values` replaying in about
  2.208 seconds. Pre-progress full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed, cached), and local CI certificate generation.
  Final after-progress full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:18 elapsed), `BackRefLang4Values` replaying in about 2.043 seconds, and
  local CI certificate generation. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding explicit accept/reject case wrappers for the
  ordinary and generalized bitcoded frontend groups keyed by final derivative
  nullability. New checked facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_xnullable_cases` and
  `gbblexer_frontends_gnullable_cases`, packaging all three frontend variants
  to reject together when `xnullable (xders r s)` / `gnullable (gxders r s)`
  is false and to return the same normalized final retrieval bit witness when
  it is true. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+66) and `PROGRESS_BACKREF.md`. Baseline
  synced pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.494 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.550 seconds. Pre-progress full
  local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:37 elapsed), Isabelle `BackRefPilot` (0:03 elapsed,
  cached), and local CI certificate generation. Explicit after-progress guards
  passed: statement guard, no-cheat guard, bounty guard, and admin role guard.
  Final after-progress full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot`
  (0:18 elapsed), `BackRefBitcodedSummary` replaying in about 0.668 seconds,
  and local CI certificate generation. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS after adding derivative-nullability
  wrappers for the ordinary and generalized bitcoded frontend groups. New
  checked facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_xnullable_iff`,
  `bblexer_frontends_xnullable_same_iff`,
  `gbblexer_frontends_gnullable_iff`, and
  `gbblexer_frontends_gnullable_same_iff`, packaging all three frontend
  variants against the nullable final derivative (`xnullable (xders r s)` /
  `gnullable (gxders r s)`) and the shared accepted-input bit witness. Files
  changed before this progress note: `BackRefBitcodedSummary.thy` (+110) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.479 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.517 seconds. Pre-progress full local CI passed with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix` (0:37 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed, cached), and local CI certificate generation;
  explicit statement guard PASS. After fast-forwarding to concurrent remote
  commit `e0aee64` and then rebasing over `23fb6c1`, the progress conflicts
  were limited to title/order; all progress entries were preserved. Final
  post-rebase full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:17
  elapsed), `BackRefBitcodedSummary` replaying in about 0.564 seconds, and
  local CI certificate generation; explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct semantic left-quotient and
  residual-left-quotient finiteness/cardinality wrappers in
  `BackRefBoundedBlueprint.thy`. New checked facts are
  `bounded_language_left_quotient_finite`,
  `bounded_language_left_quotient_card_bound`,
  `bounded_backref_lang_left_quotient_finite`,
  `bounded_backref_lang4_left_quotient_finite`,
  `bounded_backref_lang_left_quotient_card_bound`,
  `bounded_backref_lang4_left_quotient_card_bound`,
  `bounded_language_residual_left_quotient_finite`,
  `bounded_language_residual_left_quotient_card_bound`,
  `bounded_backref_lang_residual_left_quotient_finite`,
  `bounded_backref_lang4_residual_left_quotient_finite`,
  `bounded_backref_lang_residual_left_quotient_card_bound`, and
  `bounded_backref_lang4_residual_left_quotient_card_bound`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+142) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:19 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 5.2 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 4.7 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle
  `BackRefPilot` (0:16 elapsed), local CI certificate generation, and
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct semantic left-quotient member
  length wrappers in `BackRefBoundedBlueprint.thy`. New checked facts are
  `bounded_language_left_quotient_length_bound`,
  `bounded_language_left_quotient_length_bound_mono`,
  `bounded_backref_lang_left_quotient_length_bound`,
  `bounded_backref_lang4_left_quotient_length_bound`,
  `bounded_backref_lang_left_quotient_length_bound_mono`, and
  `bounded_backref_lang4_left_quotient_length_bound_mono`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+65) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 3.8 seconds. Post-edit pilot-only local CI passed with `BackRefPilot`
  (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in about 4.5
  seconds. Full local CI passed with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:03
  elapsed), local CI certificate generation, and explicit statement guard
  PASS. Next smallest safe step: stop until the admin opens a new
  bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS after adding exact accept/reject case
  wrappers for the ordinary and generalized bitcoded frontend groups. New
  checked facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_BL_final_cases` and
  `gbblexer_frontends_GBL_final_cases`, packaging all three frontend variants
  to reject together outside `BL`/`GBL` and to return the same normalized
  unsimplified final retrieval expression on accepted inputs. Files changed
  before this progress note: `BackRefBitcodedSummary.thy` (+70) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.244 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.307 seconds. Final after-progress full local CI passed with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:36 elapsed),
  Isabelle `BackRefPilot` (0:17 elapsed), `BackRefBitcodedSummary` replaying
  in about 0.323 seconds, and local CI certificate generation; explicit
  statement guard passed. After fast-forwarding to concurrent remote commit
  `8f6b34e`, the autostash conflicted only in the progress title; both
  progress entries were preserved. Post-sync pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.302 seconds. Final post-sync full local CI passed with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:35 elapsed),
  Isabelle `BackRefPilot` (0:17 elapsed), `BackRefBitcodedSummary` replaying
  in about 0.280 seconds, and local CI certificate generation; explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. After rebasing over concurrent commit `4643efa`, both
  the compact accept/reject wrappers and the final-case wrappers were
  preserved. Post-rebase pilot-only local CI passed with `BackRefPilot` (0:18
  elapsed), with `BackRefBitcodedSummary` replaying in about 0.533 seconds.
  Final post-rebase full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:17 elapsed), `BackRefBitcodedSummary` replaying in about 0.590 seconds,
  and local CI certificate generation; explicit statement guard PASS.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding compact accept/reject iff wrappers
  for the ordinary and generalized bitcoded frontend groups. New checked facts
  in `BackRefBitcodedSummary.thy` are `bblexer_frontends_all_None_iff`,
  `bblexer_frontends_same_Some_iff`, `gbblexer_frontends_all_None_iff`, and
  `gbblexer_frontends_same_Some_iff`, packaging that all three frontend
  variants reject exactly outside `BL`/`GBL` and have a shared `Some` witness
  exactly on accepted inputs. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+48) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.244 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:18 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.449 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:34 elapsed), Isabelle `BackRefPilot` (0:18 elapsed),
  `BackRefBitcodedSummary` replaying in about 0.408 seconds, local CI
  certificate generation, and explicit statement guard PASS. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only similarly
  direct downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after preserving the uncommitted final-same wrappers across the
  sync with remote commit `d3e6736` and adding normalized `Some` iff wrappers
  for the ordinary and generalized bitcoded frontend groups. New checked facts
  in `BackRefBitcodedSummary.thy` are `bblexer_frontends_BL_same_iff` and
  `gbblexer_frontends_GBL_same_iff`, packaging all three frontend variants to
  use the same unsimplified final retrieval expression in their accepted-input
  characterization. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+56 total since `d3e6736`, including +24 in
  this step) and `PROGRESS_BACKREF.md`. Sync note: `git pull --rebase
  --autostash origin codex/backref-values` fast-forwarded to `d3e6736`; the
  autostash conflicted only in the progress title, and both progress entries
  were preserved. Baseline synced pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.225 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.275 seconds. Pre-progress full local CI passed with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle
  `BackRefPilot` (0:17 elapsed), `BackRefBitcodedSummary` replaying in about
  0.282 seconds, and local CI certificate generation. Final after-progress
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:18 elapsed),
  `BackRefBitcodedSummary` replaying in about 0.290 seconds, local CI
  certificate generation, and explicit statement guard PASS. After rebasing
  over concurrent commit `ec2957d`, pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.264 seconds; final post-rebase full local CI passed with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:04 elapsed),
  Isabelle `BackRefPilot` (0:04 elapsed), local CI certificate generation, and
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `BackRefPilot`, and final full local CI after adding direct
  residual left-quotient member length wrappers in
  `BackRefBoundedBlueprint.thy`. New checked facts are
  `bounded_language_residual_left_quotient_length_bound`,
  `bounded_language_residual_left_quotient_length_bound_mono`,
  `bounded_backref_lang_residual_left_quotient_length_bound`,
  `bounded_backref_lang4_residual_left_quotient_length_bound`,
  `bounded_backref_lang_residual_left_quotient_length_bound_mono`, and
  `bounded_backref_lang4_residual_left_quotient_length_bound_mono`. Files
  changed before this progress note: `BackRefBoundedBlueprint.thy` (+87) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:19 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 3.8 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 3.8 seconds. Full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot`
  (0:03 elapsed), and local CI certificate generation. After rebasing over
  concurrent commit `59345fb`, final post-rebase full local CI passed with
  no-cheat guard, bounty guard, admin role guard, Isabelle `Posix` (0:35
  elapsed), Isabelle `BackRefPilot` (0:17 elapsed), local CI certificate
  generation, and explicit statement guard PASS. Next smallest safe step:
  stop until the admin opens a new bounty/phase, or add only similarly direct
  downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `BackRefPilot`, and final full local CI after adding direct
  residual-derivative member length wrappers in
  `BackRefBoundedBlueprint.thy`. New checked facts are
  `BL_bound_residual_derivative_length_bound`,
  `GBL_bound_residual_derivative_length_bound`,
  `BL_bound_residual_derivative_length_bound_mono`,
  `GBL_bound_residual_derivative_length_bound_mono`,
  `BL_bound_BBACKREF_residual_derivative_length_bound`,
  `GBL_bound_GBACKREF4_residual_derivative_length_bound`,
  `BL_bound_BBACKREF_residual_derivative_length_bound_mono`, and
  `GBL_bound_GBACKREF4_residual_derivative_length_bound_mono`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+87) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed). An initial post-edit pilot check exposed a
  local theorem-instantiation error in two monotone constructor wrappers; the
  proofs were narrowed to use `OF assms(...)` plus the remaining family member
  arguments. Post-fix pilot-only local CI passed with `BackRefPilot` (0:17
  elapsed), with `BackRefBoundedBlueprint` replaying in about 3.2 seconds.
  Full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation. After-progress explicit guards passed:
  bounty guard, no-cheat guard, statement guard, and admin role guard. Final
  after-progress pilot-only local CI passed with `BackRefPilot` (0:17 elapsed),
  with `BackRefBoundedBlueprint` replaying in about 3.5 seconds. Next smallest
  safe step: stop until the admin opens a new bounty/phase, or add only
  similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding monotone family-member length wrappers
  in `BackRefBoundedBlueprint.thy`. New checked facts are
  `bounded_strings_family_member_length_bound_mono`,
  `BL_bound_derivative_family_member_length_bound_mono`,
  `GBL_bound_derivative_family_member_length_bound_mono`,
  `BL_bound_residual_derivative_family_member_length_bound_mono`,
  `GBL_bound_residual_derivative_family_member_length_bound_mono`,
  `BL_bound_left_quotient_family_member_length_bound_mono`,
  `GBL_bound_left_quotient_family_member_length_bound_mono`,
  `BL_bound_xders_left_quotient_family_member_length_bound_mono`,
  `GBL_bound_gxders_left_quotient_family_member_length_bound_mono`,
  `BL_bound_BBACKREF_derivative_family_member_length_bound_mono`,
  `GBL_bound_GBACKREF4_derivative_family_member_length_bound_mono`,
  `BL_bound_BBACKREF_residual_derivative_family_member_length_bound_mono`,
  `GBL_bound_GBACKREF4_residual_derivative_family_member_length_bound_mono`,
  `BL_bound_BBACKREF_left_quotient_family_member_length_bound_mono`,
  `GBL_bound_GBACKREF4_left_quotient_family_member_length_bound_mono`,
  `BL_bound_BBACKREF_xders_left_quotient_family_member_length_bound_mono`, and
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_member_length_bound_mono`.
  Files changed before this progress note: `BackRefBoundedBlueprint.thy`
  (+183) and `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 4.0 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle
  `BackRefPilot` (0:03 elapsed), local CI certificate generation, and explicit
  statement guard PASS. After rebasing over concurrent commit `10be0c0`, final
  post-rebase full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:17
  elapsed), local CI certificate generation, `BackRefBoundedBlueprint`
  replaying in about 3.8 seconds, and explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding normalized final-result wrappers for the ordinary
  and generalized bitcoded lexer frontend groups. New checked facts in
  `BackRefBitcodedSummary.thy` are `bblexer_frontends_final_same` and
  `gbblexer_frontends_final_same`, packaging all three frontend variants to
  return the same unsimplified final retrieval expression on accepted
  `BL`/`GBL` inputs and `None` otherwise. Files changed before this progress
  note: `BackRefBitcodedSummary.thy` (+32) and `PROGRESS_BACKREF.md`.
  Baseline pilot-only local CI passed with `BackRefPilot` (0:17 elapsed).
  Post-edit pilot-only local CI passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBitcodedSummary` replaying in about 0.267 seconds. Pre-progress
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:34 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation. Final after-progress full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix`, Isabelle `BackRefPilot`, local CI certificate generation, and
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding accept/reject case wrappers for the ordinary and
  generalized bitcoded lexer frontend groups. New checked facts in
  `BackRefBitcodedSummary.thy` are `bblexer_frontends_BL_cases` and
  `gbblexer_frontends_GBL_cases`, packaging each frontend family into one
  case split: either the input is outside `BL`/`GBL` and all three frontends
  reject, or the input is accepted and all three frontends return the same
  bitcode witness. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+54) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBitcodedSummary` replaying in about 0.208 seconds. Pre-progress
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:36 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation. Final after-progress full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), local CI
  certificate generation, and explicit statement guard PASS. After rebasing
  over concurrent commit `a202417`, final post-rebase full local CI passed
  with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:03 elapsed), Isabelle `BackRefPilot` (0:16 elapsed), local CI
  certificate generation, `BackRefBitcodedSummary` replaying in about 0.599
  seconds, and explicit statement guard PASS. Next smallest safe step: stop
  until the admin opens a new bounty/phase, or add only similarly direct
  downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `BackRefPilot`, and final full local CI after rebasing over
  concurrent commit `f8a12a2` and adding direct constructor-specialized
  bounded-family member-length wrappers in `BackRefBoundedBlueprint.thy`.
  New checked facts are
  `BL_bound_BBACKREF_derivative_family_member_length_bound`,
  `GBL_bound_GBACKREF4_derivative_family_member_length_bound`,
  `BL_bound_BBACKREF_residual_derivative_family_member_length_bound`,
  `GBL_bound_GBACKREF4_residual_derivative_family_member_length_bound`,
  `BL_bound_BBACKREF_left_quotient_family_member_length_bound`,
  `GBL_bound_GBACKREF4_left_quotient_family_member_length_bound`,
  `BL_bound_BBACKREF_xders_left_quotient_family_member_length_bound`, and
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_member_length_bound`.
  Files changed before this progress note: `BackRefBoundedBlueprint.thy`
  (+88) and `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:19 elapsed). Pre-rebase post-edit pilot-only local CI
  passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBoundedBlueprint` replaying in about 3.9 seconds. Final
  post-rebase full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate
  generation, and explicit statement guard PASS. Next smallest safe step:
  stop until the admin opens a new bounty/phase, or add only similarly direct
  downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding same-witness accepted-input wrappers for all
  ordinary and generalized bitcoded lexer frontends. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_BL_obtains_same` and
  `gbblexer_frontends_GBL_obtains_same`, packaging that the ordinary,
  post-derivative simplified, and per-step simplified frontends return the
  same bitcode witness on accepted `BL`/`GBL` inputs. Files changed before
  this progress note: `BackRefBitcodedSummary.thy` (+30) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed) and `BackRefBitcodedSummary` replaying in
  about 0.208 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:36 elapsed), Isabelle
  `BackRefPilot` (0:17 elapsed), local CI certificate generation, and
  `BackRefBitcodedSummary` replaying in about 0.184 seconds. A final
  after-progress verification pass also passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:03 elapsed), Isabelle
  `BackRefPilot` (0:03 elapsed), local CI certificate generation, and explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. After rebasing over concurrent commit `3932865`,
  final post-rebase full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:18 elapsed), local CI certificate generation, `BackRefBitcodedSummary`
  replaying in about 0.239 seconds, and explicit statement guard PASS.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `BackRefPilot`, and final full local CI after rebasing over
  `e6bed9d`, preserving the residual left-quotient length wrappers, and adding
  direct bounded-family member-length wrappers in `BackRefBoundedBlueprint.thy`.
  New checked facts on top of the preserved residual length wrappers are
  `bounded_strings_family_member_length_bound`,
  `BL_bound_derivative_family_member_length_bound`,
  `GBL_bound_derivative_family_member_length_bound`,
  `BL_bound_residual_derivative_family_member_length_bound`,
  `GBL_bound_residual_derivative_family_member_length_bound`,
  `BL_bound_left_quotient_family_member_length_bound`,
  `GBL_bound_left_quotient_family_member_length_bound`,
  `BL_bound_xders_left_quotient_family_member_length_bound`, and
  `GBL_bound_gxders_left_quotient_family_member_length_bound`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+152 total since
  `e6bed9d`, including +78 for the new family-member wrappers) and
  `PROGRESS_BACKREF.md`. Post-sync pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), and post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 3.6 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, local CI
  certificate generation, and explicit statement guard PASS. Next smallest
  safe step: stop until the admin opens a new bounty/phase, or add only
  similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `BackRefPilot`, and final full local CI after rebasing over
  `85e7ba5` and preserving the direct bounded-language wrapper work. New
  checked facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_blexer_Some_retrieve`,
  `bblexer_frontends_BL_obtains`, and
  `gbblexer_frontends_GBL_obtains`, packaging successful ordinary value-lexer
  retrieval and accepted-input bitcode witnesses for all ordinary and
  generalized bitcoded frontends. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+38) and `PROGRESS_BACKREF.md`. Post-sync
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBitcodedSummary` replaying in about 0.161 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:36 elapsed), Isabelle `BackRefPilot` (0:17 elapsed), local CI
  certificate generation, and `BackRefBitcodedSummary` replaying in about
  0.214 seconds. Next smallest safe step: stop until the admin opens a new
  bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct member-length wrappers for
  residual left-quotient families in `BackRefBoundedBlueprint.thy`. New
  checked facts are `BL_bound_xders_left_quotient_length_bound`,
  `GBL_bound_gxders_left_quotient_length_bound`,
  `BL_bound_xders_left_quotient_length_bound_mono`,
  `GBL_bound_gxders_left_quotient_length_bound_mono`,
  `BL_bound_BBACKREF_xders_left_quotient_length_bound`,
  `GBL_bound_GBACKREF4_gxders_left_quotient_length_bound`,
  `BL_bound_BBACKREF_xders_left_quotient_length_bound_mono`, and
  `GBL_bound_GBACKREF4_gxders_left_quotient_length_bound_mono`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+74) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 3.5 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle
  `BackRefPilot` (0:17 elapsed), and local CI certificate generation; explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct bounded-language wrappers in
  `BackRefBoundedBlueprint.thy`. New checked facts package the original
  `BL r`/`GBL r` languages from successful `BL_bound`/`GBL_bound`
  calculations into bounded-string subsets, cardinality bounds, finiteness,
  member length bounds, monotone variants, and direct `BBACKREF`/`GBACKREF4`
  specializations. New facts include `BL_bound_subset_bounded_strings`,
  `GBL_bound_subset_bounded_strings`, `BL_bound_card_bound`,
  `GBL_bound_card_bound`, `BL_bound_finite`, `GBL_bound_finite`,
  `BL_bound_length_bound`, `GBL_bound_length_bound`,
  `BL_bound_BBACKREF_subset_bounded_strings`,
  `GBL_bound_GBACKREF4_subset_bounded_strings`,
  `BL_bound_BBACKREF_card_bound`, `GBL_bound_GBACKREF4_card_bound`,
  `BL_bound_BBACKREF_finite`, `GBL_bound_GBACKREF4_finite`,
  `BL_bound_BBACKREF_length_bound`, and
  `GBL_bound_GBACKREF4_length_bound`, with monotone variants for each bound
  family. Files changed before this progress note:
  `BackRefBoundedBlueprint.thy` (+303). Baseline pilot-only local CI passed
  with `BackRefPilot` (0:16 elapsed). Post-edit pilot-only local CI passed
  with `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint`
  replaying in about 4.1 seconds. Final full local CI passed with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:40 elapsed),
  Isabelle `BackRefPilot` (0:19 elapsed), and local CI certificate
  generation; explicit statement guard PASS. After rebasing over remote commit
  `4b952c2`, pilot-only local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 3.8 seconds. Final full
  post-rebase local CI passed with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:36 elapsed), Isabelle `BackRefPilot` (0:17
  elapsed), and local CI certificate generation; explicit statement guard
  PASS. Next smallest safe step: stop until the admin opens a new bounty/phase
  or explicitly asks for more direct packaging. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after
  rebasing over concurrent commit `a6f9492` and preserving its membership
  implication wrappers in `BackRefBitcodedSummary.thy`. New checked facts are
  `bblexer_frontends_blexer_iff` and `gbblexer_frontends_gblexer_iff`,
  packaging direct value-lexer `Some`/`None` iff summaries for all ordinary
  and generalized bitcoded lexer frontends. Files changed before this progress
  note: `BackRefBitcodedSummary.thy` (+30) and `PROGRESS_BACKREF.md`.
  Post-rebase pilot-only local CI passed with `BackRefPilot` (0:18 elapsed),
  with `BackRefBitcodedSummary` replaying in about 0.460 seconds. Final full
  local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:39 elapsed), Isabelle `BackRefPilot` (0:16 elapsed),
  local CI certificate generation, and explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after
  rebasing over concurrent commit `d04e3ba` and preserving its raw-language
  final-result wrappers in `BackRefBitcodedSummary.thy`. New checked facts on
  top of that commit are `bblexer_frontends_defined_BL_iff`,
  `bblexer_frontends_Some_BL`, `gbblexer_frontends_defined_GBL_iff`, and
  `gbblexer_frontends_Some_GBL`. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+26). Baseline pilot-only local CI before the
  rebase passed with `BackRefPilot` (0:17 elapsed), and the immediate
  post-edit pilot-only local CI passed with `BackRefPilot` (0:18 elapsed).
  Post-rebase pilot-only local CI passed with `BackRefPilot` (0:17 elapsed),
  with `BackRefBitcodedSummary` replaying in about 0.145 seconds. Final full
  local CI after continuing the rebase passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:34 elapsed), Isabelle
  `BackRefPilot` (0:03 elapsed), and local CI certificate generation; explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after adding
  direct raw-language final-result summary wrappers for all ordinary and
  generalized bitcoded lexer frontends in `BackRefBitcodedSummary.thy`. New
  checked facts are `bblexer_frontends_final_membership`,
  `bblexer_frontends_BL_iff`, `gbblexer_frontends_final_membership`, and
  `gbblexer_frontends_GBL_iff`. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+66) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.132 seconds. After rebasing
  over concurrent commit `3ca06b2` and preserving its value-lexer progress
  note, final full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:16
  elapsed), and local CI certificate generation; `BackRefBitcodedSummary`
  replayed in about 0.119 seconds, and explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after adding
  value-lexer packaging wrappers in `BackRefValues.thy`. New checked facts are
  `blexer_Some_BL`, `blexer_BL_obtains`, `blexer_defined_BPrf_iff`,
  `blexer_None_BPrf_iff`, `blexer_defined_POSIX_iff`, and
  `blexer_None_POSIX_iff`. Files changed before this progress note:
  `BackRefValues.thy` (+84). Baseline pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed). An initial post-edit pilot replay exposed two
  overly terse `None` wrapper proofs; those were replaced with explicit option
  cases. After rebasing over remote commit `4b17049`, pilot-only local CI
  passed with `BackRefPilot` (0:17 elapsed), `BackRefValues` replaying in about
  11.0 seconds, and the synced `BackRefBitcodedSummary` theory replaying in
  about 0.099 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:03 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed), and local CI certificate generation; explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding direct retrieve-iff summary wrappers
  for all ordinary and generalized bitcoded lexer frontends in
  `BackRefBitcodedSummary.thy`. New checked facts are
  `bblexer_frontends_POSIX_retrieve_iff`,
  `bblexer_frontends_BPrf_retrieve_iff`,
  `bblexer_frontends_defined_BPrf_iff`,
  `bblexer_frontends_None_BPrf_iff`, and
  `gbblexer_frontends_GPrf_retrieve_iff`. Files changed before this progress
  note: `BackRefBitcodedSummary.thy` (+56) and `PROGRESS_BACKREF.md`.
  Baseline pilot-only local CI passed with `BackRefPilot` (0:17 elapsed).
  Post-edit pilot-only local CI passed with `BackRefPilot` (0:17 elapsed),
  with `BackRefBitcodedSummary` replaying in about 0.131 seconds. Final full
  local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation; explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after
  rebasing over concurrent commit `8e5377e` and adding the new downstream
  packaging theory `BackRefBitcodedSummary.thy` to `pilot/ROOT`. New checked
  facts are `bblexer_frontends_eq`,
  `bblexer_frontends_blexer_retrieve`,
  `bblexer_frontends_POSIX_retrieve`,
  `bblexer_frontends_defined_POSIX_iff`,
  `bblexer_frontends_None_POSIX_iff`, `gbblexer_frontends_eq`,
  `gbblexer_frontends_gblexer_retrieve`,
  `gbblexer_frontends_gblexer_Some_retrieve`,
  `gbblexer_frontends_defined_GPrf_iff`, and
  `gbblexer_frontends_None_GPrf_iff`. Files changed before this progress
  note: `BackRefBitcodedSummary.thy` (+86) and `pilot/ROOT` (+1), with
  `PROGRESS_BACKREF.md` updated for the checked step and rebase note.
  Baseline pilot-only local CI passed with `BackRefPilot` (0:16 elapsed).
  Post-edit pilot-only local CI passed with `BackRefPilot` (0:17 elapsed),
  with `BackRefBitcodedSummary` replaying in about 0.064 seconds. Final
  post-rebase full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:16
  elapsed), and local CI certificate generation; explicit statement guard
  PASS. Next smallest safe step: stop until the admin opens a new bounty/phase,
  or add only similarly direct downstream packaging facts if explicitly
  requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after
  preserving the synced derivative member-length wrappers and adding semantic
  left-quotient member-length wrappers in `BackRefBoundedBlueprint.thy`. New
  checked facts in this final tree are `BL_bound_xders_length_bound`,
  `GBL_bound_gxders_length_bound`, `BL_bound_xders_length_bound_mono`,
  `GBL_bound_gxders_length_bound_mono`,
  `BL_bound_BBACKREF_xders_length_bound`,
  `GBL_bound_GBACKREF4_gxders_length_bound`,
  `BL_bound_BBACKREF_xders_length_bound_mono`,
  `GBL_bound_GBACKREF4_gxders_length_bound_mono`,
  `BL_bound_left_quotient_length_bound`,
  `GBL_bound_left_quotient_length_bound`,
  `BL_bound_left_quotient_length_bound_mono`,
  `GBL_bound_left_quotient_length_bound_mono`,
  `BL_bound_BBACKREF_left_quotient_length_bound`,
  `GBL_bound_GBACKREF4_left_quotient_length_bound`,
  `BL_bound_BBACKREF_left_quotient_length_bound_mono`, and
  `GBL_bound_GBACKREF4_left_quotient_length_bound_mono`. Files changed before
  this progress note: `BackRefBoundedBlueprint.thy` (+140) and
  `PROGRESS_BACKREF.md`. After rebasing over remote commit `8002257`,
  baseline pilot-only local CI passed with `BackRefPilot` (0:17 elapsed);
  post-edit pilot-only local CI passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 2.7 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:30 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and local CI
  certificate generation; explicit statement guard PASS. After rebasing over
  concurrent commit `44e86e8`, final full local CI passed again with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:03 elapsed),
  Isabelle `BackRefPilot` (0:17 elapsed), and local CI certificate generation;
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after adding
  direct member-length wrappers for bounded derivative residual languages in
  `BackRefBoundedBlueprint.thy`. New checked facts are
  `BL_bound_xders_length_bound`, `GBL_bound_gxders_length_bound`,
  `BL_bound_xders_length_bound_mono`, `GBL_bound_gxders_length_bound_mono`,
  `BL_bound_BBACKREF_xders_length_bound`,
  `GBL_bound_GBACKREF4_gxders_length_bound`,
  `BL_bound_BBACKREF_xders_length_bound_mono`, and
  `GBL_bound_GBACKREF4_gxders_length_bound_mono`. Files changed before this
  progress note: `BackRefBoundedBlueprint.thy` (+68). Baseline pilot-only
  local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit pilot-only
  local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 2.6 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:31 elapsed), Isabelle `BackRefPilot` (0:12 elapsed), and local CI
  certificate generation; explicit statement guard PASS. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only similarly
  direct downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct checked-evidence existence and
  rejection wrappers for the ordinary and generalized bitcoded lexer frontends.
  New checked facts are `bblexer_defined_BPrf_iff`,
  `bblexer_None_BPrf_iff`, `bblexer_simp_defined_BPrf_iff`,
  `bblexer_simp_None_BPrf_iff`,
  `bblexer_step_simp_defined_BPrf_iff`,
  `bblexer_step_simp_None_BPrf_iff`,
  `gbblexer_defined_GPrf_iff`, `gbblexer_None_GPrf_iff`,
  `gbblexer_simp_defined_GPrf_iff`,
  `gbblexer_simp_None_GPrf_iff`,
  `gbblexer_step_simp_defined_GPrf_iff`, and
  `gbblexer_step_simp_None_GPrf_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+29) and `BackRefGBlexer.thy` (+29). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBlexer` replaying in about 5.1 seconds and `BackRefGBlexer`
  replaying in about 2.0 seconds. Final full local CI passed with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:35 elapsed),
  Isabelle `BackRefPilot` (0:17 elapsed), and local CI certificate generation;
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct POSIX evidence existence and
  rejection wrappers for the ordinary bitcoded lexer frontends. New checked
  facts are `bblexer_defined_POSIX_iff`, `bblexer_None_POSIX_iff`,
  `bblexer_simp_defined_POSIX_iff`, `bblexer_simp_None_POSIX_iff`,
  `bblexer_step_simp_defined_POSIX_iff`, and
  `bblexer_step_simp_None_POSIX_iff`. Files changed before this progress note:
  `BackRefBlexer.thy` (+93). Baseline pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed), with `BackRefBlexer` replaying in about 5.2
  seconds. Final full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:33 elapsed), Isabelle `BackRefPilot` (0:16
  elapsed), and local CI certificate generation. Next smallest safe step: stop
  until the admin opens a new bounty/phase, or add only similarly direct
  downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct residual-language bounded-string
  wrappers from successful `BL_bound`/`GBL_bound` calculations in
  `BackRefBoundedBlueprint.thy`. New checked facts package subset, cardinality,
  monotone subset/cardinality, and finiteness wrappers for `BL (xders r s)` and
  `GBL (gxders r s)`, plus constructor-specific `BBACKREF` and `GBACKREF4`
  versions:
  `BL_bound_xders_subset_bounded_strings`,
  `GBL_bound_gxders_subset_bounded_strings`,
  `BL_bound_xders_card_bound`, `GBL_bound_gxders_card_bound`,
  `BL_bound_xders_subset_bounded_strings_mono`,
  `GBL_bound_gxders_subset_bounded_strings_mono`,
  `BL_bound_xders_card_bound_mono`, `GBL_bound_gxders_card_bound_mono`,
  `BL_bound_xders_finite`, `GBL_bound_gxders_finite`,
  `BL_bound_BBACKREF_xders_subset_bounded_strings`,
  `GBL_bound_GBACKREF4_gxders_subset_bounded_strings`,
  `BL_bound_BBACKREF_xders_card_bound`,
  `GBL_bound_GBACKREF4_gxders_card_bound`,
  `BL_bound_BBACKREF_xders_subset_bounded_strings_mono`,
  `GBL_bound_GBACKREF4_gxders_subset_bounded_strings_mono`,
  `BL_bound_BBACKREF_xders_card_bound_mono`,
  `GBL_bound_GBACKREF4_gxders_card_bound_mono`,
  `BL_bound_BBACKREF_xders_finite`, and
  `GBL_bound_GBACKREF4_gxders_finite`. Files changed before this progress
  note: `BackRefBoundedBlueprint.thy` (+220). Baseline pilot-only local CI
  passed with `BackRefPilot` (0:16 elapsed). Post-edit pilot-only local CI
  passed with `BackRefPilot` (0:17 elapsed) after fixing direct wrapper proofs
  to unfold `BL_bounded`/`GBL_bounded`; `BackRefBoundedBlueprint` replayed in
  about 3.1 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local
  CI certificate generation; explicit statement guard PASS. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only similarly
  direct downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding the direct value-lexer POSIX
  characterization `blexer_POSIX_correctness`, proving
  `blexer r s = Some v \<longleftrightarrow> s \<in> r \<rightarrow> v` from the existing
  POSIX soundness and determinism facts. Files changed before this progress
  note: `BackRefValues.thy` (+20). Baseline pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed), with `BackRefValues` replaying in about 9.7
  seconds. Final full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, statement guard, and
  local CI certificate generation. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct nullable-result wrappers for the
  ordinary and generalized bitcoded lexer frontends. New checked facts are
  `bblexer_None_xnullable_iff`, `bblexer_Some_xnullable_iff`,
  `bblexer_simp_None_xnullable_iff`,
  `bblexer_simp_Some_xnullable_iff`,
  `bblexer_step_simp_None_xnullable_iff`,
  `bblexer_step_simp_Some_xnullable_iff`,
  `gbblexer_None_gnullable_iff`, `gbblexer_Some_gnullable_iff`,
  `gbblexer_simp_None_gnullable_iff`,
  `gbblexer_simp_Some_gnullable_iff`,
  `gbblexer_step_simp_None_gnullable_iff`, and
  `gbblexer_step_simp_Some_gnullable_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+30) and `BackRefGBlexer.thy` (+30). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed);
  `BackRefBlexer` replayed in about 4.6 seconds and `BackRefGBlexer` replayed
  in about 1.9 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and
  local CI certificate generation. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding constructor-specific derivative-residue
  left-quotient wrappers from successful `BL_bound`/`GBL_bound` calculations
  for `BBACKREF` and `GBACKREF4` in `BackRefBoundedBlueprint.thy`. New
  checked facts are
  `BL_bound_BBACKREF_xders_left_quotient_family_subset_bounded_strings`,
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_subset_bounded_strings`,
  `BL_bound_BBACKREF_xders_left_quotient_family_card_bound`,
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_card_bound`,
  `BL_bound_BBACKREF_xders_left_quotient_family_subset_bounded_strings_mono`,
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_subset_bounded_strings_mono`,
  `BL_bound_BBACKREF_xders_left_quotient_family_card_bound_mono`,
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_card_bound_mono`,
  `BL_bound_BBACKREF_xders_left_quotient_family_finite`, and
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_finite`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+139). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 2.5 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix`, Isabelle `BackRefPilot`, and local CI certificate generation. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct derivative-residue
  left-quotient wrappers from successful `BL_bound`/`GBL_bound` calculations
  in `BackRefBoundedBlueprint.thy`. New checked facts are
  `BL_bound_xders_left_quotient_family_subset_bounded_strings`,
  `GBL_bound_gxders_left_quotient_family_subset_bounded_strings`,
  `BL_bound_xders_left_quotient_family_card_bound`,
  `GBL_bound_gxders_left_quotient_family_card_bound`,
  `BL_bound_xders_left_quotient_family_subset_bounded_strings_mono`,
  `GBL_bound_gxders_left_quotient_family_subset_bounded_strings_mono`,
  `BL_bound_xders_left_quotient_family_card_bound_mono`,
  `GBL_bound_gxders_left_quotient_family_card_bound_mono`,
  `BL_bound_xders_left_quotient_family_finite`, and
  `GBL_bound_gxders_left_quotient_family_finite`. Files changed before this
  progress note: `BackRefBoundedBlueprint.thy` (+140). Baseline pilot-only
  local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit pilot-only
  local CI passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 3.3 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix`, Isabelle `BackRefPilot`, and local CI certificate generation. After
  rebasing over concurrent commit `0267ce9`, full local CI passed again with
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct success-to-membership and
  membership-to-success obtain wrappers for the ordinary and generalized
  bitcoded lexer frontends. New checked facts are `bblexer_Some_BL`,
  `bblexer_BL_obtains`, `bblexer_simp_Some_BL`,
  `bblexer_simp_BL_obtains`, `bblexer_step_simp_Some_BL`,
  `bblexer_step_simp_BL_obtains`, `gbblexer_Some_GBL`,
  `gbblexer_GBL_obtains`, `gbblexer_simp_Some_GBL`,
  `gbblexer_simp_GBL_obtains`, `gbblexer_step_simp_Some_GBL`, and
  `gbblexer_step_simp_GBL_obtains`. Files changed before this progress note:
  `BackRefBlexer.thy` (+30) and `BackRefGBlexer.thy` (+30). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed);
  `BackRefBlexer` replayed in about 4.0 seconds and `BackRefGBlexer` replayed
  in about 1.9 seconds. Final full local CI passed with Isabelle `Posix`
  (0:29 elapsed), Isabelle `BackRefPilot` (0:03 elapsed), and local CI
  certificate generation. After rebasing over concurrent commit `65631e1`,
  full local CI passed again with Isabelle `Posix` (0:04 elapsed), Isabelle
  `BackRefPilot` (0:17 elapsed), local CI certificate generation, and explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only explicitly requested downstream convenience
  wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct semantic left-quotient wrappers
  from successful `BL_bound`/`GBL_bound` calculations in
  `BackRefBoundedBlueprint.thy`. New checked facts expose raw
  `{Ders s (BL r) | s. True}` and `{Ders s (GBL r) | s. True}` subset,
  cardinality, monotone, and finite wrappers over `bounded_strings`, plus
  constructor-specific `BBACKREF` and `GBACKREF4` packages. Files changed before
  this progress note: `BackRefBoundedBlueprint.thy` (+244). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 3.5 seconds. Final full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`,
  Isabelle `BackRefPilot`, and local CI certificate generation. After rebasing
  over concurrent commit `4c950f5`, the checked-value retrieve bridge progress
  note was preserved; post-rebase full local CI passed with Isabelle `Posix`
  (0:04 elapsed), Isabelle `BackRefPilot` (0:19 elapsed),
  `BackRefBoundedBlueprint` replaying in about 2.6 seconds, local CI
  certificate generation, and explicit statement guard PASS. Next smallest
  safe step: stop until the admin opens a new bounty/phase, or add only
  similarly direct downstream packaging facts if explicitly requested. Blockers:
  none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct checked-value retrieve wrappers
  for the ordinary and generalized bitcoded lexer frontends. New checked facts
  are `bblexer_BPrf_retrieve_iff`, `bblexer_simp_BPrf_retrieve_iff`,
  `bblexer_step_simp_BPrf_retrieve_iff`, `gbblexer_GPrf_retrieve_iff`,
  `gbblexer_simp_GPrf_retrieve_iff`, and
  `gbblexer_step_simp_GPrf_retrieve_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+19) and `BackRefGBlexer.thy` (+20). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed);
  `BackRefBlexer` replayed in about 4.2 seconds and `BackRefGBlexer` replayed
  in about 2.7 seconds. Final full local CI passed with Isabelle `Posix`
  (0:29 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and local CI
  certificate generation. After rebasing over concurrent commit `ce0492f`,
  full local CI passed again with Isabelle `Posix` (0:04 elapsed), Isabelle
  `BackRefPilot` (0:16 elapsed), local CI certificate generation, and explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only explicitly requested downstream convenience
  wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct equality wrappers from bitcoded
  lexer outputs to known value-lexer outputs. New checked facts are
  `bblexer_blexer_retrieve_eq`, `bblexer_simp_blexer_retrieve_eq`,
  `bblexer_step_simp_blexer_retrieve_eq`,
  `gbblexer_gblexer_retrieve_eq`, `gbblexer_simp_gblexer_retrieve_eq`, and
  `gbblexer_step_simp_gblexer_retrieve_eq`. Files changed before this
  progress note: `BackRefBlexer.thy` (+18) and `BackRefGBlexer.thy` (+18).
  Baseline pilot-only local CI passed with `BackRefPilot` (0:16 elapsed).
  Post-edit pilot-only local CI passed with `BackRefPilot` (0:16 elapsed);
  `BackRefBlexer` replayed in about 4.3 seconds and `BackRefGBlexer` replayed
  in about 2.1 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:34 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed), local CI certificate generation, and explicit
  statement guard PASS. Rebase over concurrent commit `79e263f` preserved both
  the new equality wrappers and the concurrently added `None` bridges.
  Post-rebase full local CI passed again with Isabelle `Posix` (0:03 elapsed),
  Isabelle `BackRefPilot` (0:03 elapsed), local CI certificate generation, and
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct `None` bridges from the ordinary
  and generalized bitcoded lexer frontends back to the corresponding value
  lexer output. New checked facts are `bblexer_None_blexer_iff`,
  `bblexer_simp_None_blexer_iff`,
  `bblexer_step_simp_None_blexer_iff`, `gbblexer_None_gblexer_iff`,
  `gbblexer_simp_None_gblexer_iff`, and
  `gbblexer_step_simp_None_gblexer_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+12) and `BackRefGBlexer.thy` (+12). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed);
  `BackRefBlexer` replayed in about 4.6 seconds and `BackRefGBlexer` replayed
  in about 2.5 seconds. Full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI
  certificate generation; the final run after this progress note replayed
  `Posix` in 0:04 elapsed and `BackRefPilot` in 0:16 elapsed. Next smallest
  safe step: stop until the admin opens a new bounty/phase, or add only
  explicitly requested downstream convenience wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct `Some` bridges from the ordinary
  and generalized bitcoded lexer frontends back to the corresponding value
  lexer output. New checked facts are `bblexer_Some_blexer_iff`,
  `bblexer_simp_Some_blexer_iff`, `bblexer_step_simp_Some_blexer_iff`,
  `gbblexer_Some_gblexer_iff`, `gbblexer_simp_Some_gblexer_iff`, and
  `gbblexer_step_simp_Some_gblexer_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+16) and `BackRefGBlexer.thy` (+16). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:12 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:11 elapsed);
  `BackRefBlexer` replayed in about 5.5 seconds and `BackRefGBlexer` replayed
  in about 2.0 seconds. After rebasing over concurrent commits `ea8d1f6` and
  `588bf64`, final full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI
  certificate generation. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only explicitly requested downstream convenience
  wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct POSIX-evidence output wrappers
  for the ordinary bitcoded lexer frontends in `BackRefBlexer.thy`. New checked
  facts are `bblexer_POSIX_retrieve`, `bblexer_POSIX_retrieve_eq`,
  `bblexer_simp_POSIX_retrieve`, `bblexer_simp_POSIX_retrieve_eq`,
  `bblexer_step_simp_POSIX_retrieve`, and
  `bblexer_step_simp_POSIX_retrieve_eq`. Files changed before this progress
  note: `BackRefBlexer.thy` (+33). Baseline pilot-only local CI passed with
  `BackRefPilot` (0:11 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:11 elapsed) and `BackRefBlexer` replaying in about 4.1
  seconds. Final full local CI passed with Isabelle `Posix`, Isabelle
  `BackRefPilot`, and local CI certificate generation. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only explicitly
  requested downstream convenience wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct POSIX-evidence retrieve wrappers
  for the ordinary bitcoded lexer frontends in `BackRefBlexer.thy`. New checked
  facts are `bblexer_POSIX_retrieve_iff`,
  `bblexer_simp_POSIX_retrieve_iff`, and
  `bblexer_step_simp_POSIX_retrieve_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+41). Baseline pilot-only local CI passed with
  `BackRefPilot` (0:11 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:11 elapsed) and `BackRefBlexer` replaying in about 4.1
  seconds. Final full local CI passed with Isabelle `Posix` (0:31 elapsed),
  Isabelle `BackRefPilot` (0:04 elapsed), and local CI certificate generation.
  Next smallest safe step: stop until the admin opens a new bounty/phase, or
  add only explicitly requested downstream convenience wrappers. Blockers:
  none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct `Some` result-characterization
  wrappers for the ordinary and generalized bitcoded lexer frontends, on top
  of the existing final-membership equations. New checked facts are
  `bblexer_Some_iff`, `bblexer_simp_Some_iff`,
  `bblexer_step_simp_Some_iff`, `gbblexer_Some_iff`,
  `gbblexer_simp_Some_iff`, and `gbblexer_step_simp_Some_iff`. Files changed
  before this progress note: `BackRefBlexer.thy` (+18) and
  `BackRefGBlexer.thy` (+18). After rebasing over parallel commit `464afc2`,
  pilot-only local CI passed with `BackRefPilot` (0:11 elapsed),
  `BackRefBlexer` replaying in about 4.3 seconds, and `BackRefGBlexer`
  replaying in about 2.4 seconds. Final full local CI passed with Isabelle
  `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:11 elapsed), and local
  CI certificate generation. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only explicitly requested downstream
  convenience wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct language-membership and `None`
  wrappers for the ordinary and generalized bitcoded lexer frontends in
  `BackRefBlexer.thy` and `BackRefGBlexer.thy`. New checked facts are
  `bblexer_final_membership`, `bblexer_None_iff`,
  `bblexer_simp_final_membership`, `bblexer_simp_None_iff`,
  `bblexer_step_simp_final_membership`, `bblexer_step_simp_None_iff`,
  `gbblexer_final_membership`, `gbblexer_None_iff`,
  `gbblexer_simp_final_membership`, `gbblexer_simp_None_iff`,
  `gbblexer_step_simp_final_membership`, and
  `gbblexer_step_simp_None_iff`. Files changed before this progress note:
  `BackRefBlexer.thy` (+36) and `BackRefGBlexer.thy` (+36). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:11 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:11 elapsed);
  `BackRefBlexer` replayed in about 4.7 seconds and `BackRefGBlexer` replayed
  in about 2.0 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:29 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed), and local CI certificate generation. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct packaging facts if explicitly requested. Blockers:
  none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct semantic residual left-quotient
  wrappers for bounded `backref_lang` and `backref_lang4` in
  `BackRefBoundedBlueprint.thy`. New checked facts expose subset,
  cardinality, monotone, and finite wrappers for
  `{Ders t (Ders s (backref_lang A B cs)) | t. True}` and the analogous
  `backref_lang4` family. Pilot-only local CI passed with `BackRefPilot`
  (0:11 elapsed) and `BackRefBoundedBlueprint` replaying in about 3.2 seconds.
  Final full local CI passed with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:30 elapsed), Isabelle `BackRefPilot` (0:04
  elapsed), and local CI certificate generation. After rebasing over
  `80c636b`, full local CI passed again with Isabelle `Posix` (0:04 elapsed),
  Isabelle `BackRefPilot` (0:11 elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding unconditional final-derivative retrieve
  equations for the ordinary and generalized bitcoded lexers in
  `BackRefBlexer.thy` and `BackRefGBlexer.thy`. New checked facts are
  `bblexer_final_retrieve`, `bblexer_simp_final_retrieve`,
  `bblexer_step_simp_final_retrieve`, `gbblexer_final_retrieve`,
  `gbblexer_simp_final_retrieve`, and
  `gbblexer_step_simp_final_retrieve`. Files changed before this progress
  note: `BackRefBlexer.thy` (+60) and `BackRefGBlexer.thy` (+60).
  Baseline pilot-only local CI passed with `BackRefPilot` (0:11 elapsed).
  Post-edit pilot-only local CI passed with `BackRefPilot` (0:11 elapsed);
  `BackRefBlexer` replayed in about 4.8 seconds and `BackRefGBlexer` replayed
  in about 1.8 seconds. Final full local CI passed with Isabelle `Posix`
  (0:32 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and local CI
  certificate generation. After rebasing over `8b8f1e0`, full local CI passed
  again with Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:12
  elapsed), and local CI certificate generation. Next smallest safe step:
  either add similarly direct `None`/membership wrappers for the bitcoded lexer
  frontends, or stop until the admin opens a new bounty/phase. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding residual left-quotient family helpers in
  `BackRefBoundedBlueprint.thy`. New checked facts expose
  `left_quotient_family_Ders_subset`, `finite_left_quotient_family_Ders`,
  `left_quotient_family_Ders_card_le`, and bounded-string universe/cardinality
  wrappers for `{Ders t (Ders s A) | t. True}`. Pilot-only local CI passed with
  `BackRefPilot` (0:11 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 2.2 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local
  CI certificate generation; explicit statement guard PASS.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct equality wrappers between the
  post-derivative and per-step simplified bitcoded lexers in
  `BackRefBlexer.thy` and `BackRefGBlexer.thy`. New checked facts are
  `bblexer_simp_step_simp_eq` and `gbblexer_simp_step_simp_eq`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:11 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:10 elapsed);
  `BackRefBlexer` replayed in about 4.1 seconds and `BackRefGBlexer` replayed
  in about 1.9 seconds. Final full local CI passed with Isabelle `Posix`
  (0:30 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and local CI
  certificate generation. After rebasing over `ade8125`, full local CI passed
  again with Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:11
  elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct retrieve/transport wrappers for
  the ordinary and generalized simplified bitcoded lexers in
  `BackRefBlexer.thy` and `BackRefGBlexer.thy`. New checked facts expose the
  exact simplified derivative expression used by `bblexer_simp`,
  `bblexer_step_simp`, `gbblexer_simp`, and `gbblexer_step_simp`, plus direct
  `map_option` transport from `blexer`/`gblexer` outputs. Final pilot-only
  local CI passed with `BackRefPilot` (0:10 elapsed); `BackRefBlexer` replayed
  in about 4.1 seconds and `BackRefGBlexer` replayed in about 2.0 seconds.
  Final full local CI passed with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:31 elapsed), Isabelle `BackRefPilot` (0:04
  elapsed), and local CI certificate generation. After rebasing over
  `5f7ee75`, full local CI passed again with Isabelle `Posix` (0:04 elapsed),
  Isabelle `BackRefPilot` (0:11 elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding residual derivative-family
  subset/cardinality helpers in `BackRefBoundedBlueprint.thy`. New checked
  facts expose `BL_residual_derivative_family_subset`,
  `GBL_residual_derivative_family_subset`,
  `finite_BL_residual_derivative_family`,
  `finite_GBL_residual_derivative_family`,
  `BL_residual_derivative_family_card_le`, and
  `GBL_residual_derivative_family_card_le`. Pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 2.5 seconds. Final full local CI passed with Isabelle `Posix` (0:37
  elapsed), Isabelle `BackRefPilot` (0:16 elapsed), and local CI certificate
  generation; explicit statement guard PASS. After rebasing over `9981ea5`,
  full local CI passed again with Isabelle `Posix` (0:03 elapsed), Isabelle
  `BackRefPilot` (0:16 elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding residual finite-quotient closure
  helpers in `BackRefBoundedBlueprint.thy`. New checked facts expose
  `Ders_append`, `finite_left_quotients_Ders`,
  `finite_BL_derivatives_iff_left_quotients`,
  `finite_GBL_derivatives_iff_left_quotients`,
  `finite_BL_derivatives_xders`, and `finite_GBL_derivatives_gxders`.
  Pilot-only local CI passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 2.6 seconds. Final full local
  CI passed with Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot`
  (0:04 elapsed), local CI certificate generation, and explicit statement
  guard PASS.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding direct finite-left-quotient
  wrappers for successful `BL_bound`/`GBL_bound` calculations in
  `BackRefBoundedBlueprint.thy`. New checked facts expose
  `finite_left_quotients (BL r)`/`finite_left_quotients (GBL r)`, their
  already-derived `xders`/`gxders` states, and constructor-specific
  `BBACKREF`/`GBACKREF4` variants. Pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 2.6 seconds. Final full local CI passed with Isabelle `Posix` (0:04
  elapsed), Isabelle `BackRefPilot` (0:04 elapsed), local CI certificate
  generation, and explicit statement guard PASS.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding direct predicate wrappers for
  derivative residues in `BackRefBoundedBlueprint.thy`. New checked facts
  expose `finite_BL_derivatives (xders r s)` and
  `finite_GBL_derivatives (gxders r s)` from successful `BL_bound`/`GBL_bound`
  calculations, plus constructor-specific `BBACKREF` and `GBACKREF4`
  variants. Pilot-only local CI passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 1.7 seconds. Final full local
  CI passed with Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:04 elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding raw finite-set wrappers for
  semantic left-quotient families in `BackRefBoundedBlueprint.thy`. New
  checked facts expose `finite {Ders s A | s. True}` for bounded languages
  and specialize that wrapper to `backref_lang` and `backref_lang4`.
  Pilot-only local CI passed with `BackRefPilot` (0:15 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 1.7 seconds. Full local CI
  passed with Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:03 elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding explicit finite-set wrappers for
  bounded derivative and residual derivative language families in
  `BackRefBoundedBlueprint.thy`. New checked facts expose raw
  `finite {...}` theorems for `BL_bound`/`GBL_bound` families and the
  constructor-specific `BBACKREF`/`GBACKREF4` packages, complementing the
  existing bounded-string subset/cardinality statements. Pilot-only local CI
  passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 2.1 seconds. Final full local
  CI passed with Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI
  certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding constructor-specific residual
  derivative-family finite-universe/cardinality wrappers in
  `BackRefBoundedBlueprint.thy`. New checked facts specialize the residual
  derivative-family subset/cardinality bounds to `BBACKREF` and `GBACKREF4`,
  and add monotone residual variants for larger external bounded-string
  universes. Pilot-only local CI passed with `BackRefPilot` (0:16 elapsed)
  and `BackRefBoundedBlueprint` replaying in about 1.7 seconds. Final full
  local CI passed with Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI
  certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding residual derivative-family
  finite-universe/cardinality wrappers in `BackRefBoundedBlueprint.thy`. New
  checked facts show that, from a successful `BL_bound`/`GBL_bound`, the
  derivative family reachable after any already consumed prefix still lies in
  the original `Pow (bounded_strings n)` universe and satisfies the same
  `2 ^ card (bounded_strings n)` cardinal upper bound. Pilot-only local CI
  passed with `BackRefPilot` (0:16 elapsed) and `BackRefBoundedBlueprint`
  replaying in about 2.0 seconds. Final full local CI passed with Isabelle
  `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and local
  CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation after adding semantic left-quotient
  finite-universe/cardinality wrappers in `BackRefBoundedBlueprint.thy`. New
  checked facts place `{Ders s A | s. True}` for any bounded language inside
  `Pow (bounded_strings n)` with an explicit `2 ^ card (bounded_strings n)`
  bound, and specialize that package to `backref_lang` and `backref_lang4`
  with exact and larger external bounds. A pilot-only precheck passed with
  `BackRefPilot` (0:15 elapsed), and `BackRefBoundedBlueprint` replayed in
  about 1.5 seconds.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding monotone finite-universe/cardinality
  wrappers in `BackRefBoundedBlueprint.thy`. New checked facts allow derivative
  language families from successful `BL_bound`/`GBL_bound` calculations, and
  the constructor-specific `BBACKREF`/`GBACKREF4` packages, to be placed in
  `Pow (bounded_strings m)` for any larger external bound `m`; corresponding
  cardinal bounds use `2 ^ card (bounded_strings m)`. Pilot-only local CI
  passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 1.3 seconds. Final full local
  CI passed with Isabelle `Posix`, Isabelle `BackRefPilot`, and certificate
  generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding constructor-specific BR-019
  finite-universe/cardinality wrappers in `BackRefBoundedBlueprint.thy`. New
  checked facts state that bounded `BBACKREF` and `GBACKREF4` derivative
  language families are subsets of the relevant `Pow (bounded_strings n)` and
  satisfy the corresponding `2 ^ card (bounded_strings n)` upper bound.
  Pilot-only local CI passed with `BackRefPilot` (0:15 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 1.2 seconds. The bounty guard
  accepted the BR-019 lock/collect ledger update. Final full local CI passed
  with Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03
  elapsed), and certificate generation. Explicit statement guard PASS.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and local CI certificate generation after adding a finite derivative-family
  universe package in `BackRefBoundedBlueprint.thy`. New checked facts define
  `bounded_strings`, prove it finite, place every derivative language from a
  successful `BL_bound`/`GBL_bound` calculation inside
  `Pow (bounded_strings n)`, and give the explicit cardinal upper bound
  `2 ^ card (bounded_strings n)`. A pilot-only precheck also passed with
  `BackRefPilot` (0:11 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 2.2 seconds.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:29 elapsed), Isabelle `BackRefPilot`, and local CI
  certificate generation after adding a BR-019 syntactic derivative-closure
  package in `BackRefBoundedBlueprint.thy`. New checked facts show that
  successful `BL_bound`/`GBL_bound` calculations remain defined after one
  derivative and after any `xders`/`gxders` derivative sequence, and that each
  syntactically bounded derivative expression again has a finite derivative
  language family. A pilot-only precheck also passed with `BackRefPilot`
  (0:11 elapsed) and `BackRefBoundedBlueprint` replaying in about 1.3 seconds.
  Closing verification after the progress update passed with Isabelle `Posix`
  (0:04 elapsed), Isabelle `BackRefPilot` (0:03 elapsed), certificate
  generation, and explicit statement guard PASS. After rebasing over the
  remote BR-015 completion commit, full local CI passed again with Isabelle
  `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:10 elapsed),
  certificate generation, and explicit statement guard PASS.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:11 elapsed),
  local CI certificate generation, and explicit statement guard after adding a
  BR-019 derivative-family bound package in `BackRefBoundedBlueprint.thy`. New
  checked facts show that semantic boundedness is preserved by
  `Ders`/`xders`/`gxders`, that every derivative language from a successful
  `BL_bound`/`GBL_bound` calculation is bounded by the same bound, and that
  syntactically bounded `BBACKREF` and `GBACKREF4` constructors have finite
  derivative-language families. `BackRefBoundedBlueprint` replayed in about
  0.8 seconds.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding syntactic bounded-fragment proof-prep
  in `BackRefBoundedBlueprint.thy`: bounded-language closure lemmas,
  conservative `BL_bound`/`GBL_bound` calculators, soundness lemmas, and
  finite derivative-language corollaries. Final full local CI also passed with
  Isabelle `Posix` (0:32 elapsed), Isabelle `BackRefPilot`, and local CI
  certificate generation; `BackRefBoundedBlueprint` replayed in about 1.1
  seconds in the pilot-only check.
- PASS on 2026-05-27 local time (2026-05-26 UTC) with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`,
  and local CI certificate generation after completing BR-015 in
  `BackRefValues.thy`. New checked facts include
  `BPosix_empty_bmkeps`, `BSEQ_split_unique`, and `BPosix_determ`;
  `BackRefValues` replayed in about 9.3 seconds. Early broad eliminations over
  `BPosix_elims` timed out because they destructed recursive POSIX assumptions;
  the checked proof uses named-target cases and small split/empty helpers.
- PASS on 2026-05-27 local time (2026-05-26 UTC) with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`,
  and local CI certificate generation after adding `BackRefBoundedBlueprint.thy`.
  The new theory defines a semantic bounded-language/finite-left-quotient
  blueprint and proves `bounded_BBACKREF_finite_derivative_languages` and
  `bounded_GBACKREF4_finite_derivative_languages`; `BackRefBoundedBlueprint`
  replayed in about 0.27 seconds after replacing an expensive nested-image
  proof route.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding BR-015 helper lemmas in
  `BackRefValues.thy`: `bval_list_eq_zipI`, `BBACKREF_split_cases`,
  `BBACKREF_split_unique`, and `BPosix_BBACKREF_value_unique`. The first
  broad `BPosix_determ` attempt and an early split proof timed out because
  `append_eq_append_conv2` was handed to recursive simplification; the checked
  version uses a one-shot `iffD1` step and explicit witnesses.
- Coordination update on 2026-05-26: Cursor/Opus retired for overnight work;
  two Codex CLI workers are now the intended parallel setup. Codex Agent B owns
  BR-015 and `BackRefValues.thy`; Codex Agent A owns BR-022 and must stay on
  non-conflicting pilot-only statement/proof-prep. Local PowerShell CI now uses
  a global Isabelle build mutex so the two clones do not collide in the shared
  Isabelle cache.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard after adding the generalized `gabbsimp` and
  per-step `gbblexer_step_simp` layer in `BackRefGBlexer.thy`. A pilot-only
  precheck passed first; `BackRefGBlexer` replayed in about 2.3 seconds.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  local CI certificate generation, and explicit statement guard after adding
  generalized bitcoded retrieve transport in `BackRefGBlexer.thy`. A
  pilot-only precheck also passed; `BackRefGBlexer` replayed in about 1.9
  seconds and the timed proof work avoided broad nullable-tail automation.
- PASS on 2026-05-26 with direct Isabelle `BackRefPilot` build under a
  120-second timeout -- standalone generalized bitcoded lexer definitions
  in `BackRefGBlexer.thy` with `gbblexer_defined_iff`. The new theory replayed
  in about 0.9 seconds. Final full local CI also passed with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix` (0:03 elapsed), Isabelle
  `BackRefPilot` (0:03 elapsed), local CI certificate generation, and explicit
  statement guard.
- PASS on 2026-05-26 with direct Isabelle `BackRefPilot` build under a
  120-second timeout -- standalone generalized constructor lexer with
  `gblexer`, `gblexer_GPrf`, `gblexer_flat`, and `gblexer_correctness`.
  `BackRefLang4Values` replayed in about 1.4 seconds in the direct build.
  Final full local CI also passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate
  generation, and explicit statement guard.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, explicit statement guard, and
  local CI certificate generation -- generalized constructor injection
  evidence with `ginjval`, `ginjval_flat`, and `ginjval_GPrf`. A broad proof
  first timed out; it was replaced with explicit constructor/local-shape
  proofs, and `BackRefLang4Values` replayed in about 2.2 seconds in the final
  direct timed build.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and statement guard --
  generalized constructor epsilon evidence with `gmkeps`, `gmkeps_flat`, and
  `gmkeps_GPrf`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and statement guard --
  generalized constructor value correspondence with `GBL_flat_GPrf` and
  `gxders_GBL_flat_GPrf`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and statement guard --
  generalized constructor/value bridge with `GBACKREF4_flat_BPrf4` and
  `gxders_GBACKREF4_flat_BPrf4`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and statement guard -- standalone generalized constructor pilot with
  `gxder_correctness` and `gxders_correctness`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and statement guard -- BR-016 generalized `backref_lang4`
  value-evidence blueprint with `backref_lang4_flat_BPrf4`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and statement guard -- BR-020
  complete per-step bitcoded derivative simplifier with
  `bblexer_step_simp_correctness`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and statement guard -- BR-020 partial post-derivative bitcoded simplifier
  with `bblexer_simp_correctness`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and statement guard -- BR-018 bitcoded derivative retrieve transport and
  `bblexer_blexer_retrieve`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and statement guard -- BR-018 partial bitcoded retrieve layer for nullable
  derivative evidence.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` and Isabelle `BackRefPilot` -- BR-017 bitcoded
  backreference lexer definitions in a separate pilot file.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and statement guard -- BR-008 generalized `backref_lang4` derivative story.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, worker role guard,
  and Isabelle `BackRefPilot` (0:04 elapsed) -- blexer definition and correctness.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` (0:05 elapsed) -- BR-014 blexer POSIX correctness
  plus `binjval` definition speedup.
- Previous PASS on 2026-05-26 with direct Isabelle `BackRefPilot`
  cold build (0:16 elapsed) after replacing slow `fun` processing.
- Previous PASS on 2026-05-26 with no-cheat guard, bounty guard, worker role guard,
  and Isabelle `BackRefPilot` (3:03 elapsed).
- Previous PASS on 2026-05-25 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, and Isabelle `BackRefPilot`.
- Local CI certificate is generated only after both sessions pass:
  `agent_hunt_pipeline/certificates/local_ci_certificate.json` (ignored by git).

## Semantic Residual Backref Quotient Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-blueprint proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+89 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked theorems:
  - `bounded_backref_lang_residual_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang4_residual_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang_residual_left_quotient_family_card_bound`
  - `bounded_backref_lang4_residual_left_quotient_family_card_bound`
  - `bounded_backref_lang_residual_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang4_residual_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang_residual_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang4_residual_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang_residual_left_quotient_family_finite`
  - `bounded_backref_lang4_residual_left_quotient_family_finite`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:11 elapsed), and local CI certificate
  generation; `BackRefBoundedBlueprint` replayed in about 3.2 seconds. Final
  full local CI PASS with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:30 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and
  local CI certificate generation. After rebasing over `80c636b`, full local
  CI passed again with Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:11 elapsed), and local CI certificate generation.
- Notes:
  - This is additive semantic proof packaging in the bounded-fragment
    blueprint. It does not touch `BackRefValues.thy`, frozen language/value
    statements, production lexer files, or production bounds/closed-form
    theories.
  - The new wrappers specialize the generic residual left-quotient family
    universe/cardinality facts to `backref_lang` and `backref_lang4`, matching
    the existing direct left-quotient wrappers.
- Next smallest safe step: stop unless the admin opens a new bounty/statement
  target, or continue only with similarly small non-conflicting blueprint
  packaging.

## Residual Left-Quotient Family Helpers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-blueprint proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+91 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked lemmas/theorems:
  - `left_quotient_family_Ders_subset`
  - `finite_left_quotient_family_Ders`
  - `left_quotient_family_Ders_card_le`
  - `bounded_language_residual_left_quotient_family_subset_bounded_strings`
  - `bounded_language_residual_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_language_residual_left_quotient_family_card_bound`
  - `bounded_language_residual_left_quotient_family_card_bound_mono`
  - `bounded_language_residual_left_quotient_family_finite`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:11 elapsed), and no certificate
  generation; `BackRefBoundedBlueprint` replayed in about 2.2 seconds. Final
  full local CI PASS with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation; explicit statement guard PASS.
- Notes:
  - This is additive proof packaging in the bounded-fragment blueprint. It
    does not touch `BackRefValues.thy`, frozen language/value statements,
    production lexer files, or production bounds/closed-form theories.
  - The new lemmas expose the exact residual quotient-family subset behind
    `finite_left_quotients_Ders` and package bounded-string universe and
    cardinality bounds for quotient families after an already-consumed prefix.
- Next smallest safe step: stop unless the admin opens a new bounty/statement
  target, or continue only with similarly small non-conflicting blueprint
  packaging.

## Residual Derivative-Family Subset Helpers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-blueprint proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+68 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked lemmas:
  - `BL_residual_derivative_family_subset`
  - `GBL_residual_derivative_family_subset`
  - `finite_BL_residual_derivative_family`
  - `finite_GBL_residual_derivative_family`
  - `BL_residual_derivative_family_card_le`
  - `GBL_residual_derivative_family_card_le`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:16 elapsed), and no certificate
  generation; `BackRefBoundedBlueprint` replayed in about 2.5 seconds. Final
  full local CI PASS with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:37 elapsed), Isabelle `BackRefPilot` (0:16 elapsed),
  local CI certificate generation, and explicit statement guard PASS. After
  rebasing over `9981ea5`, full local CI passed again with Isabelle `Posix`
  (0:03 elapsed), Isabelle `BackRefPilot` (0:16 elapsed), and local CI
  certificate generation.
- Notes:
  - This is additive proof packaging in the bounded-fragment blueprint. It
    does not touch `BackRefValues.thy`, frozen language/value statements,
    production lexer files, or production bounds/closed-form theories.
  - The new subset lemmas expose that a derivative family reachable after an
    already-consumed prefix is included in the original derivative-language
    family, giving direct finite/cardinality reuse without redoing append
    reasoning at each bounded wrapper.
- Next smallest safe step: if continuing Agent A work, keep packaging small
  generic closure facts in `BackRefBoundedBlueprint.thy` or stop until the
  admin opens a new bounty/statement target.

## Residual Finite-Quotient Closure Helpers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-blueprint proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy`, `PROGRESS_BACKREF.md`
- New checked lemmas:
  - `Ders_append`
  - `finite_left_quotients_Ders`
  - `finite_BL_derivatives_iff_left_quotients`
  - `finite_GBL_derivatives_iff_left_quotients`
  - `finite_BL_derivatives_xders`
  - `finite_GBL_derivatives_gxders`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:16 elapsed), and no certificate
  generation; `BackRefBoundedBlueprint` replayed in about 2.6 seconds. Final
  full local CI PASS with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  local CI certificate generation, and explicit statement guard PASS.
- Notes:
  - This is additive proof packaging in the bounded-fragment blueprint. It
    does not touch `BackRefValues.thy`, frozen language/value statements,
    production lexer files, or production bounds/closed-form theories.
  - The new closure lemmas expose that finite derivative-language predicates
    are stable under already-consumed prefixes without requiring a fresh
    `BL_bound`/`GBL_bound` calculation.
- Next smallest safe step: continue with small quotient/derivative packaging
  only if it remains non-conflicting and admin-useful.

## Completed

- `BackRefLang.thy` defines pilot `brexp`.
- `BackRefLang.thy` proves:
  - `xnullable_correctness`
  - `xder_correctness`
  - `xders_correctness`
  - `backref_lang_as_backref_lang4`
  - `backref_lang4I`
  - `Der_backref_lang4` (BR-008)
- `BackRefLang4Pilot.thy` now defines:
  - `gbrexp` with `GBASE`, `GALT`, and `GBACKREF4`
  - `GBL`, `gnullable`, `gtail4`, `gxder`, and `gxders`
- `BackRefLang4Pilot.thy` proves:
  - `gnullable_correctness`
  - `BL_gtail4`
  - `gxder_correctness`
  - `gxders_append`
  - `gxders_snoc`
  - `gxders_correctness`
- `BackRefBoundedBlueprint.thy` now defines:
  - `bounded_language`
  - `finite_left_quotients`
  - `suffix_closure`
  - `finite_BL_derivatives`
  - `finite_GBL_derivatives`
  - `BL_bounded`
  - `GBL_bounded`
  - `bounded_backref4_components`
  - `BL_bound`
  - `GBL_bound`
- `BackRefBoundedBlueprint.thy` proves:
  - `bounded_language_finite`
  - `finite_left_quotients_if_finite_language`
  - `finite_left_quotients_if_bounded_language`
  - `bounded_BL_finite_derivative_languages`
  - `bounded_GBL_finite_derivative_languages`
  - `bounded_backref_lang_finite_left_quotients`
  - `bounded_backref_lang4_finite_left_quotients`
  - `bounded_BBACKREF_finite_derivative_languages`
  - `bounded_GBACKREF4_finite_derivative_languages`
  - `Ders_append`
  - `finite_left_quotients_Ders`
  - `finite_BL_derivatives_iff_left_quotients`
  - `finite_GBL_derivatives_iff_left_quotients`
  - `finite_BL_derivatives_xders`
  - `finite_GBL_derivatives_gxders`
  - bounded-language closure lemmas for union, sequencing, fixed powers, and
    zero-bounded stars
  - constructor-level `BL_bounded`/`GBL_bounded` closure lemmas
  - `bounded_language_Ders`
  - `BL_bounded_xders`
  - `GBL_bounded_gxders`
  - `BL_bound_sound`
  - `GBL_bound_sound`
  - `BL_bound_finite_derivative_languages`
  - `GBL_bound_finite_derivative_languages`
  - `BL_bound_xders_bounded`
  - `GBL_bound_gxders_bounded`
  - `BL_bound_derivative_family_bounded`
  - `GBL_bound_derivative_family_bounded`
  - `BL_bound_xder_residue_defined`
  - `BL_bound_xder_defined`
  - `GBL_bound_gxder_defined`
  - `BL_bound_xders_defined`
  - `GBL_bound_gxders_defined`
  - `BL_bound_xders_finite_derivative_languages`
  - `GBL_bound_gxders_finite_derivative_languages`
  - `BL_bound_BBACKREF_finite_derivative_languages`
  - `GBL_bound_GBACKREF4_finite_derivative_languages`
  - `bounded_strings`
  - `finite_bounded_strings`
  - `BL_bound_derivative_family_subset_bounded_strings`
  - `GBL_bound_derivative_family_subset_bounded_strings`
  - `BL_bound_derivative_family_card_bound`
  - `GBL_bound_derivative_family_card_bound`
  - `BL_bound_derivative_family_finite`
  - `GBL_bound_derivative_family_finite`
  - `BL_bound_residual_derivative_family_subset_bounded_strings`
  - `GBL_bound_residual_derivative_family_subset_bounded_strings`
  - `BL_bound_residual_derivative_family_card_bound`
  - `GBL_bound_residual_derivative_family_card_bound`
  - `BL_bound_residual_derivative_family_finite`
  - `GBL_bound_residual_derivative_family_finite`
  - `BL_bound_xders_finite_BL_derivatives`
  - `GBL_bound_gxders_finite_GBL_derivatives`
  - `BL_bound_residual_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_residual_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_residual_derivative_family_card_bound_mono`
  - `GBL_bound_residual_derivative_family_card_bound_mono`
  - `BL_bound_BBACKREF_residual_derivative_family_subset_bounded_strings`
  - `GBL_bound_GBACKREF4_residual_derivative_family_subset_bounded_strings`
  - `BL_bound_BBACKREF_residual_derivative_family_card_bound`
  - `GBL_bound_GBACKREF4_residual_derivative_family_card_bound`
  - `BL_bound_BBACKREF_residual_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_GBACKREF4_residual_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_BBACKREF_residual_derivative_family_card_bound_mono`
  - `GBL_bound_GBACKREF4_residual_derivative_family_card_bound_mono`
  - `BL_bound_BBACKREF_residual_derivative_family_finite`
  - `GBL_bound_GBACKREF4_residual_derivative_family_finite`
  - `BL_bound_BBACKREF_xders_finite_BL_derivatives`
  - `GBL_bound_GBACKREF4_gxders_finite_GBL_derivatives`
  - `bounded_language_left_quotient_family_subset_bounded_strings`
  - `bounded_language_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_language_left_quotient_family_card_bound`
  - `bounded_language_left_quotient_family_card_bound_mono`
  - `bounded_language_left_quotient_family_finite`
  - `bounded_backref_lang_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang4_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang_left_quotient_family_card_bound`
  - `bounded_backref_lang4_left_quotient_family_card_bound`
  - `bounded_backref_lang_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang4_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang4_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang_left_quotient_family_finite`
  - `bounded_backref_lang4_left_quotient_family_finite`
  - `BL_bound_BBACKREF_derivative_family_subset_bounded_strings`
  - `GBL_bound_GBACKREF4_derivative_family_subset_bounded_strings`
  - `BL_bound_BBACKREF_derivative_family_card_bound`
  - `GBL_bound_GBACKREF4_derivative_family_card_bound`
  - `BL_bound_BBACKREF_derivative_family_finite`
  - `GBL_bound_GBACKREF4_derivative_family_finite`
- `BackRefValues.thy` now defines:
  - `bval`
  - `bflat`
  - `BPrf`
- `BackRefValues.thy` proves:
  - `BL_flat_BPrf1`
  - `BL_flat_BPrf2`
  - `BL_flat_BPrf`
  - `bmkeps_flat`
  - `bmkeps_BPrf`
  - `BPrf_xder_residue`
  - `binjval_flat` (BR-011)
  - `BPrf_BNTIMES_prepend`
  - `binjval_BPrf` (BR-012)
  - `blexer_BPrf` (BR-013)
  - `blexer_flat` (BR-013)
  - `blexer_correct_None` (BR-013)
  - `blexer_correct_Some` (BR-013)
  - `blexer_correctness` (BR-014 packaging)
  - `BPosix_binjval` (BR-014)
  - `blexer_POSIX` (BR-014)
  - `blexer_POSIX_iff` (BR-014)
  - `BPosix_empty_bmkeps`
  - `BSEQ_split_unique`
  - `BPosix_determ` (BR-015)
- `BackRefBlexer.thy` now defines:
  - `bbit` with `BZ`, `BS`, and `Backbit`
  - annotated `barexp` constructors including `BABACKREF`, `BAHALF`,
    and `BARESIDUE`
  - `berase`, `bfuse`, `baintern`, `bbnullable`, `bbmkeps`, `bbder`,
    `bbders`, and `bblexer`
- `BackRefBlexer.thy` proves:
  - `berase_bfuse`
  - `berase_baintern`
  - `bbnullable_correctness`
  - `berase_bbder_residue`
  - `berase_bbder`
  - `berase_bbders`
  - `bblexer_defined_iff`
  - `berase_bbsimp`
  - `bbnullable_bbsimp`
  - `bretrieve_bbsimp`
  - `bbmkeps_bbsimp`
  - `bblexer_simp_correctness`
  - `bblexer_simp_defined_iff`
  - `bblexer_simp_blexer_retrieve`
  - `bblexer_simp_retrieve_correctness`
  - `bbders_simp`
  - `bblexer_step_simp`
  - `bbders_simp_bretrieve_blexer`
  - `bblexer_step_simp_correctness`
  - `bblexer_step_simp_retrieve_correctness`
  - `bblexer_step_simp_blexer_retrieve`
  - `bbmkeps_bretrieve`
  - `bretrieve_bfuse`
  - `bbder_bretrieve`
  - `bbders_bretrieve_blexer`
  - `bblexer_bretrieve_original`
  - `bblexer_blexer_retrieve`
  - `bblexer_bretrieve`
  - `bblexer_retrieve_correctness`
- `BackRefLang4Values.thy` now defines:
  - `bval4` with `BBackref4`
  - `bflat4`
  - `BPrf4`
  - `gbval` with `GVBase`, `GVLeft`, `GVRight`, and `GVBackref4`
  - `gflat`
  - `GPrf`
  - `gmkeps`
  - `gbackref4_from_tail`
  - `ginjval`
- `BackRefLang4Values.thy` proves:
  - `backref_lang4_flat_BPrf4_1`
  - `backref_lang4_flat_BPrf4_2`
  - `backref_lang4_flat_BPrf4`
  - `backref_lang_flat_BPrf4_special`
  - `GBACKREF4_flat_BPrf4`
  - `gxders_GBACKREF4_flat_BPrf4`
  - `GBL_flat_GPrf1`
  - `GBL_flat_GPrf2`
  - `GBL_flat_GPrf`
  - `gxders_GBL_flat_GPrf`
  - `gmkeps_flat`
  - `gmkeps_GPrf`
  - `gbackref4_from_tail_flat`
  - `gbackref4_from_tail_GPrf`
  - `gbackref4_from_xder_tail_flat`
  - `gbackref4_from_xder_tail_GPrf`
  - `ginjval_flat`
  - `ginjval_GPrf`
  - `gblexer`
  - `gblexer_GPrf`
  - `gblexer_flat`
  - `gblexer_correct_None`
  - `gblexer_correct_Some`
  - `gblexer_correctness`
- `BackRefGBlexer.thy` now defines:
  - `gabexp` with `GABASE`, `GAALTs`, and `GABACKREF4`
  - `gerase`, `gfuse`, `gaintern`, `gabnullable`, `gamkeps`, `gretrieve`,
    `gabbtail4`, `gabder`, `gabders`, and `gbblexer`
- `BackRefGBlexer.thy` proves:
  - `gerase_gfuse`
  - `gerase_gaintern`
  - `gabnullable_correctness`
  - `gamkeps_gretrieve`
  - `berase_gabbtail4`
  - `gerase_gabder`
  - `gerase_gabders`
  - `gbblexer_defined_iff`
  - `gretrieve_gfuse`
  - `gabder_gretrieve`
  - `gabders_gretrieve_gblexer`
  - `gbblexer_gblexer_retrieve`
  - `gbblexer_gretrieve`
  - `gbblexer_retrieve_correctness`
  - `gerase_gabbsimp`
  - `gabnullable_gabbsimp`
  - `gretrieve_gabbsimp`
  - `gamkeps_gabbsimp`
  - `gerase_gabders_simp`
  - `gabnullable_gabders_simp`
  - `gabders_simp_gretrieve_gblexer`
  - `gbblexer_simp_correctness`
  - `gbblexer_simp_defined_iff`
  - `gbblexer_simp_gblexer_retrieve`
  - `gbblexer_simp_retrieve_correctness`
  - `gbblexer_step_simp_defined_iff`
  - `gbblexer_step_simp_correctness`
  - `gbblexer_step_simp_retrieve_correctness`
  - `gbblexer_step_simp_gblexer_retrieve`
- Local/remote CI scaffolding now checks:
  - no Isabelle proof-bypass markers;
  - bounty board invariants and checked artifacts;
  - full inherited `Posix` session;
  - pilot `BackRefPilot` session;
  - GitHub Actions artifact certificate after successful proof checking.
- Agent loop scaffolding now includes:
  - WSL/tmux repeated-prompt testing;
  - Cursor Hooks for Opus worker loops;
  - `SLEEP_RUNBOOK.md` for parallel Codex Desktop + Cursor/Opus starts.

## Current Headline Theorem

```isabelle
lemma BL_flat_BPrf:
  "BL r = {bflat v | v. BPrf v r}"
```

This is the value/Prf/flat correspondence layer for the pilot language,
including `BBACKREF`, `BHALF`, and `BRESIDUE`.

## Next Small Tasks

1. ~~Draft `binjval` for one-character derivative reconstruction.~~ DONE (BR-005)
2. ~~Prove `bflat (binjval r c v) = c # bflat v` when `BPrf v (xder c r)`.~~ DONE (BR-011)
3. ~~Prove `BPrf (binjval r c v) r` when `BPrf v (xder c r)`.~~ DONE (BR-012)
4. ~~Define and prove `blexer` for pilot `brexp` (BR-013).~~ DONE (BR-013)
5. ~~Prove `blexer` correctness for pilot `brexp` (BR-014).~~ DONE (BR-014)
6. ~~Draft derivative story for generalized `backref_lang4`.~~ DONE (BR-008)
7. ~~Start BR-017 bitcoded backreference lexer definitions in a new pilot file.~~ DONE (BR-017)
8. ~~Finish derivative-retrieve/decode-to-original-value correctness for BR-018.~~ DONE (BR-018)
9. ~~Finish BR-020 simplification rules for the bitcoded lexer.~~ DONE (BR-020)
10. ~~Finish BR-016 generalized value pilot.~~ DONE (BR-016)
11. ~~Add standalone generalized constructor derivative pilot.~~ DONE
12. ~~Bridge generalized constructor derivatives to `BPrf4` value evidence.~~ DONE
13. ~~Add generalized constructor value correspondence for all `gbrexp`.~~ DONE
14. ~~Add generalized constructor one-step value injection.~~ DONE
15. ~~Package a standalone generalized `gblexer` from `gnullable`/`gmkeps`/`gxder`/`ginjval`.~~ DONE
16. ~~Draft standalone generalized bitcoded lexer layer in a new theory.~~ DONE
    (`BackRefGBlexer.thy`)
17. ~~Extend generalized bitcoded layer with derivative retrieve transport
    relating `gbblexer` to `gblexer`.~~ DONE
18. ~~Optional next generalized bitcoded layer: add a conservative
    `gabbsimp`/step-simplifier story mirroring `BackRefBlexer.thy`.~~ DONE
19. ~~Add BR-022 bounded-fragment statement blueprint.~~ DONE
20. ~~Complete BR-015 POSIX value ordering with `BPosix_determ`.~~ DONE
21. ~~Complete BR-019 bounded fragment theorem for backreferences.~~ DONE
22. BR-019 now has a checked semantic finite-derivative-language blueprint and
    checked syntactic bounded-fragment proof-prep through
    `BL_bound_finite_derivative_languages` and
    `GBL_bound_finite_derivative_languages`, plus derivative-family boundedness
    and syntactic derivative-closure/constructor packages. The latest package
    also places the derivative-language family for bounded `BBACKREF` and
    `GBACKREF4` constructors inside the finite universe
    `Pow (bounded_strings n)` with explicit cardinal bounds. The residual
    derivative-family package shows the same original universe/cardinality
    bound after any already consumed prefix, and the latest wrapper package
    specializes those residual facts to `BBACKREF`/`GBACKREF4` with monotone
    larger-universe variants. The current finite-wrapper packages also expose
    raw `finite {...}` facts for semantic left quotients, derivative families,
    and residual derivative families. The newest residue-predicate wrappers
    expose direct `finite_BL_derivatives`/`finite_GBL_derivatives` facts for
    arbitrary already-derived states, including constructor-specific
    `BBACKREF`/`GBACKREF4` states. The latest predicate wrapper package also
    exposes `finite_left_quotients` facts for successful syntactic bounds and
    for already-derived bounded states, including constructor-specific
    `BBACKREF`/`GBACKREF4` states. No active bounty remains on
    `BACKREF_BOUNTIES.md`; production bounds or closed-form work should still
    wait for a new admin task.
23. ~~Add direct retrieve/transport wrappers for simplified bitcoded lexers.~~
    DONE
24. ~~Package direct equality between post-derivative and per-step simplified
    bitcoded lexer entry points.~~ DONE

## Simplified Lexer Equality Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent B implementation packaging lane
- Files changed: `BackRefBlexer.thy` (+4), `BackRefGBlexer.thy` (+4),
  `PROGRESS_BACKREF.md`
- New checked theorems:
  - `bblexer_simp_step_simp_eq`
  - `gbblexer_simp_step_simp_eq`
- Build:
  - Baseline pilot-only local CI PASS with no-cheat guard, bounty guard, admin
    role guard, and Isabelle `BackRefPilot` (0:11 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:10 elapsed);
    `BackRefBlexer` replayed in about 4.1 seconds and `BackRefGBlexer`
    replayed in about 1.9 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:30 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed), and local CI certificate generation.
  - Post-rebase full local CI PASS over remote `ade8125` with no-cheat guard,
    bounty guard, admin role guard, Isabelle `Posix` (0:03 elapsed), Isabelle
    `BackRefPilot` (0:11 elapsed), and local CI certificate generation.
- Notes:
  - This is additive theorem packaging only. It identifies the two checked
    simplified lexer entry points directly, without changing definitions,
    semantics, frozen statements, production `Blexer*`, bounds files, or
    closed-form theories.
- Next smallest safe step: no active bounty remains; wait for an admin-created
  production integration task or a new bounty before changing frozen semantics,
  production lexers, bounds, or closed-form theories.

## Simplified Bitcoded Transport Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `03625a6`
- Agent lane: Codex Agent B implementation packaging lane
- Files changed: `BackRefBlexer.thy` (+54), `BackRefGBlexer.thy` (+54),
  `PROGRESS_BACKREF.md`
- New checked theorems:
  - `bblexer_simp_defined_iff`
  - `bblexer_simp_blexer_retrieve`
  - `bblexer_simp_retrieve_correctness`
  - `bblexer_step_simp_retrieve_correctness`
  - `bblexer_step_simp_blexer_retrieve`
  - `gbblexer_simp_defined_iff`
  - `gbblexer_simp_gblexer_retrieve`
  - `gbblexer_simp_retrieve_correctness`
  - `gbblexer_step_simp_retrieve_correctness`
  - `gbblexer_step_simp_gblexer_retrieve`
- Build:
  - Pre-edit baseline pilot-only local CI PASS with no-cheat guard, bounty
    guard, admin role guard, and Isabelle `BackRefPilot` (0:11 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:11 elapsed);
    `BackRefBlexer` replayed in about 4.7 seconds and `BackRefGBlexer` replayed
    in about 1.9 seconds.
  - Final pilot-only local CI PASS after the direct transport wrappers with
    no-cheat guard, bounty guard, admin role guard, and Isabelle
    `BackRefPilot` (0:10 elapsed); `BackRefBlexer` replayed in about 4.1
    seconds and `BackRefGBlexer` replayed in about 2.0 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:31 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed), and local CI certificate generation.
  - Post-rebase full local CI PASS over remote `5f7ee75` with no-cheat guard,
    bounty guard, admin role guard, Isabelle `Posix` (0:04 elapsed),
    Isabelle `BackRefPilot` (0:11 elapsed), and local CI certificate
    generation.
- Notes:
  - This is additive theorem packaging only. It does not change lexer
    definitions, semantics, frozen statements, `BackRefBoundedBlueprint.thy`,
    production `Blexer*`, bounds files, or closed-form theories.
  - The new wrappers characterize the actual simplified derivative expression
    used by each simplified bitcoded lexer and expose the direct
    `map_option` transport from `blexer`/`gblexer`, instead of requiring users
    to rewrite through the base `bblexer`/`gbblexer` retrieve theorem.
- Next smallest safe step: no active bounty remains; wait for an admin-created
  production integration task or a new bounty before changing frozen semantics,
  production lexers, bounds, or closed-form theories.

## Finite Left-Quotient Predicate Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `159374c`
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+368 current theory delta
  before this progress note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_finite_left_quotients`
  - `GBL_bound_finite_left_quotients`
  - `BL_bound_xders_finite_left_quotients`
  - `GBL_bound_gxders_finite_left_quotients`
  - `BL_bound_BBACKREF_finite_left_quotients`
  - `GBL_bound_GBACKREF4_finite_left_quotients`
  - `BL_bound_BBACKREF_xders_finite_left_quotients`
  - `GBL_bound_GBACKREF4_gxders_finite_left_quotients`
- Build:
  - Pre-edit dirty-state pilot-only local CI PASS with no-cheat guard, bounty
    guard, admin role guard, and Isabelle `BackRefPilot` (0:04 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:16 elapsed);
    `BackRefBoundedBlueprint` replayed in about 2.6 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed), local CI certificate generation, and explicit statement guard
    PASS.
- Notes:
  - This is additive theorem packaging over the checked syntactic boundedness
    calculator and already checked `xders`/`gxders` boundedness facts.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Derivative Residue Predicate Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `159374c`
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+294 current theory delta
  before this progress note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_xders_finite_BL_derivatives`
  - `GBL_bound_gxders_finite_GBL_derivatives`
  - `BL_bound_BBACKREF_xders_finite_BL_derivatives`
  - `GBL_bound_GBACKREF4_gxders_finite_GBL_derivatives`
- Build:
  - Pre-edit dirty-state pilot-only local CI PASS with no-cheat guard, bounty
    guard, admin role guard, and Isabelle `BackRefPilot` (0:03 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:16 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.7 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed), and local CI certificate generation.
- Notes:
  - This is additive theorem packaging over already checked residual
    derivative-family finite-set facts.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Semantic Left-Quotient Finite Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `159374c`
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+267 current theory delta
  before this progress note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `bounded_language_left_quotient_family_finite`
  - `bounded_backref_lang_left_quotient_family_finite`
  - `bounded_backref_lang4_left_quotient_family_finite`
- Build:
  - Pre-edit dirty-state pilot-only local CI PASS with no-cheat guard, bounty
    guard, admin role guard, and Isabelle `BackRefPilot` (0:03 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:15 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.7 seconds.
  - Full local CI PASS with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
    and local CI certificate generation.
- Notes:
  - This is additive theorem packaging over the existing
    `finite_left_quotients` bounded-language package.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Finite Derivative-Family Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `159374c`
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+246 total worktree delta
  before this progress note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_derivative_family_finite`
  - `GBL_bound_derivative_family_finite`
  - `BL_bound_residual_derivative_family_finite`
  - `GBL_bound_residual_derivative_family_finite`
  - `BL_bound_BBACKREF_residual_derivative_family_finite`
  - `GBL_bound_GBACKREF4_residual_derivative_family_finite`
  - `BL_bound_BBACKREF_derivative_family_finite`
  - `GBL_bound_GBACKREF4_derivative_family_finite`
- Build:
  - Existing dirty state pilot-only local CI PASS with no-cheat guard, bounty
    guard, admin role guard, and Isabelle `BackRefPilot` (0:03 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:16 elapsed);
    `BackRefBoundedBlueprint` replayed in about 2.1 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
    generation.
- Notes:
  - This is additive theorem packaging over already checked finite-derivative,
    residual subset, and constructor-specific bounded-string universe facts.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Constructor Residual Derivative-Family Bounds (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `159374c`
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+174 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_residual_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_residual_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_residual_derivative_family_card_bound_mono`
  - `GBL_bound_residual_derivative_family_card_bound_mono`
  - `BL_bound_BBACKREF_residual_derivative_family_subset_bounded_strings`
  - `GBL_bound_GBACKREF4_residual_derivative_family_subset_bounded_strings`
  - `BL_bound_BBACKREF_residual_derivative_family_card_bound`
  - `GBL_bound_GBACKREF4_residual_derivative_family_card_bound`
  - `BL_bound_BBACKREF_residual_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_GBACKREF4_residual_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_BBACKREF_residual_derivative_family_card_bound_mono`
  - `GBL_bound_GBACKREF4_residual_derivative_family_card_bound_mono`
- Build:
  - Pre-edit pilot-only local CI PASS with no-cheat guard, bounty guard, admin
    role guard, and Isabelle `BackRefPilot` (0:03 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:16 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.7 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
    generation.
- Notes:
  - This is additive theorem packaging over the checked residual
    derivative-family universe bounds and the constructor-specific
    `BL_bound`/`GBL_bound` arithmetic wrappers.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Residual Derivative-Family Universe Bounds (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+60 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_residual_derivative_family_subset_bounded_strings`
  - `GBL_bound_residual_derivative_family_subset_bounded_strings`
  - `BL_bound_residual_derivative_family_card_bound`
  - `GBL_bound_residual_derivative_family_card_bound`
- Build:
  - Pre-edit pilot-only local CI PASS with no-cheat guard, bounty guard, admin
    role guard, and Isabelle `BackRefPilot` (0:04 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:16 elapsed);
    `BackRefBoundedBlueprint` replayed in about 2.0 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed), and local CI certificate generation.
- Notes:
  - This is additive theorem packaging over `xders_append`/`gxders_append` and
    the existing `bounded_strings` finite universe.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Semantic Left-Quotient Finite-Universe Bounds (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+117 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `bounded_language_left_quotient_family_subset_bounded_strings`
  - `bounded_language_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_language_left_quotient_family_card_bound`
  - `bounded_language_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang4_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang_left_quotient_family_card_bound`
  - `bounded_backref_lang4_left_quotient_family_card_bound`
  - `bounded_backref_lang_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang4_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang4_left_quotient_family_card_bound_mono`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:15 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.5 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:03
    elapsed), and certificate generation.
- Notes:
  - This is additive theorem packaging over the semantic bounded-language
    layer and the checked `backref_lang`/`backref_lang4` boundedness lemmas.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## BR-019 Monotone Finite-Universe Bounds (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+116 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked lemmas:
  - `bounded_strings_mono`
  - `bounded_language_subset_bounded_strings_mono`
- New checked theorems:
  - `BL_bound_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_derivative_family_card_bound_mono`
  - `GBL_bound_derivative_family_card_bound_mono`
  - `BL_bound_BBACKREF_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_GBACKREF4_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_BBACKREF_derivative_family_card_bound_mono`
  - `GBL_bound_GBACKREF4_derivative_family_card_bound_mono`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:04 elapsed).
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03
    elapsed), and certificate generation.
  - Explicit statement guard PASS.
- Notes:
  - This is an additive theorem-packaging step over the checked BR-019
    finite-universe package.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## BR-019 Constructor Finite-Universe Bounds (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+54 before this progress
  note), `BACKREF_BOUNTIES.md` (+6/-3 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_BBACKREF_derivative_family_subset_bounded_strings`
  - `GBL_bound_GBACKREF4_derivative_family_subset_bounded_strings`
  - `BL_bound_BBACKREF_derivative_family_card_bound`
  - `GBL_bound_GBACKREF4_derivative_family_card_bound`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:15 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.2 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03
    elapsed), and local CI certificate generation.
  - Explicit statement guard PASS.
  - Bounty guard PASS after moving BR-019 to completed and recording
    `L-CODEX-A-019`.
- Bounty:
  - BR-019 is now marked DONE with Codex as owner.
  - The active bounty table is empty; allocated and collected pool totals both
    stand at 24,970.
- Notes:
  - This is additive theorem packaging over the already checked
    `BL_bound`/`GBL_bound` finite-universe package.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; no active bounty remains in `BACKREF_BOUNTIES.md`.

## BR-019 Finite Derivative-Family Universe Package (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+90 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked definitions:
  - `bounded_strings`, the finite universe of strings with length at most a
    successful syntactic bound
- New checked lemmas/theorems:
  - `finite_bounded_strings`
  - `bounded_language_subset_bounded_strings`
  - `card_Pow_finite`
  - `BL_bound_derivative_family_subset_bounded_strings`
  - `GBL_bound_derivative_family_subset_bounded_strings`
  - `BL_bound_derivative_family_card_bound`
  - `GBL_bound_derivative_family_card_bound`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:11 elapsed);
    `BackRefBoundedBlueprint` replayed in about 2.2 seconds.
  - Full local CI PASS with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
    and local CI certificate generation.
- Performance note:
  - The first draft failed fast on finite-list and powerset-cardinality proof
    details; the checked version uses explicit `finite_lists_length_le`,
    `card_image`, and `card_mono` steps. No slow proof command was accepted.
- Notes:
  - This does not touch `BackRefValues.thy`, production `Blexer*`, bounds, or
    closed-form theories.
  - This strengthens the BR-019 bounded-fragment blueprint from "finite" to an
    explicit finite universe/cardinality bound for derivative languages.
- Next smallest safe step: ask the admin whether the accumulated
  `BL_bound`/`GBL_bound` finite-universe package is enough to mark BR-019 done,
  or whether a production-facing theorem name/statement should be frozen first.

## BR-019 Syntactic Derivative-Closure Package (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+186 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked lemmas/theorems:
  - `BL_bound_xder_residue_defined`
  - `BL_bound_xder_defined`
  - `GBL_bound_gxder_defined`
  - `BL_bound_xders_defined`
  - `GBL_bound_gxders_defined`
  - `BL_bound_xders_finite_derivative_languages`
  - `GBL_bound_gxders_finite_derivative_languages`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:11 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.3 seconds.
  - Full local CI PASS with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (0:29 elapsed), Isabelle `BackRefPilot`, and local CI
    certificate generation.
  - Closing full local CI PASS after this progress update with no-cheat guard,
    bounty guard, admin role guard, Isabelle `Posix` (0:04 elapsed), Isabelle
    `BackRefPilot` (0:03 elapsed), and local CI certificate generation.
  - Post-rebase full local CI PASS after replaying over the remote BR-015
    completion commit with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:10 elapsed),
    and local CI certificate generation.
  - Explicit statement guard PASS: 2 frozen theory files checked, no statement
    modifications.
- Performance note:
  - The first draft failed fast because three existential witnesses were left
    implicit. The checked proof uses explicit residue cases and explicit
    witness choices; no slow proof command was accepted.
- Notes:
  - This proves syntactic closure of the conservative `BL_bound` and
    `GBL_bound` calculators under `xder`/`gxder` and `xders`/`gxders`.
  - This still does not touch `BackRefValues.thy`, production `Blexer*`,
    bounds, or closed-form theories.
- Next smallest safe step: run the statement guard and commit this checked
  additive package; then keep BR-015 reserved for Codex Agent B and ask admin
  whether the accumulated `BL_bound`/`GBL_bound` packages are sufficient for
  BR-019's production target.

## BR-019 Derivative-Family Bound Package (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+77 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked lemmas/theorems:
  - `bounded_language_Ders`
  - `BL_bounded_xders`
  - `GBL_bounded_gxders`
  - `BL_bound_xders_bounded`
  - `GBL_bound_gxders_bounded`
  - `BL_bound_derivative_family_bounded`
  - `GBL_bound_derivative_family_bounded`
  - `BL_bound_finite_left_quotients`
  - `GBL_bound_finite_left_quotients`
  - `BL_bound_xders_finite_left_quotients`
  - `GBL_bound_gxders_finite_left_quotients`
  - `BL_bound_BBACKREF_finite_left_quotients`
  - `GBL_bound_GBACKREF4_finite_left_quotients`
  - `BL_bound_BBACKREF_xders_finite_left_quotients`
  - `GBL_bound_GBACKREF4_gxders_finite_left_quotients`
  - `BL_bound_BBACKREF_finite_derivative_languages`
  - `GBL_bound_GBACKREF4_finite_derivative_languages`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:10 elapsed);
    `BackRefBoundedBlueprint` replayed in about 0.7 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:11
    elapsed), and local CI certificate generation; `BackRefBoundedBlueprint`
    replayed in about 0.8 seconds.
  - Explicit statement guard PASS: 2 frozen theory files checked, no statement
    modifications.
- Performance note:
  - The first `bounded_language_Ders` proof failed fast on a local length
    arithmetic step. The checked proof uses an explicit `Ders` membership
    witness and a length chain; no slow command was accepted.
- Notes:
  - This is still bounded-fragment proof-prep for BR-019. It does not claim a
    finite syntactic derivative-state bound.
  - This does not touch `BackRefValues.thy`, production `Blexer*`, bounds, or
    closed-form theories.
- Next smallest safe step: BR-015 is complete; ask admin
  whether the `BL_bound`/`GBL_bound` and derivative-family boundedness
  statements are acceptable as the BR-019 production target.

## BR-019 Syntactic Bounded Fragment Proof-Prep (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `3418f0f`
- Agent lane: Codex Agent A bounded-fragment proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+288 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked definitions:
  - `BL_bound`, a conservative syntactic bound calculator for current `brexp`
  - `GBL_bound`, the corresponding calculator for standalone generalized
    `gbrexp`
- New checked lemmas/theorems:
  - bounded-language closure for empty/singleton languages, union, sequencing,
    fixed powers, and zero-bounded stars
  - constructor-level `BL_bounded` lemmas for non-star constructors,
    `BNTIMES`, zero-bounded `BSTAR`, `BBACKREF`, `BHALF`, and `BRESIDUE`
  - constructor-level `GBL_bounded` lemmas for `GBASE`, `GALT`, and
    `GBACKREF4`
  - `BL_bound_sound`
  - `GBL_bound_sound`
  - `BL_bound_finite_derivative_languages`
  - `GBL_bound_finite_derivative_languages`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:10 elapsed); `BackRefBoundedBlueprint`
    replayed in about 1.1 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:32 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed/no rebuild), and local CI certificate generation.
- Performance note:
  - Initial proof scripts failed fast on local helper facts. The checked version
    uses explicit induction/case facts for `bounded_language_pow` and
    `bounded_language_star_zero`, avoiding broad search.
- Notes:
  - This remains semantic proof-prep for BR-019 and does not claim a finite
    syntactic derivative-state bound.
  - This does not touch `BackRefValues.thy`, production `Blexer*`, bounds, or
    closed-form theories.
- Next smallest safe step: BR-015 is complete; ask admin
  whether the `BL_bound`/`GBL_bound` statements are acceptable as the BR-019
  bounded-fragment production target.

## BR-015 POSIX Value Ordering Complete (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent B, BR-015 POSIX value ordering
- Files changed: `BackRefValues.thy` (+356 before progress/bounty notes),
  `PROGRESS_BACKREF.md`, `BACKREF_BOUNTIES.md`
- New checked helper lemmas:
  - `bval_list_eq_replicateI`
  - `BPosix_empty_bmkeps`
  - `BSEQ_split_unique`
- New checked theorem:
  - `BPosix_determ`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:16 elapsed); `BackRefValues`
    replayed in about 8.9 seconds.
  - Final post-rebase full local CI PASS with no-cheat guard, bounty guard,
    admin role guard, Isabelle `Posix` (0:03 elapsed/no rebuild), Isabelle
    `BackRefPilot` (0:11 elapsed), and local CI certificate generation;
    `BackRefValues` replayed in about 9.3 seconds.
  - Explicit statement guard PASS: 2 frozen theory files checked, no statement
    modifications.
- Performance note:
  - Initial `BPosix_determ` attempts timed out when `auto elim!: BPosix_elims`
    was used in contexts containing recursive POSIX premises. The checked proof
    case-splits only the named target derivation and reuses
    `BPosix_BBACKREF_value_unique` for the backreference constructor.
- Notes:
  - BR-015 is now marked collected in `BACKREF_BOUNTIES.md`.
  - No production `Blexer*`, bounds, closed-form, or frozen language semantics
    files were touched.
- Next smallest safe step:
  - Leave BR-019 blocked pending admin acceptance of the bounded-fragment
    statement.

## BR-022 Bounded-Fragment Statement Blueprint (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit on top of `19e32b8`
- Agent lane: Codex Agent A new-file bounded-fragment blueprint lane
- Files changed: `BackRefBoundedBlueprint.thy`, `pilot/ROOT`,
  `PROGRESS_BACKREF.md`, `BACKREF_BOUNTIES.md`
- New checked definitions:
  - `bounded_language`
  - `finite_left_quotients`
  - `suffix_closure`
  - `finite_BL_derivatives`
  - `finite_GBL_derivatives`
  - `BL_bounded`
  - `GBL_bounded`
  - `bounded_backref4_components`
- New checked lemmas/theorems:
  - `bounded_language_finite`
  - `finite_left_quotients_if_finite_language`
  - `finite_left_quotients_if_bounded_language`
  - `bounded_BL_finite_derivative_languages`
  - `bounded_GBL_finite_derivative_languages`
  - `bounded_backref_lang_finite_left_quotients`
  - `bounded_backref_lang4_finite_left_quotients`
  - `bounded_BBACKREF_finite_derivative_languages`
  - `bounded_GBACKREF4_finite_derivative_languages`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `BackRefPilot` (0:13 elapsed), and no certificate;
    `BackRefBoundedBlueprint` replayed in about 0.25 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:13
    elapsed), and local CI certificate generation; `BackRefBoundedBlueprint`
    replayed in about 0.27 seconds.
  - Explicit statement guard PASS: 2 frozen theory files checked, no
    statement modifications.
- Performance note:
  - An earlier nested-product image proof for `backref_lang4` caused an
    abnormal long proof command and left a child build alive after the outer
    timeout. The child build was stopped, and the proof route was replaced by
    the simpler bounded-language path.
- Notes:
  - This is semantic statement/proof-prep for BR-019: bounded component
    languages imply finitely many semantic derivative languages for current
    `BBACKREF` and generalized `GBACKREF4`.
  - This does not claim a finite syntactic derivative-state bound and does not
    touch `BackRefValues.thy`, production `Blexer*`, bounds, or closed-form
    theories.
- Next smallest safe step: wait for Agent B's BR-015 result or admin approval
  of the precise BR-019 bounded-fragment theorem statement.

## BR-015 Backreference POSIX Split Helpers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent B, BR-015 POSIX value ordering
- Files changed: `BackRefValues.thy` (+122 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked lemmas:
  - `bval_list_eq_zipI`
  - `BBACKREF_split_cases`
  - `BBACKREF_split_unique`
  - `BPosix_BBACKREF_value_unique`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:08 elapsed); `BackRefValues` replayed
    in about 5.6 seconds after the final helper proof.
- Performance note:
  - A broad `BPosix_determ` attempt and an early version of
    `BBACKREF_split_unique` timed out. Root cause: using
    `append_eq_append_conv2` as a simplification rule recursively rewrote newly
    generated append equalities. The checked proof applies it once through
    `iffD1` in `BBACKREF_split_cases` and then constructs greedy-condition
    contradiction witnesses explicitly.
- Next smallest safe step:
  - Prove `BPosix_determ` by reusing `BPosix_BBACKREF_value_unique` and
    replacing broad `cases`/`auto` blocks by constructor-specific eliminations.

## Generalized Bitcoded Simplifier (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit on top of `32e5ff7`
- Agent lane: Codex new-file generalized bitcoded pilot lane
- Files changed: `BackRefGBlexer.thy` (+243 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked definitions:
  - `gabbsimp`
  - `gabders_simp`
  - `gbblexer_simp`
  - `gbblexer_step_simp`
- New checked lemmas/theorems:
  - `gerase_gabbsimp`
  - `gabnullable_gabbsimp`
  - `gabbsimp_gfuse`
  - `gretrieve_gabbsimp`
  - `gamkeps_gabbsimp`
  - `gerase_gabders_simp`
  - `gabnullable_gabders_simp`
  - `gabders_simp_gabnullable_gblexer`
  - `gabders_simp_gretrieve_gblexer`
  - `gbblexer_simp_correctness`
  - `gbblexer_step_simp_defined_iff`
  - `gbblexer_step_simp_correctness`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `BackRefPilot` (0:14 elapsed), and local CI certificate
    generation; `BackRefGBlexer` replayed in about 2.3 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI
    certificate generation.
  - Explicit statement guard PASS: 2 frozen theory files checked, no statement
    modifications.
- Notes:
  - This mirrors the existing `BackRefBlexer.thy` simplifier story at the
    generalized annotated layer and proves exact preservation of `gbblexer`.
  - This remains additive in `BackRefGBlexer.thy`; it does not touch frozen
    `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production `Blexer*`, bounds,
    closed-form theories, or Opus's BR-015 lock.
- Next smallest safe step: keep BR-019 blocked until an explicit
  bounded-fragment statement is accepted, or wait for Opus/admin direction on
  the remaining POSIX ordering lane.

## Generalized Bitcoded Retrieve Transport (2026-05-26)

- Branch: `codex/backref-values`
- Commit: uncommitted working-tree step on top of `cd72208`; `git fetch
  --all --prune` succeeded and `git pull --rebase --autostash origin
  codex/backref-values` reported already up to date before the edit.
- Agent lane: Codex new-file generalized bitcoded pilot lane
- Files changed: `BackRefGBlexer.thy` (+356 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked lemmas/theorems:
  - `gretrieve_alts_append`
  - `gretrieve_gfuse`
  - `gretrieve_gbackref4_from_tail`
  - `gretrieve_gbackref4_from_xder_tail`
  - `gabder_GAALTs_gretrieve`
  - `gabder_gretrieve`
  - `gabders_gabnullable_gblexer`
  - `gabders_gretrieve_gblexer`
  - `gbblexer_gretrieve_original`
  - `gbblexer_gblexer_retrieve`
  - `gbblexer_gretrieve`
  - `gbblexer_retrieve_correctness`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `BackRefPilot` (0:10 elapsed), and local CI certificate
    generation; `BackRefGBlexer` replayed in about 1.9 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03
    elapsed), and local CI certificate generation.
  - Explicit statement guard PASS: 2 frozen theory files checked, no statement
    modifications.
- Notes:
  - This is additive generalized bitcoded infrastructure only. It does not
    touch frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production
    `Blexer*`, bounds, closed-form theories, or Opus's BR-015 lock.
  - The nested nullable `GBACKREF4` tail branch is proved explicitly through
    `gabbtail4` and `gbackref4_from_tail`; no slow broad proof method was kept.
- Next smallest safe step: optionally mirror the checked `bbsimp`/per-step
  simplifier story for the generalized bitcoded layer, or wait for admin
  direction on BR-019's bounded-fragment statement.

## Generalized Bitcoded Lexer (2026-05-26)

- Branch: `codex/backref-values`
- Commit: uncommitted working-tree step on top of `ea9c7d0`; `git fetch
  --all --prune` succeeded and `git pull --rebase --autostash origin
  codex/backref-values` reported already up to date before the edit.
- Agent lane: Codex new-file generalized bitcoded pilot lane
- Files changed: `BackRefGBlexer.thy`, `pilot/ROOT`, `PROGRESS_BACKREF.md`
- New checked definitions:
  - `gabexp`, an annotated expression layer for `gbrexp`
  - `gerase`, `gfuse`, `gaintern`, and `gabnullable`
  - `gamkeps`, `gretrieve_alts`, and `gretrieve`
  - `gabbtail4`, `gabder`, `gabders`, and `gbblexer`
- New checked lemmas:
  - `gerase_gfuse`
  - `gerase_gaintern`
  - `gabnullable_correctness`
  - `gamkeps_gretrieve`
  - `berase_gabbtail4`
  - `gerase_gabder`
  - `gerase_gabders`
  - `gbblexer_defined_iff`
- Build: direct `timeout 120s isabelle build -v -d pilot BackRefPilot` PASS
  (0:13 elapsed, `BackRefGBlexer` 0.873s); final full local CI PASS with
  no-cheat guard, bounty guard, admin role guard, Isabelle `Posix` (0:03
  elapsed), Isabelle `BackRefPilot` (0:03 elapsed), and local CI certificate
  generation. Explicit statement guard PASS.
- Notes:
  - This is an additive new-file checkpoint and does not touch frozen `brexp`, `BL`,
    `xnullable`, `xder`, `BPrf`, production `Blexer*`, bounds, or closed-form
    theories.
  - The generalized `Backbit` retrieve order records prefix evidence first,
    then the captured `r2` string, matching the `backref_lang4` capture role.
  - A stale zero-CPU Isabelle build worker had been live for more than two
    hours; it was stopped before starting the timed direct build.
- Next smallest safe step: extend this layer with derivative retrieve transport
  relating `gbblexer` to `gblexer`.

## Standalone Generalized Constructor Lexer (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit; the branch was clean and synchronized with
  `origin/codex/backref-values` before this edit.
- Agent lane: Codex generalized constructor/value bridge lane
- Files changed: `BackRefLang4Values.thy`, `PROGRESS_BACKREF.md`
- New checked definition:
  - `gblexer`, a standalone lexer for the `gbrexp` layer using
    `gnullable`/`gmkeps`, `gxder`, and `ginjval`
- New checked lemmas/theorem:
  - `gblexer_GPrf`
  - `gblexer_flat`
  - `gblexer_correct_None`
  - `gblexer_correct_Some`
  - `gblexer_correctness`
- Build: direct `timeout 120s isabelle build -v -d pilot BackRefPilot` PASS
  (0:13 elapsed, `BackRefLang4Values` 1.441s); final full local CI PASS with
  no-cheat guard, bounty guard, admin role guard, Isabelle `Posix` (0:03
  elapsed), Isabelle `BackRefPilot` (0:04 elapsed), local CI certificate
  generation, and explicit statement guard PASS.
- Notes:
  - This is additive generalized-constructor packaging and does not touch
    frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production lexer files,
    bounds theories, or Opus's BR-015 lock.
  - It mirrors the checked `blexer` proof shape at the standalone generalized
    layer rather than adding POSIX ordering rules for `gbrexp`.
- Next smallest safe step: either commit this additive checkpoint or wait for
  BR-015/BR-019 direction from the admin.

## Generalized Constructor Injection Evidence (2026-05-26)

- Branch: `codex/backref-values`
- Commit: uncommitted working-tree step on top of local `986a4ca`; the branch
  was clean before this edit and `git fetch --all --prune` succeeded.
- Agent lane: Codex generalized constructor/value bridge lane
- Files changed: `BackRefLang4Values.thy` (+179 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked definitions:
  - `gbackref4_from_tail`, extracting `GBACKREF4` evidence from the checked
    post-capture tail value shape
  - `ginjval`, one-character derivative value reconstruction for `gbrexp`
- New checked lemmas:
  - `gbackref4_from_tail_flat`
  - `gbackref4_from_tail_GPrf`
  - `gbackref4_from_xder_tail_flat`
  - `gbackref4_from_xder_tail_GPrf`
  - `ginjval_flat`
  - `ginjval_GPrf`
- Build: direct `timeout 90s isabelle build -v -d pilot BackRefPilot` PASS
  (0:16 elapsed, `BackRefLang4Values` 2.172s); pilot-only local CI PASS with
  no-cheat guard, bounty guard, admin role guard, Isabelle `BackRefPilot`
  (0:05 elapsed), and local CI certificate generation; final full local CI
  PASS with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), certificate
  generation, and explicit statement guard PASS.
- Performance note:
  - An earlier broad `auto` over the whole `gbrexp` induction timed out after
    the wrapper's 300 second limit and left a child build running; the child
    build was stopped, and the proof was replaced with explicit `GALT` value
    cases plus localized backreference/tail helper lemmas.
- Notes:
  - This is additive generalized-constructor infrastructure and does not touch
    frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production lexer files,
    bounds theories, or Opus's BR-015 lock.
- Next smallest safe step: optionally package a `gblexer` for the standalone
  `gbrexp` layer from `gnullable`/`gmkeps`/`gxder`/`ginjval`; keep BR-015
  reserved for Opus and keep BR-019 blocked until an explicit bounded-fragment
  statement is accepted.

## Generalized Constructor Epsilon Evidence (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit; remote fetch was blocked by an HTTPS TLS
  handshake failure before work, and local `HEAD` matched
  `origin/codex/backref-values`.
- Agent lane: Codex generalized constructor/value bridge lane
- Files changed: `BackRefLang4Values.thy` (+20 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked definition:
  - `gmkeps`, nullable epsilon evidence for `GBASE`, `GALT`, and
    `GBACKREF4`
- New checked lemmas:
  - `gmkeps_flat`
  - `gmkeps_GPrf`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:14 elapsed), and local CI
  certificate generation; final full local CI PASS with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`,
  statement guard, and certificate generation.
- Notes:
  - This is additive generalized-constructor infrastructure and does not touch
    frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production lexer files,
    bounds theories, or Opus's BR-015 lock.
  - `gmkeps` mirrors `bmkeps` at the generalized layer and reuses checked
    component epsilon evidence for `GBACKREF4`.
- Next smallest safe step: keep BR-015 reserved for Opus; keep BR-019 blocked
  until an explicit bounded-fragment statement is accepted.

## Generalized Constructor Value Correspondence (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex generalized constructor/value bridge lane
- Files changed: `BackRefLang4Values.thy` (+90 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked definitions:
  - `gbval`, value evidence for the standalone `gbrexp` constructor layer
  - `gflat`, flattening `GBASE`, `GALT`, and `GBACKREF4` evidence
  - `GPrf`, proof evidence for `GBASE`, `GALT`, and `GBACKREF4`
- New checked lemmas/theorems:
  - `GBL_flat_GPrf1`
  - `GBL_flat_GPrf2`
  - `GBL_flat_GPrf`
  - `gxders_GBL_flat_GPrf`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:09 elapsed), and local CI
  certificate generation; final full local CI PASS with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`,
  statement guard, and certificate generation.
- Notes:
  - This extends the standalone generalized constructor pilot without
    modifying frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production
    lexer files, or bounds theories.
  - `GVBackref4` reuses the existing checked `BPrf4` evidence rather than
    duplicating the four-component value bridge.
- Next smallest safe step: leave BR-015 to Opus and keep BR-019 blocked until
  an admin accepts an explicit bounded-fragment statement.

## Generalized Constructor/Value Bridge (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex generalized constructor/value bridge lane
- Files changed: `BackRefLang4Values.thy` (+20/-1 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked theorems:
  - `GBACKREF4_flat_BPrf4`, connecting the standalone `GBACKREF4`
    constructor language to the four-component `BPrf4` evidence set
  - `gxders_GBACKREF4_flat_BPrf4`, lifting that bridge through generalized
    derivatives via `gxders_correctness`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:09 elapsed), and local CI
  certificate generation; final full local CI PASS with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix` (0:03 elapsed),
  Isabelle `BackRefPilot` (0:03 elapsed), and certificate generation.
- Notes:
  - This only imports `BackRefLang4Pilot` into `BackRefLang4Values.thy` and
    adds bridge theorems.
  - It does not modify frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`,
    production lexer files, or bounds theories.
- Next smallest safe step: leave BR-015 to Opus and keep BR-019 blocked until
  an admin accepts an explicit bounded-fragment statement.

## Generalized backref_lang4 Constructor Pilot (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex generalized constructor blueprint lane
- Files changed: `BackRefLang4Pilot.thy`, `pilot/ROOT`,
  `PROGRESS_BACKREF.md`
- New checked definitions:
  - `gbrexp`, a standalone generalized expression layer wrapping existing
    `brexp` with `GBASE`, `GALT`, and `GBACKREF4`
  - `GBL`, `gnullable`, `gtail4`, `gxder`, and `gxders`
- New checked lemmas/theorems:
  - `gnullable_correctness`
  - `BL_gtail4`
  - `gxder_correctness`
  - `gxders_append`
  - `gxders_snoc`
  - `gxders_correctness`
- Build: full local CI PASS with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03
  elapsed), and statement guard.
- Notes:
  - This does not modify frozen `brexp`, `BL`, `xnullable`, `xder`, or
    `backref_lang`.
  - `gxder` uses `Der_backref_lang4` and represents the post-capture tail via
    the existing `BSEQ r3 (BSEQ (BRESIDUE (rev cs) (rev cs)) r4)` language.
  - This is a checked statement blueprint for a later admin-approved migration
    to real `BBACKREF4`-style constructors.
- Next smallest safe step: leave BR-015 to Opus and keep BR-019 blocked until
  the bounded-fragment statement is explicit.

## BR-016 Generalized backref_lang4 Value Pilot (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex generalized value blueprint lane
- Files changed: `BackRefLang4Values.thy`, `pilot/ROOT`,
  `PROGRESS_BACKREF.md`, `BACKREF_BOUNTIES.md`
- New checked definitions:
  - `bval4` with `BBackref4`
  - `bflat4`, flattening to `s1 @ s2 @ s3 @ rev cs @ s2 @ s4`
  - `BPrf4`, reusing existing `BPrf` evidence for the four component
    `brexp` languages
- New checked lemmas/theorems:
  - `backref_lang4_flat_BPrf4_1`
  - `backref_lang4_flat_BPrf4_2`
  - `backref_lang4_flat_BPrf4`
  - `backref_lang_flat_BPrf4_special`
- Build: full local CI PASS with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:04
  elapsed), and statement guard.
- Notes:
  - This is a blueprint theory only. It does not migrate the frozen `brexp`
    datatype or change `backref_lang`, `BL`, `xder`, `BPrf`, or `bval`.
  - The special-case corollary checks that the old two-language
    `backref_lang` is represented by the four-language value story with
    empty prefix and tail languages.
- Next smallest safe step: leave BR-015 to Opus; defer BR-019 until the bounded
  fragment statement is explicit.

## BR-020 Per-Step Derivative Simplifier (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex new-file implementation lane
- Files changed: `BackRefBlexer.thy`, `PROGRESS_BACKREF.md`,
  `BACKREF_BOUNTIES.md`
- New checked definitions:
  - `bbders_simp`
  - `bblexer_step_simp`
- New checked lemmas/theorem:
  - `berase_bbders_simp`
  - `bbnullable_bbders_simp`
  - `bbders_simp_bbnullable_blexer`
  - `bbders_simp_bretrieve_blexer`
  - `bblexer_step_simp_defined_iff`
  - `bblexer_step_simp_correctness`
- Build: full local CI PASS with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and statement guard.
- Notes:
  - `bbders_simp` applies `bbsimp` after each bitcoded derivative step.
  - The proof reuses the existing retrieve transport: simplifying a derivative
    preserves retrieval for any checked derivative value, then induction over
    the input string recovers the same bitcode as `bblexer`.
- Next smallest safe step: BR-016 generalized value evidence, unless Opus
  releases or completes BR-015 first.

## BR-020 Post-Derivative Simplifier Partial (2026-05-26)

- Branch: `codex/backref-values`
- Commit: `968c32b`
- Agent lane: Codex new-file implementation lane
- Files changed: `BackRefBlexer.thy` (+174), `PROGRESS_BACKREF.md`
- New checked definitions:
  - `bbsimp`
  - `bblexer_simp`
- New checked lemmas/theorem:
  - `bfuse_append`
  - `berase_bbsimp`
  - `bbnullable_bbsimp`
  - `bbsimp_bfuse`
  - `bretrieve_stars_bbsimp`
  - `bretrieve_bbsimp`
  - `bbmkeps_bbsimp`
  - `bblexer_simp_correctness`
- Build: full local CI PASS with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04
  elapsed), and statement guard.
- Notes:
  - This is a conservative post-derivative simplifier:
    `bblexer_simp r s` simplifies `bbders (baintern r) s` once before the
    nullable/epsilon-code check.
  - It proves exact preservation of `bblexer`; it does not yet prove a
    `bbders_simp` loop that simplifies after each character derivative.
- Next smallest safe step: decide whether to extend BR-020 to a per-step
  `bbders_simp` theorem, or switch to BR-016 generalized value evidence.

## BR-018 Bitcoded Backreference Lexer Correctness (2026-05-26)

- Branch: `codex/backref-values`
- Agent lane: Codex new-file implementation lane
- Files changed: `BackRefBlexer.thy`, `PROGRESS_BACKREF.md`,
  `BACKREF_BOUNTIES.md`
- Bitcode semantic fixes:
  - `bretrieve` for `BABACKREF` now emits `Backbit (rev cs @ bflat v1)`,
    so retrieval from non-null capture values records the full captured string.
  - `bbder` now carries `bbmkeps r` into the transition from `BABACKREF` to
    `BAHALF`, matching the Scala reference shape where nullable capture
    evidence is preserved when replay begins.
- New checked lemmas/theorem:
  - `bretrieve_stars_append`
  - `bretrieve_alts_append`
  - `bretrieve_bfuse`
  - `bbder_residue_bretrieve`
  - `bbder_BAALTs_bretrieve`
  - `bbder_bretrieve`
  - `bbders_bbnullable_blexer`
  - `bbders_bretrieve_blexer`
  - `bblexer_bretrieve_original`
  - `bblexer_blexer_retrieve`
- Build: direct Isabelle `BackRefPilot` PASS with 90s timeout wrapper
  (0:09 elapsed after the final proof edit); full local CI PASS with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:04 elapsed),
  Isabelle `BackRefPilot` (0:04 elapsed), and statement guard.
- Notes:
  - `bblexer_blexer_retrieve` proves
    `bblexer r s = map_option (bretrieve (baintern r)) (blexer r s)`.
  - A broad proof attempt caused a timeout before this final structure; it was
    replaced with explicit list/case lemmas per the proof-performance rule.
- Next smallest safe step: BR-020 simplification rules in the new pilot file,
  or BR-016 generalized value pilot if avoiding simplification work.

## BR-018 Retrieve Layer Partial (2026-05-26)

- Branch: `codex/backref-values`
- Agent lane: Codex new-file implementation lane
- Files changed: `BackRefBlexer.thy` (+157 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked definitions:
  - `bretrieve_alts`
  - `bretrieve_stars`
  - `bretrieve`
- New checked lemmas/theorem:
  - `bretrieve_stars_replicate`
  - `bbmkeps_BAALTs_bretrieve`
  - `bbmkeps_bretrieve`
  - `bblexer_bretrieve`
  - `bblexer_retrieve_correctness`
- Build: full local CI PASS; no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and statement guard.
- Notes:
  - This does not complete BR-018 yet. It proves that nullable bitcoded
    evidence from an annotated derivative is exactly retrieval from
    `bmkeps (berase r)`, and packages the result for `bblexer`.
  - The next proof step should connect retrieval across `bbder`/`binjval` or
    define a decode/flex bridge back to the original `blexer` value.
- Next smallest safe step: prove a `bbder` retrieval transport lemma analogous
  to ordinary `bder_retrieve`, likely after adding any small helper facts for
  `bfuse` and backreference transition cases.

## BR-017 Bitcoded Backreference Lexer Definitions (2026-05-26)

- Branch: `codex/backref-values`
- Agent lane: Codex new-file implementation lane
- Files changed: `BackRefBlexer.thy`, `pilot/ROOT`, `PROGRESS_BACKREF.md`,
  `BACKREF_BOUNTIES.md`
- New checked definitions:
  - `bbit` with `Backbit string`
  - `barexp` with ordinary pilot constructors plus `BABACKREF`, `BAHALF`,
    and `BARESIDUE`
  - `berase`, `bfuse`, `baintern`, `bbnullable`, `bbmkeps`, `bbder`,
    `bbders`, and `bblexer`
- New checked lemmas:
  - `berase_bfuse`
  - `berase_baintern`
  - `bbnullable_correctness`
  - `berase_bbder_residue`
  - `berase_bbder`
  - `berase_bbders`
  - `bblexer_defined_iff`
- Build: full local CI PASS; Isabelle `Posix` (0:03 elapsed) and Isabelle
  `BackRefPilot` (0:03 elapsed).
- Notes:
  - The theory imports `BackRefValues` and does not modify production
    `Blexer.thy` or `BlexerSimp.thy`.
  - The derivative mirrors the checked `xder` shape after erasure. `Backbit`
    is emitted by nullable backreference evidence and by the transition to
    replay/half state.
- Next smallest safe step: BR-018 should add the retrieve/decode or code-value
  correctness story for the new bitcoded pilot.

## BR-008 Generalized backref_lang4 Derivative Story (2026-05-26)

- Branch: `codex/backref-values`
- Agent lane: Codex language-blueprint lane
- Files changed: `BackRefLang.thy`, `PROGRESS_BACKREF.md`,
  `BACKREF_BOUNTIES.md`
- New checked lemmas:
  - `backref_lang4I`
  - `Der_backref_lang4`
- Statement summary:
  - derivative splits into prefix derivative;
  - nullable-prefix capture derivative with accumulator update `c # cs`;
  - nullable-prefix and nullable-capture tail derivative
    `Der c (L3 ;; ({rev cs} ;; L4))`.
- Build: full local CI PASS; Isabelle `Posix` (0:35 elapsed) and
  Isabelle `BackRefPilot` (0:04 elapsed). Earlier pilot-only check passed in
  0:06 elapsed inside Isabelle.
- Guards: no-cheat, bounty, admin role guard, and statement guard pass
- Next smallest safe step: draft BR-016 value evidence shape for the
  generalized language without migrating the frozen datatype yet, or start
  BR-017 in a new `BackRefBlexer.thy` lane.

## BR-014 blexer POSIX Correctness (2026-05-26)

- Branch: `codex/backref-values`
- Agent lane: Opus proof lane with Codex stabilization/build verification
- Files changed: `BackRefValues.thy`, `PROGRESS_BACKREF.md`,
  `BACKREF_BOUNTIES.md`, and short coordination docs
- New checked lemmas:
  - `BPosix_BSTAR_value_shape`
  - `BPosix_BNTIMES_empty_replicate`
  - `blexer_correctness`
  - `BPosix_binjval`
  - `blexer_POSIX`
  - `blexer_POSIX_iff`
- Performance fix:
  - replaced slow `fun (sequential) binjval` with `primrec binjval`
    over `brexp` plus explicit `case v of ...` branches.
  - cold `BackRefPilot` build no longer spends about 200 seconds processing
    the `fun` command; checked cold build completed in about 16 seconds.
- Build: Isabelle `BackRefPilot` PASS
- Guards: no-cheat, bounty, role guard pass

## Do Not Start Yet

- Do not touch `Blexer.thy`.
- Do not touch `BlexerSimp.thy`.
- Do not touch bounds or closed-form theories.
- Do not claim a finite derivative bound for backreferences.

## Cubic Bound Research: Frontier Universe Accounting (2026-05-31)

- Branch: `codex/backref-values`
- Agent: Codex
- Files changed: `GeneralRegexBound.thy`, `BlexerSimp.thy`, `FBound.thy`
- New checked lemmas:
  - `quadratic_times_linear_cubic_bound`
  - `rsizes_distinct_frontier_universe_cubic`
  - `RLS_rpders_norm1_rows`
  - `rsizes_rpders_norm1_rows_frontier_universe_cubic`
  - `rpders_norm1_rows_rerase`
- Design result:
  - The viable repeated-derivative invariant should be frontier/product based:
    `partial_derivative_frontier_universe` has quadratic cardinality and
    linear member size, hence any distinct row list inside it has cubic total
    size.
  - A tempting invariant, "all subterms are closed under normalized partial
    derivatives", is too broad. In particular, subterms under an outer suffix
    can lose that suffix if treated as standalone states; `RNTIMES` exposes
    this sharply because `RNTIMES r n` can step to smaller repetition payloads.
  - Next target: prove that the normalized Antimirov rows/frontier generated
    by `rpder_norm_list`/`rpd_der_norm` stay inside the original
    `partial_derivative_frontier_universe` across repeated derivatives.
  - Added the explicit Antimirov state drivers:
    `rpder_norm_set`/`rpders_norm1` for set semantics and
    `rpder_norm_rows`/`rpders_norm1_rows` for executable distinct row lists.
    The row-list driver is language-correct and has a conditional cubic hook:
    once `set (rpders_norm1_rows r s)` is shown to stay in the original
    frontier universe, `rsizes` is bounded by `3 * (rsize r + 2)^3`.
  - Mirrored the row-list driver in the annotated layer with
    `bpder_norm_rows`/`bpders_norm1_rows`, and proved erasure back to the
    proof-level driver via `rpders_norm1_rows_rerase`.
- Build: Isabelle `Posix` and `BackRefPilot` PASS via
  `agent_hunt_pipeline/scripts/isabelle_ci.ps1`

## blexer Definition and Correctness (2026-05-26)

- Branch: `codex/backref-values`
- Agent: Opus (Cursor headless recovery)
- Files changed: `BackRefValues.thy` (+53 lines), `PROGRESS_BACKREF.md`
- New checked definitions and lemmas:
  - `blexer`: lexer function for pilot `brexp` using `xder`/`binjval`/`bmkeps`
  - `blexer_BPrf`: soundness (`blexer r s = Some v \<Longrightarrow> BPrf v r`)
  - `blexer_flat`: flat correctness (`blexer r s = Some v \<Longrightarrow> bflat v = s`)
  - `blexer_correct_None`: rejection correctness (`s \<notin> BL r \<longleftrightarrow> blexer r s = None`)
  - `blexer_correct_Some`: full characterization
    (`s \<in> BL r \<longleftrightarrow> (\<exists>v. blexer r s = Some v \<and> BPrf v r \<and> bflat v = s)`)
- Build: Isabelle `BackRefPilot` PASS (0:04 elapsed)
- Guards: no-cheat, bounty, worker role all pass
- This completes BR-013. Next: BR-014 (blexer correctness w.r.t. POSIX ordering).

## binjval Correctness Proofs (2026-05-26)

- Branch: `codex/backref-values`
- Agent: Opus (Cursor headless recovery)
- Files changed: `BackRefValues.thy` (+17 lines), `PROGRESS_BACKREF.md`
- New checked lemmas:
  - `BPrf_xder_residue`: eliminates `BPrf v (xder_residue c cs rep)`
  - `binjval_flat`: `bflat (binjval r c v) = c # bflat v` (BR-011)
  - `BPrf_BNTIMES_prepend`: helper for BNTIMES value prepend
  - `binjval_BPrf`: `BPrf (binjval r c v) r` when `BPrf v (xder c r)` (BR-012)
- Build: Isabelle `BackRefPilot` PASS (3:03 elapsed)
- Guards: no-cheat, bounty, worker role all pass
- Blocker resolved: BNTIMES case in `binjval_BPrf` needed explicit helper
  because `BPrf.intros(7)` pattern `BStars (vs1 @ vs2)` does not unify with
  `BStars (v # ws1 @ ws2)` (Cons vs append).

## Cubic Bound Research: rsimp9 RONE Stability (2026-06-02)

- Branch: `codex/backref-values`
- Agent: Codex heartbeat lane
- Files changed: `GeneralRegexBound.thy`, `PROGRESS_BACKREF.md`,
  `agent_hunt_pipeline/projects/posix-backref/DESIGN_LOG.md`
- New checked invariant:
  - `rtail_nf`: proof-only right-tail normal form for the `rrexp` bound layer.
    It rules out the sequence shapes that `rsimp4_SEQ_atom _ RONE` would still
    reassociate or erase.
- New checked lemmas:
  - `rtail_nf_RONE_stable`
  - `rtail_nf_flat_member_props`
  - `rtail_nf_flat_RONE_stable`
  - `rtail_nf_rsimp_ALTs`
  - `rtail_nf_rsimp4_SEQ_atom`
  - `rtail_nf_rsimp7_SEQ_atom`
  - `rtail_nf_rflts_map_rsimp9`
  - `rtail_nf_rsimp9`
  - `rsimp4_SEQ_atom_RONE_stable_rsimp9_pair`
  - `rsimp4_SEQ_atom_RONE_stable_rflts_map_rsimp9`
  - `rsimp4_SEQ_atom_RONE_stable_rflts_rsimp9`
  - `rsimp4_SEQ_atom_RONE_stable_rsimp9`
  - `rsimp9_rsimp4_SEQ_atom_rsimp9_RONE`
- Design result:
  - The earlier tempting lemma "if a list is stable then `rflts` of the list is
    stable" is false: flattening can expose unstable sequence payloads hidden
    under an alternative. The checked replacement proves stability through the
    exact normal-form invariant produced by `rsimp9`.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash, under the
  300s guard.
- Next step: use `rsimp4_SEQ_atom_RONE_stable_rsimp9` and the flat-member
  variant to close the carried-continuation bridge for general `RSEQ`, then
  reuse it for `RSTAR` and nonzero `RNTIMES`.

## Cubic Bound Research: path9 Raw-Spine Obstruction (2026-06-02)

- Branch: `codex/backref-values`
- Agent: Codex heartbeat lane
- Files changed: `GeneralRegexBound.thy`, `PROGRESS_BACKREF.md`,
  `agent_hunt_pipeline/projects/posix-backref/DESIGN_LOG.md`
- New checked counterexamples:
  - `rpath9_tail_rsimp4_SEQ_atom_not_subset_raw_spine`
  - `path9_raw_spine_parent_misses_rsimp7_star_absorption`
- Design result:
  - The tempting generalized carried-continuation bridge from
    `rsimp4_SEQ_atom body tail` into the parent raw-spine path9 universe is
    false. In the concrete pattern `(a · a*) · a*`, the carried simplifier plus
    `rsimp9`/`rsimp7` exposes `a · a*`, while the parent raw spine records
    `a · (a* · a*)`. Therefore the next cubic-bound universe cannot be just
    the current path9 atom frontier of the raw parent; it must include a
    checked account of normalized carried tails or use a stronger state-space
    simplification.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash, under the
  300s guard.
- Next step: prototype the refined universe/continuation relation that
  explicitly admits `rsimp9 (rsimp4_SEQ_atom body tail)` members, then retry
  the `RSEQ`/`RSTAR`/`RNTIMES` carried closure.

## Cubic Bound Research: carry9 Frontier Prototype (2026-06-02)

- Branch: `codex/backref-values`
- Agent: Codex heartbeat lane
- Files changed: `GeneralRegexBound.thy`, `PROGRESS_BACKREF.md`,
  `agent_hunt_pipeline/projects/posix-backref/DESIGN_LOG.md`
- New checked definitions:
  - `rcarry9_atom_frontier_acc`
  - `rcarry9_atom_frontiers`
  - `partial_derivative_carry9_atom_frontier_universe`
- New checked closure/core facts:
  - `finite_rcarry9_atom_frontier_acc`
  - `finite_rcarry9_atom_frontiers`
  - `finite_partial_derivative_carry9_atom_frontier_universe`
  - `rcarry9_atom_frontiers_universe`
  - `rder_path_continuations_acc_rcarry9_frontier`
  - `rder_path_continuations_acc_rcarry9_universe`
  - `rpder_norm9_carry9_atom_frontier_step`
  - `carry9_raw_spine_parent_covers_rsimp7_star_absorption`
- New checked cubic interface:
  - `partial_derivative_carry9_atom_frontier_universe_card_le`
  - `rsizes_distinct_carry9_atom_frontier_universe_cubicI`
  - `rsizes_rpders_norm19_rows_carry9_atom_frontier_universe_cubic`
  - `rsizes_rpders_norm19_rows_rsimp9_carry9_atom_frontier_cubicI`
  - `quadratic_plus_linear_times_param_linear_cubic_bound`
  - `rsizes_distinct_carry9_atom_frontier_universe_param_cubicI`
  - `rsizes_rpders_norm19_rows_carry9_atom_frontier_universe_param_cubic`
  - `rsizes_rpders_norm19_rows_rsimp9_carry9_atom_frontier_param_cubicI`
- Design result:
  - `carry9` aligns the proof-only frontier recursion with
    `rder_path_continuations_acc`: sequence/star/countdown tails are carried
    with `rsimp4_SEQ_atom`, and only character leaves take the `rsimp9`
    frontier. This repairs the checked `(a · a*) · a*` obstruction that the
    raw path9 spine missed.
  - The checked one-step theorem is a self-step:
    `rpder_norm9_list c r` lands in the carried universe of `r` for every
    `legacy_rrexp r`. This is progress toward the cubic route, not a final
    bound: repeated derivatives still need root-owned closure for every
    member of the root universe.
- Remaining obligations for a carry9 cubic theorem:
  - prove `card (rcarry9_atom_frontiers r) <= (rsize r + 2)^2`;
  - prove every member of `partial_derivative_carry9_atom_frontier_universe r`
    has size at most `K * (rsize r + 2)` for some fixed constant `K`;
  - prove root-owned closure:
    if `q` is in the root carry9 universe, then
    `set (rflts (rpder_norm9_list c q))` is also in that same root universe.
- Checked obstruction:
  - `carry9_member_size_two_bound_counterexample` shows the earlier
    `Suc (rsize r + rsize r)` member-size premise is too optimistic for
    carry9. A small star/sequence regex has a carry9 member larger than that
    bound. Therefore the viable cubic interface is the parameterized one
    above, not the fixed-2 member-size hook.
- Stronger checked obstruction:
  - `carry9_bad_root` defines a pure non-backref star/sequence family with
    linear root size (`rsize_carry9_bad_root`: `6*n+2`).
  - `carry9_bad_witness_acc`/`carry9_bad_witness` pick the repeated
    carried-continuation witness along that family.
  - `carry9_member_size_eight_bound_counterexample` shows that even
    `K = 8` is too small at depth 7: the witness is in the carry9 universe,
    but its size exceeds `8 * (rsize root + 2)`.
  - This means carry9 is best understood as a diagnostic/refinement prototype,
    not the final cubic universe. The next viable route should test whether a
    stronger Chapter-7-style simplifier collapses this family, or replace the
    carried-tail frontier with a more compact state representation.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash, under the
  300s guard.

## Cubic Bound Research: rStrong Shared-Suffix Prototype (2026-06-02)

- Branch: `codex/backref-values`
- Agent: Codex heartbeat lane
- Files changed: `GeneralRegexBound.thy`, `PROGRESS_BACKREF.md`,
  `agent_hunt_pipeline/projects/posix-backref/DESIGN_LOG.md`
- New checked definitions:
  - `rprune_eq_against`
  - `rsimpStrong_prune_pair`
  - `rsimpStrong_prune_against_rows`
  - `rsimpStrong_prune_rows_acc`
  - `rsimpStrong_prune_rows`
  - `rsimpStrong_ALTs`
  - `rsimpStrong`
  - `rders_simpStrong`
- New checked language facts:
  - `set_append_rprune_eq_against`
  - `RL_rprune_eq_against_cover_UN`
  - `RL_rprune_eq_against_shared_suffix`
  - `RL_rsimpStrong_prune_pair_shared_suffix`
  - `RL_rsimpStrong_prune_pair_with_earlier`
  - `RL_rsimpStrong_prune_against_rows`
  - `RL_rsimpStrong_prune_rows_acc`
  - `RL_rsimpStrong_prune_rows`
  - `RL_rsimpStrong_ALTs`
  - `RL_rsimpStrong`
  - `RL_rders_simpStrong`
- New checked size-control facts:
  - `rsizes_rprune_eq_against_le`
  - `rsize_rsimp_ALTs_le`
  - `rsize_rsimpStrong_pruned_ALTs_le`
  - `rsize_rsimpStrong_prune_pair_le`
  - `rsize_rsimpStrong_prune_against_rows_le`
  - `rsizes_rsimpStrong_prune_rows_acc_le`
  - `rsizes_rsimpStrong_prune_rows_le`
  - `rsize_rsimpStrong_ALTs_le`
  - `rsize_rsimpStrong_le`
- New checked partial-derivative route facts:
  - `rpder_strong_list`
  - `rpder_strong_rows`
  - `rpd_der_strong`
  - `rpders_strong_rows`
  - `rpders_strong1_rows`
  - `RLS_set_rflts`
  - `RLS_set_rsimpStrong_prune_rows`
  - `RLS_set_concat_rpder_strong_list`
  - `RLS_rpder_strong_rows`
  - `RL_rpd_der_strong`
  - `legacy_rprune_eq_against`
  - `legacy_rsimpStrong_prune_pair`
  - `legacy_rsimpStrong_prune_against_rows`
  - `legacy_rsimpStrong_prune_rows_acc`
  - `legacy_rsimpStrong_prune_rows`
  - `legacy_rsimpStrong_ALTs`
  - `legacy_rsimpStrong`
  - `legacy_rpder_strong_list`
  - `legacy_rpder_strong_rows`
  - `legacy_rpders_strong_rows`
  - `rsizes_rpder_strong_list_le`
  - `rsizes_concat_rpder_strong_list_le`
  - `rsizes_rpder_strong_rows_le`
  - `rsize_rpd_der_strong_le_rsizes`
  - `RLS_rpders_strong_rows`
  - `RLS_rpders_strong1_rows`
- New checked Chapter-7 regression facts:
  - `thesis_ch7_rstrong_prunes_overlap`
  - `thesis_ch7_rstrong_overlap_same_language`
  - `thesis_ch7_rsimpStrong_ALTs_prunes_overlap`
  - `thesis_ch7_rsimpStrong_ALTs_overlap_smaller`
  - `thesis_ch7_rsimpStrong_same_language`
- Design result:
  - The bound layer now has a small proof-level analogue of the `bsimpStrong`
    shared-suffix deletion: for two rows `RSEQ (RALTS lrs) k` and
    `RSEQ (RALTS rrs) k`, the later row may remove left alternatives already
    covered by the earlier row while preserving erased language.
  - The pair rule is now lifted to a full left-to-right row scanner and an
    `rsimpStrong` proof-level simplifier. The checked theorem
    `RL_rsimpStrong` proves it preserves `RL`, and `RL_rders_simpStrong`
    proves repeated derivatives interleaved with this simplifier still compute
    `Ders`.
  - The scanner and recursive simplifier are now size-safe:
    `rsize_rsimpStrong_le` proves the full proof-level simplifier never
    increases `rsize`, while the row-level lemmas show pruning, flattening, and
    duplicate removal stay within the original row budget. This is necessary
    evidence for a future cubic theorem because bounds can remain stated in
    terms of the original regex size.
  - The strong simplifier is now connected to the Antimirov-style row pipeline:
    `rpder_strong_rows` takes the existing normalized partial-derivative rows,
    applies `rsimpStrong`, then performs the Chapter-7 shared-suffix row prune.
    `RLS_rpder_strong_rows` proves the row set still denotes the derivative,
    and `rsizes_rpder_strong_rows_le` proves its row-size budget is no larger
    than the pre-strong normalized row budget.
  - The one-step route is now lifted to repeated input strings:
    `rpders_strong_rows` iterates the strong row step, while
    `RLS_rpders_strong_rows` proves the repeated row set denotes `Ders` for
    any legacy/non-backref start rows. The accompanying legacy lemmas ensure
    the repeated pipeline stays inside the non-backref fragment.
  - This directly checks the core Chapter-7 pattern behind
    `(a+b)c + (a+d)c -> (a+b)c + dc` when `d` is fresh with respect to
    `a,b`. If `d` is already covered, the later row correctly collapses
    further instead of producing `dc`. The checked size regression
    `thesis_ch7_rsimpStrong_ALTs_overlap_smaller` proves the multi-row
    simplifier strictly shrinks that overlap example.
  - This is deliberately not a production `bsimpStrong` payout: it is an
    `rrexp`/language-only prototype for the cubic-bound route. POSIX/bitcode
    preservation and the full repeated-derivative cubic theorem are still open.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash, under the
  300s guard.

## Cubic Bound Research Checkpoint: Annotated Strong Simplifier Size (2026-06-02)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked theorem added in `FBound.thy`:
  - `asize_bsimpStrong_le`
- Supporting size lemmas:
  - `asizes_flts_le`
  - `asizes_distinctWith_le`
  - `asizes_prune_eq1_against_le`
  - `asize_bsimp_AALTs_le`
  - `asize_bsimp7_ASEQ_atom_le`
  - `asize_bsimpStrong_prune_pair_le`
  - `asize_bsimpStrong_prune_against_rows_le`
  - `asizes_bsimpStrong_prune_rows_acc_le`
  - `asizes_bsimpStrong_prune_rows_le`
  - `asize_bsimpStrong_AALTs_le`
- Design result:
  - The executable annotated `bsimpStrong` prototype now has checked size
    control: simplification, row pruning, duplicate removal, and alternative
    flattening do not increase `asize`.
  - This is the annotated counterpart of the earlier proof-level
    `rsize_rsimpStrong_le` checkpoint. It makes the Chapter-7 shared-suffix
    pruning route usable for future `arexp` bounds without hiding the work in a
    wrapper.
  - POSIX/bitcode preservation for the stronger simplifier and the full cubic
    theorem are still open; no bounty is claimed from this checkpoint.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.

## Cubic Bound Research Checkpoint: Annotated Strong Loop Semantics (2026-06-02)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked theorem added in `FBound.thy`:
  - `RL_rerase_bders_simpStrong`
- Supporting semantic bridge lemmas:
  - `RL_rerase_AALTs`
  - `RL_rerase`
  - `RL_rerase_bsimpStrong`
- Design result:
  - The executable annotated strong loop now has a direct erased-language
    correctness theorem:
    `RL (rerase (bders_simpStrong r s)) = Ders s (RL (rerase r))`.
  - This deliberately avoids claiming syntactic equality with
    `rders_simpStrong`; the proof-level strong pair prune normalizes
    `rflts/rdistinct` immediately, while the annotated implementation
    performs that cleanup through `bsimpStrong_AALTs`.
  - Together with `asize_bsimpStrong_le`, this gives the annotated prototype
    both semantic and size-control evidence needed before attempting POSIX/
    bitcode preservation or a full cubic closure theorem. No bounty is claimed.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.

## Cubic Bound Research Checkpoint: Annotated Strong Loop Legacy Closure (2026-06-02)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked theorem added in `FBound.thy`:
  - `legacy_rerase_bders_simpStrong`
- Supporting legacy-preservation lemmas:
  - `legacy_rerase_flts`
  - `legacy_rerase_distinctWith`
  - `legacy_rerase_prune_eq1_against`
  - `legacy_rerase_bsimp_AALTs`
  - `legacy_rerase_bsimpStrong_prune_pair`
  - `legacy_rerase_bsimpStrong_prune_against_rows`
  - `legacy_rerase_bsimpStrong_prune_rows_acc`
  - `legacy_rerase_bsimpStrong_prune_rows`
  - `legacy_rerase_bsimpStrong_AALTs`
  - `legacy_rerase_bsimpStrong`
- Design result:
  - The executable annotated strong simplifier and its derivative loop now stay
    inside the proof-level legacy/non-backref fragment whenever the initial
    annotated regex erases to that fragment.
  - This closes an important invariant gap for the cubic-bound route: future
    bounds for `bders_simpStrong` can state the non-backref premise as
    `legacy_rrexp (rerase r)` and know that all recursive states remain in the
    fragment where finite-universe accounting is meaningful.
  - This is not POSIX/bitcode preservation and not a full cubic theorem; no
    bounty is claimed.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.

## Cubic Bound Research Checkpoint: Annotated Strong Row Pipeline (2026-06-02)

- Branch: `codex/backref-values`
- Agent: Codex
- Added executable annotated row definitions in `BlexerSimp.thy`:
  - `bpder_strong_list`
  - `bpder_strong_rows`
  - `bp_der_strong`
  - `bpders_strong_rows`
  - `bpders_strong1_rows`
- Checked semantic/fragment bridge lemmas in `FBound.thy`:
  - `RLS_set_map_rerase_bpder_strong_rows`
  - `RLS_rerase_bp_der_strong`
  - `legacy_rerase_bpder_strong_rows`
  - `legacy_rerase_bpders_strong_rows`
  - `RLS_set_map_rerase_bpders_strong_rows`
  - `RLS_set_map_rerase_bpders_strong1_rows`
- Design result:
  - The proof-level `rpder_strong_rows` route now has an annotated executable
    counterpart that performs the same staged idea: normalized partial
    derivative rows, strong recursive simplification, cross-row shared-suffix
    pruning, flattening, and duplicate removal.
  - The checked theorem
    `RLS_set_map_rerase_bpders_strong_rows` proves that repeated annotated
    strong-row derivatives compute `Ders` after `rerase`, assuming the start
    rows are in the legacy/non-backref fragment.
  - This still does not prove POSIX/bitcode preservation or the final cubic
    closure theorem, but it closes the main executable/proof-level gap for the
    strong-row prototype.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.

## Governance Upgrade (2026-05-25)

- Branch: `codex/backref-values`
- Agent: Opus (Cursor)
- Authorized by: admin (Chengsong)
- Changes:
  - `BOUNTY_PROTOCOL.md`: rewritten to replicate Agent Hunt paper mechanics
    (competitive-collaborative system, 50k pool, 10% deposit locks, max 10 locks,
    lock-or-lose, sub-bounties, early-finish bonus, effort estimates, statement
    immutability).
  - `BACKREF_BOUNTIES.md`: added pool tracking, effort estimate columns,
    new bounties BR-011 through BR-020, updated lock rules to max 10.
  - `CLAUDE.md` (project profile): expanded bounty discipline section with
    full Agent Hunt mechanics, added statement immutability section, added
    guard scripts table.
  - `backref_bounty_guard.py`: upgraded to enforce max 10 locks, pool cap,
    effort estimate validation, sub-bounty ledger actions, lock deposit
    verification (10% of bounty).
  - `backref_statement_guard.py`: new guard enforcing frozen statement
    immutability by comparing against snapshots.
  - `agent_hunt_pipeline/snapshots/`: frozen snapshots of BackRefLang.thy
    and BackRefValues.thy.
- Guard results: all four guards pass.
- Build: no theory file changes; Isabelle build not required.

## Open Design Questions

- Whether `rep` should remain pure reconstruction metadata in values, or later
  become part of a stronger value invariant.
- Whether `BBackref` value evidence should carry both the captured value and
  the replayed copy explicitly. The current checked design carries one captured
  value and flattens it twice.
- Whether the pilot should migrate from the current two-language
  `backref_lang A B cs` to the generalized four-language
  `backref_lang4 L1 L2 L3 L4 cs`. The old definition is now checked as the
  special case `backref_lang4 {[]} A B {[]} cs`.
