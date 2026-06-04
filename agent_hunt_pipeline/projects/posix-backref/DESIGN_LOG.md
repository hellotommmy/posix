# Posix Backref Design Log

This file records semantic design changes that affect later proofs. It is meant
to be read before continuing long-running agent work.

## 2026-06-04: Memo-strong owner metrics replace bsimpCubic proof attempts

- The graph evidence is now treated as decisive negative evidence for direct
  `bsimpCubic` emitted-tree cubic proofs. The active route is memo-strong:
  keep `bders_simpStrong` as the nullable recognition gate, reconstruct exact
  POSIX values with original-regex span memoization, and prove size through the
  final-active row-DAG owner table.
- Extended the Scala smoke metrics to decompose active/final rows into
  ALT nodes, payload roots, payload DAG universe, suffix-key DAG universe, and
  both a component union observation and the proof-facing decomposition bound
  `rows + altNodes + payloadDag + keyDag`. The key proof-facing metrics are now
  `strongMemoFinalActiveRowDagUniverse` and
  `strongMemoFinalActiveDecompBound`; emitted tree size is diagnostic only.
- Future proof work should target linear component/owner bounds feeding
  `strong_deferred_memo_lexer_final_active_row_dag_linear_contract`. Do not
  claim a cubic bounty for a reassociated or emitted-tree simplifier unless it
  also has exact POSIX value reconstruction checked.

## 2026-06-04: Decomposition linear hook

- Added
  `FBound.thy:card_strong_deferred_final_active_suffix_row_dag_universe_decomp_linearI`.
  It turns three component premises
  `rows <= R * rxsize r`, `payloadDag <= P * rxsize r`, and
  `keyDag <= Q * rxsize r` into
  `rowDagUniverse <= (2 * R + P + Q) * rxsize r`.
- This is now the preferred bridge from the smoke metric
  `strongMemoFinalActiveDecompBound` to the memo-strong lexer contract. The
  remaining proof obligations should be attacked as component bounds, not as a
  raw emitted-tree bound.

## 2026-06-04: The main memo-strong proof target is linear final row-DAG

- Added
  `strong_deferred_memo_lexer_final_active_row_dag_linear_contract`.
  This is the preferred BR-040 statement shape until it is discharged:
  prove
  `card (strong_deferred_final_active_suffix_row_dag_universe r s)
   <= K * rxsize r`, then exact POSIX correctness and the relevant row/pair
  budgets follow through the named `strong_deferred_memo_lexer`.
- This deliberately avoids proving over the emitted recognition tree. The tree
  may be useful operationally, but the bounded object is the final-active
  hash-consed row-DAG owner table.
- The final-active scout script now exposes `RowDagUniverseFactor` and reports
  the worst row-DAG universe ratio. Future smoke summaries must include this
  metric because it is the one matching the Isabelle theorem target.

## 2026-06-04: Memo-strong size proof uses one final row-DAG owner

- The derivative-size graphs make direct emitted-tree `bsimpCubic` the wrong
  object to prove cubic bounds about. Treat it as negative evidence unless a
  future implementation first beats the memo-strong traces and preserves exact
  POSIX values.
- The current proof architecture is: `bders_simpStrong (intern r) s` is a
  recognition gate, `strong_deferred_memo_lexer` is the exact POSIX value
  interface, and `strong_deferred_final_active_suffix_row_dag_universe r s`
  is the hash-consed size object.
- Added
  `strong_deferred_memo_lexer_final_active_dag_owner_contract`. A finite
  owner table `DagU` containing the final-active row-DAG universe now controls
  the named lexer value theorem, row count, pair budget, payload/root/key
  coverage, row-DAG/max-row-DAG size, and span/split memo budgets.
- Future BR-040 work should therefore prove a concrete bound on `DagU`. Do
  not return to proof-first `bsimpCubic` tree-size attempts unless smoke tests
  and exact POSIX reconstruction are already green.

## 2026-06-04: Strong-memo smoke checks the nullable gate directly

- The Scala `strong-memo` route now has an explicit
  `checkStrongMemoRecognitionGate` guard. It checks that
  `bnullable (bdersStrong (intern r) s)` agrees with the baseline lexer
  acceptance before comparing reconstructed values.
- This matters because the candidate architecture separates recognition from
  reconstruction: a false-positive strong gate can still yield no original
  POSIX value from the span table. Value equality alone would not necessarily
  expose that bug on rejecting inputs.
- Future candidate tests must keep both checks: gate correctness and exact
  POSIX value reconstruction. The Isabelle analogue is the pair of facts
  `strong_deferred_span_value_ex1_iff` and
  `strong_deferred_memo_lexer_Some_iff_span_value`.

## 2026-06-04: Memo-strong lexer is the named value candidate

- Treat emitted-tree `bsimpCubic` as negative evidence. Do not spend proof
  effort on it unless a future implementation first passes the strong smoke
  suite and beats the memo-strong final-active row-DAG traces.
- The proof-facing value candidate is now named
  `strong_deferred_memo_lexer`. Its implementation is intentionally the
  memo-strong architecture:
  `bders_simpStrong (intern r) s` is only the nullable recognition gate, and
  the returned POSIX value is reconstructed from the original regex/string via
  `strong_deferred_span_value`.
- The checked facts
  `strong_deferred_memo_lexer_eq_lexer`,
  `strong_deferred_memo_lexer_POSIX_correctness`,
  `strong_deferred_memo_lexer_flat`, and
  `strong_deferred_memo_lexer_Some_iff_span_value` are the main semantic entry
  points. Future size theorems should state their value conclusion through
  this named function, then separately account for the final-active row-DAG
  owner table.
- Added `agent_hunt_pipeline/scripts/strong_memo_value_gate.ps1` as the
  route-specific smoke command. It calls the Scala `strong-memo` route and
  checks exact POSIX values, known counterexamples, deterministic random
  cases, and the final-active row-DAG universe metric. Use this before
  attempting any new cubic proof candidate.

## 2026-06-04: RowU + DagU owner contract matches hash-consing

- Added `strong_deferred_original_final_active_rowU_dag_owner_contract`.
  It is now the preferred handoff when the candidate proof constructs a finite
  hash-consed owner table `DagU` that contains the final-active row-DAG
  universe.
- `RowU` controls only the number of final-active rows and therefore the pair
  budget. `DagU` controls exact-DAG/max-row-DAG size and, via the previous
  root/key containment lemmas, also owns payload roots, suffix keys, and their
  DAG components.
- This is slightly more implementation-shaped than the subterm-closed
  universe handoff: future proofs may show `row_dag_universe ⊆ DagU` directly
  without also proving `DagU` is closed under all `rsubterms`.

## 2026-06-04: Final row-DAG owns payload/key roots

- Added raw and lifted subset facts showing that final-active payload roots,
  suffix keys, payload DAG nodes, and key DAG nodes are all contained in the
  final-active row-DAG universe.
- The important packaged facts are
  `strong_deferred_final_active_suffix_roots_keys_subset_row_dag_universe` and
  `strong_deferred_final_active_suffix_payload_key_dag_universe_subset_row_dag_universe`.
- Proof consequence: future BR-040 work can make
  `strong_deferred_final_active_suffix_row_dag_universe r s` the canonical
  hash-consed table. Once a candidate `U` covers that table, it also covers
  the payload/key roots and DAG components required by the `RowU/root-U`
  contract. This avoids proving the same root/key coverage separately in every
  universe instantiation.

## 2026-06-04: RowU + root-owned U is the active memo-strong handoff

- The graph evidence makes the direct emitted-tree `bsimpCubic` route
  implausible. Treat it as a counterexample/regression playground, not as the
  theorem candidate.
- The active candidate is memo strong tree: use
  `bders_simpStrong (intern r) s` only as the small nullable recognition tree,
  then reconstruct exact POSIX values from the original regex/string through
  `strong_deferred_span_value`.
- Added
  `strong_deferred_original_final_active_rowU_shared_root_universe_contract`.
  This is the most modular checked handoff currently available. It assumes:
  final-active rows are included in a finite `RowU` of size `R`; payload roots
  and suffix keys are included in a finite subterm-closed `U` of size `D`.
  It concludes exact POSIX `Some`/`None`, `flat`, legacy preservation, row and
  pair budgets, and final row-DAG/max-row-DAG bounds `<= 2 * R + D`.
- Future BR-040 work should therefore construct/bound `RowU` and root-owned
  `U`. Do not spend proof effort on `bsimpCubic` output unless a new executable
  candidate first beats the smoke graphs and preserves POSIX values.

## 2026-06-04: Shared universe plugs directly into POSIX contract

- Added `strong_deferred_original_final_active_shared_row_dag_linear_contract`.
  This is now the preferred BR-040 handoff when a candidate proof can build a
  single shared universe for payload/key DAG components.
- The remaining obligations are exactly: final-active row count linear in
  `rxsize r`, payload/key DAG components included in a finite `U`, and
  `card U <= C * rxsize r`. The theorem then gives
  `finalRowDag <= (C + 2) * rxsize r` plus exact POSIX `Some`/`None`,
  `flat`, legacy, pair-budget, span-state, and split-probe facts.
- Prefer this theorem over manually chaining
  `card_strong_deferred_final_active_suffix_row_dag_universe_shared_component_boundI`
  with POSIX reconstruction in future proofs. It avoids duplicating the same
  arithmetic and keeps the proof target visibly about constructing `U`.
- Added `rsubterm_closure_subsetI` and
  `strong_deferred_original_final_active_shared_root_universe_linear_contract`.
  Prefer this even higher-level handoff when possible: prove that the
  payload-root set and suffix-key set are contained in a finite root-owned
  universe `U`, and prove `U` is closed under `rsubterms`. The theorem lifts
  this to payload/key DAG coverage automatically and then supplies the same
  exact POSIX and `(C + 2) * rxsize r` row-DAG conclusions.

## 2026-06-04: Memo-strong tree is the only active cubic route

- The derivative-size graphs and the latest smoke run make the decision
  operational: stop treating emitted-tree `bsimpCubic` as a proof target.
  Keep it only as negative evidence and as a regression playground.
- The active architecture is:
  1. run `bders_simpStrong (intern r) s`;
  2. use the resulting strong tree only as the nullable recognition gate;
  3. reconstruct exact POSIX values from the original regex/string via
     `strong_deferred_span_value` / span memoization;
  4. prove size over the final-active row-DAG/shared universe.
- Fresh `strong-memo` smoke passed exact POSIX values on the default
  exhaustive grid, the known CE grid, and `5,000` deterministic random
  depth-`7`/input-`8` cases with seed `20260602`. The Chapter 7 traces through
  `n=80` give:
  - `k=5,rsize=46`: `strongMemoTree=957`, `strongMemoDag=69`,
    `strongMemoFinalActiveRowDagUniverse=41`, pair budget `17` at `n=80`;
  - `k=8,rsize=97`: `strongMemoTree=3233`, `strongMemoDag=133`,
    `strongMemoFinalActiveRowDagUniverse=91`, pair budget `65` at `n=80`.
- The focused report is
  `agent_hunt_pipeline/reports/ch7_memo_strong_size_compare/index.html`.
  Use this report when judging whether a future candidate is at least as good
  as the thesis Chapter 7 behavior.
- Proof work should reuse the existing checked POSIX layer:
  `strong_deferred_memo_tree_POSIX_correctness`,
  `strong_deferred_memo_tree_POSIX_flat`, and the final-active contracts.
  The remaining hard theorem is the row-DAG/shared-universe bound, not POSIX
  value preservation from the simplified emitted tree.

## 2026-06-04: Memo-strong proof route uses row-DAG decomposition

- Treat emitted-tree `bsimpCubic` as negative evidence and stop optimizing it
  as a theorem candidate. The promising route is memo strong tree: preserve
  exact POSIX values by reconstructing from the original regex and bound a
  shared final-active row universe.
- The new proof-facing decomposition is:
  `final row-DAG <= rows + alt-nodes + payload-DAG + suffix-key-DAG`.
  At the raw level this is checked by
  `card_raw_final_active_suffix_row_dag_universe_decomp_boundI`; at the lifted
  memo-strong level by
  `card_strong_deferred_final_active_suffix_row_dag_universe_decomp_boundI`.
  This is sharper than the earlier `rows * maxRowDag` bridge and better
  matches the hash-consed/memo interpretation seen in the Scala data.
- The `alt-nodes` component is now checked to be bounded by the row count.
  Use the tighter interface
  `card_strong_deferred_final_active_suffix_row_dag_universe_decomp_rows_boundI`
  when possible: the remaining accounting target is
  `2 * rows + payload-DAG + suffix-key-DAG`.
- The payload/key DAG components are now closure interfaces rather than opaque
  sets. For keys, use
  `strong_deferred_final_active_suffix_key_dag_universe_eq_rsubterm_closure`
  and `card_strong_deferred_final_active_suffix_key_dag_universe_boundI`.
  For payloads, use
  `strong_deferred_final_active_suffix_payload_roots`,
  `strong_deferred_final_active_suffix_payload_dag_universe_eq_rsubterm_closure`,
  and
  `card_strong_deferred_final_active_suffix_payload_dag_universe_boundI`.
  This leaves the real BR-040 work in two concrete obligations: bound the
  number of roots/keys and bound each root/key DAG by an original-owned
  universe.
- The preferred high-level accounting handoff is now
  `card_strong_deferred_final_active_suffix_row_dag_universe_component_boundI`.
  It packages the component story as
  `finalRowDag <= 2*R + P*PM + K*KM`. Future proof attempts should try to
  instantiate this theorem with original-regex-owned bounds rather than
  reopening the whole row-DAG definition.
- Payload roots now have the same invariant hooks as rows and keys:
  `legacy_strong_deferred_final_active_suffix_payload_roots` for all inputs
  and
  `row_group_deep_nf_strong_deferred_final_active_suffix_payload_roots_nonempty`
  for nonempty derivative runs. Use these when building the original-owned
  row universe; do not re-split `RSEQ (RALTS rows) k` by hand in every proof.
- When possible, prefer the shared-universe handoff
  `card_strong_deferred_final_active_suffix_row_dag_universe_shared_component_boundI`
  over the product-style component handoff. It says that a single finite
  universe `U` covering both payload-DAG and key-DAG components gives
  `finalRowDag <= 2*rows + card U`, which better matches hash-consing and
  avoids double-counting shared subterms.
- The proof style matters: the checked bridge uses explicit `rsubterms`
  witnesses and explicit suffix-key membership, not large `auto`/`blast`
  searches. Keep this style for the remaining component bounds.
- The latest smoke after the bridge still preserves exact POSIX values on the
  default exhaustive grid, known CE grid, and `1,000` deterministic random
  depth-6/input-8 cases. The worst random final-active row-DAG universe ratio
  in that run was `57 / 28 = 2.035714`, so the factor-`3` gate remains the
  current executable guard while the theorem statement stays parameterized by
  a small constant.

## 2026-06-04: Row-DAG universe is wired into POSIX reconstruction

- The active executable metric is now wired directly into the Scala smoke
  gate. `PosixCubicSmoke.scala` reports the final-active row-DAG universe,
  which mirrors `strong_deferred_final_active_suffix_row_dag_universe`, and
  `scala_cubic_smoke.ps1` exposes
  `-StrongFinalActiveRowDagUniverseFactor`. This is the metric future proof
  attempts should explain.
- `isabelle_ci.ps1` now passes the same final-active row-DAG-universe budget
  into Scala with default factor `3.0` and top-`3` reporting. This prevents
  the main CI gate from silently checking only POSIX value preservation while
  omitting the current size metric.
- Fresh Chapter 7 long-tail smoke distinguishes the three size notions that
  were previously easy to conflate. For `k=5,rsize=46,n<=80`, emitted strong
  tree reaches `959` and prefix active row-DAG universe reaches `320`, but
  final-active row-DAG universe stays in `40..44`. For `k=8,rsize=97,n<=80`,
  emitted strong tree reaches `3245` and prefix active row-DAG universe
  reaches `870`, but final-active row-DAG universe stays in `83..97`.
- Do not target constant-`1` or constant-`2` theorems of the form
  `card final_active_row_dag_universe <= K * rxsize r`. The factor-`1`
  shrinker finds `STAR(ALT(CH(b),STAR(CH(b))))` on input `b`, where exact
  POSIX values agree, `rsize=5`, and the final-active row-DAG universe has
  size `7`. The factor-`2` shrinker finds
  `NTIMES(NTIMES(STAR(ALT(STAR(CH(b)),CH(b))),2),2)` on `bbb`, where
  `rsize=11` and the universe has size `23`. Keep the statement
  parameterized by a small constant; the current executable gate uses
  factor `3.0`, with no CE found in the latest 5,000-case finder run.
- These two minimized failures are now checked inside Isabelle as
  `thesis_memo_strong_row_dag_factor1_counterexample` and
  `thesis_memo_strong_row_dag_factor2_counterexample`. They are intentionally
  tiny proof-side regression facts, not broad executable testing; broad grids
  still belong in Scala.
- Therefore the proof target is final-only active sharing. Do not use
  `bsimpCubic` emitted-tree traces or prefix-cumulative active-universe traces
  as success criteria. They are useful diagnostics only. A theorem candidate
  must preserve exact POSIX values through the original-regex reconstruction
  contract and control the final-active row-DAG universe.
- Current route after the derivative-size graphs: do not rescue emitted-tree
  `bsimpCubic`. The proof target is memo strong tree as a nullable recognition
  gate, exact original-regex POSIX reconstruction via
  `strong_deferred_span_value`, and final-active row-DAG accounting.
- Added empty-row bridge facts at both raw and lifted levels, including
  `raw_final_active_suffix_row_dag_universe_empty_iff`,
  `raw_final_active_suffix_pair_budget_empty`,
  `raw_final_active_suffix_max_row_dag_empty`,
  `strong_deferred_final_active_suffix_row_dag_universe_empty_iff`,
  `strong_deferred_final_active_suffix_pair_budget_empty`, and
  `strong_deferred_final_active_suffix_max_row_dag_empty`. This formalizes why
  a large inactive whole-final DAG with `finalRows=0` should not block the
  primary row-DAG theorem.
- Added `strong_deferred_original_final_active_empty_rows_contract`, which
  packages the `finalRows=0` case with exact POSIX `Some`/`None`
  reconstruction, `flat v = s`, and zero active budgets. This is the clean
  theorem to cite when a smoke counterexample has no final-active rows.
- Do not revive linear raw-tree one-step bounds such as
  `asize (bder c (intern r)) <= K * rxsize r` as the main route; they miss the
  sharing that the final-active row-DAG metric is designed to expose. Raw tree
  bounds may be useful as diagnostics only.
- Added the final raw DAG handoff
  `strong_deferred_original_final_raw_dag_linear_contract`, plus the checked
  base facts `strong_deferred_final_raw_dag_size_empty_le_rxsize` and
  `strong_deferred_final_raw_dag_size_singleton_le_rxsize_square`. The proof
  route can now target the Scala `strongMemoDag` metric directly: a future
  linear bound on the exact DAG of the whole final memo-strong recognition
  tree implies exact POSIX reconstruction and the final-active row/pair/DAG
  budgets through existing contracts.
- However, whole-final-DAG constants are not the primary route. Seed
  `20260607` gives a factor-`3.0` CE for `strongMemoDag`:
  `NTIMES(STAR(NTIMES(ALT(CH(a),NTIMES(STAR(CH(b)),2)),3)),2)` on `abbb`,
  with `rsize=15`, `strongDag=48`, and `finalRows=0`. This shows inactive
  final DAG structure can defeat small whole-DAG constants while final-active
  accounting remains tiny. Keep BR-040 focused on final-active row-DAG
  universe unless a stronger whole-DAG theorem with an acceptable constant is
  discovered.
- Added the one-character base case
  `card_strong_deferred_final_active_suffix_row_dag_universe_singleton_le_rxsize_square`,
  supported by `asize_bder_intern_legacy_le_rxsize_square`. This extends the
  checked row-DAG evidence from `s = []` to `s = [c]` for legacy roots. The
  proof intentionally uses constructor-local arithmetic helper lemmas instead
  of broad nonlinear automation. It is proof infrastructure only; it does not
  close BR-040 or justify any bounty payout.
- Added the empty-input base case
  `card_strong_deferred_final_active_suffix_row_dag_universe_empty_le_rxsize`.
  This checks the target row-DAG universe inequality at `s = []` with
  `K = 1`; the remaining theorem should now be viewed as the nonempty
  derivative-step/induction problem.
- Added `strong_deferred_original_final_active_single_row_dag_linear_contract`.
  It states the current proof objective in its cleanest form: prove one
  original-regex-owned linear bound on
  `strong_deferred_final_active_suffix_row_dag_universe`, and the existing
  memo-strong route yields exact POSIX reconstruction plus all final-active
  row/pair/max-DAG budgets. Future work should try to prove this single
  premise, not reintroduce a separate row-count proof unless that split is
  genuinely easier.
- Latest route decision: emitted-tree `bsimpCubic` should be treated as
  negative evidence and tooling residue. The active route is memo strong tree
  plus exact original-regex POSIX reconstruction and final-active row-DAG
  accounting.
- Added a whole-final-DAG budget shrinker to the Scala smoke gate. It is
  useful for falsifying over-tight constants, not for replacing the
  proof-facing row-DAG target. Recent runs found no CE for factors `4` and `3`
  on random grids, but factor `2` shrinks to
  `STAR(NTIMES(STAR(CH(b)),2))` on input `bb`, where exact POSIX values still
  agree and `strongDag=13` for `rsize=6`.
- The default final-active scout remains the main executable gate. The
  refreshed three-seed run has no CE for rows `1.0 * rsize`, pair budget
  `1.0 * rsize^2`, and exact-DAG/shape-DAG row-member budget
  `2.0 * rsize`. The Chapter 7 report now extends to `n=80`; for `k=5/8`,
  final rows are `5/9` and final max row-DAG is `31/61`.
- Follow-up smoke on seed `20260605` reinforces the same target: exact POSIX
  values pass on `5,000` random depth-6/input-8 cases, and Chapter 7 long tails
  keep final-active row DAGs small (`k=5,n=80`: final max row DAG `31`;
  `k=8,n=80`: `61`). Raw row tree size can exceed `3 * rsize` on random cases,
  so future proofs should not try to bound raw row-tree member size linearly.
  Keep targeting DAG/row-universe accounting.
- Added `strong_deferred_final_raw_dag_size`, the erased exact-DAG size of the
  final memo-strong recognition tree. The bridge
  `strong_deferred_final_raw_dag_bound_to_row_dag_universe_bound` means a
  future bound on the whole final DAG is enough to feed the existing
  row-DAG/POSIX reconstruction contract.
- Refreshed the Chapter 7 plot for `k=5,8,n<=64` with
  `strongTree`, `strongMemoTree`, `strongMemoDag`,
  `strongMemoFinalActiveMaxRowDag`, and `strongMemoFinalActiveRows`. At
  `n=64`, `strongMemoDag` is `72` for `k=5` and `133` for `k=8`, while
  final max row-DAG is `31` and `61`. This supports a proof route through
  exact DAG sharing; it is not yet the original-size theorem.
- Route decision after the derivative-size graphs: do not spend proof effort
  rescuing emitted-tree `bsimpCubic`. The active candidate is memo strong tree:
  use `bders_simpStrong` only as the small nullable recognition gate and
  reconstruct exact POSIX values from the original regex via
  `strong_deferred_span_value`.
- A stronger smoke run on seed `20260602` checked `2,000` random depth-6/input-8
  cases plus the default `84,300` exhaustive cases. The thesis Chapter 7
  `k=5,n=4..32` trace kept the recognition tree in `474..918`, with final
  rows `4/5` and final max row-DAG `31`. This supports proving a final-active
  row-DAG bound rather than an emitted-tree bound.
- Added row-DAG eliminators at both raw and lifted levels:
  `raw_final_active_suffix_row_dag_universeE` and
  `strong_deferred_final_active_suffix_row_dag_universeE`. Future row-universe
  proofs should use these to recover the carrying `RSEQ (RALTS rows) k`
  instead of reopening the whole final derivative tree.
- The active size target is now final-active row exact-DAG size, not raw row
  tree size. `strong_memo_final_active_scout.ps1` defaults to rows
  `1.0 * rsize`, pair budget `1.0 * rsize^2`, and exact-DAG/shape-DAG member
  budgets `2.0 * rsize`, with raw member size disabled as a gate. The latest
  three-seed scout passes and shows the key separation: a raw row-tree ratio
  of `5.633333` can correspond to exact-DAG and shape-DAG ratios `1.266667`.
  Future proof work should explain this sharing, not try to bound the raw
  emitted member tree.
- Added `rsubterm_closure U = (\<Union>q\<in>U. rsubterms q)` and proved it is
  finite, extensive, closed under `rsubterms`, and bounded by
  `card U * M` when every member's exact-DAG size is at most `M`.
- Added `strong_deferred_original_final_active_row_dag_row_closure_contract`.
  This instantiates the two-universe handoff with
  `DagU = rsubterm_closure RowU`. The next proof target can therefore focus
  on one original-regex-owned row universe: cover final-active rows, bound
  its cardinality, and bound each member's exact-DAG size.
- Added `strong_deferred_original_final_active_row_metrics_contract`, the
  direct proof-side mirror of the Scala final-active metrics. It sets
  `RowU = strong_deferred_final_active_suffix_rows r s`, so the proof
  obligations now match the smoke columns: final row count `R`, per-row
  exact-DAG size `M`, pair budget `R * R`, and row-DAG universe size `R * M`.
  This is a handoff contract only; the cubic proof still has to derive `R`
  and `M` from the original regex, not from the emitted tree.
- Added the scalar metric
  `strong_deferred_final_active_suffix_max_row_dag` and theorem
  `strong_deferred_original_final_active_max_row_dag_metrics_contract`. This
  is now the preferred statement shape for BR-040 because it matches the
  executable `finalMaxRowDag` report directly.
- Added the bridge
  `strong_deferred_original_final_active_row_dag_universe_metrics_contract`:
  a cardinality bound for `strong_deferred_final_active_suffix_row_dag_universe`
  implies the scalar `finalMaxRowDag` bound. This keeps the proof route
  flexible: either prove the scalar metric directly or prove the row-DAG
  universe bound and inherit the scalar one.
- Added final-size fallback lemmas for the scalar max-row-DAG metric. These
  are not the desired original-size bounds, but they keep the new metric
  compatible with older final-tree accounting.
- Added the single-universe contract
  `strong_deferred_original_final_active_single_row_dag_universe_contract`.
  The next main theorem can now aim at one object:
  `card (strong_deferred_final_active_suffix_row_dag_universe r s) <= D`.
  That one bound controls final row count, pair budget, scalar max-row-DAG,
  row-member exact-DAG size, and exact POSIX reconstruction.
- Added the decomposition
  `strong_deferred_final_active_suffix_row_dag_universe_eq_rsubterm_closure`
  plus
  `card_strong_deferred_final_active_suffix_row_dag_universe_le_rows_times_max`.
  This gives the proof split `row-DAG <= finalRows * finalMaxRowDag`; future
  work may prove those two scalar bounds separately instead of constructing a
  monolithic universe.
- Added `strong_deferred_original_final_active_row_dag_two_universe_contract`.
  It separates the accounting objects: `RowU` bounds the number of
  final-active rows and hence the pair budget, while `DagU` is closed under
  `rsubterms` and bounds exact-DAG nodes. This matches the smoke evidence
  better than forcing a single universe to be both a tight row-count universe
  and a closed hash-cons universe.
- Added a finite-universe bridge for row-DAG accounting. At the raw layer,
  `raw_final_active_suffix_row_dag_universe_closed_subsetI` says that if a
  candidate universe covers final-active rows and is closed under `rsubterms`,
  then it contains every exact-DAG node of those rows. `FBound.thy` lifts this
  to `strong_deferred_final_active_suffix_row_dag_universe_closed_subsetI`.
- Added `strong_deferred_original_final_active_row_dag_finite_universe_contract`.
  This is the sharper handoff for the next proof stage: build a finite
  original-regex-owned universe `U`, prove final-active row coverage, prove
  `rsubterms` closure, and prove `card U <= K * rxsize r`. The memo-strong
  route then inherits exact POSIX reconstruction plus per-row exact-DAG bounds.
- Added raw closure facts for the row-DAG universe:
  `legacy_raw_final_active_suffix_row_dag_universe` and
  `row_group_deep_nf_raw_final_active_suffix_row_dag_universe`. Any node in
  the exact-DAG accounting universe remains inside the non-backref fragment
  and inherits the final strong tree's grouped normal form.
- Lifted those facts to `strong_deferred_final_active_suffix_row_dag_universe`.
  For nonempty inputs, the row-DAG universe can now be used in later
  normal-form/budget arguments without reopening the final tree.
- Added `strong_deferred_memo_tree_value_final_active_row_dag_interface` and
  `strong_deferred_original_final_active_row_dag_linear_contract`. The latter
  is the current proof handoff: prove
  `card (strong_deferred_final_active_suffix_row_dag_universe r s) <= K *
  rxsize r` plus the row-count bound, and the memo-strong route gives exact
  POSIX values and `card (rsubterms q) <= K * rxsize r` for every final-active
  row.
- Design consequence: the remaining cubic proof should focus on original-size
  control of row and row-DAG universes, not on raw emitted-tree simplification
  and not on raw row tree size.

## 2026-06-04: Isabelle row-DAG universe replaces raw member-size target

- Added `raw_final_active_suffix_row_dag_universe`: the union of exact
  `rsubterms` of all final-active rows. This is the proof-side analogue of the
  Scala `maxRowDag` metric.
- Checked that the raw row-DAG universe is a subset of the final raw tree's
  `rsubterms`, is finite, and has cardinality bounded by final raw `rsize`.
  For any final-active row `q`, `card (rsubterms q)` is bounded by this
  universe.
- Lifted the same interface to the memo-strong final state as
  `strong_deferred_final_active_suffix_row_dag_universe`. The important future
  target is now:
  `card (strong_deferred_final_active_suffix_row_dag_universe r s) <= K *
  rxsize r`.
- Design consequence: row-DAG cardinality is now an explicit Isabelle proof
  object. Future cubic work should prove an original-size bound for this
  object, then connect it to POSIX reconstruction. Do not try to prove a
  linear bound for raw `rsize q` of final-active rows.

## 2026-06-03: Final-active member DAG is now measured directly

- Added erased `Rexp` exact-DAG and shape-DAG size metrics to the Scala smoke
  harness, and threaded them through `ActiveSuffixStats`. The final-active
  row-member reports now show raw tree size, exact DAG size, and shape-DAG
  size side by side.
- Added optional budget gates for final-active member DAG and member shape-DAG.
  A seed-`20260602` scout with rows `1.0`, pair `1.0`, raw member disabled,
  and DAG/shape-DAG factors `2.0` found no CE in 5,000 random depth-6/input-8
  cases while preserving exact POSIX values.
- The same scout preserves the important separation: the raw tree CE at
  random case `4784` has `rsize=30` and raw row tree size `169`, but exact
  row DAG/shape-DAG size `38`. Chapter 7 k=`5`, n=`4,8,12` shows raw final
  row size `126` versus DAG/shape-DAG `31`.
- Design consequence: future Isabelle work should prove a finite
  hash-consed/indexed row-member universe and a reconstruction theorem over
  that universe. Do not interpret raw-tree row-member failures as failures of
  the memo-strong route; they are precisely the evidence for using DAG/indexed
  accounting.

## 2026-06-03: Raw row-member tree size is not the final metric

- Added checked subterm/size handles for final-active row payloads and suffix
  keys. At the raw layer, each `p \<in> set rows` and `k` from a final-active
  `RSEQ (RALTS rows) k` is now known to be a subterm of the final raw strong
  tree and size-bounded by that final tree. `FBound.thy` lifts the same facts
  to `strong_deferred_final_raw` and `asize (bders_simpStrong (intern r) s)`.
- The handles are useful fallback facts, but the Scala scout rejects the raw
  tree-size member metric as the main cubic proof target. Rows and pair-budget
  stay small, while final-active row-member tree size can exceed small linear
  constants: factor `1` fails on the known greedy-sequence CE (`15/10`),
  factor `2` fails on a nested-star random case (`59/26`), and factor `3`
  fails on another random case (`169/30`) whose strong DAG is only `42`.
- Design consequence: the next serious proof target is a hash-consed/member-DAG
  or indexed/quotiented final-active universe with POSIX reconstruction. Do not
  try to claim the cubic theorem by proving raw final-active member tree size
  linear in the original regex.

## 2026-06-03: Final-active row elements are proof-facing handles

- The final-active proof route now has direct inheritance lemmas for raw rows,
  suffix keys, and active buckets. If the final raw tree is legacy and
  `row_group_deep_nf`, then every active row/key/bucket member inherits the
  corresponding legacy/deep-normal property.
- The `FBound.thy` lift exposes the same facts for the memo-strong final tree.
  In particular, from
  `RSEQ (RALTS rows) k \<in> strong_deferred_final_active_suffix_rows r (c # s)`
  and `legacy_rexp r`, future proofs can immediately obtain
  `row_group_deep_nf p` for every `p \<in> set rows` and
  `row_group_deep_nf k`.
- This is the intended entry shape for the remaining row/member-size proof.
  Do not reason from cumulative active-prefix pools when the theorem is about
  final-active rows; and do not return to emitted-tree `bsimpCubic` unless a
  new candidate first beats the Chapter 7 smoke grid and preserves exact
  POSIX values.

## 2026-06-03: Final-active rows inherit strong normal form

- Confirmed the route switch: emitted-tree `bsimpCubic` is negative evidence
  after the graphs and should not receive proof effort. The live object is the
  memo strong tree: `bders_simpStrong` is a nullable recognition gate, and
  exact POSIX values are recovered from the original regex by the span/memo
  reconstruction theorem.
- Added `legacy_rrexp_rsubterms` and
  `row_group_deep_nf_legacy_rsubterms` in `GeneralRegexBound.thy`. These are
  intentionally legacy-restricted: backref constructors can contain arbitrary
  subterms while `row_group_deep_nf` treats them as opaque, so the unrestricted
  statement would be dishonest.
- Added FBound bridges showing that, for a legacy root and nonempty input,
  `strong_deferred_final_raw r (c # s)` is `row_group_deep_nf`, and each
  final-active shared-suffix row/key extracted from it is also
  `row_group_deep_nf`.
- This is the next proof handle for the memo-strong cubic route. Future row
  count/member-size work should reason from these final-active syntax facts,
  not from cumulative active-prefix pools and not from `bsimpCubic` emitted
  trees.
- Proof-performance lesson: a broad `by auto` over `rsubterms` and legacy/deep
  normal-form premises produced long-running proof lines. The checked proof
  uses explicit constructor cases and explicit contradictions for non-legacy
  backref constructors.

## 2026-06-03: Strong simplification enters `NTIMES` bodies

- Updated `bsimpStrong`, `rsimpStrong`, `rsimpStrong_raw`, and the Scala smoke
  model so strong simplification recurses into `ANTIMES`/`RNTIMES` bodies.
- The rule is intentionally weaker than `bsimpCubic`: it normalizes the body
  only. It does not collapse `n = 0`, zero bodies, or epsilon bodies to a
  value-carrying `ONE`, because the memo-strong route uses `bsimpStrong` as a
  recognition tree and keeps POSIX values reconstructed from the original
  regex.
- This closes the initial-normalization gap from the previous checkpoint:
  checked lemmas now show a legacy state becomes `row_group_deep_nf` after
  `bsimpStrong`, and the invariant holds for both `bsimpStrong (intern r)`
  starts and nonempty existing `bders_simpStrong (intern r) (c # s)` runs.
- Smoke consequence: exact `StrongDeferredMemo` POSIX reconstruction still
  passes deterministic random testing after the change. The Chapter 7 strong
  trace is unchanged on the default k=5 grid.

## 2026-06-03: Memo strong tree normal-form route

- The derivative-size graphs make `bsimpCubic` a negative result for the
  current proof effort. Do not try to rescue it as an emitted-tree theorem
  target unless a future candidate first beats the thesis Chapter 7 grid and
  preserves exact POSIX values.
- Added raw normal-form preservation for the actual erased form of
  `bsimpStrong`: annotated `bsimpStrong` erases to `rsimpStrong_raw`, so the
  proof route must preserve `row_group_deep_nf` through the raw shared-prune
  functions, not through a convenient non-raw wrapper.
- Checked lemmas now cover raw pair pruning, pruning against seen rows, row
  pruning, strong raw alternatives, full `rsimpStrong_raw`, and the annotated
  lift `row_group_deep_nf_rerase_bsimpStrong`.
- Design consequence: the next theorem should be a derivative-step invariant
  for `bsimpStrong (bder c r)` and then a final-active row/member-size bound
  for the memo strong tree. POSIX values remain delegated to the already
  checked span/memo reconstruction theorem.
- That derivative-step invariant is now checked for the legacy non-backref
  fragment:
  `row_group_deep_nf_rsimpStrong_raw_rder`,
  `row_group_deep_nf_rerase_bsimpStrong_bder`, and
  `row_group_deep_nf_rerase_bders_simpStrong`.
- Do not silently remove the starting-state precondition. `intern r` preserves
  legacy syntax for legacy `rexp`, but arbitrary source syntax is not yet
  proved to erase to `row_group_deep_nf`. The next bridge should either start
  from `bsimpStrong (intern r)` or prove a separate initial-normalization
  theorem before applying the loop invariant.

## 2026-06-03: Final-active member-size bound is parameterized

- Added `strong_deferred_original_final_active_budget_contract_with_member_bound`
  in `FBound.thy`; kept `strong_deferred_original_final_active_budget_contract`
  as the special case where `M = rxsize r`.
- Added `strong_deferred_original_final_active_linear_member_cubic_contract`.
  This is the proof-facing bridge from the current scout shape to a true cubic
  statement: prove rows `<= rxsize r`, pair-budget `<= rxsize r^2`, and
  member-size `<= K * rxsize r`, and the final-active closure is bounded by
  `rxsize r + K * rxsize r^3`.
- The theorem packages the current intended handoff: for a legacy root, once
  final-active rows and final-active pair-budget are bounded by the original
  `rxsize r`, and final-active row member size is bounded by an explicit `M`,
  the memo strong-tree route already gives exact POSIX correctness, `flat`
  correctness, a legacy final raw state, final-active closure size
  `<= rxsize r + rxsize r * rxsize r * M`, and the existing span/split memo
  budgets.
- Small constants are too strong: Scala smoke found `rsize=10`, final-active
  max row size `15` on the known full-cert greedy sequence CE; Chapter 7 gives
  stable `maxRowSize=126` for `k=5` (`126/46 ~= 2.74`) and `maxRowSize=297`
  for `k=8` (`297/91 ~= 3.26`) on lengths `4..32`; a deeper random run found
  `rsize=30`, final-active max row size `195` (`6.5x`). Keep the theorem
  parameterized by `K` until a larger scout stabilizes the working constant.
- This keeps the proof obligation aligned with the Scala scout instead of
  letting value reconstruction, memo accounting, and size accounting drift into
  separate ad hoc targets.

## 2026-06-03: Final-active scout added for memo strong tree

- Added a dedicated final-active budget gate to the Scala smoke harness. It
  checks exact POSIX values first, then optionally enforces
  `finalActiveRows <= rowsFactor * rsize(r)` and
  `finalActiveMaxRowSize <= memberFactor * rsize(r)` and
  `finalActivePairBudget <= pairFactor * rsize(r)^2`.
- Added `strong_memo_final_active_scout.ps1`, which runs the gate across
  deterministic seeds and writes logs under
  `agent_hunt_pipeline/reports/strong_memo_final_active_scout/`.
- A smoke run (`20260602,20260603`, `2000` random cases each, depth `6`, input
  length `8`, factors rows/member/pair `1.0/4.0/1.0`) found no final-active
  budget CE, but a larger `5000`-case run at seed `20260602` found a `4.0x`
  member-size CE. Treat `4.0x` as rejected evidence, not as a theorem target.
- Current larger scout (`20260602,20260603,20260604`, `5000` random cases
  each, depth `6`, input length `8`, factors rows/member/pair `1.0/8.0/1.0`)
  found no final-active budget CE. Worst ratios: rows `0.782609`, member
  `6.500000`, pair `0.040000`. This makes `8.0x` the current smoke-passing
  candidate constant, not a theorem.
- Added `strong_memo_final_active_factor_sweep.ps1` to sweep member factors
  reproducibly. The current sweep over `4,6,8` records `4` and `6` as failed
  by seed `20260602`, case `4784` (`finalActiveMaxRowSize=195`, `rsize=30`),
  and `8` as passed on the three-seed `5000`-case grid. The script keeps
  per-factor logs so future agents can extend the factor/depth grid without
  overwriting the main scout report.
- A deeper sweep over `8,10,12` with seeds
  `20260602,20260603,20260604,20260605,20260606`, `10000` cases per seed,
  depth `7`, input length `10`, also passes. Worst observed member ratio is
  `6.809524`. Keep `K=8` as a plausible candidate, not a checked constant.
- Added syntax-facing final-active lemmas:
  `raw_final_active_suffix_rows_iff`, `raw_final_active_suffix_keys_iff`,
  `raw_final_active_suffix_bucket_iff`, and their
  `strong_deferred_final_active_suffix_*` lifts. The proof route should use
  these to reason about concrete `RSEQ (RALTS rows) k` subterms instead of
  repeatedly unfolding image/filter definitions.
- Added key/bucket support for the final-active route: active keys and active
  buckets are now exposed as final-tree subterms, with card/member-size bounds
  by the final raw tree size. This deliberately does not claim the desired
  original-size cubic bound; it gives the next proof step syntax-level handles.
- Reduced the proof contract by discharging the pair-budget premise from the
  row-count premise: `strong_deferred_final_active_suffix_pair_budget_le_rxsize_square`
  shows that linear final-active rows imply quadratic final-active pair
  budget. The current handoff theorem can therefore be driven by two real
  original-size obligations: final-active rows and row member-size.
- The Chapter 7 trace now prints both cumulative active-prefix metrics and
  final-active metrics. For k=5 and lengths `4,8,12,16,20`, cumulative pairs
  grow from `82` to `1601`, while final-active rows/pairs stay `5/17`.
- Design consequence: `bsimpCubic` should remain retired as a proof target.
  The proof route should make memo strong tree work: preserve POSIX values by
  span/memo reconstruction, then prove a final-tree or final-active indexed
  universe bound.

## 2026-06-03: Direct strong-tree budget scout added

- Added `strong_memo_budget_scout.ps1`, a reproducible smoke harness for the
  direct memo strong-tree budget. It runs exact POSIX `strong-memo` smoke plus
  `-FindStrongCubicBudgetCE` across one or more deterministic seeds and writes
  a markdown report under `agent_hunt_pipeline/reports/strong_memo_budget_scout/`.
- Current smoke evidence is positive but still non-proof: seeds `20260602` and
  `20260603`, `2000` random cases each at depth `6`, input length `8`, find no
  witness above `1.0 * rsize(r)^3`. A larger one-off seed `20260602` run with
  `10000` random cases also found no witness; its worst random ratio was
  `0.143519`.
- Design consequence: the direct `bders_simpStrong` final tree remains the
  route to explain. Do not interpret the scout as a payout artifact; use it as
  a guard before attempting a concrete indexed/quotiented universe theorem.

## 2026-06-03: Memo strong tree, not rowRoot, is the proof target

- Added a dedicated Scala shrinker for row-list/factoring bridge failures:
  `-FindStrongRowsBridgeCE`. This should be used before any new attempt to make
  a row-list bridge theorem candidate.
- The shrinker gives a compact counterexample even after local branch
  factoring, bounded local sequence/ALT expansion, and an 8-round factoring
  closure:
  `SEQ(SEQ(STAR(SEQ(STAR(ALT(SEQ(CH(a),CH(b)),CH(a))),CH(a))),CH(a)),CH(b))`
  on input `a`.
- The natural reconstruction root
  `bsimpStrong (AALTs [] (bpdersStrong1Rows (intern r) s))` is not structurally
  the Brzozowski strong derivative on that case (`rowRootEq1 = false`) and its
  subterms still do not cover the missing final-active row (`rowRootHit =
  false`). Treat this as negative evidence against making the row list the
  executable long-tail object.
- The checked POSIX-value story is already the direct memo strong tree:
  `strong_deferred_memo_tree_POSIX_correctness` plus
  `strong_deferred_span_value` reconstruction. Future proof work should target
  a size bound or finite indexed/quotiented representation for that final
  strong recognition tree. Do not revive emitted-tree `bsimpCubic`, and do not
  spend theorem effort on rowRoot unless smoke first removes the CE above.

## 2026-06-03: Row-gated memo is checked; row-list bridge remains smoke-only

- Added a Scala mirror of `bpders_strong1_rows` plus
  `-CheckStrongRowsBridge` / `-RequireStrongRowsBridgeCoverage` smoke flags.
  The executable check now verifies that the nullable row gate agrees with the
  final `bdersStrong` gate and that row-gated memo reconstruction returns the
  same POSIX value as the baseline memo.
- Added a candidate final-active coverage diagnostic: row-list subterms,
  common-suffix factoring, small iterative factoring closure, local
  `bsimpStrong` normalization, and bounded local sequence/alt expansion.
  This passes exhaustive depth `2`, input length `3` (`84,300` pairs) and
  deterministic random depth `5`, input length `6`, `2,000` cases at seed
  `20260602`.
- The stronger random guard is not yet green: depth `6`, input length `8`,
  `10,000` cases at the same seed still produces a final-active coverage
  counterexample. Therefore this bridge is not a theorem candidate yet; keep it
  CE-driven until it survives stronger smoke.
- Important operational lesson: running the row-list bridge on the Chapter 7
  long tail can exhaust the Scala heap even while `strongMemoTree` remains
  small. Do not use `bpdersStrong1Rows` as the long-tail executable object.
  The proof route should keep the memo strong tree as the recognition object
  and use row/factoring universes only as bounded proof abstractions.

## 2026-06-03: Final active pair-budget has a square fallback

- Added a checked equality between active suffix pair-budget and the cardinality
  of the active pair relation. The reason is structural: active buckets are
  disjoint by suffix key.
- Since active pairs are a subset of `U x U`, every finite active universe now
  gets `raw_shared_prune_active_suffix_pair_budget U <= card U * card U`.
- Lifted this to the final strong derivative tree, giving
  `strong_deferred_final_active_suffix_pair_budget r s <=
   asize (bders_simpStrong (intern r) s)^2`.
- Design consequence: if future work proves the final strong tree is cubic in
  the original regex size, the final active pair-budget is at worst quadratic
  in that final tree size. This is a fallback interface; the sharper route is
  still to prove the tiny final-active row/bucket behavior directly.

## 2026-06-03: Strong memo tree is now the active proof route

- The derivative-size graphs make the emitted-tree `bsimpCubic` route
  unattractive: it does not reproduce the thesis Chapter 7 tree plateau, so do
  not spend proof effort optimizing it unless a new smoke-tested design
  replaces it.
- The active route is `StrongDeferredMemo`: run the thesis-strength
  `bders_simpStrong` tree as a nullable/recognition gate, then reconstruct the
  exact POSIX value from the original regex and input span relation.
- Added checked final-active bridge definitions and lemmas:
  `raw_final_active_suffix_rows`,
  `raw_final_active_suffix_pair_budget`,
  `strong_deferred_final_active_suffix_rows`, and
  `strong_deferred_memo_tree_value_final_active_interface`.
- Design consequence: future cubic work should prove a small final-active
  row/pair-budget invariant for the final strong tree, or a quotient for the
  prefix pool. It must not count the unquotiented cumulative prefix pool as the
  final cubic proof object.

## 2026-06-03: Active closure is monotone

- Added monotonicity lemmas for active suffix keys, buckets, pairs, closure,
  and pair-budget.
- Design consequence: the concrete root-owned active universe can now be built
  by closure iteration or by embedding a smaller candidate in a larger
  candidate without re-proving the active accounting from scratch.
- The pair-budget monotonicity theorem is intentionally finite-on-the-target:
  `U <= V` and `finite V` imply
  `raw_shared_prune_active_suffix_pair_budget U <=
   raw_shared_prune_active_suffix_pair_budget V`. This is the shape needed by
  future finite universe proofs.

## 2026-06-03: Long-tail deferred-memo grid separates tree from prefix pool

- Regenerated the deferred-memo Chapter 7 grid to `n=200` for
  `k=5,8,10,12`.
- The recognition tree remains promising: `strongMemoTree` peaks at `959` for
  `k=5`, `3425` for `k=8`, `5940` for `k=10`, and `9686` for `k=12` on this
  grid.
- The cumulative active prefix pool is not a final proof universe by itself:
  for `k=8`, active rows/max bucket/pair-budget still grow through `n=200`.
- Design consequence: do not try to prove the final regex-size theorem by
  bounding the unquotiented prefix active pool. Use it as diagnostics only.
  The proof object probably needs a periodic/indexed/quotiented row universe,
  or a final-state invariant closer to the bounded `strongMemoTree` itself.

## 2026-06-03: Final active rows look bounded on the thesis grid

- Added final-state active metrics to the Scala smoke model:
  `strongMemoFinalActiveRows`, `strongMemoFinalActiveKeys`,
  `strongMemoFinalActiveMaxBucket`, and
  `strongMemoFinalActivePairBudget`.
- On the same `k=5,8,10,12,n<=200` grid, final active rows stay tiny:
  max `5`, `9`, `11`, and `13`; final active pair-budget maxes at `17`, `65`,
  `101`, and `145`, respectively.
- Design consequence: separate the final derivative state from the cumulative
  prefix/memo pool. The proof route should prefer a final-state active-row
  invariant for regex-size derivative bounds, while the span/value memo table
  may keep its input-length-dependent budget for POSIX reconstruction.

## 2026-06-03: Active pair-budget is a proof-facing quantity

- Added `raw_shared_prune_active_suffix_pair_budget`, the exact sum of
  squared active bucket sizes over active suffix keys.
- Added checked bounds:
  `card_raw_shared_prune_active_suffix_pairs_le_pair_budget`,
  `card_raw_shared_prune_active_suffix_closure_pair_budget_bound`, and
  `card_raw_shared_prune_active_suffix_closure_member_pair_budget_bound`.
- Follow-up bounds keep both entry points available:
  `raw_shared_prune_active_suffix_pair_budget_bucket_bound` recovers the old
  `S * K * K` estimate, while
  `card_raw_shared_prune_active_suffix_closure_member_pair_budget_card_bound`
  packages the direct `C + P * M` closure-cardinality shape.
- This matches the Scala `strongMemoActivePairBudget` metric and gives a
  sharper contract than the older `S * K * K` max-bucket accounting.
- Design consequence: the next concrete universe proof may prove one aggregate
  pair-budget bound for root-owned active suffix rows, then combine it with
  member-size to instantiate active closure. This is closer to the actual
  Chapter 7 behavior, where key count is tiny and one large bucket dominates.

## 2026-06-03: Active-suffix metrics are now plotted

- Added `ActiveSuffixStats` to the Scala smoke model and wired it into
  `StrongDeferredMemoResult`.
- New Chapter 7 metrics:
  `strongMemoActiveRows`, `strongMemoActiveKeys`,
  `strongMemoActiveMaxBucket`, and `strongMemoActivePairBudget`.
- Added `agent_hunt_pipeline/scripts/ch7_deferred_memo_grid.ps1` as the
  preferred reproducibility command for deferred-memo plots.
- Current `k=5,8,n<=80` evidence:
  active suffix keys stay at `2`; `k=5` active max bucket plateaus around
  `84`; `k=8` reaches `176` at `n=80`; pair budget follows the expected
  square-of-bucket accounting.
- Design consequence: proving the active-suffix memo contract should now be
  attacked by bounding suffix-key count and per-key bucket size directly,
  rather than inventing another emitted-tree simplifier.

## 2026-06-03: Active-suffix closure replaces broad same-suffix buckets

- The emitted-tree `bsimpCubic` route remains retired. The current proof target
  is memo strong tree: `bsimpStrong` is a recognition tree, while POSIX values
  come from original-regex span/memo reconstruction.
- Added `raw_shared_prune_active_suffix_keys`,
  `raw_shared_prune_active_suffix_bucket`,
  `raw_shared_prune_active_suffix_pairs`, and
  `raw_shared_prune_active_suffix_closure`.
- This active closure only counts pairs that can actually trigger raw
  shared-suffix pruning: both sides must be `RSEQ (RALTS rows) k` for the same
  concrete suffix `k`. Non-row `None` key pairs are not part of the preferred
  accounting contract.
- Checked bridge:
  `raw_shared_prune_closedI_active_suffix_closure_subset`.
- Checked accounting:
  `card_raw_shared_prune_active_suffix_closure_member_bucket_bound`. The next
  concrete universe proof should bound active suffix-key count, max active
  bucket size, and ordinary member size.
- Added the proof-facing memo interface
  `FBound.thy:strong_deferred_original_raw_row_norm_active_suffix_memo_cubic_interface`.
- Regenerated deferred-memo Chapter 7 plots to `n=80` for `k=5,8`. The `k=5`
  strong tree plateaus around the thesis-strength few-hundred/near-thousand
  range; `k=8` still rises slowly but is far below the old emitted-tree blowup.

## 2026-06-03: Same-suffix pair output is member-size bounded

- Added `rsize_rsimpStrong_prune_pair_raw_le` and
  `card_raw_shared_prune_pair_outputs_le_later_size`.
- Consequence: in same-suffix closure accounting, the output of one raw prune
  pair is bounded by the size of the later row. If the universe has a member
  size bound `M`, then the one-pair output bound is automatically `M`.
- Added
  `card_raw_shared_prune_same_suffix_closure_member_bucket_bound`, reducing the
  closure cardinality task to suffix-key count, per-key bucket size, and the
  existing member-size bound.
- Design consequence: the next concrete universe proof only needs to explain
  how many continuation buckets there are and how large each bucket can get.
  Pair-output size is no longer a separate source of growth.

## 2026-06-03: Same-suffix accounting is bucketized

- Added `raw_shared_prune_same_suffix_pairs` and
  `raw_shared_prune_suffix_bucket`.
- The same-suffix pair domain is now proved equal to a union of
  `bucket(k) \<times> bucket(k)` over suffix keys. This records the intended
  accounting model: do not count arbitrary global pairs; count pairs inside
  continuation buckets.
- Added cardinality bounds that reduce closure size to:
  number of suffix keys, maximum bucket size, and maximum one-pair output
  size.
- Design consequence: the next concrete universe attempt should prove those
  three quantities for root-owned strong rows. If the bucket size is the
  hidden exponential part, that is the exact place to refine the universe or
  add a memo/indexed representation.

## 2026-06-03: Same-suffix closure is the active proof contract

- Added `raw_shared_prune_same_suffix_closure_subsetI` and
  `raw_shared_prune_closed_iff_same_suffix_closure_subset`.
- Under the existing `flat_closed` premise, the old abstract
  `raw_shared_prune_closed U` proof obligation is equivalent to the concrete
  same-suffix closure obligation
  `raw_shared_prune_same_suffix_closure U \<subseteq> U`.
- Added same-suffix variants of the raw row-size and memo cubic interfaces,
  ending in
  `FBound.thy:strong_deferred_original_raw_row_norm_same_suffix_memo_cubic_interface`.
- Design consequence: future universe work should not prove an undirected
  global pair-closure property first. It should organize the universe by
  continuation/suffix bucket, prove same-suffix row-difference closure in each
  bucket, and then instantiate this interface.

## 2026-06-03: Memo strong tree is the proof target

- Decision: stop treating emitted-tree `bsimpCubic` as the main cubic-bound
  candidate. The comparison graphs show it is not as good as the thesis
  Chapter 7 `bsimpStrong` tree on the evil family, so proving it would prove
  the wrong object.
- The main target is now the memo strong tree architecture:
  `bsimpStrong` remains the small nullable-recognition tree, while exact POSIX
  values are reconstructed from the original regex by a span/memo table.
- This avoids the central conflict that broke `bsimpCubic`: destructive
  reassociation/pruning can make trees small, but it changes POSIX values.
  The memo route keeps the value-producing structure in the reconstruction
  theorem instead of demanding that the simplified emitted tree itself carry
  the original POSIX value shape.
- Added `GeneralRegexBound.thy:raw_shared_prune_suffix_key` and
  `GeneralRegexBound.thy:raw_shared_prune_same_suffix_closure`. This is a
  narrower proof-facing closure than arbitrary pair closure: row-difference
  pruning is only required inside same-continuation buckets.
- Checked consequence: same-suffix closure is sufficient for
  `raw_shared_prune_closed`, and it includes the known path9/carry9 missing
  row-difference witness. The final cubic proof should instantiate this idea
  with a root-owned memo/frontier universe and prove cubic cardinality/member
  size bounds.

## 2026-06-03: Row-difference closure is now explicit

- Added `GeneralRegexBound.thy:raw_shared_prune_pair_outputs` and
  `GeneralRegexBound.thy:raw_shared_prune_pair_closure`.
- The operator takes a universe `U` and adds every output of one raw
  `rsimpStrong_prune_pair_raw` comparison between two members of `U`. It is
  finite when `U` is finite, includes `U`, and gives a clean proof interface:
  if `raw_shared_prune_pair_closure U \<subseteq> U`, then `U` satisfies
  `raw_shared_prune_closed`; conversely, `raw_shared_prune_closed` plus
  singleton-flattening closure implies the pair closure stays inside `U`.
- Added checked witnesses showing that the path9/carry9 atom-frontier
  counterexample result is included after one pair-closure step.
- Design consequence: a final cubic proof should not saturate arbitrary tree
  subsets blindly. It needs a compact row-difference representation with the
  same behavior as this pair-closure operator on actual strong-prune pairs,
  plus a polynomial cardinality/member-size argument.

## 2026-06-03: Strong memo POSIX value is a theorem, not a wrapper

- Added `FBound.thy:strong_deferred_span_value_THE_lexer` and
  `FBound.thy:strong_deferred_memo_exact_value_budget`.
- The theorem states the intended architecture directly: the strong derivative
  tree is the nullable gate, and the original-regex span/memo table supplies
  the unique POSIX value. The resulting option value is exactly `lexer r s`.
- Added `GeneralRegexBound.thy:path9_atom_frontier_not_raw_shared_prune_closed`
  and `GeneralRegexBound.thy:carry9_atom_frontier_not_raw_shared_prune_closed`.
  These are small checked counterexamples showing that current path9/carry9
  atom-frontier universes do not survive raw strong shared-prune.
- Design consequence: the next successful cubic universe must include a
  principled representation of same-suffix ALT row differences, or prove an
  equivalent memo/shared representation that avoids emitting those difference
  rows as ordinary frontier members. Reusing the old frontier universe directly
  is now checked-false.

## 2026-06-03: StrongDeferredMemo replaces bsimpCubic as the main route

- The Chapter 7 comparison plots made the call: current emitted-tree
  `bsimpCubic` is not competitive with the thesis `bsimpStrong` baseline.
- Updated `scala_cubic_smoke.ps1` and `isabelle_ci.ps1` so the default route is
  now `strong-memo`: `bsimpStrong` supplies the small recognition tree and the
  original regex supplies POSIX values through span/memo reconstruction.
- The legacy `bsimpCubic` checks remain runnable via `-Route legacy-cubic` or
  `-ScalaSmokeRoute legacy-cubic`; they are no longer the route that future
  proof work should optimize.
- Design consequence: future proof work should not try to rescue
  `bsimpCubic` ordinary tree size. It should make the `StrongDeferredMemo`
  reconstruction theorem stronger and instantiate the concrete raw/shared
  universe required by
  `strong_deferred_original_raw_row_norm_closed_memo_cubic_interface`.

## 2026-06-03: sizeNregex specialization is a fallback, not the target

- Added `GeneralRegexBound.thy:rflts_sizeNregex_closed` and
  `FBound.thy:strong_deferred_original_sizeNregex_memo_cubic_interface`.
- The new theorem specializes the strong deferred memo interface to
  `sizeNregex N`. This is useful because it removes the purely mechanical
  universe obligations: finiteness, singleton-flattening closure,
  raw shared-prune closure, and member-size projection.
- Design consequence: this theorem is a scaffold only. It deliberately keeps
  the norm-closure and `card(sizeNregex N) * N` obligations visible, so it
  cannot be mistaken for the final cubic result. The real route still needs a
  smaller Antimirov/frontier universe that is closed under the strong-row step
  while preserving the deferred POSIX value story.

## 2026-06-03: Row-universe and memo accounting now share one interface

- Added
  `FBound.thy:strong_deferred_original_raw_row_norm_closed_memo_cubic_interface`.
- The theorem intentionally does not invent a new simplifier. It packages the
  current leading route: thesis-strength `bsimpStrong` recognition, raw
  strong-row cubic-universe premises, and original-regex span/memo POSIX
  reconstruction.
- The interface now exposes all of the facts a later final theorem will need:
  row-size bounds, raw/annotated erasure alignment, row nullable gate,
  deferred POSIX gate, recognition-state legacy closure, quadratic memo-state
  budget, cubic split-probe budget, and legacy-subterm closure for the memo
  tables.
- Design consequence: the next real research problem is narrower and sharper:
  instantiate the raw/shared universe `U` with a POSIX-safe quotient strong
  enough for the Chapter 7 family, then discharge this interface's closure and
  cardinality/member-size premises.

## 2026-06-03: Deferred memo budget has a checked theorem

- Added `FBound.thy:strong_deferred_memo_budget` and
  `FBound.thy:strong_deferred_original_memo_budget`.
- The theorem mirrors the Scala `StrongDeferredMemo` accounting at proof
  level: acceptance span states plus POSIX value span states are bounded by a
  quadratic span table over original subterms, while split probes are bounded
  by a cubic table.
- It also keeps the crucial semantic gate: there is a unique deferred POSIX
  value exactly when the final `bders_simpStrong (intern r) s` state is
  nullable.
- The original/legacy variant additionally records that the accept/value span
  states and split probes are still over legacy subterms when the input regex
  is in the non-backref fragment.
- Design consequence: future cubic-bound statements should cite this theorem
  for memo reconstruction accounting instead of restating ad hoc bounds. The
  remaining proof problem is not the span/memo table size; it is the bridge
  from thesis-strength recognition/share representation to this bounded
  reconstruction table.

## 2026-06-03: Direct derivative-size compare plots for Chapter 7

- Added a side-task report:
  `agent_hunt_pipeline/reports/ch7_derivative_size_compare/index.html`.
- The new entry script is
  `agent_hunt_pipeline/scripts/ch7_derivative_size_compare.ps1`; it uses the
  same Scala CSV emitter as the smoke suite and then overlays multiple metrics
  on one graph per Chapter 7 parameter `k`.
- Default comparison is `strongTree` versus `strongMemoTree` versus
  `cubicTree`, over `k=1..8,n=0..30`. This makes the thesis baseline visually
  immediate instead of requiring the reader to compare separate per-metric
  charts.
- Current conclusion is unchanged but easier to see: `strongMemoTree` follows
  thesis `bsimpStrong`, while current emitted `cubicTree` is still larger
  (`3.387x` at k=5,n=30 and `2.762x` at k=8,n=30).
- Design consequence: before promoting any new cubic simplifier candidate to
  proof work, refresh this compare report. A candidate that cannot beat or
  match the thesis baseline on this grid should remain a diagnostic tool.

## 2026-06-03: Deferred POSIX memo keeps the thesis-strength tree line

- Extended the Chapter 7 plot pipeline with metrics for the existing
  `StrongDeferredMemo` route: strong tree/DAG/shape plus POSIX memo states,
  split probes, and their coarse span/split bounds.
- New report:
  `agent_hunt_pipeline/reports/ch7_deferred_memo_grid/index.html`.
- Evidence on `k=1..8,n=0..30`: `strongMemoTree` matches the thesis-style
  `bsimpStrong` tree line. At `k=5,n=30`, `strongMemoTree=958`; at
  `k=8,n=30`, `strongMemoTree=2747`.
- The value-reconstruction memo is small on the same family: at `n=30`,
  k=5 and k=8 both have `strongMemoStates=1703` and
  `strongMemoSplitProbes=6011`, far below the coarse bounds.
- Smoke evidence: `-CheckStrongDeferredMemo` passes exact POSIX value
  comparison on the exhaustive depth `2` / input `3` grid, the known CE grid,
  and 500 deterministic random cases.
- Design consequence: the best current tree-level route is not current
  `cubicTree`. It is thesis-strength `bsimpStrong` as the nullable/size gate,
  plus original-regex span/memo reconstruction for POSIX values. The next
  proof work should package this route rather than trying to make the weaker
  emitted `cubicTree` look thesis-good.

## 2026-06-03: Chapter 7 size-grid plots are now a required intuition check

- Added `agent_hunt_pipeline/scripts/ch7_size_grid.ps1` and
  `plot_ch7_size_grid.py`. The script asks the Scala smoke model to emit a
  CSV and then renders dependency-free SVG plots over Chapter 7 parameters
  `k` and input length `n`.
- Default report:
  `agent_hunt_pipeline/reports/ch7_size_grid/index.html`.
- Current default grid is `k=1..8`, `n=0..30`, with metrics
  `strongTree`, `cubicTree`, `sharedShapeStatePool`, and
  `langContPruneShapeStatePool`.
- The result is sobering and useful: the thesis-style `bsimpStrong` baseline
  is still better by ordinary tree size. At `k=5,n=30`,
  `strongTree=958` while current `cubicTree=3245`; at `k=8,n=30`,
  `strongTree=2747` while current `cubicTree=7587`.
- Design consequence: shared diagnostics may be promising, but the current
  emitted tree simplifier is not yet Chapter-7-good. Any future candidate
  should regenerate the plot before theorem work, and must distinguish ordinary
  tree-size claims from shared-representation claims.

## 2026-06-03: Metric-only long-tail tests expose a stronger but still incomplete quotient

- Added `-SharedPlateauMetricOnly` and the matching CI flag
  `-ScalaSmokeSharedPlateauMetricOnly`. This mode is only for long-tail
  diagnostics: it skips full `arexp` reconstruction and uses a bit-erased
  diagnostic `DagStore`, while ordinary value smoke remains bit-preserving.
- Added `langContPruneShapeStatePool`, which keys row-continuation coverage by
  approximate unary language patterns instead of raw continuation syntax.
- This metric finally gives a checked non-increase for the larger Chapter 7
  `k=8` root: sampled every 64 characters, it reaches
  `... 878,885,885`, first non-increase at `n=960`.
- The result is not general enough. A harder `k=10` run, sampled every 128
  characters, timed out after reaching `n=1664` with the metric still strictly
  increasing (`1731`). This is negative evidence against claiming a constant
  universe from the current quotient.
- Design consequence: the current proof side is not about a final
  `bsimpCubic` tree simplifier. It is about whether an erased/shared
  row-family representation for value-safe `unary-cover-no-reassoc` can be
  bounded. The only metric currently giving `k=8` plateau evidence is
  `langContPruneShapeStatePool` under metric-only bit erasure; any theorem
  candidate must replace this diagnostic with a real indexed/periodic row
  universe plus reconstruction/value theorem.

## 2026-06-03: Long-tail smoke must reach plateau or report failure

- Strengthened the Scala smoke harness for long-tail plateau work. The
  proof-facing `shapeStatePool` and `shapeDag` metrics now use hash-consed
  structural shape IDs instead of huge recursive string keys; compact strings
  remain only for small witness examples. This separates true algorithmic
  blow-up from diagnostic-format blow-up.
- Added progress sampling (`-SharedPlateauProgress` and
  `-ScalaSmokeSharedPlateauProgress`). A long-tail run now prints sampled
  points as it goes, so timeout/OOM runs still leave a checked high-water
  boundary.
- Tested `unary-cover-no-reassoc`, a Scala-only diagnostic mode that keeps
  no-reassociation output syntax while pruning later all-`a` rows when an
  earlier same-continuation row contains `a*`.
  It preserves exact POSIX values on the current exhaustive depth `2`/input
  `3` grid and deterministic random `1,000` cases at depth `5`/input `6`.
- The mode reproduces a thesis-like positive on Chapter 7 `k=5`:
  `shapeStatePool` first stops increasing at `n=124` (`337 -> 337`) with
  `-SharedPlateauRequire`.
- The same mode fails as a general constant-universe candidate on Chapter 7
  `k=8`: it stays strictly increasing through `n=500`
  (`shapeStatePool=2072`), and a progress run is still strictly increasing at
  `n=624` (`shapeStatePool=2568`, `statePool=201915`, `pool=795128`) before
  the current direct-DAG simplifier runs out of heap inside
  `eq1Id/distinctWithIds`.
- Design consequence: small evil-family plots are not enough. Any future
  constant/plateau claim must either run until the chosen metric first stops
  strictly increasing, or report the exact high-water boundary and failure
  mode. `unary-cover-no-reassoc` is useful negative/diagnostic evidence, not a
  BR-039/BR-040 simplifier.

## 2026-06-03: Unary modulo is not enough for k=8

- Added diagnostic plateau metrics `unaryModShapeStatePool` and
  `unaryPruneShapeStatePool`.
- `unaryModShapeStatePool` tests whether the `k=8` tail is mostly caused by
  repeated `a^m . (a^p)*` rows that differ only by a period. It is not:
  at Chapter 7 `k=8,n=624`, ordinary `shapeStatePool` is `2568`, while
  `unaryModShapeStatePool` is still `2552` and strictly increasing.
- The first pruning traversal, `unaryPruneShapeStatePool`, skips simple later
  unary ALT children when an earlier unary child covers them. It also does not
  move the `k=8` needle; through `n=160` it matches the modulo metric exactly
  and remains strictly increasing.
- Design consequence: the remaining growth is not a shallow unary-period
  normalization bug. The next candidate needs continuation-aware row-set
  coverage: treat a prior row block with continuation `c` as covering a later
  row block with the same continuation when every later row language is already
  included in the earlier POSIX-prior row set. This is much closer to the
  Antimirov linear-form/pruning idea than a local rewrite of individual
  `a^m . (a^p)*` children.

## 2026-06-03: First continuation-aware row-set coverage is still too shallow

- Added `contPruneShapeStatePool`, a diagnostic metric that decomposes
  left-associated sequence branches into `(row-set, continuation)` pairs and
  skips later branches when an earlier same-continuation row-set covers them.
- This is the first diagnostic that actually improves the smaller evil roots:
  Chapter 7 `k=3` stops at `n=12` with value `36`, and `k=5` stops at `n=68`
  with value `269`.
- It still fails the larger root: Chapter 7 `k=8` remains strictly increasing
  through `n=624`, ending at `2552`, matching the unary-modulo metric. The
  direct-DAG simplifier then runs out of heap in the existing pruning path.
- Design consequence: the right idea is not local unary child pruning, but the
  current syntactic continuation key is still too fine or too shallow for
  `k=8`. The next attempt should identify the repeated Chapter 7 base
  continuation as an indexed family/linear form, or otherwise quotient
  continuations before testing row-set inclusion.

## 2026-06-03: Direct-DAG smoke separates state pool from temporary pool

- Added an optional `SharedDirectDag` smoke route. It runs derivative and
  simplification directly on hash-consed node IDs instead of expanding the
  current DAG root into an ordinary tree at each derivative step.
- Added `statePool` to shared traces: the union of nodes reachable from every
  prefix derivative root. This is the proof-relevant shared-state measure,
  while the raw `pool` additionally counts dead temporary nodes allocated
  during derivative/simplification construction.
- Current evidence: direct `expanded-keyed-no-reassoc` preserves exact POSIX
  values on exhaustive depth `2`/input `3` and random `1,000` cases at
  depth `5`/input `6`. On Chapter 7, `k=5,n=30` gives final DAG `276`,
  shape DAG `132`, `statePool` `1042`, and total temporary pool `4005`;
  `k=8,n=32` gives final DAG `408`, shape DAG `173`, `statePool` `1400`,
  and total temporary pool `5292`.
- Added `SharedDirectCompareTree`: when enabled, the direct-DAG path compares
  every prefix derivative root against the old tree-step reference algorithm
  for exact `arexp` syntax. The current direct `no-reassoc` and
  `expanded-keyed-no-reassoc` modes pass exhaustive depth `2`/input `3` plus
  random `1,000` cases at depth `5`/input `6` under this stricter check.
- Added an optional shared `statePool` cubic budget/frontier gate. Use
  `-SharedStatePoolCubicFactor` or
  `-ScalaSmokeSharedStatePoolCubicFactor` to make the smoke fail when
  `statePool > factor * rsize(r)^3` for regexes above the configured size
  floor; use the matching `Top` option to report the highest-ratio witnesses.
  With direct `expanded-keyed-no-reassoc`, factor `1.0` passes the current
  exhaustive/random smoke and the Chapter 7 `k=5` grid, whose worst logged
  trace point is `statePool=1042`, `rsize=46`, ratio `0.010705`.
- Added a long-tail plateau check with selectable metric. The most relevant
  metric for the current Isabelle proof side is `shapeStatePool`, because
  `rsimpStrong_raw` and `rpder_strong_rows_raw` operate on erased `rrexp`
  terms rather than exact annotated nodes. Results are mixed and important:
  Chapter 7 `k=5` first stops strictly increasing at `n=124`
  (`shapeStatePool 523 -> 523`), while Chapter 7 `k=8` remains strictly
  increasing through `n=500` (`shapeStatePool=3257`, exact
  `statePool=139153`). This is negative evidence for any claim that the
  current direct-DAG/reference simplifier already provides a constant
  root-owned proof universe.
- Design consequence: the next proof-facing universe should bound prefix
  reachable rows/nodes, not the whole allocation pool. If an eventual
  executable algorithm exposes the raw pool, it will need garbage-free
  construction, garbage collection, or a separate dead-temporary accounting
  argument. Because `k=8` still grows in the erased/shape prefix pool, future
  work must add a stronger quotient/pruning/indexed-row universe rather than
  merely hash-consing the current syntax.

## 2026-06-03: sizeNregex closes raw shared pruning

- Added `raw_shared_prune_closed_sizeNregex`, plus small size and legacy
  helper lemmas for the raw delayed shared-prune result.
- Design consequence: raw shared pruning itself is no longer a mystery
  closure obligation. Any coarse legacy size-bounded universe `sizeNregex N`
  is closed under the raw shared-prune result, because the result is legacy and
  no larger than the later row already in the universe.
- This is deliberately not the final cubic universe. `sizeNregex N` is too
  large for the desired cardinality statement. The remaining hard target is to
  replace it with a root-owned shared-row/linear-form universe that has cubic
  card/member bounds while reusing the same local closure shape.

## 2026-06-03: Shared-prune closure now uses both earlier and later rows

- Added `raw_shared_prune_closed`, a predicate saying that raw shared pruning
  is closed when both row shapes `RSEQ (RALTS lrs) k` and
  `RSEQ (RALTS rrs) k` are already in the universe.
- Added checked derivations from this predicate to raw row closure and to the
  original-entry annotated size/value interface.
- Design consequence: the next candidate universe does not need to be closed
  for arbitrary left-row lists. It only needs pairwise shared-prune closure for
  rows it already contains, which is the operational invariant maintained by
  the pruning accumulator.

## 2026-06-03: Raw one-step closure is split into local obligations

- Added raw subset decomposition lemmas for pruning and derivative rows:
  `rsimpStrong_prune_rows_raw_later_shared_subsetI`,
  `rflts_rpder_strong_list_raw_subsetI`,
  `rpder_strong_rows_raw_norm_later_shared_subsetI`, and the iterated row
  interface.
- Added
  `strong_deferred_original_raw_row_norm_later_shared_cubic_universe_interface`
  in `FBound.thy`.
- Design consequence: the next finite-universe proof should not unfold
  `rpder_strong_rows_raw` all at once. Prove `flat_closed`, `norm`, and
  `shared` closure lemmas for the proposed universe, then use the checked
  interface to obtain the annotated size bound and deferred-value gate.

## 2026-06-03: Raw-row closure is now the preferred cubic obligation

- Added raw-row finite-universe bookkeeping for `rpders_strong_rows_raw`:
  subset induction, distinct preservation, length bounds, and `rsizes` bounds.
- Added `strong_deferred_original_raw_row_cubic_universe_interface`. It says
  that a finite universe closed under raw one-step rows
  `rpder_strong_rows_raw` yields the annotated
  `bpders_strong1_rows (intern r) s` size bound and keeps the exact
  `map rerase` bridge plus deferred POSIX value gate.
- Design consequence: when proving the next cubic closure theorem, do not
  phrase the primary step premise over annotated witnesses unless necessary.
  Prove closure for raw erased rows first; annotated bounds now follow from
  the checked erasure bridge.

## 2026-06-03: Raw strong skeleton restores exact erasure

- Added a raw skeleton mirror of the annotated strong simplifier:
  `rsimpStrong_prune_pair_raw`, `rsimpStrong_prune_rows_raw`,
  `rsimpStrong_ALTs_raw`, `rsimpStrong_raw`, and raw strong row derivative
  entry points.
- This is intentionally not the earlier normalized skeleton. The raw version
  preserves the same delayed row-normalization shape as annotated
  `bsimpStrong`, which makes exact erasure bridges true again:
  `rerase_bsimpStrong_raw`, `map_rerase_bpder_strong_rows_raw`, and the
  iterated row bridge.
- Design consequence: after the exact-erasure counterexample, the proof route
  should use this raw skeleton as the erased carrier for shared-row or
  reconstruction universes. Normalize/share only at a layer that has an
  explicit reconstruction theorem; do not silently replace the raw carrier by
  normalized syntax.

## 2026-06-03: Strong prune is not exact under erasure

- Added checked counterexample
  `rerase_bsimpStrong_prune_pair_not_exact`.
- This refutes a tempting shortcut: annotated `bsimpStrong_prune_pair` does
  not erase syntactically to `rsimpStrong_prune_pair`. The annotated version
  keeps bit/value-carrying alternative syntax and relies on an outer
  `distinctWith/flts` cleanup, while the skeleton version normalizes the
  pruned row internally with `rdistinct/rflts`.
- Design consequence: do not base the cubic route on a naive exact
  `map rerase` commutation theorem for strong pruning. The viable proof shape
  is either a language/coverage-row universe bound, or an explicit
  normalized/shared-row representation with a checked reconstruction theorem.

## 2026-06-03: Original-entry cubic row interface

- Added `strong_deferred_original_row_cubic_universe_interface`.
- This is the current theorem-shaped contract for the strong-row route from
  the original `rexp`: assume `legacy_rexp r`, a finite erased row universe
  containing `rerase (intern r)`, one-step closure under
  `bpder_strong_rows`, and card/member-size bounds. Then the row-list size
  after `bpders_strong1_rows (intern r) s` is bounded by the product budget.
- The interface also keeps the acceptance/value story attached: nullable row
  existence is equivalent to unique `strong_deferred_span_value r s`, and
  `intern`/`rerase` preserve `rxsize`.
- Design consequence: the remaining hard work is now isolated as the actual
  cubic row-universe construction and closure proof. This theorem is not a
  bounty payout by itself; it is a checked boundary between the smoke-tested
  deferred-value route and future Antimirov/hash-cons row accounting.

## 2026-06-03: Strong rows are an acceptance gate for deferred values

- Added a checked bridge from annotated row nullability to erased row-set
  language membership:
  `bnullable_iff_RL_rerase_empty` and
  `bex_bnullable_iff_RLS_map_rerase_empty`.
- Added `bpders_strong1_rows_nullable_iff_bders_simpStrong`, and the original
  entry version
  `bpders_strong1_rows_intern_nullable_iff_bders_simpStrong`.
- Added `strong_deferred_original_row_gate`: under `legacy_rexp r`,
  `bpders_strong1_rows (intern r) s` contains a nullable row exactly when
  there is a unique deferred span POSIX value for `(r, s)`.
- Design consequence: future cubic work can bound and close the strong row
  universe, then use nullable-row existence as the acceptance interface for the
  existing deferred value reconstruction route. This is a better fit for the
  Antimirov/linear-form idea than trying to decode POSIX values directly from
  the aggressively simplified strong derivative tree.
- Added `asize_intern` and `rsize_rerase_intern`, so any skeleton-side size
  bound starting from `rerase (intern r)` can be stated exactly in terms of
  the original `rxsize r`.

## 2026-06-03: Deferred span tables stay in the original fragment

- Added checked closure facts showing that if the original root satisfies
  `legacy_rexp`, then every regex state in `rexp_subterms`,
  `rexp_span_states`, `rexp_span_split_probes`,
  `rexp_span_all_split_probes`, `rexp_span_posix`, and
  `rexp_span_posix_states` also satisfies `legacy_rexp`.
- Strengthened `strong_deferred_original_legacy_budget` with those closure
  facts for the POSIX value table and split-probe table.
- Design consequence: deferred reconstruction is now tied to a finite
  non-backref universe at the original `rexp` level, which is the right
  premise shape for future regex-size cubic statements.
- Proof-performance lesson: do not write impossible constructor cases as
  `then show ?case by simp` when the case context contains large induction
  hypotheses. In this checkpoint the `BACKREF4` case of
  `legacy_rexp_subterms` ran past the CI timeout until it was rewritten to use
  only `BACKREF4.prems(1)` to obtain `False`, then discharge by `FalseE`.

## 2026-06-03: Original non-backref fragment bridge

- Added `legacy_rexp` on the original `rexp` datatype. It is the user-facing
  non-backref premise for the current cubic-bound route: original regular
  constructors are accepted, while `BACKREF4`, `HALF`, and `RESIDUE` are
  excluded.
- Added `legacy_rerase_intern`, proving that interning an original `rexp` and
  erasing it into the bounds skeleton preserves exactly this fragment
  predicate.
- Added `legacy_rexp_rerase_bders_simpStrong_intern` and
  `strong_deferred_original_legacy_budget`, so future proof work can state the
  route directly from `legacy_rexp r`: the strong derivative gate remains in
  the legacy skeleton fragment and the existing deferred reconstruction budget
  is available at the same original-regex entry point.
- Design consequence: use `legacy_rexp r` for original-file non-backref cubic
  statements. Use `legacy_rrexp (rerase a)` only when the theorem is genuinely
  about an already-annotated state.

## 2026-06-03: Strong-deferred reconstruction package is checked

- Added a small package of `FBound.thy` facts around
  `strong_deferred_span_value`.
- The main interface is `strong_deferred_reconstruction_budget`: the final
  `bsimpStrong` derivative state has a unique deferred POSIX value exactly
  when it is nullable, and the original-root POSIX value table/split probes
  stay within the checked span budgets.
- Design consequence: future proof work can cite one theorem for the current
  route's semantic skeleton instead of reassembling it from prose and Scala
  smoke. This still leaves the true regex-size cubic tree/share bound open.

## 2026-06-03: Frontier reports include structurally distinct regexes

- `StrongDeferredMemo` top-N reporting now prints a second top-N list that is
  deduplicated by regex structure, keeping the highest-ratio input per regex.
- This addresses a CEGAR failure mode in the report itself: repeated inputs for
  one regex can consume the entire top-N list and hide different structural
  pressure families.
- Design consequence: use the distinct-regex frontier when looking for the
  next compact regression or proof obligation. Use the raw top-N frontier when
  studying how one structure changes across inputs.

## 2026-06-03: Strong cubic frontier reports can show top-N witnesses

- Added `-StrongCubicTop` to the Scala smoke and
  `-ScalaSmokeStrongCubicTop` to full CI.
- The strong-deferred route now keeps a bounded frontier of observed
  size-pressure witnesses. With the default `1`, behavior is the same as the
  old worst-only report. With values such as `3` or `5`, the report shows
  several high-ratio regex/input pairs.
- Design consequence: when tightening the cubic constant or modifying
  `bsimpStrong`/the deferred reconstruction story, inspect the frontier rather
  than one witness. The top-N report is evidence for the CEGAR loop only; it is
  not a theorem, payout, or replacement for checked POSIX reconstruction.

## 2026-06-03: Strong cubic CE search has a size floor

- Added `-StrongCubicMinRegexSize` to make the strong cubic frontier search
  asymptotic-facing rather than dominated by tiny constant examples.
- Ordinary budget checks still apply to all regexes. The size floor only
  affects reports and random CE search, and the shrinker preserves the floor
  when reducing regex structure.
- Design consequence: when tuning constants, use a small floor such as `5` to
  get compact structural witnesses, or a larger floor such as `10` to ask
  whether the apparent issue survives beyond toy syntax.

## 2026-06-03: Strong cubic budget finder shrinks CEs

- Added optional `-FindStrongCubicBudgetCE` for the strong-deferred route.
  It searches random regex/input pairs for a violation of
  `factor * rsize(regex)^3`, then greedily shrinks the witness.
- The shrinker tracks visited `(regex,input)` pairs. This matters because
  same-size replacements can cycle even when every individual candidate looks
  harmless.
- Design consequence: use this before proof work when tightening constants or
  changing the strong simplifier. A size-budget failure should come with a
  compact witness, not just a large random term.

## 2026-06-03: Strong cubic smoke reports worst witnesses

- The `StrongDeferredMemo` smoke now reports the largest observed
  `asize(final strong tree) / rsize(regex)^3` ratio in the exhaustive,
  known-CE, random, and Chapter 7 grids.
- Tiny regexes with `rsize < 5` are still checked against the budget but are
  ignored for the summary so that `ZERO`/`ONE` do not hide useful witnesses.
- Design consequence: use this as the next CEGAR steering signal. If the cubic
  factor is tightened or a future simplifier changes the frontier, the reported
  witness should be minimized/analyzed before moving to proof work.

## 2026-06-03: Strong-deferred cubic budget is now global smoke

- Added `-StrongCubicFactor` / `-ScalaSmokeStrongCubicFactor` to check the
  `StrongDeferredMemo` exhaustive, known-CE, and random grids against
  `factor * rsize(regex)^3`.
- This is separate from `-Ch7StrongCubicFactor`, which checks the Chapter 7
  family. The former searches general generated regex/input pairs for
  cubic-budget CEs; the latter protects the thesis evil family trace.
- Design consequence: use both when evaluating a candidate. Passing only the
  Ch7 family is too narrow; passing value smoke without a size budget is too
  weak for the cubic route.

## 2026-06-03: Strong deferred cubic-budget smoke

- Added optional `-Ch7StrongCubicFactor` /
  `-ScalaSmokeCh7StrongCubicFactor` for the current positive route.
- This checks the Chapter 7 strong recognition tree against
  `factor * rsize(root)^3`, while the existing fixed threshold still protects
  the thesis Figure 7.6 scale. Both run alongside reconstructed-value flatness
  and memo universe checks.
- Design consequence: this is a smoke-level bridge toward the desired
  regex-size cubic theorem. It should be used to find CEs and tune the route,
  but it does not replace a checked Isabelle frontier/bound theorem.

## 2026-06-03: Strong deferred trace is a guard, not just a report

- The current counterexample-driven route is: keep the small thesis
  `bsimpStrong` tree for recognition, and recover the exact POSIX value from
  the original-root span/memo table.
- `-TraceStrongDeferredMemo` now enforces this discipline on the Chapter 7
  evil family: it checks reconstructed value flatness, checks optional
  tree/DAG/shape thresholds, and verifies the memo span/split universe bound.
  Exact baseline value comparison remains in the bounded exhaustive/random and
  known-CE smoke grids; running the old baseline derivative on the full Ch7
  trace is itself heap-explosive.
- Design consequence: future simplifier experiments should be judged by both
  constraints at once. A small final tree with a bad value is a counterexample;
  a correct value with an exploding tree is also a counterexample for the cubic
  route.

## 2026-06-03: Full span value table is key-bounded

- Added `rexp_span_posix_key` and proved it is injective over
  `rexp_span_posix` because `Posix` values are deterministic for a fixed
  `(q, i, j)` slice.
- The checked theorem `card_rexp_span_posix_bound` now bounds the full value
  table by the same quadratic state-key universe as `rexp_span_posix_states`.
- Design consequence: the deferred reconstruction proof can treat the value
  table as a memo map keyed by `(subregex, start, stop)`, matching the Scala
  `valueStates` accounting. Values do not introduce a separate unbounded
  cardinality dimension for a fixed regex/input.

## 2026-06-03: Named deferred span value relation

- Added `strong_deferred_span_value r s v` in `FBound.thy`.
- This is now the Isabelle-level object corresponding to the positive Scala
  route: `bsimpStrong` supplies the small nullable recognition state, while
  `rexp_span_posix` supplies the original POSIX value.
- Checked facts show this relation is equivalent to both original `Posix` and
  original `lexer` semantics, is defined exactly when the strong state is
  nullable, is unique, and has `flat v = s`.
- Design consequence: proof attempts should target this relation and its
  bounded span table, not direct ordinary decoding from the final
  `bsimpStrong` regex.

## 2026-06-03: Span flat/index boundary and slow inversion lesson

- Added checked `FBound.thy` boundary facts for `rexp_span_posix`:
  `rexp_span_posix_flat_eq`, `rexp_span_posix_flat_length`,
  `rexp_span_posix_empty_flat_index_eq`, and
  `rexp_span_posix_nonempty_flat_index_lt`.
- These facts are the lightweight side of the span/memo reconstruction route:
  before proving full STAR/NTIMES longest-left extraction, we can already use
  value flatness to show whether a span consumed an empty or nonempty input
  interval.
- Attempted direct nonempty STAR/NTIMES extraction from `Posix` values. Both
  broad `Posix_elims(6/7)` and specialized `inductive_cases` variants produced
  long-running proof commands, so those lemmas were removed before commit.
  Future attempts should build bespoke helper lemmas with explicit cases in
  `PosixSpec.thy` or a small dedicated inversion layer; do not reintroduce
  generated eliminator lines that run for tens of seconds.

## 2026-06-03: StrongFull known-CE guard

- Added optional smoke gate `-CheckStrongFullKnownCE` to
  `scala_cubic_smoke.ps1` and `-ScalaSmokeCheckStrongFullKnownCE` to
  `isabelle_ci.ps1`.
- The guard checks the minimal greedy-boundary CE
  `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`.
- It is intentionally a two-sided guard: `StrongFullCert` must still fail this
  known local-certificate case, while `StrongDeferredMemo` must match the
  baseline POSIX value. If `StrongFullCert` is later repaired, this guard should
  be updated with the new reconstruction theorem/story rather than silently
  letting the old route be mistaken for proved.
- Current checked diagnostic: the local-certificate tree remains size `13`, so
  the blocker is greedy boundary reconstruction, not small-state recognition.

## 2026-06-03: Countdown-aware original span universe

- The original-root span table cannot be bounded by plain syntactic subterms
  alone: POSIX reconstruction for `NTIMES q (Suc n)` recursively refers to
  `NTIMES q n`.
- `FBound.thy` now treats `rexp_subterms (NTIMES r n)` as a reconstruction
  universe containing all countdown states `NTIMES r k` with `k <= n`.
  Correspondingly, `rxsize (NTIMES r n)` now includes the `Suc n` countdown
  budget. This is the original-`rexp` analogue of the continuation/countdown
  accounting already used in the `rrexp` bound work.
- Added `rexp_subterms_NTIMES_countdown` as the reusable closure fact. This
  avoids trying to prove false tail-subterm claims during span reconstruction.
- Added `rslice_prefix_split` and original span inversion rules for ALT/SEQ:
  `rexp_span_posix_ALT1E`, `rexp_span_posix_ALT2E`, and
  `rexp_span_posix_SEQE`. These expose the split index needed by greedy
  POSIX value reconstruction.
- STAR/NTIMES inversion should be added later with explicit structured cases.
  A broad `auto elim!` attempt was rejected because it produced long-running
  proof search, exactly the performance debt this project is trying to avoid.

## 2026-06-03: Strong tree plus CE-driven span values

- The current preferred route matches the user's counterexample-driven
  requirement: keep the `bsimpStrong` tree-size behavior, mine exact-value CEs,
  and repair the semantic layer without inflating the emitted tree.
- Latest negative CE for direct/local certificates:
  `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`. The small final tree
  is preserved, but the local certificate chooses the right-star boundary
  incorrectly. This confirms that derivative-time local `Val => Option[Val]`
  transformers do not carry enough POSIX longest-left split information.
- Latest positive evidence for the span/memo route:
  `-CheckStrongDeferredMemo` passes exhaustive depth `2`/input `3`, the known
  CE grid, and `10,000` deterministic random cases at depth `7`/input `8`.
  Chapter 7 `k=5` keeps the thesis-scale strong tree sequence
  `46,474,730,771,820,875,918,958`.
- Design consequence: the small derivative tree should be proved as a nullable
  acceptance certificate. Exact POSIX values should be reconstructed by a
  bounded original-root span relation, where greedy sequence/star/countdown
  split choices are explicit table facts.

## 2026-06-03: Checked original split probes and POSIX constructors

- Added original-`rexp` split-probe universes in `FBound.thy`:
  `rexp_span_split_probes`, `rexp_span_all_split_probes`, and their cardinality
  bounds.
- Added original-value constructor introduction rules:
  `rexp_span_posix_ONE_emptyI`, `rexp_span_posix_CHI`,
  `rexp_span_posix_ALT1I`, `rexp_span_posix_ALT2I`,
  `rexp_span_posix_SEQI`, `rexp_span_posix_STAR_emptyI`,
  `rexp_span_posix_STAR_stepI`, `rexp_span_posix_NTIMES_zero_emptyI`, and
  `rexp_span_posix_NTIMES_SucI`.
- Design consequence: future reconstruction correctness can proceed by
  bounded split-probe induction/table construction rather than broad proof
  search or direct decoding from a simplified final regex.

## 2026-06-03: Checked root span POSIX bridge

- Added original-`rexp` span/value proof infrastructure in `FBound.thy`.
  `rexp_span_posix r s` records span entries `(q,i,j,v)` where the slice
  `s[i,j)` has original POSIX value `v` for subexpression `q`.
- The value-erased projection `rexp_span_posix_states r s` is bounded by
  `rxsize r * (|s|+1)^2`, via `rexp_span_states` and `rexp_subterms`.
- The main checked bridge is
  `bnullable_bders_simpStrong_intern_iff_rexp_span_posix_root`: the final
  `bders_simpStrong` nullable bit is exactly existence of a root POSIX span
  entry. `bnullable_bders_simpStrong_intern_unique_rexp_span_posix_root`
  records uniqueness at the root via `Posix_determ`.
- Design consequence: future work can treat the strong derivative tree as the
  small acceptance certificate, while proving exact values through original
  span reconstruction. This is the proof-facing analogue of the Scala
  `strongDeferredMemoValue` route.

## 2026-06-03: Strong tree, counterexamples, and span reconstruction

- The user-requested target is now interpreted as: keep the `bsimpStrong`
  derivative tree small, but do not require ordinary epsilon decoding from
  that final small tree to be the original POSIX value.
- The direct/local certificate route remains useful for mining CEs. Its stable
  minimal blocker is
  `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`: local reconstruction
  assigns the final `a` to the right star, while POSIX greediness assigns
  `bba` to the left star and leaves the right star empty.
- Therefore the positive route is `strongDeferredMemoValue`: use
  `bdersStrong` as a small nullable acceptance certificate, then reconstruct
  the exact POSIX value from original-regex spans. This keeps the thesis
  Figure 7.6 tree behavior while making the missing greedy split information
  explicit in a memo table.
- `-CheckStrongDeferredMemo` now includes a known-CE grid for the nested-star
  and greedy-sequence failures, so this path stays counterexample-driven.

## 2026-06-03: More checked span constructor rules

- Added further one-directional constructor rules for the checked memo table:
  `rspan_accepts_RALTSI`, `rspan_accepts_RONE_emptyI`,
  `rspan_accepts_RSTAR_stepI`, `rspan_accepts_RNTIMES_zeroI`, and
  `rspan_accepts_RNTIMES_SucI`.
- Design consequence: future POSIX reconstruction proofs can now construct
  language-accepted table entries for alternatives, empty/unit entries,
  nonempty star steps, and counted-repetition steps without relying on broad
  automation.

## 2026-06-02: Checked span reconstruction algebra

- Added the first correctness-side lemmas for the span/memo route in
  `GeneralRegexBound.thy`.
- `rslice_append` is the key string fact: when `i <= k <= j`, the span
  `s[i,j)` splits as `s[i,k) @ s[k,j)`.
- `rspan_accepts_root_iff` connects the root table entry
  `(r, 0, length s)` to ordinary language membership.
- `rspan_accepts_RSEQI` is the first grammar constructor rule for the checked
  memo table: a legal split with accepted left/right slices yields an accepted
  `RSEQ` span. `rspan_accepts_RSTAR_emptyI` records the empty-star case.
- Design consequence: future work should continue adding constructor rules for
  `RALTS`, `RSTAR` nonempty split, and `RNTIMES`, then connect the table to a
  POSIX value/reconstruction relation.

## 2026-06-02: Checked span memo-table specifications

- Extended the Isabelle span interface with `rslice`, `rspan_accepts`, and
  `rspan_all_split_probes`.
- `rspan_accepts r s` is the checked specification of the acceptance memo table
  over original-regex spans: `(q, i, j)` belongs when `q` is a subterm of `r`,
  `i <= j <= length s`, and `rslice s i j : RL q`.
- `rspan_all_split_probes r s` is the checked specification of all legal split
  positions `(q, i, k, j)` with `i <= k <= j <= length s`.
- New checked facts show both sets are subsets of the previously added finite
  universes and inherit their cardinality bounds. This is the next bridge from
  Scala `posixMemoValue` evidence toward an Isabelle reconstruction relation.

## 2026-06-02: Checked span-universe bounds for deferred reconstruction

- Added `rspan_states` and `rspan_split_probes` in `GeneralRegexBound.thy`.
  These are proof-facing finite universes for the Scala `posixMemoValue`
  reconstruction route:
  - `rspan_states r s` contains `(subregex, i, j)` states;
  - `rspan_split_probes r s` contains `(subregex, i, k, j)` split probes.
- Checked bounds:
  - `card_rspan_states_bound` and `card_subset_rspan_states_bound` give
    `rsize r * Suc (length s) * Suc (length s)`;
  - `card_rspan_split_probes_bound` and
    `card_subset_rspan_split_probes_bound` give the corresponding cubic
    input-span split-probe bound.
- Design consequence: the next theorem should define a POSIX reconstruction
  relation/table and prove its queried states are subsets of these universes.
  This avoids relying on direct decoding from `bdersStrong` and directly
  addresses left-greedy boundary CEs such as
  `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`.

## 2026-06-02: CE-driven full strong certificate route

- Added an experimental `StrongFullCert` route to
  `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`. Unlike the side-conditioned
  `StrongCoreCert`, this tries to keep the small `bsimpStrong` tree shape and
  attach reconstruction transformers to the strong rewrites.
- New switches in `scala_cubic_smoke.ps1`:
  `-CheckStrongFullLoop`, `-FindStrongFullCE`, `-TraceStrongFullLoop`, and
  `-TraceStrongFullKnown`.
- This route confirms the user's preferred counterexample-driven method is the
  right engineering discipline. The first depth-6 CE localized to trailing
  right-unit deletion under nested stars:
  `STAR(STAR(ALT(SEQ(b,ONE), SEQ(SEQ(STAR(a),a),ONE))))` on `abbab`.
  Broad local reparsing was not stable enough; explicit transformers for unit
  deletion, reassociation, and star absorption repaired that witness.
- Positive evidence after that repair: exhaustive depth `2`/input `3` and
  deterministic random depth `6`/input `7` pass exact POSIX value smoke, and
  the Chapter 7 `k=5` strong-full loop has max state `721`.
- Remaining blocker: depth `7`, input length `8`, seed `20260602`, case `622`
  shrinks to `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`. The
  original POSIX value assigns `bba` to the left star and leaves the right star
  empty; the current full certificate assigns `bb` left and `a` right.
- Design consequence: a local `Val => Option[Val]` certificate is useful
  route evidence but not yet a proof target. To keep the thesis small tree and
  get exact POSIX values, the next serious object should either carry richer
  greedy-boundary history in the certificate or use the span/memo
  reconstruction relation over the original regex and input.

## 2026-06-02: Memoized deferred POSIX reconstruction prototype

- Added `posixMemoValue` in `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`.
  It reconstructs the original POSIX value from the original regex and consumed
  input using dynamic programming over `(regex, start, end)` spans, rather than
  running the derivative lexer as a fallback.
- The parser mirrors the existing POSIX rules directly: alternatives are
  left-priority; `SEQ`, `STAR`, and `NTIMES` choose the longest left component;
  `STAR` and positive `NTIMES` only consume nonempty heads, with empty
  `NTIMES` values handled by repeated empty-body values.
- Added `strongDeferredMemoValue`, gated by the full thesis-style
  `bdersStrong` nullable state. This keeps the current separation:
  `bsimpStrong` is the small recognition certificate, and memoized POSIX
  reconstruction supplies the exact value from the original syntax/input.
- Added smoke switch `-CheckStrongDeferredMemo` in both Scala wrappers. Current
  evidence:
  - exhaustive depth `2`, input length `3`: `84,300` regex/input pairs pass;
  - deterministic random depth `6`, input length `7`: `10,000` cases pass with
    seed `20260602`.
- This is not yet the cubic regex-size proof. Its value is that it replaces the
  earlier `baselineValue` fallback by an explicit reconstruction algorithm that
  can be specified and optimized. The next step is to expose its table/universe
  size and relate it to the non-backref cubic frontier argument.
- Added `posixMemoResult`, `strongDeferredMemoResult`, and
  `-TraceStrongDeferredMemo` to expose the table/universe size. On the Chapter
  7 family:
  - k=5, n=30: strong tree `958`, memo accepts states `1577`, memo value states
    `126`, split probes `6011`, span bound `44206`, split bound `1370386`;
  - k=8, n=48: strong tree `2963`, memo accepts states `3818`, memo value
    states `198`, split probes `22145`, span bound `232897`, split bound
    `11411953`.
  The accepts table grows like a span-indexed parser universe in these traces,
  while value states stay close to the chosen POSIX path. This is useful
  positive evidence for proving a reconstruction universe bound separately from
  the strong derivative state bound.
- `-CheckStrongDeferredMemo` now enforces the conservative universe checks on
  every smoke case: accepts/value states must be below
  `rsize(r) * (|s| + 1)^2`, and split probes below
  `rsize(r) * (|s| + 1)^3`. These are deliberately input-span bounds for the
  reconstruction layer, not a replacement for the regex-size bound on the
  derivative state.
- Design consequence: the next Isabelle-facing artifact should not be another
  output simplifier. It should specify a span-indexed reconstruction relation
  over `(subregex, i, j)` and prove that it agrees with the existing POSIX value
  relation, then pair that relation with the checked `bders_simpStrong`
  acceptance bridge.

## 2026-06-02: Deferred strong route gets a checked acceptance bridge

- The current viable way to preserve thesis `bsimpStrong` tree behavior is not
  to decode ordinary POSIX values from the final simplified derivative. The
  smallest direct-decode CE found by the new Scala shrinker is
  `STAR(STAR(CH(b)))` on input `b`: the baseline value is a nested `Stars`
  value, while direct `strongValue` fails to decode the simplified final
  epsilon bits.
- Added `PosixCubicSmoke -FindStrongDirectCE` plus wrapper flags in
  `scala_cubic_smoke.ps1` and `isabelle_ci.ps1`. This is the CE-driven guard
  for future changes: first find/shrink direct-value failures, then repair the
  reconstruction route; do not attempt a proof from a candidate that fails this
  smoke layer.
- Added checked Isabelle lemmas in `FBound.thy`:
  `bnullable_bders_simpStrong_iff_Ders` and
  `bnullable_bders_simpStrong_iff_member`. They show that
  `bders_simpStrong` remains a correct small acceptance state:
  `bnullable (bders_simpStrong r s)` iff `s \<in> RL (rerase r)`.
- Extended the bridge to original POSIX values and the production lexer:
  `bnullable_bders_simpStrong_intern_iff_Posix`,
  `bnullable_bders_simpStrong_intern_iff_lexer_defined`,
  `bnullable_bders_simpStrong_intern_obtain_lexer`, and
  `bnullable_bders_simpStrong_intern_unique_Posix`. These theorems deliberately
  do not decode ordinary values from the strong final derivative. They say that
  a nullable strong state authorizes the unique original POSIX value, currently
  via `lexer r s`.
- Design consequence: keep the small final `bsimpStrong` tree as the
  recognition certificate, and define a deferred/generalized POSIX value
  relation over the original regex and consumed string. Direct decoding of the
  simplified derivative is historical negative evidence only.
- Proof-engineering note: an early version used a broad
  `using lexer_correct_Some lexer_correctness(1) by blast`, which caused a
  runaway build. The checked version splits the equivalence with explicit
  `iffI`/`obtain` steps and uses `Posix1`/`Posix_determ` directly. Keep this
  pattern for future POSIX-value bridge lemmas.

## 2026-06-02: CE-driven strong route needs value transformers

- Added a Scala-only `bsimpStrongSafe` diagnostic to test the user's proposed
  counterexample-driven route: start from thesis-style `bsimpStrong`, repair
  value counterexamples, and measure how much of the small-tree behavior
  survives.
- Four value-unsafe output rewrites were isolated:
  1. nested-star collapse loses the outer `Stars` constructor;
  2. dropping right `AONE bs` loses nonempty epsilon bits such as `[S]`;
  3. star absorption `r* . r* -> r*` loses the second star's value;
  4. left-nested sequence reassociation reorders prefix bits.
- Disabling those rewrites in the output syntax gives a value-safe baseline:
  `bsimpStrongSafe` passes exhaustive depth `2`/input `3`, random depth `4` with
  `5,000` cases, and random depth `5` with `2,000` cases, all at seed
  `20260602`. But the price is too high for the Figure 7.6 tree goal: on
  `k=5,n=30`, tree size is `5133` rather than thesis strong's `958`.
- Therefore the next path should not keep weakening the output regex. To retain
  the thesis strong tree size and still return correct POSIX values, the small
  regex must be paired with a reconstruction/transformer layer. Each strong
  rewrite should contribute a local map from values of the simplified regex
  back to values of the original regex, e.g. nested-star collapse maps
  `Stars vs` back to a nested `Stars` value, star absorption maps `r*` values
  back to `Seq (Stars vs) (Stars [])`, and reassociation maps
  `Seq x (Seq y z)` back to `Seq (Seq x y) z`.
- Added `scala_cubic_smoke.ps1 -TraceStrongRecon` as a first executable sketch
  of that route. It does not weaken `bsimpStrong`; instead, it checks the local
  reconstruction equations on the current CE witnesses. The result is positive
  but deliberately narrow: CE witnesses can be repaired while retaining small
  strong output trees, so the next algorithmic object should be a compositional
  derivative-time certificate, not another safe-output simplifier.
- The sketch now includes `decodeAValue`, an annotated-regex decoder used to
  test local certificate laws over input grids. This catches the exact POSIX
  value shape of the pre-rewrite and post-rewrite annotated regexes, then checks
  that the local transformer maps the post-rewrite value back to the
  pre-rewrite value. Current passing laws cover nested-star collapse, star
  absorption, star-zero collapse, right-unit deletion with carried bits, and
  sequence reassociation. This is still local: the next design step is to
  compose these certificates through `bder`/`bsimpStrong` iterations.
- Added `StrongCoreCert`, which is the first compositional implementation of
  that idea. It returns a simplified regex and a value transformer for nested
  sequence/star rewrites. The certificate is checked on derivative-generated
  expressions with `decodeAEpsValue`, a
  separate epsilon decoder that avoids treating non-nullable `ACHAR` rows as
  nullable values. This split matters: ordinary annotated decoding is for input
  bitstreams, while certificate checks compare epsilon values of derivative
  expressions.
- `StrongCoreCert` now also certifies alternation flattening and `distinctWith`.
  Flattened rows remember their original alternative index, so output choices
  can be rewrapped into the original nested/shifted ALT value shape. This closes
  the easy alternation layer but not shared-suffix pruning.
- Size comparison on the Chapter 7 k=5 family shows why pruning is the next
  certificate target. At n=30, thesis `bsimpStrong` is `958`, certified
  `bsimpStrongCore` is `2342`, and current uncertified `bsimpCubic full` is
  `900`. The certificate gap is therefore concentrated in row pruning rather
  than the already-certified sequence/star and flatten/distinct rewrites.
- Certified row pruning is now prototyped for the direct shared-suffix pattern.
  The design point is contextual POSIX priority: a later duplicate row may be
  removed because an earlier outer alternative with the same suffix has already
  claimed that language. Therefore the certificate belongs to the whole AALTs
  traversal, not to the later row as a standalone equivalence. Surviving later
  rows reconstruct through their original later-row transformer; deleted rows
  have no output values and are represented by the earlier branch.
- This reduces the Chapter 7 k=5 certified-core trace dramatically. At n=30,
  certified `bsimpStrongCore` is now `678`, compared with thesis `bsimpStrong`
  at `958`. This is strong evidence that the certificate route can preserve the
  desired tree-size behavior, but it is still Scala smoke: the next semantic
  artifact must compose certificates through the derivative loop.
- Added the first derivative-loop certificate smoke. A loop state carries the
  current simplified derivative regex and a continuation from values of that
  regex back to the original POSIX value. Each character composes the
  simplification certificate with `injectA`, an executable annotated-regex
  derivative injection function. This closes the main executable gap between
  one-step simplification certificates and whole-lexer POSIX values.
- Current loop smoke passes exhaustive depth `2`/input `3` and deterministic
  random depth `5`/input `6` (`3,000` cases, seed `20260602`). The remaining
  design task is no longer finding an executable value path; it is extracting a
  proof-facing invariant suitable for Isabelle.
- Added `CERTIFIED_STRONG_CORE.md` as the proof-facing route document. It names
  the relation-style invariant (`cert_recon`) that should replace Scala
  closures in Isabelle, lists the certificate constructors, and records the
  loop-level size trace. The new `-TraceStrongCoreLoop` smoke shows `maxCore`
  stabilizing at `721` on Chapter 7 k=5 by input length `12`, which is the
  current concrete size target for the proof-facing frontier argument.

## 2026-06-02: Virtual expanded keys complement hash-consing

- `PosixCubicSmoke.scala` now has a diagnostic
  `expanded-keyed-no-reassoc` sequence mode. It implements the accumulator-key
  idea: when a row such as `(a+b).c` is considered for coverage, the comparison
  index also records virtual rows like `a.c` and `b.c`. The executable output
  remains `no-reassoc` shaped, so this does not intentionally change POSIX
  value constructors the way direct distribution would.
- Smoke evidence is positive but not yet proof-level. With exhaustive depth
  `2`, input length `3`, and deterministic random smoke of `2,000` cases at
  depth `5`, input length `6`, seed `20260602`, exact POSIX values are
  preserved. On Chapter 7 `k=8`, lengths `4,8,16,32`, the final tree sizes are
  `1616,3226,6178,10218`, exact DAG sizes `78,130,232,408`, and shape-DAG
  sizes `61,87,125,173`.
- Compared with plain `no-reassoc` at Chapter 7 `k=8`, lengths `32,64,128`,
  the virtual-key mode improves final tree/DAG/shape sizes
  `48077/1721/718 -> 34581/1465/462` at length `128`. Its cumulative shared
  pool is slightly larger (`11170 -> 11810`), so it should be understood as a
  pruning/index improvement rather than a smaller store by itself.
- The design conclusion is that hash-consing and virtual expanded keys solve
  different parts of the Antimirov/POSIX tension. Hash-consing gives a shared
  representation and a plausible size metric; virtual keys expose covered row
  contributions such as `a.c` without emitting distributed POSIX syntax. A
  production candidate should combine them as a delayed row universe with a
  checked reconstruction theorem, not as a wrapper or bounty shortcut.
- On the thesis Figure 7.6 `k=5`, lengths `0..30` test, `bsimpStrong` still
  gives the expected hundreds-scale tree behavior. The current Scala
  `-TraceStrong` mirror aligns with the Isabelle sanity point at `n=16`
  (`820`, with checked facts `<825` and not `<812`). The value-safe
  `expanded-keyed-no-reassoc` route does not yet match that ordinary tree
  plateau: at `n=30` its tree size is `3849`, although exact DAG/shape-DAG are
  only `276/132`. This is the main design fork: either recover a tree-level
  POSIX-safe strong simplifier, or make the theorem statement use the shared
  row/DAG representation with reconstruction.
- Optional `-CheckStrong` value smoke now makes the first fork concrete. It
  fails on the minimal nested-star example `STAR (STAR (CH a))` over input `a`:
  the baseline POSIX value has nested stars, but `bsimpStrong` collapses the
  final regex to a single star-shaped bitstream. Therefore thesis-style
  `bsimpStrong` cannot be treated as a POSIX candidate merely because its size
  trace matches Figure 7.6. A tree-level route must keep enough nested-star
  structure, or explicitly transfer generalized values back to the original
  `val` shape.

## 2026-06-02: Hash-consed no-reassoc prototype gives reconstruction evidence

- `PosixCubicSmoke.scala` now has an optional hash-consed shared store for
  annotated regexes. It interns nodes, runs the value-safe `no-reassoc`
  derivative/simplification path, reconstructs a normal `arexp` from the final
  root, and decodes the resulting bits against the original regex. This tests
  the crucial reconstruction shape before any Isabelle commitment.
- Evidence so far is positive for the shared-state route. Exhaustive depth `2`
  and input length `3` preserve exact POSIX values on `84,300` cases; random
  depth `5`, input length `6`, seed `20260602`, preserves values on `1,000`
  cases. On Chapter 7 `k=8`, length `32`, the shared final root has tree size
  `18643`, exact DAG size `547`, shape-DAG size `312`, and cumulative store
  pool `1312`.
- This should be interpreted carefully. The prototype currently computes each
  derivative step using the existing tree functions and then interns the
  result, so it is a reconstruction/representation prototype rather than a
  fully shared derivative algorithm. The next design should define bder/bsimp
  directly over node IDs or over delayed linear-form rows, then prove that
  expanding/reconstructing the final root gives the same POSIX value.

## 2026-06-02: Value-safe route should exploit sharing, not reassociation

- The Scala smoke harness now reports three Chapter 7 size measures:
  tree `asize`, exact DAG size over annotated expressions, and shape-DAG size
  that ignores bit payloads. The tree threshold remains the default CI gate,
  but the DAG measures are now first-class diagnostics for Antimirov-style row
  universe work.
- The important observation is that the value-safe `no-reassoc` mode is not
  fundamentally exploding in distinct structure. On the thesis Chapter 7 family
  with `k=5`, lengths `4,8,16,32,64`, the tree sizes are
  `880,2057,3281,5325,8342`, while exact DAG sizes are only
  `65,124,206,348,575` and shape-DAG sizes are `51,90,132,194,278`. For
  `k=8`, lengths `4,8,16,32`, the tree reaches `18643`, but exact DAG is
  `547` and shape DAG is `312`.
- This suggests a better cubic-bound design: keep executable output
  `no-reassoc`/POSIX-value shaped, but represent states with hash-consed
  sharing or delayed linear forms so repeated continuations are counted once.
  This matches the Antimirov set/row intuition without forcing syntactic
  distribution or `(x.y).z -> x.(y.z)` into the value-carrying regex.
- This is still a route, not a payout. A future candidate must specify the
  shared representation, prove or smoke-test reconstruction to ordinary POSIX
  values, and then state the size theorem over that representation or transfer
  it back to tree syntax with a checked expansion bound.

## 2026-06-02: Destructive sequence reassociation is not value-safe output

- A diagnostic Scala switch `POSIX_SMOKE_SEQ_MODE` now isolates the sequence
  simplification rules inside `bsimpCubic_ASEQ_atom`. The default remains
  `full`, but modes such as `no-reassoc`, `keyed-no-reassoc`,
  `reassoc-nonnullable-left`, and `zeros-only` are available for smoke
  localization.
- The localization result is decisive enough to guide later proof work. Full
  destructive reassociation gives the attractive Chapter 7 trace
  `4->413, 8->725, 12->800, 16->800, 20->820`, but fails deterministic random
  POSIX value smoke at seed `20260602`, case `99`. Disabling reassociation
  makes the same random smoke pass but loses the Chapter 7 threshold:
  `no-reassoc` reaches `8->2057`, and `keyed-no-reassoc` still reaches
  `8->2157`.
- The attempted compromise "reassociate only when the left factor is
  non-nullable" is also not POSIX-value safe; it fails random smoke at seed
  `20260602`, case `370`. Therefore ordinary `(x.y).z -> x.(y.z)` cannot be
  part of a production `bsimpCubic` output rewrite without an explicit
  bitcode/value transfer theorem.
- Future cubic candidates should use reassociation only as a proof/index/key
  device, or introduce delayed linear forms/generalized POSIX values with a
  reconstruction theorem back to the original `val` shape. A pretty size trace
  is not evidence of a payable simplifier unless exact POSIX value smoke also
  passes.

## 2026-06-02: Scala smoke caught value bugs in bsimpCubic

- Broad cubic experiments now live in Scala, not as large Isabelle `eval`
  grids. The executable gate is
  `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`, run directly by
  `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1` and by full
  `isabelle_ci.ps1`. It enumerates bounded non-backref regexes and input
  strings, then compares exact decoded POSIX values between the baseline
  derivative lexer and `bders_simpCubic`.
- The first Scala smoke run exposed real value-level bugs. Treating
  `ANTIMES _ _ 0` as `AONE []` lost the terminating `S` bit, and collapsing
  nested stars changed values for examples such as `STAR (STAR a)`. The current
  `bsimpCubic` preserves those bits: zero-count repetition and empty stars
  return value-carrying `AONE (bs @ [S])`, and nested-star collapse is not part
  of the POSIX-preserving candidate.
- Sequence-level star absorption is also not POSIX-value safe in general.
  Scala found the counterexample `SEQ (STAR a) (STAR a)` on input `a`: dropping
  the second star loses the required `Seq (Stars [a]) (Stars [])` value shape.
  This rule may remain historical language/size evidence, but it cannot be used
  in `bsimpCubic` without a separate generalized-value transfer theorem.
- The value-safe pruning step added here is generalized covered-continuation
  pruning. If an earlier row is `p.k` or `(p+q).k`, then a later row
  `(p+r).k` can remove the covered `p` contribution while preserving POSIX
  first-match behavior. In Scala this brings the Chapter 7 `k=5` trace to
  `4->413, 8->725, 12->800, 16->800, 20->820` while exact POSIX value smoke
  passes on the default bounded enumeration.
- Stronger random smoke has now found a deeper POSIX counterexample for the
  current `bsimpCubic` candidate:
  `STAR (ALT ONE (STAR (STAR (STAR (STAR (STAR (CH a)))))))` on input `aaa`
  with seed `20260602`, random case `99`. The baseline lexer returns a nested
  right-branch star value, while `bders_simpCubic` produces a bitstream that
  does not decode against the original regex. This blocks any BR-039/BR-040
  payout: the next design needs a value-aware row identity, reconstruction
  theorem, or generalized POSIX-value transfer before the size candidate can
  be treated as production.
- Exhaustive depth `3` over the two-character grammar is not a practical
  default smoke level: it attempts about `63,191,284` raw regexes before
  deduplication. The Scala harness now has a cap and reports this clearly
  instead of running out of memory.

## 2026-06-02: Cubic route must be smoke-first and POSIX-aware

- Cubic-bound proof work is now explicitly smoke-gated. A simplifier candidate
  must first pass checked regression tests for shared-suffix pruning, including
  `(a+b).c + (a+d).c`, and for the thesis Chapter 7 three-layer-star family
  `((a* + (aa)* + ... + (a...a)*)*)*`. A candidate with a known missing pruning
  operation is diagnostic only; do not spend proof effort trying to certify it
  as the final cubic route.
- The reason is conceptual, not only engineering. Antimirov partial derivatives
  get their finite/set-based behavior by organizing derivative results as rows
  or linear forms, where exposing `(a+b).c` as comparable `a.c`/`b.c` rows lets
  set reasoning remove duplicates or covered rows. The reference point is
  Antimirov 1996, "Partial derivatives of regular expressions and finite
  automaton constructions", DOI `10.1016/0304-3975(95)00182-4`, whose bounded
  partial-derivative set theorem is the model for the desired state-space
  accounting. POSIX lexing cannot simply distribute syntax this way, because
  language-equivalent expressions can carry different value shapes.
- In particular, `(a+b).c` and `a.c + b.c` can correspond to values shaped like
  `Seq (Left x) y` versus `Left (Seq x y)`. Future candidates therefore need a
  real pruning/reconstruction story: shared-suffix row pruning that preserves
  POSIX values, delayed/indexed linear forms that compare rows without
  destructively expanding the executable regex, proof-only normalization with
  executable reconstruction, or a generalized POSIX-value equivalence with a
  transfer theorem back to the original semantics.
- `rsimp9` remains historical technical evidence only. It does not solve this
  Antimirov/POSIX tension and must not be treated as a cubic-bound payout
  candidate.

## 2026-05-31: Cubic non-backref size-bound direction

- `rsimp7`/`bsimp7` is not safe as the root normalizer for an
  original-regex-size cubic theorem. The checked lemma
  `rsimp7_can_increase_root_size` exhibits `(a + b) · (c + d)`, where eager
  row-product distribution increases `rsize`. This does not invalidate
  `rsimp7` as a per-row normalizer, but the root used for the global cubic
  accounting must not perform that expansion.
- `rsimp8`/`bsimp8` is the new root-safe simplifier layer. It keeps the
  language-changing obligations checked by `RL_rsimp8`/`bsimp8_rerase`, keeps
  star cleanup and prefix-star absorption via `rsimp7_SEQ_atom`, but avoids
  full `rsimp7_SEQ` row products at roots. The checked lemma
  `rsize_rsimp8_le` is the reason the conditional interface
  `rsizes_rpders_norm17_rows_rsimp8_live_row_cubicI` is stated w.r.t. the
  original `rsize r`.
- The next proof target is unchanged in shape but should use `rsimp8 r` as the
  normalized root:
  `set (rflts (rpder_norm7_list c q)) \<subseteq>
   partial_derivative_live_row_universe (rsimp8 r)` for live-row states `q`.
  If this closes, the numeric bound is already cubic in the original regex
  size.
- This target is now known to be too narrow as stated. The checked lemma
  `rsimp8_live_row_universe_not_closed` gives the obstruction
  `(((1+a).a))* --a--> ((a+(a.a)))*`; the target universe for `rsimp8 r`
  contains the raw star body but not this normalized star image. The next
  design should either add a controlled normalized-star-image component to the
  universe, or refine the root simplifier to normalize nullable-left sequence
  bodies while still avoiding general row-product expansion such as
  `(a+b)·(c+d)`.
- The better immediate route is `norm18`, defined by applying `rsimp8` rather
  than full `rsimp7` to each partial-derivative row. Small-model search found
  no closure counterexample up to regex size 7 over a two-character alphabet,
  and the checked artifacts `rpder_norm8_list`, `rpders_norm18_rows`,
  `RLS_rpders_norm18_rows`, and
  `rsizes_rpders_norm18_rows_rsimp8_live_row_cubicI` now make this a formal
  proof target. This keeps Antimirov row lists while avoiding recursive
  row-product expansion inside star bodies. The checked lemma
  `norm18_closes_rsimp8_live_row_obstruction` verifies that the concrete
  `(((1+a).a))*` failure of `norm17` is fixed by `norm18`.
- Closure proof infrastructure is now being split by row shape. Checked
  support includes named intro lemmas for `partial_derivative_live_row_universe`,
  the non-alt `RALTS` child monotonicity lemma
  `partial_derivative_live_row_universe_alt_child_mono`, base cases
  `rpder_norm8_live_row_step_RZERO`/`RONE`/`RCHAR`, and the conditional list
  decomposition lemma `rpder_norm8_live_row_step_RALTSI`, plus
  `rpder_norm8_live_row_step_RALTS_selfI` for the normalized-alternative
  case where every child is non-alt. The sequence/star/ntimes branches are
  now split by `rpder_norm8_live_row_step_RSEQI`,
  `rpder_norm8_live_row_step_RSTARI`, and
  `rpder_norm8_live_row_step_RNTIMESI`, so the remaining work can focus on
  carried-continuation membership rather than repeatedly unfolding
  `rpder_list`, `rpder_norm_list`, and `rflts`. This deliberately avoids a
  broad `auto` proof over the final closure statement.
- Checked normal-form support now extends through the root-safe normalizer:
  `good_rsimp7_SEQ_atom`, `good_rsimp8`, `good_rpder_norm8_list`, and
  `good_rflts_rpder_norm8_list`. Use these facts when a proof needs to reason
  about children exposed by `rflts (map rsimp8 ...)`; do not re-open the
  simplifier by datatype induction unless a branch-specific lemma really
  needs it.
- Flattened `rsimp8` rows now have a checked bridge through their own
  live-row universe:
  `rflts_singleton_good_live_row_universe`,
  `rflts_singleton_rsimp8_live_row_universe`, and
  `rflts_map_rsimp8_live_row_subsetI`. This changes the preferred next proof
  shape: prove that each raw carried continuation's `rsimp8` live-row
  universe is contained in the target root universe, then use the bridge to
  discharge the flattened row. The normalized-alternative case is covered by
  `rpder_norm8_live_row_step_rsimp_ALTsI`.
- Carried `RSEQ`/`RSTAR`/`RNTIMES` branches now have path-continuation
  reducers:
  `rflts_map_rsimp8_rpder_list_path_subsetI`,
  `rflts_map_rsimp8_rpder_list_norm_tail_subsetI`,
  `rpder_norm8_live_row_step_RSEQ_pathI`,
  `rpder_norm8_live_row_step_RSTAR_pathI`, and
  `rpder_norm8_live_row_step_RNTIMES_pathI`. Use these instead of unfolding
  the nested `map rsimp8 (map ... (rpder_list ...))` goals by hand.
- A weaker direct-frontier interface is now checked:
  `rflts_map_rsimp8_direct_subsetI`,
  `rflts_map_rsimp8_rpder_list_path_direct_subsetI`,
  `rflts_map_rsimp8_rpder_list_norm_tail_direct_subsetI`, and the direct
  `RSEQ`/`RSTAR`/`RNTIMES` path-step lemmas. This is the preferred interface
  after the normalized-tail counterexample: instead of proving the whole
  universe inclusion
  `partial_derivative_live_row_universe (rsimp8 p) \<subseteq> U`, prove the smaller
  obligation `set (rflts [rsimp8 p]) \<subseteq> U` for the carried continuation that
  is actually emitted by the row step.
- The plain `norm18` closure target is now also refuted for `RNTIMES`. The
  checked lemma `rsimp8_live_row_universe_RNTIMES_not_closed` uses
  `(((0 + 1) + b)*){1}`: because `rsimp8` does not recurse under
  `RNTIMES`, the live-row universe contains a carried tail with
  `((0 + 1) + b)*`, while the `b` step emits the normalized frontier
  `(1 + b)*` outside that universe. Future BR-036 work needs either a
  recursively normalized `RNTIMES` root/tail invariant or a larger
  norm18 universe that explicitly accounts for normalized repetition bodies.
- The checked sanity lemma `norm18_live_row_NTIMES_body_normalized_sanity`
  shows the same carried counted-repetition tail closes when the repeated body
  is already in the normalized star form emitted by the frontier. This points
  to a small `RNTIMES` repair: normalize counted-repetition bodies/tails while
  still avoiding full `rsimp7_SEQ` row-product expansion at roots.
- The proof-level prototype `rsimp9` implements that repair locally:
  `RSEQ`, `RALTS`, and `RSTAR` follow `rsimp8`, while `RNTIMES r n`
  recursively normalizes `r`, collapses normalized `RZERO`/`RONE` powers,
  and sends every zero-count repetition `RNTIMES r 0` to `RONE`.
  Checked facts `RL_rsimp9` and `rsize_rsimp9_le` show the prototype is
  language preserving and original-size safe. The checked
  `norm19_closes_RNTIMES_countdown_sanity` confirms that a simple counted-tail
  decrement no longer leaks `RNTIMES _ 0`; do not expand the universe just to
  carry that identity. The checked
  `norm19_RNTIMES_body_normalization_obstruction_persists` shows the harder
  body-normalization case is still open: derivatives may emit `rsimp9 body`
  where the current live-row universe only remembers an unnormalized carried
  continuation. The checked
  `norm19_RNTIMES_body_normalization_obstruction_in_path_universe` shows that
  the same witness is not outside the existing cubic accounting: it lands in
  `partial_derivative_path_universe (rsimp9 r)` as a subterm of the normalized
  root. Prefer the new path-universe hook over further ad hoc live-row
  enlargement.
- Full one-step closure for arbitrary states in
  `partial_derivative_path_universe (rsimp9 r)` is checked-false. The lemma
  `norm19_path_universe_RNTIMES_subterm_not_closed` uses root `(a){2}.b`:
  the bare counted subterm `(a){2}` is in the root path universe, but its
  derivative emits bare `(a){1}`, while the root universe only carries the
  sequenced continuation `(a){1}.b`. The final invariant should track reachable
  row/path-carried states, or explicitly add a countdown-aware closure, instead
  of quantifying over every path-universe subterm.
- The existing `partial_derivative_frontier_universe` is the current
  countdown-aware route. It already uses `rlinear_continuations`, which contains
  all decrements `RNTIMES r k` for `k <= n`, has quadratic cardinality and
  linear member-size bounds, and now has a checked norm19 cubic hook:
  `rsizes_rpders_norm19_rows_frontier_universe_cubic`,
  `rsizes_rpders_norm19_rows_frontier_universe_cubicI`, and
  `rsizes_rpders_norm19_rows_rsimp9_frontier_cubicI`. The sanity lemma
  `norm19_frontier_universe_repairs_RNTIMES_subterm_countdown` confirms it
  repairs the `(a){2}.b` counted-tail counterexample.
- The first frontier splitter layer is checked:
  `rflts_singleton_rsimp9_frontier_universe`,
  `rflts_map_rsimp9_frontier_subsetI`,
  `partial_derivative_frontier_universe_alt_child_mono`, and
  `rpder_norm9_frontier_universe_step_RZERO/RONE/RCHAR/RALTS/rsimp_ALTs`.
  It proves the base and alternation cases for the frontier route without
  unfolding large derivative rows. The carried-constructor layer is now also
  checked: `rflts_map_rsimp9_rpder_list_frontier_subsetI`,
  `rflts_map_rsimp9_rpder_list_norm_tail_frontier_subsetI`, and
  `rpder_norm9_frontier_universe_step_RSEQ/RSTAR/RNTIMES_pathI`. These are the
  preferred entry points for the remaining one-step closure proof.
- The old left-nested sequence obstruction for `rpder_norm_list` is now checked
  repaired by `rsimp9`: `norm19_frontier_universe_repairs_left_nested_seq_counterexample`
  shows `((a*).b).d` normalizes to `a*.(b.d)` and the corresponding `a`
  derivative remains inside `partial_derivative_frontier_universe`. This keeps
  the frontier route aligned with the intended stronger simplifier, rather than
  masking the problem with a larger accounting set.
- The older nested-star cubic obstruction is also checked repaired by `rsimp9`:
  `norm19_frontier_universe_repairs_nested_star_counterexample` shows
  `RSTAR (RSTAR a)` normalizes to `RSTAR a`, and the normalized derivative row
  remains inside the same frontier universe.
- The thesis cubic-bound examples are now represented as checked regression
  sanity lemmas. `thesis_cubic_evil3_aaa_norm19_rows_cubic` exercises the
  Chapter 6 evil shape `(a* + (aa)* + (aaa)*)*` after the input `aaa`; the
  smaller `thesis_cubic_small_alt3_aaa_norm19_rows_cubic` remains only as a
  cheap non-starred contrast. The
  `thesis_cubic_ntimes_countdown_norm9_no_zero_counter` plus
  `thesis_cubic_ntimes_countdown_norm19_rows_cubic` exercise the `(a){3}`
  countdown. These examples are evidence for the `rsimp9` route and should be
  kept fast; they are not a final cubic theorem.
- The thesis Chapter 7 stronger-simplification idea has not yet been
  implemented as a real checked simplifier. The current `rsimp9/path9` line is
  a proof-level normalization/accounting route, not the `distinctWith`/pruning
  route. If the path9 linear-size proof remains brittle, the next serious
  simplifier should implement that Chapter 7 pruning rule directly.
- The exact Chapter 7 diagnostic is now checked in `FBound.thy`.
  `thesis_ch7_evil5_bders_simp_size_16` fixes the production `bders_simp`
  size for `((a* + (aa)* + ... + (aaaaa)*)*)*` after `a^16` at `14876`.
  The root-safe `bsimp8` variant is far smaller but still not the Chapter 7
  prune rule: `thesis_ch7_evil5_bders_simp8_size_16 = 1308`. The
  partial-derivative row route is smaller again:
  `thesis_ch7_evil5_bpders_norm17_row_size_16 = 645`. This supports the
  current conclusion: a cubic production path should either transfer the row
  route to the annotated lexer, or implement `bsimpStrong` with non-invasive
  pruning rather than relying on old `bsimp`.
- The overlap-prune target is also checked. Current `bsimp` leaves
  `(a + b + d).c + (a + c + e).c` unchanged
  (`thesis_ch7_bsimp_misses_overlap_prune`), while the hand-pruned expression
  is strictly smaller and language-equivalent after erasure
  (`thesis_ch7_overlap_pruned_smaller`,
  `thesis_ch7_overlap_pruned_same_language`). This is only an erasure-level
  safety sanity check; POSIX/bitcode preservation still needs a rewrite or
  retrieve/decode proof before this can become production `bsimpStrong`.
- `BlexerSimp.thy` now contains the first executable `bsimpStrong` prototype
  on the original `arexp` datatype. The core deletion is
  `prune_eq1_against`: later alternatives are removed only when `eq1` matches
  an earlier covered alternative. `L_prune_eq1_against_AALTs` is the generic
  erasure-language safety lemma for that deletion. `bsimpStrong_prune_pair`
  uses it in the Chapter 7 shape: if two sequence rows share the same
  continuation under `eq1`, prune the later row's left alternative by the
  earlier row's left alternative. The checked regression
  `thesis_ch7_bsimpStrong_prunes_overlap` confirms that the prototype reduces
  `(a + b + d).c + (a + c + e).c` to
  `(a + b + d).c + (c + e).c`, with checked smaller size and same erasure
  language. The first full evil-family regression is checked too:
  on `((a*) + ((aa)*) + ... + ((aaaaa)*))^**` after `a^16`,
  `bders_simpStrong` is below `825` but not below `812`. This beats
  `bsimp8 = 1308` and old `bders_simp = 14876`, but does not yet match the
  row-list route (`645`).
  Do not mark this as production yet; the next design step is a POSIX/bitcode
  preservation theorem plus a general cubic proof.
- The dual-frontier route now has a checked conditional cubic hook:
  `rsizes_distinct_path_dual_frontier_universe_cubicI`. It reduces the
  remaining arithmetic/accounting work to two local obligations: prove
  `card (rpath_frontiers r) + card (rpath_atom_frontiers r)` is quadratic in
  `rsize r`, and prove linear member size for
  `partial_derivative_path_dual_frontier_universe r`.
- That second obligation is checked-false for the current full dual universe:
  `current_dual_frontier_universe_member_size_not_linear` exhibits a
  left-nested sequence with five binary suffix alternatives and a dual-frontier
  member larger than `Suc (rsize r + rsize r)`. The full frontier component is
  too large for the intended cubic accounting; prefer atom-only frontiers or a
  smaller reachable-row invariant.
- The old atom-only universe is also checked too broad:
  `current_path_atom_frontier_universe_member_size_not_linear` shows that
  sequence continuations using `rsimp4 r2` can eagerly expand a right-nested
  binary suffix chain before it enters the atom frontier. A plausible next
  universe must be norm9-specific, carrying `rsimp9`/`rsimp7_SEQ_atom`
  continuations instead of the older `rsimp4` collector.
- The first norm9-specific atom-frontier scaffold is now checked:
  `rpath9_atom_frontier_acc`, `rpath9_atom_frontiers`, and
  `partial_derivative_path9_atom_frontier_universe` use `rsimp9` plus
  `rsimp7_SEQ_atom` carried continuations and have finite support. The sanity
  lemma `path9_atom_frontier_avoids_old_atom_explosion` proves that the old
  right-nested binary suffix explosion is absent from this new universe. Next
  target: prove its cardinality/member-size bounds and then its one-step
  `rpder_norm9_list` closure.
- The norm9 atom-frontier accounting interface is checked:
  `partial_derivative_path9_atom_frontier_universe_card_le`,
  `partial_derivative_path9_atom_frontier_universe_member_size_boundI`,
  `partial_derivative_path9_atom_frontier_universe_member_size_linearI`, and
  `rsizes_distinct_path9_atom_frontier_universe_cubicI`. The cubic hook now
  needs only local bounds on `rpath9_atom_frontiers r`: quadratic cardinality
  and member size at most `Suc (rsize r + rsize r)`.
- The path9 closure plumbing now has checked base facts:
  `rsubterms_rsimp_ALTs_member`, `set_rflts_singleton_map_member`,
  `rflts_singleton_rsimp9_path9_atom_frontier`,
  `rflts_map_rsimp9_path9_atom_subsetI`,
  `rflts_rsimp9_alt_child_path9_atom_subset`, and
  `rpder_norm9_path9_atom_frontier_step_RZERO/RONE/RCHAR`. Keep these proofs
  explicit: a broad singleton `blast` once ran past the proof-performance
  budget before being split.
- The path9 `RALTS`/`rsimp_ALTs` layer now has parent-target closure plumbing:
  `set_rflts_map_member_exists`, `set_rflts_map_memberE`,
  `rflts_map_rsimp9_alt_path9_atom_subset`,
  `rflts_map_rsimp9_rsimp_ALTs_path9_atom_subset`,
  `rpath9_atom_frontiers_alt_child_subset`,
  `rpath9_atom_frontiers_alt_child_universe`,
  `rpder_norm9_path9_atom_frontier_step_RALTS_parentI`, and
  `rpder_norm9_path9_atom_frontier_step_rsimp_ALTs_parentI`. This is a
  deliberately weaker replacement for full child-universe monotonicity, which
  is suspicious because `rsimp9 (RALTS rs)` flattens child alternatives.
- Carried-frontier parent inclusions are checked for the constructors that
  matter next: `rpath9_atom_frontiers_universe`,
  `rpath9_atom_frontiers_seq_left_subset`,
  `rpath9_atom_frontiers_seq_left_universe`,
  `rpath9_atom_frontiers_seq_right_subset`,
  `rpath9_atom_frontiers_seq_right_universe`,
  `rpath9_atom_frontiers_star_body_subset`,
  `rpath9_atom_frontiers_star_body_universe`,
  `rpath9_atom_frontiers_ntimes_body_subset`, and
  `rpath9_atom_frontiers_ntimes_body_universe`. Next proof layer should connect
  these parent inclusions to the existing `rpder_norm9_live_row_step_*`
  splitters.
- The parent-target derivative splitters are now checked:
  `rpder_norm9_path9_atom_frontier_step_RSEQ_parentI`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_parentI`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_parentI`. These do not claim
  closure by themselves; they factor the closure goal into carried left/body
  branch subset obligations plus the nullable right branch for sequence.
- The sequence nullable-right branch now has a checked child-to-parent lift:
  `rnullable_rsimp9`,
  `rsubterms_rsimp4_SEQ_atom_nullable_right_subset`,
  `rsubterms_rsimp7_SEQ_atom_nullable_right_subset`,
  `rsubterms_rsimp9_RSEQ_right_nullable_universe`,
  `partial_derivative_path9_atom_frontier_universe_RSEQ_right_nullable_subset`,
  and `rpder_norm9_path9_atom_frontier_step_RSEQ_parent_childI`. Future
  `RSEQ` path9 closure work should spend effort on the carried left branch,
  not on re-proving the nullable right side.
- The `RALTS`/`rsimp_ALTs` child-to-parent lift must respect flattening. A
  full `partial_derivative_path9_atom_frontier_universe q` subset is too strong
  for nested alternatives, because parent normalization may flatten away the
  child `RALTS` node. The checked facts instead lift the data that matters for
  rows: `partial_derivative_path9_atom_frontier_universe_RALTS_flat_child_subset`,
  `rsubterms_nonalt_flattened_subterms`,
  `rsubterms_rsimp9_alt_child_nonalt_path9_atom_subset`,
  `partial_derivative_path9_atom_frontier_universe_RALTS_nonalt_child_member`,
  `rpder_norm9_path9_atom_frontier_step_RALTS_childI`, and
  `rpder_norm9_path9_atom_frontier_step_rsimp_ALTs_childI`.
- The first `rpath9_atom_frontiers` card-accounting split is checked:
  `plus2_square_plus_plus3_square_le`,
  `sum_list_rsize_plus2_square_le_rsizes_plus3_square`,
  `card_rpath9_atom_frontier_acc_list_le`,
  `card_rpath9_atom_frontiers_RALTS_le`, and
  `card_rpath9_atom_frontiers_RALTS_quadraticI`. This closes the alternative
  branch of the desired quadratic-card proof from child hypotheses; remaining
  accounting work is `RSEQ/RSTAR/RNTIMES` and member-size.
- The `RALTS` member-size split is also checked:
  `rpath9_atom_frontiers_RALTS_member_sizeI`. Together with the card split,
  the alternative branch of both path9 accounting premises now reduces to
  child hypotheses.
- Path9 accounting base cases are checked for `RZERO`, `RONE`, `RCHAR`, and
  zero-count `RNTIMES`: `card_rpath9_atom_frontiers_RZERO_quadratic`,
  `card_rpath9_atom_frontiers_RONE_quadratic`,
  `card_rpath9_atom_frontiers_RCHAR_quadratic`,
  `rpath9_atom_frontiers_RZERO_member_size`,
  `rpath9_atom_frontiers_RONE_member_size`,
  `rpath9_atom_frontiers_RCHAR_member_size`,
  `card_rpath9_atom_frontiers_RNTIMES_zero_quadratic`, and
  `rpath9_atom_frontiers_RNTIMES_zero_member_size`.
- The next path9 accounting layer has local carried-continuation bounds:
  `rfrontier_member_size_le_rsize`, `card_rfrontier_rsimp7_SEQ_atom_le`, and
  `rfrontier_rsimp7_SEQ_atom_member_size_le`. These are intended for the
  `RSEQ`/`RSTAR`/`RNTIMES` cases, where the path9 accumulator carries
  `rsimp7_SEQ_atom (rsimp9 suffix) k` rather than the older `rsimp4` tail.
- The norm19 row-driver runway is checked: `rpders_norm19_rows` is backed by
  `rpders_norm9_rows`, has finite/distinct support, preserves language through
  `RLS_rpders_norm19_rows`, and has conditional cubic theorems
  `rsizes_rpders_norm19_rows_rsimp9_live_row_cubicI`,
  `rsizes_rpders_norm19_rows_rsimp9_path_cubicI`, and
  `rsizes_rpders_norm19_rows_rsimp9_frontier_cubicI`. The path version keeps
  the bound at `2 * (rsize r + 3)^3`; the frontier version gives
  `3 * (rsize r + 2)^3` and is currently more plausible because it carries
  counted decrements. The remaining obligation is not arbitrary path-universe
  closure, but one-step closure for this frontier universe or a smaller
  reachable-row subuniverse.
- The `rpder_norm9_live_row_step_*` splitter layer is checked, including
  base constructors, `RALTS`, `RSEQ`, `RSTAR`, `RNTIMES`, and path/direct
  carried-continuation interfaces. Future work should not unfold
  `rpder_norm9_list` broadly; use these splitters and prove only the local
  carried-continuation premise generated by the relevant constructor.
- The path-universe counterpart is now checked for the carried constructors:
  `rflts_singleton_rsimp9_path_universe`,
  `rflts_map_rsimp9_path_subsetI`,
  `rflts_map_rsimp9_rpder_list_path_universe_subsetI`,
  `rflts_map_rsimp9_rpder_list_norm_tail_path_universe_subsetI`, and
  `partial_derivative_path_universe_alt_child_mono` plus
  `rpder_norm9_path_universe_step_RZERO/RONE/RCHAR/RALTS/rsimp_ALTs` and
  `RSEQ/RSTAR/RNTIMES_pathI`. These remain useful splitters, but do not target
  the refuted arbitrary path-universe closure directly. Adapt them toward
  `partial_derivative_frontier_universe (rsimp9 r)`.
- Rejected shortcut: `rsimp4_SEQ_atom r RONE = r` is false in general because
  `rsimp4_SEQ_atom` deliberately removes zero/one sequence structure and
  reassociates left-nested sequences. A raw path-continuation transitivity
  proof based on that equation failed; future work needs a normalized-tail
  invariant or a weaker monotonicity statement.
- Rejected stronger shortcut: `rsimp8 (rsimp4_SEQ_atom r RONE) = rsimp8 r` is
  also false. The checked lemma
  `rsimp8_rsimp4_SEQ_atom_RONE_counterexample` uses the shape
  `((b . b*) . b*)`; applying `rsimp4_SEQ_atom _ RONE` first exposes the inner
  star absorption `b* . b*`, while direct root-safe `rsimp8` does not. Do not
  base BR-036 on equality between normalized tails. Use a closure invariant
  that accounts for these local tail normalizations, or prove direct
  membership for the normalized carried branch.
- Proof-engineering note: `rsimp_ALTs` has length-sensitive equations
  (`[]`, singleton, and two-or-more). In nested list cases, save the outer
  shape equation with a named fact before entering an inner `cases`; relying
  on a shadowed `Cons` case name caused a failed proof and is easy to repeat.
- Do not use a monolithic `rsimp8` idempotence proof as the next shortcut. A
  naive induction over `rsimp8` timed out because the `RALTS` branch expands
  `rsimp_ALTs`, `rdistinct`, and `rflts` together. If idempotence is needed,
  first prove small list-normalization helper facts and keep each proof line
  under the performance budget.
- `rsimp7`/`bsimp7` is now the checked stronger simplifier definition for the
  25k new-definition bounty. It keeps the Antimirov row-product/state-list
  pipeline and extends `rsimp6` with prefix star absorption:
  `r* . (r* . k) = r* . k`. The proof-level language facts
  `RL_rsimp7`, `RLS_rpders_norm17_rows`, and `RL_rders_pder_norm7`, plus the
  annotated erasure facts `bsimp7_rerase`, `bp_der_norm7_rerase`,
  `rpders_norm17_rows_rerase`, and `RL_rerase_bders_pder_norm7`, are checked.
  This completes the algorithmic-definition milestone but not the final cubic
  repeated-state closure theorem.
- `norm17` now has the same conditional cubic hooks as `norm16`, including the
  rflts-based live-path interface
  `rsizes_rpders_norm17_rows_live_path_universe_cubicI'`. The next proof
  target is the one-step premise
  `set (rflts (rpder_norm7_list c q)) \<subseteq> partial_derivative_live_path_universe r`
  for reachable/live `q`.
- Correction after a checked counterexample: the premise above is too narrow
  for row lists that flatten alternatives. The lemma
  `live_path_universe_misses_flattened_alt_row` shows that
  `a · (b + c)` derives to a flattened row containing `b`, but the live-path
  universe contains only the whole continuation `b + c`. The proof target
  should use a row/frontier closure over live continuations, introduced as the
  prototype `partial_derivative_live_row_universe`, rather than closing only
  continuation terms.
- The corrected row universe is not a larger accounting burden: checked lemmas
  `rfrontier_path_continuation_subset_path_universe` and
  `partial_derivative_live_row_universe_subset_path` show it is still contained
  in `partial_derivative_path_universe`. Consequently
  `rsizes_distinct_live_row_universe_cubic` and
  `rsizes_rpders_norm17_rows_live_row_universe_cubicI'` reuse the existing
  `2 * (rsize r + 3)^3` bound. The remaining closure premise is now
  `set (rflts (rpder_norm7_list c q)) \<subseteq>
  partial_derivative_live_row_universe r` for reachable/live-row `q`.
- The root must still be normalized. The checked lemma
  `raw_live_row_universe_not_closed_under_norm7` shows the raw expression
  `((0 + a)*)` reaches `a*`, outside its raw live-row universe, while `a*` is
  inside the live-row universe of `rsimp7 ((0 + a)*)`. Future closure lemmas
  should target `rpders_norm17_rows (rsimp7 r) s` or explicitly close under
  normalized images.
- The current 50k cubic-size bounty is for the non-backref fragment only.
  `RBACKREF4`, `RHALF`, and `RRESIDUE` remain excluded from the bounded
  fragment because their payload strings can grow with input, not just regex
  size.
- `rsimp6` is now the first checked star-absorbing redesign prototype. It
  preserves `rsimp5`'s row-product behavior but adds `r* · r* = r*` and
  `(r*)* = r*`, then threads that normalizer through `rpder_norm6_list`,
  `rpd_der_norm6`, `rpder_norm6_rows`, and `rpders_norm16_rows`.
- The immediate motivation is the checked repeated-row counterexample for
  `(a*)*`: without star absorption, `a* · ((a*)* · a*)` escapes the current
  cubic universe. The checked lemma
  `rsimp6_collapses_cubic_counterexample_row` proves that the new normalizer
  collapses precisely that obstruction to `a*`.
- This is still a proof-level prototype. Before claiming the 25k new-definition
  bounty, mirror the normalizer into the annotated `bsimp`/`bders` layer and
  prove the erasure/size transfer facts, or prove the repeated-row cubic
  closure theorem directly for `rpders_norm16_rows`.
- Annotated mirror status: `bsimp6`, `bpder_norm6_list`, `bp_der_norm6`,
  `bpder_norm6_rows`, `bders_pder_norm6`, and `bpders_norm16_rows` now exist
  with checked erasure transfer in `FBound.thy`. This satisfies the structural
  annotated-mirror part of the new-definition work, but it is still not wired
  into `blexer_simp` because erasure/language preservation is weaker than the
  value/bitcode theorem needed for production POSIX matching.
- Do not try to prove closure of `rpders_norm16_rows` inside the old syntactic
  `partial_derivative_cubic_universe r`. The checked lemma
  `reachable_norm6_row_can_leave_current_cubic_universe` refutes it:
  `((0 + a)*) --a--> a*`, and `a*` is not in the old root universe. The next
  closure theorem should be parameterized by `rsimp6 r` or by a universe closed
  under normalized images of subterms and continuations.
- Do not try to prove the all-member one-step premise of
  `rsizes_rpders_norm16_rows_normalized_root_cubicI` either. The checked lemma
  `normalized_root_universe_not_all_q_closed_under_norm6` refutes that stronger
  premise for `((b · b)*)`. The conditional theorem remains useful as an
  interface, but the final proof must strengthen the invariant with reachability
  information or refine the universe to include the specific carried
  continuation chains that reachable rows expose.
- `rsimp6`/`bsimp6` now also absorb `0*` and `1*` to `1`. This removed the
  small-model obstruction where a derivative row became `(1)*`.
- Star absorption is now product-local, not just top-level. `rsimp6_SEQ` uses
  `rsimp6_SEQ_atom` inside `rsimp6_seq_products`, and the annotated mirror uses
  `bsimp6_ASEQ_atom` inside `bsimp6_seq_products`. This matters because
  alternative distribution can create an internal `r* · r*` product even when
  the whole sequence is not syntactically two stars.
- Current sharper target: `partial_derivative_live_path_universe r =
  {0, 1, r} \<union> rpath_continuations r`. The checked theorem
  `rsizes_rpders_norm16_rows_live_path_universe_cubicI` gives a cubic row-size
  bound with the path-universe constant once the live-path closure premise is
  proved. Small-model search found no reachable counterexample up to size 7 and
  depth 7 after the `0*/1*` absorption rule.
- Prefer the rflts-based interface
  `rsizes_rpders_norm16_rows_live_path_universe_cubicI'` over the older
  subterm-based one. A live-path universe is intentionally not closed under all
  syntactic subterms of a row; the exact operation performed by the row driver
  is `rflts`, followed by `rdistinct`.
- The strongest checked candidate is no longer eager `rsimp5` row products.
  `rsimp5` is language-correct, but checked counterexamples show that full
  right-side row-product distribution wants a larger universe than the current
  cubic accounting can justify.
- The current preferred route is the normalized Antimirov row-list driver:
  `rpder_norm_list`, `rpder_norm_rows`, and `rpders_norm1_rows`, mirrored by
  `bpder_norm_rows` in the annotated layer and connected by erasure lemmas in
  `FBound.thy`.
- The accounting target is the combined universe
  `partial_derivative_cubic_universe r =
   partial_derivative_path_universe r union
   partial_derivative_frontier_universe r`. The path side has linear
  cardinality and quadratic member size; the frontier side has quadratic
  cardinality and linear member size. The checked partition lemma avoids the
  quartic bound that would come from multiplying the union cardinality by the
  worst member size.
- New checked closure support:
  `set_rflts_subset_rsubterms_list`,
  `rpder_norm_rows_single_path_subterms_subset`,
  `rsubterms_linear_continuation_subset`, and
  `rsubterms_frontier_universe_member_subset`. These lemmas show where the
  real remaining theorem lives: repeated normalized rows must be shown to stay
  in the original combined universe, or the simplifier must be redesigned so
  that this invariant is structurally obvious.
- Do not claim BR-032/BR-033 completion for wrappers or restatements. A valid
  claim needs a checked new algorithmic definition or the repeated-state
  closure theorem, plus the standard Isabelle/guard run.

## 2026-05-29: Structured proof-shape rule

- Do not start difficult Isabelle proofs by throwing broad `auto` at the whole
  goal. Split first by datatype constructor or inductive case, expose the case
  facts, and keep the goal shape close to the semantic proof idea.
- For production proofs, a single line taking more than about 1-2 seconds is
  already suspect. Prefer a named helper lemma with only the branch-specific
  assumptions over accepting a slow monolithic tactic line.
- If a branch is still complex, make it a named helper lemma with only the
  assumptions needed for that branch. This keeps later repair local and avoids
  burying the invariant inside a giant proof state.
- Use broad automation only after the structure is understood. An early `auto`
  can rewrite, split, or simplify away information in a way that leaves a less
  recoverable goal.
- `Blexer.thy:bder_retrieve_ABACKREF4` follows this rule: the old 16-branch
  `auto` proof was split into prefix, capture, r3-tail, residue-tail, and
  r4-tail retrieve lemmas, then reassembled with explicit nullable cases.

## 2026-05-28: Long-run execution model

- The 4h40m work interval was a single Codex Desktop conversation that kept
  making bounded tool calls, patches, and proof-check attempts. It was not two
  still-running spawned agents.
- A disconnected UI can interrupt the current conversation. Detached CLI/tmux
  loops survive only when they were actually started in tmux or a background
  process group.
- For robust overnight work, prefer the WSL/tmux loop scripts in
  `agent_hunt_pipeline` and keep every proof command under an explicit timeout.
- Human proof-search rule added after the `Blexer.thy:bder_retrieve` slowdown:
  `auto`/`simp`/broad proof search that does not return within roughly 0.5s
  should be treated as the wrong tactic. Split the goal immediately instead of
  letting the command run for tens of seconds.

## 2026-05-28: Why `injval` is `primrec`

- Earlier definitions with nested, overlapping pattern matching made Isabelle's
  function package spend too long on generated obligations and simplification.
- The current direction is to recurse structurally on `rexp` only, and inspect
  the derivative value with local `case` expressions inside each constructor.
- If a proof command around `injval` runs for tens of seconds, split it into
  constructor-specific lemmas instead of adding broader `auto`/`cases` calls.

## 2026-05-28: `RESIDUE` injection invariant

- `injval r c v` maps a value for `der c r` back to a value for `r`; therefore
  the expression and the value differ by exactly the consumed character `c`.
- For `RESIDUE cs rep`, a valid derivative value must be `Residue ds rep` where
  `cs = c # ds`. Injection must reject any mismatched tail or representation.
- This also affects `HALF` and the residue-tail branch of `BACKREF4`; they must
  validate the residue value before reconstructing the original value.

## 2026-05-28: Status of `rep`

- `rep` is currently intended as reconstruction metadata for the original replay
  string, while `cs` is the remaining residue to consume.
- The current language semantics does not use `rep` directly, so the field is
  suspicious unless maintained by explicit proof invariants.
- Short-term policy: keep `rep` only with equality checks during residue
  injection. Deleting it is a separate migration across `RegLangs`, `PosixSpec`,
  `Lexer`, `Blexer`, and the proof scripts.

## 2026-05-28: Current `injval_inj` proof boundary

- `RESIDUE`, `HALF`, BACKREF4 prefix-only, and BACKREF4 prefix/capture
  injectivity have been split into named helper lemmas.
- The remaining direct proof case is BACKREF4 with both `nullable r1` and
  `nullable r2`. Continue by splitting `nullable r3`, then prove tail3,
  residue-tail, and tail4 branch disjointness as small lemmas.
- Do not replace this with a broad `auto` over all value splits; previous runs
  reached 90-200 seconds on that line.

## 2026-05-28: BACKREF4 value-shape guards

- `injval` now rejects malformed BACKREF4 branch values instead of silently
  ignoring stale metadata.
- Prefix branches require the derivative value to carry the same `cs`.
- Capture branches require the derivative value to carry `c # cs`.
- Tail3 branches require the intermediate residue value to be exactly
  `Residue (rev cs) (rev cs)`.
- Tail-residue branches use `inj_residue (rev cs) (rev cs) c res`; the checked
  invariant is `rev cs = c # ds`, hence `cs = rev ds @ [c]`.
- Tail4 is accepted only when `rev cs = []`.

## 2026-05-31: Path9 carried-continuation proof shape

- For the norm19/path9 cubic route, do not try to discharge
  `RSEQ`/`RSTAR`/`RNTIMES` carried branches as whole `map`/`rflts` goals.
- First reduce them to singleton continuation obligations
  `set (rflts [rsimp9 p]) <= parent_universe` using the direct splitter
  lemmas. This keeps each remaining proof tied to one raw
  `rder_path_continuations_acc` member and avoids broad automation over the
  row driver.
- The checked splitters are
  `rpder_norm9_path9_atom_frontier_step_RSEQ_directI`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_directI`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_directI`.

## 2026-05-31: Path9 frontier accounting splitters

- Keep path9 card/member-size accounting constructor-local. For
  `RSEQ`, split the parent frontier into the left carried continuation
  collector and the right child frontier before applying cardinality or size
  bounds.
- For `RSTAR` and nonzero `RNTIMES`, expose the body carried-continuation
  collector directly. The remaining hard work is to bound that collector, not
  to repeatedly unfold `rpath9_atom_frontiers`.
- The checked accounting splitters are
  `card_rpath9_atom_frontiers_RSEQ_le`,
  `card_rpath9_atom_frontiers_RSTAR_le`,
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_le`,
  `rpath9_atom_frontiers_RSEQ_member_sizeI`,
  `rpath9_atom_frontiers_RSTAR_member_sizeI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_sizeI`.

## 2026-05-31: Path9 quadratic card shape

- The path9 frontier cardinality proof should reduce `RSEQ`, `RSTAR`, and
  nonzero `RNTIMES` to a carried-collector product bound:
  `card (rpath9_atom_frontier_acc body carried_k) <=
   rsize body * (rsize parent + 2)`.
- Once that product bound is available, the checked lemmas
  `card_rpath9_atom_frontiers_RSEQ_quadraticI`,
  `card_rpath9_atom_frontiers_RSTAR_quadraticI`, and
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_quadraticI` close the parent
  quadratic inequality.
- When instantiating the sequence arithmetic, use
  `seq_component_product_plus_child_square_le` with
  `algebra_simps`/`power2_eq_square`; plain `simp` does not normalize the
  expanded `rsize (RSEQ _ _)` product enough.

## 2026-05-31: Tail normalization with `RONE`

- Do not use or try to prove the false equality
  `rsimp7_SEQ_atom r RONE = r`.  The useful checked fact is weaker:
  `rsize (rsimp7_SEQ_atom r RONE) <= rsize r`.
- For norm19/path9 carried collectors, the normalized tail form
  `rsimp7_SEQ_atom (rsimp9 r) RONE` is also size-bounded by the original
  `rsize r`. Its frontier cardinality and each frontier member's size are
  bounded by `rsize r`.
- These lemmas should be used when a carried continuation ends in `RONE`;
  they avoid equality shortcuts while still giving the product-bound inputs
  needed by the cubic route.

## 2026-05-31: Carried collector base cases

- The future product-bound induction over `rpath9_atom_frontier_acc` should not
  unfold the zero/one/char cases repeatedly. Keep the base cases as named facts
  and use them directly.
- The checked base facts are `card_rpath9_atom_frontier_acc_RZERO_product`,
  `card_rpath9_atom_frontier_acc_RONE_product`,
  `card_rpath9_atom_frontier_acc_RCHAR_le`,
  `rpath9_atom_frontier_acc_RCHAR_member_size_le`,
  `card_rpath9_atom_frontier_acc_RCHAR_rsimp9_RONE_product`, and
  `rpath9_atom_frontier_acc_RCHAR_rsimp9_RONE_member_size`.
- The `RCHAR` case reduces to `rfrontier k`; for normalized
  `rsimp9 _ . RONE` tails, use the already checked tail-frontier bounds to get
  both product cardinality and member-size bounds.

## 2026-05-31: Carried collector constructor splitters

- The product-bound route now has named local splitters for the carried
  accumulator, not just the top-level `rpath9_atom_frontiers` wrapper.
- `card_rpath9_atom_frontier_acc_RALTS_productI` reduces alternatives to a
  per-child product hypothesis, with `sum_list_map_rsize_mult_right` handling
  the arithmetic. This is the model for the future induction: expose the
  constructor shape, then hand off arithmetic to small named lemmas.
- `card_rpath9_atom_frontier_acc_RSEQ_le`,
  `card_rpath9_atom_frontier_acc_RSTAR_le`, and
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_le` record only the structural
  card split. Their matching member-size lemmas carry an arbitrary bound `N`,
  so later linear-size proofs can reuse them without unfolding the accumulator.

## 2026-05-31: Product-introduction layer for carried collector

- The constructor splitters now have checked product-introduction companions:
  `card_rpath9_atom_frontier_acc_RSEQ_productI`,
  `card_rpath9_atom_frontier_acc_RSTAR_productI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_productI`,
  `card_rpath9_atom_frontier_acc_RBACKREF4_productI`,
  `card_rpath9_atom_frontier_acc_RHALF_productI`, and
  `card_rpath9_atom_frontier_acc_RRESIDUE_product`.
- These lemmas deliberately assume the recursive carried calls already fit the
  same budget `n`. They do not solve the hard budget-selection problem, but
  they remove constructor arithmetic from the later induction.
- Natural-number product goals such as `a*n + b*n <= n + (a+b)*n` need
  `algebra_simps`; keep that explicit rather than relying on plain `simp`.

## 2026-05-31: Normalized nested-tail budget, not associativity

- Do not try to prove syntactic associativity for `rsimp7_SEQ_atom`; even the
  RONE-tail version leaves constructor-specific obligations because `rsimp7`
  may simplify while reassociating.
- The checked facts to use instead are
  `rsize_rsimp7_SEQ_atom_rsimp9_nested_RONE_le`,
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_nested_RONE_le`, and
  `rfrontier_rsimp7_SEQ_atom_rsimp9_nested_RONE_member_size_le`.
- These facts are the budget version of the desired reassociation: the nested
  carried tail `rsimp9 r . (rsimp9 s . 1)` is controlled by the structural size
  of `RSEQ r s`, without requiring the expressions to be syntactically equal.
- The checked `RCHAR` accumulator instances,
  `card_rpath9_atom_frontier_acc_RCHAR_rsimp9_nested_RONE_product` and
  `rpath9_atom_frontier_acc_RCHAR_rsimp9_nested_RONE_member_size`, should be
  used as the base case when the carried collector sees one extra normalized
  sequence layer.

## 2026-05-31: `RSEQ` normalized-tail handoff

- The checked handoff lemmas are
  `card_rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_productI` and
  `rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_member_sizeI`.
- Use them when the parent collector has tail `rsimp7_SEQ_atom (rsimp9 k) RONE`.
  The left child receives the nested tail `rsimp9 r2 . (rsimp9 k . 1)`, while
  the right child keeps the ordinary normalized tail for `k`.

## 2026-05-31: Star and countdown normalized-tail handoffs

- The checked handoff lemmas are
  `card_rpath9_atom_frontier_acc_RSTAR_rsimp9_RONE_productI`,
  `rpath9_atom_frontier_acc_RSTAR_rsimp9_RONE_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_productI`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_member_sizeI`.
- Use these when a star/countdown parent has an already-normalized carried
  tail. They expose the recursive body call with the extra nested tail and
  leave only that body obligation to the future induction.

## 2026-05-31: Budget-compatible handoffs

- The checked variants
  `card_rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_balanced_productI` and
  `rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_balanced_member_sizeI` let the
  right `RSEQ` child use the same `RSEQ r2 k` budget as the left nested-tail
  obligation. This is closer to the desired induction than the earlier stronger
  `rsize k` right-child requirement.
- The checked variants
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_outer_productI`
  and `rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_outer_member_sizeI`
  lift the predecessor countdown budget to the current countdown parent.

## 2026-05-31: Path9 frontier cardinality closed

- The path9 frontier cardinality route now has a checked direct accumulator
  induction:
  `card_rpath9_atom_frontier_acc_le_size_frontier`.
- The key design shift is to bound an accumulator by
  `rsize r * (rsize r + card (rfrontier k))`, not by repeatedly trying to
  normalize or syntactically compare the carried tail. This makes `RSTAR` and
  nonzero `RNTIMES` manageable because the normalized star/countdown tail only
  increases frontier cardinality by one:
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RSTAR_le` and
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RNTIMES_le`.
- The resulting top-level theorem
  `card_rpath9_atom_frontiers_quadratic` proves
  `card (rpath9_atom_frontiers r) <= (rsize r + 2)^2`.
- The relaxed constructor interfaces
  `card_rpath9_atom_frontiers_RSEQ_quadratic_seq_RONEI`,
  `card_rpath9_atom_frontiers_RSTAR_quadratic_seq_RONEI`, and
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_quadratic_seq_RONEI` are checked
  for future handoff proofs that naturally produce an `RSEQ parent RONE`
  budget. Next BR-036 step: prove the matching linear member-size theorem and
  then connect path9 closure to `rpder_norm9_list`.

## 2026-05-31: Path9 cubic hook after cardinality

- The checked theorem
  `rsizes_distinct_path9_atom_frontier_universe_cubic_member_sizeI` packages
  the new `card_rpath9_atom_frontiers_quadratic` result into the cubic
  accounting theorem, so later work no longer needs to pass a cardinality
  premise around.
- The checked row interfaces
  `rsizes_rpders_norm19_rows_path9_atom_frontier_universe_cubic` and
  `rsizes_rpders_norm19_rows_rsimp9_path9_atom_frontier_cubicI` are the
  intended BR-036 landing zone: prove path9 one-step closure and the linear
  member-size premise, then instantiate this hook.

## 2026-06-01: Path9 raw-tail bridge

- Added `rpath9_tail` to represent the normalized continuation carried by
  path9 as a function of the raw continuation syntax. This avoids trying to
  prove arbitrary-tail accumulator member-size facts, which are too broad for
  `RSTAR`/`RNTIMES` because the tail can reintroduce the parent.
- The checked lemmas `rsize_rpath9_tail_le`,
  `rfrontier_rpath9_tail_member_size_le`,
  `rfrontier_rsimp7_SEQ_atom_rsimp9_rpath9_tail_member_size_le`, and
  `rfrontier_rpath9_tail_RSEQ_member_size_le` show that normalized tails and
  their frontier members are bounded by the corresponding raw continuation
  size.
- Added `rfrontier_rsimp7_SEQ_atom_rsimp9_member_size_le` as the generic
  frontier estimate for a normalized left component, plus the `RCHAR` leaves
  `rpath9_atom_frontier_acc_RCHAR_rpath9_tail_member_size_le` and
  `rpath9_atom_frontier_acc_RCHAR_rpath9_tail_RSEQ_member_size_le`. These are
  intentionally small: they give the next induction a clean base case without
  unfolding `rsimp9` or `rpath9_atom_frontier_acc`.
- Added carried-constructor raw-tail handoffs:
  `rpath9_atom_frontier_acc_RSEQ_rpath9_tail_member_sizeI`,
  `rpath9_atom_frontier_acc_RSTAR_rpath9_tail_member_sizeI`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_rpath9_tail_member_sizeI`. Their
  purpose is to keep the recursive member-size induction in raw-continuation
  syntax; `rpath9_tail (RSEQ p k)` is the named form of the expanded
  normalized tail.
- Added the matching top-level raw-tail interfaces
  `rpath9_atom_frontiers_RSEQ_member_size_rpath9_tailI`,
  `rpath9_atom_frontiers_RSTAR_member_size_rpath9_tailI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_size_rpath9_tailI`. These
  facts bridge the public `rpath9_atom_frontiers` constructors to the raw-tail
  induction premises, including the outer `RSEQ ... RONE` continuation shape.
- The checked counterexample
  `rpath9_tail_prefix_continuation_bound_counterexample` shows why the
  continuation-only raw-tail budget cannot be the global induction target:
  a long prefix can leave an internal suffix plus the carried continuation.
  Use the checked parent-budget interfaces
  `rpath9_atom_frontiers_RSEQ_member_size_rpath9_tail_parentI`,
  `rpath9_atom_frontiers_RSTAR_member_size_rpath9_tail_parentI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_size_rpath9_tail_parentI`
  for the remaining top-level member-size proof instead.
- Checked `path9_frontiers_not_subset_norm9_frontier_universe` and
  `path9_frontiers_not_subset_original_frontier_universe`. The first refutes
  dropping unreachable prefixes by normalizing the root (`0.(a.b)` still
  contributes the over-approximation frontier `b`), while the second refutes
  using the original frontier universe after `rsimp9` has normalized a loop
  body (`(1.a)*` contributes `a*`). So the path9 member-size proof must stay
  within the dedicated path9 accounting layer.
- Added the recursive budget layer
  `rpath9_member_budget`/`rpath9_member_budget_list`. The checked theorem
  `rpath9_atom_frontier_acc_rpath9_tail_member_budget` follows the accumulator
  recursion case-by-case, and `rpath9_atom_frontiers_member_budget` exposes the
  top-level `RONE` instance. This is the current bridge between raw-tail
  membership and a later linear arithmetic bound on the budget.
- The raw budget is sound but not tight enough: the checked
  `rpath9_member_budget_nested_star_not_linear` witness shows nested stars
  make it count the raw tail before `rsimp9`/`rsimp7` absorption. The tighter
  budget `rpath9_tight_member_budget` uses `rsize (rpath9_tail k)` at character
  leaves, preserving normalized-tail absorption. Its soundness is checked by
  `rpath9_atom_frontier_acc_rpath9_tail_tight_member_budget` and
  `rpath9_atom_frontiers_tight_member_budget`; the sanity lemma
  `rpath9_tight_member_budget_nested_star_linear_sanity` confirms the nested
  star obstruction is repaired by the tight budget.
- The tight budget has now been related back to the raw budget by
  `rpath9_tight_member_budget_le_member_budget` (and the list helper), so it is
  a verified strengthening of the prior sound budget. The checked witness
  `rpath9_tight_member_budget_nested_star_less_raw` records that this
  strengthening is strict on the nested-star obstruction that defeated the raw
  budget.
- The cubic hook now has a direct tight-budget entry point:
  `rpath9_atom_frontiers_tight_member_budget_linearI`,
  `partial_derivative_path9_atom_frontier_universe_member_size_tight_budgetI`,
  and `rsizes_rpders_norm19_rows_rsimp9_path9_tight_budget_cubicI`. Once the
  single inequality `rpath9_tight_member_budget r RONE <=
  Suc (rsize r + rsize r)` is checked, the path9 universe member-size premise
  for the norm19 cubic row theorem no longer needs to be supplied separately.
- The first tight-budget constructor interfaces are now checked:
  `rpath9_tail_RSEQ_size_le`,
  `rpath9_tight_member_budget_list_boundI`,
  `rpath9_tight_member_budget_RALTS_boundI`,
  `rpath9_tight_member_budget_RSEQ_boundI`,
  `rpath9_tight_member_budget_RSTAR_boundI`, and
  `rpath9_tight_member_budget_RNTIMES_nonzero_boundI`.
  Scratch attempts ruled out two naive proof shapes: direct induction on the
  top-level `RONE` budget leaves carried-continuation cases, while a global
  arbitrary-continuation linear invariant double-counts `RSTAR` bodies. The
  next invariant should be root-owned: continuations must be known to come
  from the same path9 root rather than from an arbitrary `k`.
- The first one-step closure self interfaces are checked:
  `rpder_norm9_path9_atom_frontier_step_RALTS_selfI` and
  `rpder_norm9_path9_atom_frontier_step_RSEQ_selfI`. These are not final
  BR-036 closure theorems, but they remove boilerplate from the global
  induction: alternatives close by child self-closure, and `RSEQ` now handles
  nullable right-child lifting internally. The remaining `RSEQ` blocker is the
  left carried-continuation bridge from
  `rder_path_continuations_acc c r1 (rsimp4_SEQ_atom r2 RONE)` into the
  parent path9 universe.
- The first checked slice of that bridge is
  `rder_path_continuations_acc_RCHAR_left_path9_stable`. It says the `RCHAR`
  left leaf is closed as soon as the carried right tail is norm-tail stable:
  `rsimp9 (rsimp4_SEQ_atom r2 RONE) = rsimp9 r2` and
  `rsimp4_SEQ_atom (rsimp9 r2) RONE = rsimp9 r2`. The checked leaves
  `..._RZERO`, `..._RONE`, `..._RCHAR`, `..._RSTAR`, and `..._RNTIMES`
  discharge the obvious stable constructor cases. Scratch attempts showed
  that a broad associativity lemma for `rsimp7_SEQ_atom` and `rsimp4_SEQ_atom`
  can explode if proved by global `auto`; keep the remaining `RALTS`/nested
  `RSEQ` proof modular and prove only the exact stability facts needed.
- The first reusable stability facts are now checked:
  `rsimp4_SEQ_atom_RONE_stable_rsimp7_SEQ_atom`,
  `rsimp4_SEQ_atom_RONE_stable_rsimp_ALTs`, and
  `rsimp4_SEQ_atom_RONE_stable_rdistinct`. They preserve the invariant
  `rsimp4_SEQ_atom x RONE = x` through the exact constructors used by
  `rsimp9`; this is the next bridge toward proving all normalized right tails
  stable without unfolding the whole simplifier in one proof command.
- The executable Chapter 7 prototype now has the checked erased-language
  theorem `L_bsimpStrong`. The proof was deliberately split through small
  helper lemmas for pruning, flattening, distinctness, and star cases; avoid
  replacing it with broad `auto`/datatype-split commands. This supports the
  stronger-simplification route but is not a POSIX/bitcode proof.
- The path9 closure lane now has universe-parametric carried-continuation
  splitters for `RCHAR`, `RALTS`, `RSEQ`, `RSTAR`, and nonzero `RNTIMES`.
  They are deliberately weaker than the final theorem: each recursive branch
  accepts a local target-universe premise, so future proofs can close the
  root-owned path9 universe case-by-case without a monolithic `auto`.
- The raw `RCHAR` leaf now has a checked path9-tail bridge:
  `rder_path_continuations_acc_RCHAR_path9_tail` sends a raw derivative
  continuation `k` into the normalized frontier tail
  `rsimp7_SEQ_atom (rsimp9 k) RONE`, and
  `rder_path_continuations_acc_RCHAR_raw_left_path9` lifts that base case into
  the parent `RSEQ (RCHAR _) k` universe. This is the right base case for the
  next carried-continuation induction. A scratch nested-`RSEQ` direct theorem
  left dozens of subgoals because the target was too narrow: after
  `rsimp9 (rsimp4_SEQ_atom r k)`, members may be accounted for by the child
  `rpath9_atom_frontier_acc r ...`, not only by the single frontier of
  `rsimp7_SEQ_atom (rsimp9 r) ...`. Future work should generalize to a
  carried set/accumulator theorem rather than forcing one frontier equality.
- The first rpath9-tail carried splitter layer is checked. The useful facts
  are `rsimp7_SEQ_atom_rsimp9_RONE`, `rpath9_tail_rsimp9`,
  `rtail_nf_rpath9_tail`, `rder_path_continuations_acc_RCHAR_rpath9_tail`,
  and the constructor handoff rules
  `rder_path_continuations_acc_RALTS_rpath9_tailI`,
  `rder_path_continuations_acc_RSEQ_rpath9_tailI`,
  `rder_path_continuations_acc_RSTAR_rpath9_tailI`, and
  `rder_path_continuations_acc_RNTIMES_rpath9_tailI`. These mirror the
  existing path9 member-budget recursion: the carried proof obligations for
  sequence, star, and counted repetition are now expressed with
  `rpath9_tail (RSEQ ... k)`. A direct global associativity proof for
  `rsimp7_SEQ_atom` was tried and backed out because it created large
  nested-sequence subgoals. The next bridge should be a small continuation
  relation between the derivative accumulator's `rsimp4_SEQ_atom ... k` and
  the path accumulator's raw spine `RSEQ ... k`.
- The first one-step leaves using those splitters are checked:
  `RSEQ (RCHAR _) _` under stable right tails, `RSTAR (RCHAR _)`, and
  `RNTIMES (RCHAR _) n`. In the counted case, the proof explicitly routes
  through the predecessor-count path9 frontier; do not replace it with a broad
  claim that the whole predecessor universe embeds into the successor universe.
- The `RSEQ` carried-left lane now also covers alternatives whose children are
  all character leaves. The checked bridge lifts
  `rder_path_continuations_acc c (RALTS rs) (rsimp4_SEQ_atom r2 RONE)` into
  the parent path9 universe under the same stable right-tail invariant, and
  packages the `RZERO`/`RONE`/`RCHAR`/`RSTAR`/`RNTIMES` right-tail instances.
  This is useful for the thesis-style left-nested character-alternative cases,
  but general `RALTS` and nested-`RSEQ` carried-left closures are still open.
- The same `RALTS`-of-characters splitter now feeds the loop-body closure
  lane for `RSTAR` and `RNTIMES`. The counted case is slightly different from
  the star case: when the predecessor count is zero, the derivative row is
  `RONE`, so route it through `partial_derivative_path9_atom_frontier_universe`
  directly instead of pretending it came from
  `rpath9_atom_frontier_acc (RALTS rs) ...`.
- Character alternatives are now also packaged through `rsimp_ALTs`, which is
  the actual constructor returned by normalized alternative branches in
  `rsimp9`. The proofs deliberately split the empty, singleton, and
  many-alternative cases; this keeps the normalizer bridge local and avoids a
  broad theorem about arbitrary `rsimp_ALTs` output.
- The bridge has also been pushed one step deeper to the literal
  `rsimp9 (RALTS rs)` expression. For character-only alternatives,
  `map rsimp9`, `rflts`, and `rdistinct` preserve the all-character property,
  so the existing `rsimp_ALTs` packages can be reused on the exact list that
  `rsimp9` constructs. This is the shape later closure proofs should prefer
  when a normalized alternative body appears under `RSEQ`, `RSTAR`, or
  `RNTIMES`.
- Next step: show every `rpath9_atom_frontiers r` member is the frontier of
  such a normalized raw continuation where the raw continuation is either a
  linear continuation or `RSEQ p k` with `p` a subterm and `k` a linear
  continuation. That should discharge the remaining linear member-size premise
  for the path9 cubic hook.
- The first general `rsimp9` right-tail stability layer is checked. The useful
  invariant is not merely `good`/`nonalt`: a non-alt sequence such as a hidden
  `RSEQ RONE r` can still be changed by `rsimp4_SEQ_atom _ RONE`. The new
  proof-only predicate `rtail_nf` records the exact right-associated,
  no-trailing-one normal form preserved by `rsimp4_SEQ_atom`,
  `rsimp7_SEQ_atom`, `rsimp_ALTs`, and `rsimp9`. From it we now have both
  top-level stability
  `rsimp4_SEQ_atom (rsimp9 r) RONE = rsimp9 r` and the corresponding
  `rflts [rsimp9 r]` member stability. This replaces the false generic
  "stable list implies stable flattened list" attempt.
- The right-tail stability layer now feeds the path9 RSEQ closure lane for
  arbitrary normalized right tails. Checked bridges include
  `rder_path_continuations_acc_RCHAR_left_path9_rsimp9`,
  `rder_path_continuations_acc_RCHAR_alt_left_path9_rsimp9`,
  `rder_path_continuations_acc_RALTS_RCHARs_left_path9_rsimp9`,
  `rpder_norm9_path9_atom_frontier_step_RSEQ_RCHAR_rsimp9`,
  `rpder_norm9_path9_atom_frontier_step_RSEQ_RALTS_RCHARs_rsimp9`,
  `rpder_norm9_path9_atom_frontier_step_RSEQ_rsimp_ALTs_RCHARs_rsimp9`, and
  `rpder_norm9_path9_atom_frontier_step_RSEQ_rsimp9_RALTS_RCHARs_rsimp9`.
  This removes the need for separate RZERO/RONE/RCHAR/RSTAR/RNTIMES right-tail
  packages in the character-left and character-alternative RSEQ lane. General
  alternatives and nested `RSEQ` left branches remain the next closure target.
- A checked obstruction now rules out the naive raw-spine path9 bridge for
  general carried continuations. For `(a · a*) · a*`, the carried expression
  `rsimp9 (rsimp4_SEQ_atom (a · a*) a*)` exposes `a · a*`, but the raw parent
  `RSEQ d ((a · a*) · a*)` accounts for `a · (a* · a*)` instead. The checked
  lemmas are `rpath9_tail_rsimp4_SEQ_atom_not_subset_raw_spine` and
  `path9_raw_spine_parent_misses_rsimp7_star_absorption`. Future closure
  attempts should either enlarge the universe with normalized carried tails or
  move to a stronger state simplifier; do not try to prove a plain subset from
  `rpath9_tail (rsimp4_SEQ_atom body tail)` into
  `rpath9_tail (RSEQ body tail)`.
- The first refined carried-tail universe is now checked as `carry9`.
  `rcarry9_atom_frontier_acc` follows `rder_path_continuations_acc` exactly:
  `RSEQ`, `RSTAR`, and nonzero `RNTIMES` use `rsimp4_SEQ_atom` to carry the
  continuation, while `RCHAR` leaves expose `rfrontier (rsimp9 k)`. This gives
  the generic self-step `rpder_norm9_carry9_atom_frontier_step`, so one-step
  normalized partial derivatives of any `legacy_rrexp` land in that regex's
  own carried universe. It also checks
  `carry9_raw_spine_parent_covers_rsimp7_star_absorption`, the positive
  counterpart to the raw-spine obstruction. The remaining work is not another
  one-step bridge but the root-owned theorem: every `q` already in a root
  `partial_derivative_carry9_atom_frontier_universe r` must step back into the
  same root universe, plus the quadratic cardinal and linear member-size
  bounds needed by `rsizes_rpders_norm19_rows_rsimp9_carry9_atom_frontier_cubicI`.
- The fixed `Suc (rsize r + rsize r)` member-size premise for carry9 is now
  known false. `carry9_member_size_two_bound_counterexample` gives a checked
  small star/sequence regex whose carried frontier member exceeds that bound.
  Keep the older fixed-2 hook only as a conditional reference; future carry9
  work should use the parameterized linear-constant interface
  `rsizes_rpders_norm19_rows_rsimp9_carry9_atom_frontier_param_cubicI` and
  prove a concrete constant `K` for member size.
- A deeper checked obstruction shows the parameterized carry9 member-size
  route is probably not the final design either. `carry9_bad_root` is a
  non-backref star/sequence family with checked linear root size
  `rsize_carry9_bad_root = 6*n+2`; `carry9_member_size_eight_bound_counterexample`
  shows that at depth 7 the carry9 witness already exceeds
  `8 * (rsize root + 2)`. Treat carry9 as a useful diagnostic universe that
  repairs the raw-spine omission, but do not spend more proof effort trying to
  tune a small constant. The next route should either add a stronger
  simplifier that collapses this family, or represent carried tails in a
  compact/quotiented way instead of materializing the growing sequence.
- The first proof-level stronger-simplification hook is now checked in
  `GeneralRegexBound.thy`. `rprune_eq_against` and
  `rsimpStrong_prune_pair` mirror the core `bsimpStrong` idea on plain
  `rrexp`: when two rows share an identical continuation
  `RSEQ (RALTS lrs) k` and `RSEQ (RALTS rrs) k`, delete from the later
  row the left alternatives already covered by the earlier row. The language
  theorem `RL_rsimpStrong_prune_pair_shared_suffix` checks this deletion
  without invoking annotated bitcode. The concrete regression
  `thesis_ch7_rstrong_prunes_overlap` captures the Chapter-7 shape
  `(a+b)c + (a+d)c -> (a+b)c + dc` under freshness of `d`; without freshness,
  the later row may correctly collapse even further. This is not yet a
  production simplifier theorem or bounty payout, but it is the first checked
  bound-layer bridge from the carry9 obstruction toward the stronger
  simplifier route.
- The proof-level hook has been extended from one pair to a real multi-row
  simplifier: `rsimpStrong_prune_against_rows`,
  `rsimpStrong_prune_rows_acc`, `rsimpStrong_prune_rows`,
  `rsimpStrong_ALTs`, and `rsimpStrong`. The proof avoids a monolithic
  search step by using small `RALTS` set/order congruence lemmas and explicit
  star cases. `RL_rsimpStrong` proves the simplifier preserves plain
  language, and `RL_rders_simpStrong` proves the derivative loop with
  interleaved `rsimpStrong` still computes `Ders`. The size regression
  `thesis_ch7_rsimpStrong_ALTs_overlap_smaller` confirms the multi-row
  version strictly shrinks the Chapter-7 overlap example. Remaining production
  work is still substantial: integrate the idea with annotated `arexp`
  POSIX/bitcode preservation and prove a general cubic bound rather than only
  language preservation and a local shrink regression.
- The same proof-level simplifier now has checked size control. The key theorem
  is `rsize_rsimpStrong_le`: applying `rsimpStrong` never increases `rsize`.
  Supporting row lemmas (`rsize_rsimpStrong_prune_pair_le`,
  `rsize_rsimpStrong_prune_against_rows_le`,
  `rsizes_rsimpStrong_prune_rows_acc_le`,
  `rsize_rsimpStrong_ALTs_le`) isolate the accounting for pruning, flattened
  alternatives, and duplicate removal. This is a useful cubic-bound checkpoint:
  future derivative-size arguments may state their polynomial in the original
  regex size rather than a potentially inflated strong-normalized size.
- The proof-level strong simplifier is now wired into a one-step
  Antimirov-style row route. `rpder_strong_list` maps `rsimpStrong` over the
  existing `rpder_norm_list`; `rpder_strong_rows` then flattens, prunes
  shared-suffix rows, and removes duplicates. `RLS_rpder_strong_rows` proves
  this one-step row set denotes the derivative, and
  `rsizes_rpder_strong_rows_le` proves its row-size budget is no larger than
  the old normalized row budget. This is the first checked bridge from
  Chapter-7 pruning into the partial-derivative pipeline. The next proof target
  should be a repeated-row closure/cubic interface for `rpders_strong_rows`,
  followed by the annotated `arexp` POSIX/bitcode preservation analogue.
- The repeated-row correctness part of that target is now checked.
  `rpders_strong_rows` iterates `rpder_strong_rows` over an input string, and
  `RLS_rpders_strong_rows` proves it computes `Ders` for legacy/non-backref
  row lists. The necessary preservation lemmas (`legacy_rsimpStrong`,
  `legacy_rpder_strong_rows`, and `legacy_rpders_strong_rows`) show the route
  stays inside the non-backref fragment. The remaining cubic work is now more
  sharply isolated: prove a finite strong-row universe/closure and a polynomial
  row-size bound for `rpders_strong_rows`, then transfer the design to annotated
  `arexp` with POSIX/bitcode preservation.
- The repeated strong-row route now has that conditional finite-universe
  interface checked. `rpders_strong_rows_subsetI` and
  `rsizes_rpders_strong_rows_finite_universe_boundI` deliberately use a
  row-list one-step closure premise
  `set xs <= U ==> set (rpder_strong_rows c xs) <= U`, because
  `rpder_strong_rows` collects all one-step rows before applying
  cross-row pruning. Treating it as a pointwise derivative closure would be
  too weak and would miss the Chapter-7 shared-suffix deletion. The cubic
  hooks `rsizes_rpders_strong_rows_cubic_universe_boundI` and
  `rsizes_rpders_strong1_rows_cubic_universe_boundI` are therefore honest
  conditional interfaces: the remaining work is still to instantiate a
  finite root-owned universe and prove the hard one-step closure, especially
  the carried-continuation cases for `RSEQ`, `RSTAR`, and nonzero `RNTIMES`.
- The old `partial_derivative_path_frontier_universe` route is now explicitly
  marked as a no-go for one-step `rsimp4` derivative closure:
  `current_path_frontier_universe_not_closed_under_rsimp4_derivative` packages
  the middle-alternative witness into a direct non-subset theorem. This is a
  route-management checkpoint, not a negative result about the whole project:
  it says future closure proofs should instantiate the later `path9`,
  `carry9`, or strong-row universes rather than trying to repair the original
  path/frontier universe with a monolithic carried-continuation proof.
- The executable annotated `bsimpStrong` route now has checked size control in
  `FBound.thy`. The key theorem `asize_bsimpStrong_le` proves that the stronger
  annotated simplifier never increases `asize`; helper lemmas isolate the
  accounting for `flts`, `distinctWith`, `prune_eq1_against`, pairwise
  shared-suffix pruning, and the left-to-right row scanner. This is important
  because the earlier `rsize_rsimpStrong_le` result lived in the proof-level
  `rrexp` layer only. The new theorem does not yet prove POSIX/bitcode
  preservation or cubic closure, but it means future annotated transfer work
  can use the stronger Chapter-7 simplifier without paying a hidden size
  increase.
- The annotated strong loop now has erased-language correctness. `RL_rerase`
  first names the basic bridge between annotated erasure and the proof-level
  language skeleton, including a separate `AALTs` helper because `erase` uses a
  binary `ALT` spine while `rerase` uses `RALTS`. The theorem
  `RL_rerase_bders_simpStrong` then proves that `bders_simpStrong` computes
  `Ders` after `rerase`. We intentionally did not force a syntactic equality
  with `rders_simpStrong`: proof-level pruning performs `rflts/rdistinct`
  inside `rsimpStrong_prune_pair`, whereas the annotated executable version
  leaves the equivalent cleanup to the enclosing `bsimpStrong_AALTs`.
- The annotated strong loop also now preserves the legacy/non-backref fragment.
  The theorem `legacy_rerase_bders_simpStrong` says that if the initial
  annotated expression erases to a legacy `rrexp`, every state produced by
  `bders_simpStrong` does too. The proof is intentionally modular: first
  preserve legacy through `flts`, `distinctWith`, `prune_eq1_against`, and
  `bsimp_AALTs`; then through pairwise and row-wise `bsimpStrong` pruning; then
  through the recursive simplifier and derivative loop. This gives future
  cubic-bound statements a stable fragment invariant instead of relying on an
  informal "non-backref only" side condition.
- The proof-level strong-row route now has an annotated executable counterpart.
  `BlexerSimp.thy` defines `bpder_strong_list`, `bpder_strong_rows`,
  `bp_der_strong`, `bpders_strong_rows`, and `bpders_strong1_rows`. The row
  definition mirrors the intended staged pipeline: normalized partial
  derivative rows, `bsimpStrong`, row collection, shared-suffix pruning,
  flattening, and `eq1` duplicate removal. `FBound.thy` proves the key
  semantic bridge `RLS_set_map_rerase_bpders_strong_rows`, plus the one-step
  bridge and legacy preservation lemmas. This does not solve the finite
  universe/cubic closure problem, but it means future annotated bounds can
  target a real row pipeline rather than only the direct `bders_simpStrong`
  loop or the proof-only `rpders_strong_rows` model.
- The annotated strong-row route now also has the finite-universe bookkeeping
  needed for future cubic statements. The new `FBound.thy` lemmas prove that
  `bpder_strong_rows` and its iterated form remain `distinct` after erasure,
  propagate any row-list closure premise over `map rerase`, and transfer the
  proof-level `rsizes_distinct_finite_universe_bound` into an annotated
  `asizes` bound. This keeps the pipeline honest: the hard theorem is still
  the root-owned closure of the chosen universe, but later work no longer has
  to redo the erasure/distinct/cardinality accounting.
- The same annotated bookkeeping is now packaged as cubic hooks. The row-list
  facts `asizes_bpders_strong_rows_cubic_universe_boundI` and
  `asizes_bpders_strong1_rows_cubic_universe_boundI` mirror the proof-level
  `rpders_strong_rows` hooks, while `asize_bp_der_strong_cubic_universe_boundI`
  gives a direct one-step expression bound for `bp_der_strong`. The theorem
  shape deliberately keeps the closure premise explicit; the next real
  research step is still to instantiate a root-owned universe closed under the
  strong row step.
- The proof-level strong-row one-step closure premise is now factored into
  smaller named obligations. `rpder_strong_rows_norm_prune_subsetI` says a
  universe is closed under `rpder_strong_rows` if it covers every
  `rsimpStrong`-normalized member of the underlying `rpder_norm_list` after
  flattening, and if it is preserved by the shared-suffix
  `rsimpStrong_prune_rows` pass. This gives the next root-owned closure proof
  a usable structure: attack normalized derivative members and row pruning
  separately instead of unfolding the whole row pipeline.
- The row-pruning half of that closure premise is now split again. The checked
  lemmas from `rsimpStrong_prune_pair_shared_subsetI` through
  `rsimpStrong_prune_rows_shared_subsetI` isolate the only nontrivial prune
  case: two rows with a common suffix, where the later row is replaced by
  `rsimp7_SEQ_atom (rsimp_ALTs (rdistinct (rflts (rprune_eq_against ...)) {}))
  k`. The row scanner itself is now just induction/bookkeeping. This is the
  right shape for a root-owned universe proof because the Chapter-7 operation
  can be admitted or bounded locally.
- The proof-level route now has a composed conditional cubic hook for that
  shape. `rsizes_rpders_strong_rows_norm_shared_cubic_universe_boundI` takes
  a root-owned universe `U` with three obligations: `U` is closed under
  singleton flattening, every normalized partial-derivative member remains in
  `U` after `rsimpStrong` and flattening, and the isolated shared-suffix
  prune result remains in `U`. Together with finite/cardinality/member-size
  bounds, this yields the repeated-row cubic bound. The remaining research is
  now to instantiate these three obligations for a concrete universe, then
  transfer the same shape through the annotated/bit-coded layer.
- The singleton-flattening obligation is now packaged through row-normal
  conditions. The new `flat_rows` and `row_nf` variants show that a universe
  whose members are non-alt/nonzero, or satisfy `row_nf`, automatically meets
  the flat-closure premise of the composed hook. This removes one bookkeeping
  branch from future root-owned universe instantiations: the universe proof can
  maintain row normal form and spend its effort on the normalized derivative
  and shared-suffix prune cases.
- Row-normality is useful but not sufficient as the whole concrete universe.
  `row_nf_rsimp7_SEQ_atom` shows `rsimp7_SEQ_atom` preserves row-normal rows
  up to `RZERO`, and `row_nf_rflts_singleton` packages singleton flattening.
  However `strong_shared_prune_result_can_leave_row_nf` gives a checked
  obstruction: a shared-suffix prune may build
  `rsimp7_SEQ_atom (RALTS [...]) k`, which is outside strict `row_nf`. Future
  closure work should either enlarge the root-owned universe to include these
  grouped-left rows or prove a stronger local collapse for the prune result;
  do not spend time trying to close the composed hook with `row_nf` alone.
- The first enlargement is now named and checked as `row_group_nf`. This is a
  shape invariant, not the finite universe itself: it admits `RALTS` rows and
  `RSEQ (RALTS ...) k` grouped-left rows in addition to ordinary row-normal
  rows. The checked preservation lemmas are intentionally local:
  `row_group_nf_rflts`, `row_group_nf_normalize`,
  `row_group_nf_rsimp4_SEQ_atom`, `row_group_nf_rsimp7_SEQ_atom`, and
  `row_group_nf_shared_prune_result`. The last lemma is the important prune
  bridge: if the later alternative rows and suffix are grouped-row normal, the
  Chapter-7 shared-suffix replacement is grouped-row normal. Future work should
  refine this into a finite root-owned universe and cardinality/member-size
  proof, rather than using the infinite predicate directly.
- The same grouped-row shape is now preserved by the proof-level strong
  simplifier itself. The pair/prune scanner lemmas
  `row_group_nf_rsimpStrong_prune_pair`,
  `row_group_nf_rsimpStrong_prune_against_rows`, and
  `row_group_nf_rsimpStrong_prune_rows` use the shared-prune bridge above,
  while `row_group_nf_rsimpStrong_ALTs` packages the final normalize step.
  The recursive theorem `row_group_nf_rsimpStrong` is the useful entry point
  for the remaining closure work: after a normalized derivative member is
  shown to have grouped-row shape, `rsimpStrong` will preserve it. What is
  still missing is finite root-owned membership, not shape preservation.
- Shallow `row_group_nf` is not an induction invariant for repeated
  derivatives. It intentionally treats `RSTAR r` and `RNTIMES r n` as
  row-shaped without inspecting `r`, but `rpder_list` exposes those bodies.
  The checked replacement invariant is `row_group_deep_nf`: it implies
  `row_group_nf`, recurses through `RSTAR`/`RNTIMES`, and is preserved by
  `rsimp4_SEQ_atom`, `rsimp7_SEQ_atom`, `rsimpStrong`, `rpder_list`,
  `rpder_norm_list`, `rpder_strong_list`, `rpder_strong_rows`, and
  `rpders_strong_rows`. Use `row_group_deep_nf_rpders_strong_rows` for
  iteration, then project back with `row_group_deep_nf_imp_row_group_nf`.
- `rsimp9` is now the checked entry normalizer from arbitrary roots into
  `row_group_deep_nf`. This matters because raw roots, especially `RNTIMES`
  bodies, need not already satisfy the deep invariant; `rsimp9` recursively
  normalizes those bodies before the strong-row iteration starts. Use
  `row_group_deep_nf_rsimp9`,
  `row_group_deep_nf_rpders_strong1_rows_rsimp9`, and
  `row_group_nf_rpders_strong1_rows_rsimp9` when starting from an arbitrary
  root. This is still only the entry shape guarantee; the remaining hard
  target is a finite root-owned universe with cubic cardinality/member-size
  bounds.
- The shared-suffix prune closure obligation has a checked later-row-local
  form now. Prefer `rsimpStrong_prune_pair_later_shared_subsetI`,
  `rsimpStrong_prune_rows_later_shared_subsetI`,
  `rpder_strong_rows_norm_later_shared_subsetI`,
  `rpders_strong_rows_norm_later_shared_subsetI`, and the corresponding
  finite/cubic hooks when instantiating a concrete universe. These lemmas only
  ask for the Chapter-7 deletion result when the later row
  `RSEQ (RALTS rrs) k` is already in `U`, instead of requiring unconditional
  closure for every synthetic `lrs rrs k`. This is the right obligation shape
  for a root-owned finite universe; do not revert to the older global shared
  premise unless there is a specific reason.
- The Chapter-7 full-cover deletion atom is now checked in both layers. On
  proof-level `rrexp`, use `rprune_eq_against_subset_empty`,
  `rsimpStrong_prune_pair_full_cover`, and
  `rsimpStrong_ALTs_full_cover_shared_suffix`: if every later alternative is
  already in the covered earlier row, the later shared-suffix row is removed.
  On executable `arexp`, use `prune_eq1_against_all_covered_empty` and
  `bsimpStrong_prune_pair_full_cover`, where coverage is stated via
  `eq1_member`. These are the small facts to use when explaining why the
  stronger simplifier actually controls the thesis Chapter-7 overlap family,
  rather than relying only on concrete examples.
- The executable full-cover fact is also available at the actual
  `bsimpStrong_AALTs` surface. `bsimpStrong_AALTs_full_cover_shared_suffix`
  returns `fuse bs earlier_row`, and
  `bsimpStrong_AALTs_full_cover_shared_suffix_Nil` returns the earlier row
  exactly for top-level `[]` bits. Use these when connecting row-prune
  reasoning to `bp_der_strong`/`bpder_strong_rows`, since those definitions
  call the alternative simplifier rather than the pair-prune helper directly.
- The full-cover deletion atom now also has row-output forms for the exact
  data inspected by row derivative definitions. On `rrexp`, use
  `rflts_rsimpStrong_prune_rows_full_cover_shared_suffix` and
  `rdistinct_rflts_rsimpStrong_prune_rows_full_cover_shared_suffix`. On
  `arexp`, use `flts_bsimpStrong_prune_rows_full_cover_shared_suffix` and
  `distinctWith_flts_bsimpStrong_prune_rows_full_cover_shared_suffix`. These
  show that a fully covered later row disappears after pruning, flattening,
  and duplicate removal; they are the facts to reach for when proving
  cardinality decrease or row-count control.
- The same deletion mechanism is now exposed at the real row-derivative
  surfaces. Use `rpder_strong_rows_shared_suffix` and
  `bpder_strong_rows_shared_suffix` when the raw derivative rows flatten to
  `[shared-earlier, shared-later]`; the actual `*_strong_rows` output is then
  the earlier row plus the later row after shared-alternative pruning and
  normalization. Under the full-cover premise, the specializations
  `rpder_strong_rows_full_cover_shared_suffix` and
  `bpder_strong_rows_full_cover_shared_suffix` say the output is exactly the
  earlier row. This avoids a fragile proof style where future bounds reason
  about helper functions but forget to reconnect to the row pipeline that
  `rpd_der_strong` and `bp_der_strong` actually use.
- The matching accounting lemmas are
  `rsizes_rpder_strong_rows_full_cover_shared_suffix` and
  `asizes_bpder_strong_rows_full_cover_shared_suffix`. They expose the same
  full-cover deletion as a one-row size equation, which is the form future
  cardinality/member-size proofs should use when counting the Chapter-7
  overlap family.
- For partial overlap, the reusable accounting atoms are
  `rsize_rsimpStrong_shared_prune_result_le`,
  `rsizes_rpder_strong_rows_shared_suffix_le`,
  `asize_bsimpStrong_shared_prune_result_le`, and
  `asizes_bpder_strong_rows_shared_suffix_le`. These bounds count the actual
  row-derivative output as the earlier shared-suffix row plus the later row
  after covered alternatives have been deleted. This is the form needed for
  examples such as `(a+b+d).c + (a+c+e).c`, where the second row is shrunk but
  not erased.
- Strict shrinkage is now checked too. Use
  `rsizes_rprune_eq_against_lt` / `asizes_prune_eq1_against_lt` to show the
  prune pass removes positive size when it hits a covered alternative, then
  `rsizes_rpder_strong_rows_shared_suffix_lt` /
  `asizes_bpder_strong_rows_shared_suffix_lt` to conclude that the actual
  proof/executable row derivative is smaller than retaining both raw
  shared-suffix rows.
- Do not try to prove a raw syntactic erasure equation for
  `bsimpStrong_prune_pair` against `rsimpStrong_prune_pair`; the current
  definitions normalize the pruned alternatives at different syntactic points.
  The checked bridge is semantic and row-contextual:
  `RL_rerase_bsimpStrong_prune_pair_with_earlier`. Supporting erasure facts
  are `eq1_member_rerase`, `map_rerase_prune_eq1_against`,
  `RL_rerase_bsimpStrong_rsimpStrong`, and
  `RL_rerase_bders_simpStrong_rders_simpStrong`.
- Proof-performance rule reinforced: avoid `then show ... by simp` in
  constructor cases when `then` carries large or irrelevant induction
  hypotheses. In this checkpoint the `RBACKREF4` case of
  `row_group_deep_nf_rpder_list` looped for more than two minutes because the
  simplifier received unused IH facts for the backref fields; the checked fix
  was the plain `show ?case by simp`, since the derivative list is empty.
- The strong-row route now has expression-level shape/size entry lemmas:
  `row_group_deep_nf_rpd_der_strong`,
  `row_group_deep_nf_rpd_der_strong_rsimp9`,
  `row_group_nf_rpd_der_strong`,
  `row_group_nf_rpd_der_strong_rsimp9`, and
  `rsize_rpd_der_strong_cubic`. Use these when a future proof reasons about
  `rpd_der_strong` directly instead of the row list `rpder_strong_rows c [r]`.
  They are glue for the root-owned universe route, not a bounty claim.
- The annotated layer now has the matching one-step size bridge:
  `asizes_bpder_norm_list_cubic` transfers the proof-level
  `rsizes_rpder_norm_list_cubic` theorem through `rerase_bpder_norm_list`, and
  `asize_bp_der_strong_cubic` shows `bp_der_strong` inherits that immediate
  cubic one-step budget. This deliberately stops short of a repeated
  `bpders_strong_rows` cubic theorem; the missing ingredient is still the
  root-owned strong-row closure/cardinality proof.
- The exact syntactic transfer
  `rerase (bsimpStrong_prune_pair earlier later) =
   rsimpStrong_prune_pair (rerase earlier) (rerase later)` is checked-false
  via `bsimpStrong_prune_pair_exact_rerase_counterexample`. The witness has a
  later shared-suffix row with duplicate alternatives: the executable pair
  leaves those duplicates under `bsimp_AALTs`, while the proof-level pair
  normalizes through `rflts/rdistinct` before `rsimp_ALTs`. Keep using the
  semantic union bridge and the row-context facts instead of trying to recover
  exact erasure equality.
- The annotated row-closure route now has local splitter lemmas mirroring the
  proof-level interface:
  `map_rerase_flts_bpder_strong_list_subsetI`,
  `map_rerase_flts_concat_map_bpder_strong_list_subsetI`,
  `map_rerase_bpder_strong_rows_local_subsetI`, and
  `map_rerase_bpder_strong_rows_norm_prune_subsetI`. Use them to reduce future
  `bpder_strong_rows` universe obligations to normalized-member closure and
  shared-suffix prune closure, without attempting a global exact-erasure
  equation for the executable prune.
- The annotated route now also has the later-row-local shared-prune bridge:
  `map_rerase_bsimpStrong_prune_pair_later_shared_subsetI`,
  `map_rerase_bsimpStrong_prune_rows_later_shared_subsetI`,
  `map_rerase_bpder_strong_rows_norm_later_shared_subsetI`,
  `map_rerase_bpders_strong_rows_norm_later_shared_subsetI`, and the matching
  finite/cubic hooks
  `asizes_bpders_strong_rows_norm_later_shared_finite_universe_boundI` /
  `asizes_bpders_strong_rows_norm_later_shared_cubic_universe_boundI`.
  This is the executable analogue of the proof-level later-shared interface,
  but its shared premise is intentionally phrased over the actual
  `bsimpStrong`/`bsimp7_ASEQ_atom` syntax before applying `rerase`; do not
  replace it with a false exact-erasure transfer.
- The path9 frontier route now has carried-tail closure hooks for the
  remaining `RSEQ`/`RSTAR`/nonzero-`RNTIMES` one-step proof shape. The local
  singleton helpers are
  `rder_path_continuations_acc_RSEQ_rpath9_universeI`,
  `rder_path_continuations_acc_RSTAR_rpath9_universeI`,
  `rder_path_continuations_acc_RNTIMES_rpath9_universeI`, plus the explicit
  tail-to-root lifts
  `rpath9_atom_frontiers_seq_left_tail_universe`,
  `rpath9_atom_frontiers_star_body_tail_universe`, and
  `rpath9_atom_frontiers_ntimes_body_tail_universe`. The row-level hooks are
  `rpder_norm9_path9_atom_frontier_step_RSEQ_left_tailI`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_tailI`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_tailI`. Future closure proofs
  should now prove accumulator-local obligations instead of manually lifting
  each carried continuation back into
  `partial_derivative_path9_atom_frontier_universe`.
- The path9 member-size route now has root-linear tight-budget constructor
  hooks:
  `rpath9_tight_member_budget_RALTS_child_root_linearI`,
  `rpath9_tight_member_budget_RSEQ_left_tail_root_linearI`,
  `rpath9_tight_member_budget_RSTAR_tail_root_linearI`, and
  `rpath9_tight_member_budget_RNTIMES_tail_root_linearI`. For the character
  alternative family already used by the closure slices, use
  `rpath9_tight_member_budget_RALTS_RCHARs_tail_le`,
  `rpath9_tight_member_budget_RALTS_RCHARs_root_linear`,
  `rpath9_tight_member_budget_RSTAR_RALTS_RCHARs_root_linear`, and
  `rpath9_tight_member_budget_RNTIMES_RALTS_RCHARs_root_linear`.
- Do not present `rsimp9` as the Chapter-7 overlap-pruning solution.
  `rsimp9` is the root-safe/tail-normalizing/countdown repair. The shared
  suffix example `(a+b)c + (a+d)c` is handled by the stronger
  `rsimpStrong`/`bsimpStrong` row-prune route, which should be the eventual
  production replacement candidate once its POSIX/bitcode and cubic closure
  facts are strong enough.
- CE-driven strong-core reassessment (2026-06-02): the earlier local
  certificate route is not sufficient for exact POSIX values through future
  derivatives. Minimal hand CE:
  `STAR(STAR(ALT(SEQ(STAR(a), ONE), b)))` on `bab`; the unsafe core loses the
  final `b`. Raw derivative injection alone did not reproduce the failure on
  1,000 deterministic random cases, so the culprit is derivative-state
  simplification of nullable expressions, not the first-order `injectA` smoke.
  Current side-conditioned core avoids nullable unit/reassociation/star
  rewrites and passes the hand grid, but random smoke still finds nullable
  `NTIMES(ONE,3)` / `STAR(STAR(ZERO))` failures and the Chapter-7 tree trace
  regresses (`k=5`, n=30: 3674; `k=8`, n=32: 18473). Do not claim this as a
  bounty. The next credible route is smart/certified pruning or generalized
  POSIX values that retain enough history for nullable-star segmentation while
  keeping the strong tree plateau.
- Deferred/generalized-value route (2026-06-02): a promising way to keep the
  thesis `bsimpStrong` tree plateau is to stop decoding ordinary POSIX values
  directly from the simplified derivative state. The Scala smoke
  `strongDeferredValue` uses `bdersStrong` only as an acceptance/small-state
  witness, then reconstructs the exact POSIX value from the original regex and
  consumed string. This passes depth-2 exhaustive smoke, 50k deterministic
  random cases at depth 7/input 8, and keeps the Chapter-7 traces at the
  thesis scale (`k=5`, n=30: 958; `k=8`, n=48: 2963). This is not a bounty
  claim: the remaining work is to replace the Scala `baselineValue` reference
  with a proof-facing deferred reconstruction relation and, eventually, an
  executable reconstruction procedure if runtime matters.
- Strong-memo contract checkpoint (2026-06-03): `bsimpCubic` is no longer the
  active route after the plots; keep it as negative evidence unless a future
  definition beats the thesis baseline and preserves POSIX values. The checked
  route is now: final `bders_simpStrong (intern r) s` tree supplies the small
  nullable gate, while `strong_deferred_span_value` supplies exact POSIX value
  reconstruction. The theorem `strong_deferred_memo_tree_bounded_contract`
  makes the remaining obligation precise: prove a final strong-tree bound
  `asize (...) <= T`, and the contract gives POSIX correctness, `flat v = s`,
  final active rows `<= T`, final active pair-budget `<= T*T`, and the existing
  span/split memo cubic budgets. Future work should attack that final tree or
  an indexed final-active universe; do not optimize emitted `bsimpCubic` trees.
- Final-active closure contract checkpoint (2026-06-03): the proof side now has
  `raw_final_active_suffix_closure` and its lifted
  `strong_deferred_final_active_suffix_closure`. This closure is the active
  shared-prune closure generated by the final strong tree's active suffix rows,
  not the cumulative prefix pool. The checked bridge
  `strong_deferred_memo_tree_bounded_active_closure_contract` reduces the next
  universe step to two obligations: final strong tree `asize <= T` and final
  active row member-size `rsize q <= M`; together they imply closure cardinality
  `<= T + T*T*M`. This is deliberately still conditional infrastructure, but it
  is the shape to instantiate with an indexed/final-active universe.
- Final-active cubic contract update (2026-06-03): the member-size premise for
  final active rows is now discharged by subterm accounting. Raw active rows are
  subterms of the final raw strong tree, and the lifted theorem
  `strong_deferred_final_active_suffix_rows_member_size_le_final_asize` turns
  that into an annotated final-tree bound. Consequently
  `strong_deferred_memo_tree_bounded_active_closure_cubic_contract` states that
  any future final strong-tree bound `asize <= T` directly implies
  `card strong_deferred_final_active_suffix_closure <= T + T*T*T`. The live
  problem is therefore no longer a separate row-size proof; it is the final
  strong-tree/indexed-representation bound while preserving the
  `strong_deferred_span_value` POSIX reconstruction contract.
- Active-suffix POSIX contract update (2026-06-03): the checked theorem
  `strong_deferred_original_raw_row_norm_active_suffix_memo_POSIX_contract`
  is now the most convenient proof-facing statement for the current route.
  Under the active-suffix cubic-universe premises it exposes exact POSIX
  reconstruction, exact failure, `flat v = s`, row-list and raw-row size
  bounds, the row nullable gate, and the span/split memo budgets in one place.
  This is still infrastructure, not a bounty payout, but it prevents future
  work from accidentally proving only language recognition while forgetting
  the POSIX value contract.
- Long-tail smoke update (2026-06-03): regenerated
  `agent_hunt_pipeline/reports/ch7_deferred_memo_grid/` for k=`5,8,10,12`,
  n=`0..200`. The strong memo tree remains thesis-scale: peaks are
  `959`, `3425`, `5940`, and `9686` respectively. Final-active pair budgets
  stay tiny on this family: `17`, `65`, `101`, and `145`. By contrast,
  cumulative active pair-budget still grows with n for k=`8,10,12`, so it
  remains diagnostic only. The final proof should target the final strong tree
  or a quotiented/indexed final-active representation, not the cumulative
  prefix pool.
- Memo-strong decomp gate update (2026-06-04): after reviewing the latest
  plots, emitted-tree `bsimpCubic` is not a proof route. The smoke and CI path
  now gate the proof-facing final-active decomposition metric directly:
  `rows + altNodes + payloadDag + keyDag`. This matches the checked Isabelle
  bridge `card_strong_deferred_final_active_suffix_row_dag_universe_decomp_linearI`.
  Future BR-040 work should either prove linear bounds for these components or
  replace the owner-table representation with an equivalently checked POSIX
  reconstruction theorem. Do not spend effort reducing `bsimpCubic` tree size
  unless a new candidate first beats memo-strong traces and passes exact POSIX
  value smoke.
- Isabelle decomp metric update (2026-06-04): `FBound.thy` now names the same
  final-active decomp metric as
  `strong_deferred_final_active_suffix_decomp_bound` and packages the final
  memo-lexer handoff in
  `strong_deferred_memo_lexer_final_active_decomp_linear_contract`. This makes
  the next proof obligation precise: prove component linear bounds for final
  rows, payload-DAG universe, and suffix-key-DAG universe.
- Closed-root decomp bridge (2026-06-04): added
  `strong_deferred_final_active_suffix_payload_key_dag_universe_subset_closed_root_universe`,
  `strong_deferred_final_active_suffix_decomp_bound_shared_root_boundI`, and
  `strong_deferred_final_active_suffix_decomp_bound_shared_root_linearI`.
  These are the next memo-strong proof bridge after retiring emitted-tree
  `bsimpCubic`: a finite owner/root universe `U` covering payload roots and
  suffix keys and closed under `rsubterms` also covers payload/key DAG nodes.
  Because the current decomp metric sums payload-DAG and key-DAG cardinalities
  separately, the checked bound is `2 * rows + 2 * card U`, not
  `2 * rows + card U`. Use this bridge when proving the memo strong tree
  cubic interface; use a separate component-union theorem only if the metric is
  explicitly changed and connected back to exact POSIX reconstruction.
- Component-union owner metric (2026-06-04): added the Isabelle-side
  `strong_deferred_final_active_suffix_component_union`, matching the Scala
  `componentUnionSize` metric. The checked lemmas
  `card_strong_deferred_final_active_suffix_row_dag_universe_le_component_union`
  and
  `card_strong_deferred_final_active_suffix_component_union_closed_root_linearI`
  make the hash-cons owner-table target precise: a finite `rsubterms`-closed
  owner/root universe covering final-active payload roots and suffix keys
  bounds the component union by `2 * rows + card U`, while the older decomp
  metric still separately sums payload/key DAG sizes. The smoke pipeline now
  has `POSIX_SMOKE_STRONG_FINAL_ACTIVE_COMPONENT_UNION_FACTOR`; default CI
  gates row-DAG universe, component union, and decomp bound at factor 3 on the
  strong-memo route. The full local CI passed with exact POSIX value smoke,
  `Posix`, and `BackRefPilot`.
