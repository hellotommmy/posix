# Backreference Pilot Bounties

This is the competitive-collaborative bounty board for the POSIX backreference
formalization pilot. It follows the Agent Hunt bounty mechanics: agents compete
for theorem bounties but are incentivized to collaborate.

Amounts are in simulated USD. A payout is valid only when the named artifact
exists, the guards pass, and the required Isabelle CI session succeeds.

Admin policy update: wrapper-only theorem packages do not count as bounty
deliverables. Summary/cases/iff/same/retrieve-equality facts may remain as API
convenience lemmas, but future bounty claims must introduce a new semantic or
algorithmic layer, or a nontrivial proof bridge needed by later work.

See `agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md` for the
full rules including locking, sub-bounties, effort estimates, and statement
immutability.

## Pool

| Category | Amount |
| --- | ---: |
| Total pool | 150,000 |
| Allocated (active + completed) | 149,090 |
| Collected (paid out) | 74,970 |
| Reserved (unallocated) | 910 |

## Agent Balances

| Agent | Role | Balance | Notes |
| --- | --- | ---: | --- |
| Codex | Admin/Worker | 67,750 | Completed BR-001 through BR-004, BR-006 through BR-010, BR-015 through BR-022, BR-032, BR-035 |
| Opus | Worker | 6,200 | Completed BR-005, BR-011, BR-012, BR-013, BR-014; BR-015 lock released when Cursor was retired |
| MergeSteward | Steward | 0 | Integration role |
| Alice | Worker | 0 | Optional future worker |
| Bob | Worker | 0 | Optional future worker |

## Active

| ID | Task | Bounty | Est. Lines | Difficulty | Est. USD | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |
| BR-023 | Original-file migration TODO audit | 120 | 30 | 3 | 120 | OPEN | - | RegLangs.thy;PosixSpec.thy;Lexer.thy;LexerSimp.thy;Blexer.thy;BlexerSimp.thy;BasicIdentities.thy;GeneralRegexBound.thy;ClosedForms.thy;ClosedFormsBounds.thy;FBound.thy | AdminReview | Small planning bounty only; no theorem payout until admin approves direct original-file implementation |
| BR-024 | Migrate backref4 language semantics into original RegLangs | 1,400 | 120 | 8 | 1,400 | OPEN | - | RegLangs.thy:backref_lang4,nullable_correctness,der_correctness,ders_correctness | Isabelle:Posix | Direct `rexp/L/nullable/der/ders` extension with BACKREF4/HALF/RESIDUE; no brexp/gbrexp wrappers |
| BR-025 | Migrate backref values and POSIX rules into original PosixSpec | 1,800 | 180 | 9 | 1,800 | OPEN | - | PosixSpec.thy:L_flat_Prf,LV_finite,Posix_determ,Posix_LV | Isabelle:Posix | Direct `val/flat/Prf/LV/Posix` extension; no bval/bval4/gbval wrappers |
| BR-026 | Migrate backref injection and lexer correctness into original Lexer | 1,400 | 140 | 9 | 1,400 | OPEN | - | Lexer.thy:Prf_injval,Posix_injval,lexer_correctness,Prf_flex | Isabelle:Posix | Direct `mkeps/injval/lexer/flex` extension after BR-024/025 |
| BR-027 | Migrate backref bitcoded lexer into original Blexer | 1,800 | 170 | 9 | 1,800 | OPEN | - | Blexer.thy:erase_bder,retrieve_code,bmkeps_retrieve,bder_retrieve,MAIN_decode,blexer_correctness | Isabelle:Posix | Direct `bit/arexp/code/decode/retrieve/bder/blexer` extension; no bbit/barexp/gabexp wrappers |
| BR-028 | Preserve aggressive original BlexerSimp for backrefs | 1,400 | 140 | 9 | 1,400 | OPEN | - | BlexerSimp.thy:rewrites_to_bsimp,rewrite_preserves_bder,central,main_blexer_simp,blexersimp_correctness | Isabelle:Posix | Must use original rewrite-system route; weak structural simplifier or wrapper equality does not count |
| BR-029 | Add backref closed-form families in original closed-form machinery | 1,200 | 160 | 9 | 1,200 | OPEN | - | BasicIdentities.thy;ClosedForms.thy:backref4_closed_form,half_closed_form,residue_closed_form | Isabelle:Posix | Decide rexp vs temporary rrexp, then add real BACKREF4/HALF/RESIDUE closed-form coverage |
| BR-030 | Close original bounds after backref migration | 1,000 | 120 | 8 | 1,000 | OPEN | - | GeneralRegexBound.thy;ClosedFormsBounds.thy;FBound.thy:finite_size_n,rders_simp_bounded,annotated_size_bound | Isabelle:Posix | Final boundedness through original theorem chain; BackRefBoundedBlueprint wrappers do not count |
| BR-031 | Cubic non-backref size-bound blueprint | 5,000 | 120 | 8 | 5,000 | OPEN | - | PROGRESS_BACKREF.md;BasicIdentities.thy;ClosedFormsBounds.thy;FBound.thy | AdminReview | State the cubic target, fragment invariant, and Antimirov-style frontier plan; no theorem payout for wrapper-only restatements |
| BR-033 | Prove partial-derivative universe cubic bound | 12,000 | 300 | 10 | 12,000 | OPEN | - | GeneralRegexBound.thy:partial_derivative_path_universe,partial_derivative_live_row_universe,rfrontier_path_continuation_subset_path_universe,partial_derivative_live_row_universe_subset_path,rsizes_distinct_live_row_universe_cubic,rsizes_rpders_norm17_rows_live_row_universe_cubic,raw_live_row_universe_not_closed_under_norm7 | Isabelle:Posix | Replace `card(sizeNregex N)` reasoning with a finite universe generated from subterms/continuations of the original non-backref regex; corrected live-row accounting is checked and inherits the path-universe cubic bound; remaining work is the normalized-root live-row one-step closure for `rpder_norm7_list` |
| BR-034 | Transfer cubic bound to annotated lexer states | 8,000 | 260 | 10 | 8,000 | OPEN | - | FBound.thy:asize_bp_der_norm_cubic,RL_rerase_bders_pder_norm,rpders_norm1_rows_rerase,annotated_size_bound_cubic_nonbackref | Isabelle:Posix | Final non-backref theorem for normalized row-list `bpders_norm1_rows`/future production `bsimp`; backref constructors explicitly excluded from the fragment |
| BR-038 | Cubic smoke and counterexample suite | 6,000 | 120 | 8 | 6,000 | OPEN | - | agent_hunt_pipeline/scala/PosixCubicSmoke.scala;agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1;FBound.thy:thesis_cubic_smoke_A_shared_suffix,thesis_cubic_smoke_B_ch7_three_star,thesis_cubic_counterexample_C,thesis_cubic_counterexample_D,thesis_cubic_counterexample_E,thesis_cubic_counterexample_F,thesis_cubic_counterexample_G,thesis_cubic_counterexample_H | ScalaSmoke+Isabelle:Posix | Build a smoke suite before any new cubic proof attempt. Scala owns broad grids/enumeration and exact POSIX value comparisons; Isabelle owns compact proof-facing sanity facts. A is `(a+b)c + (a+d)c`; B is the thesis Chapter 7 three-star family. No proof bounty may depend on a simplifier that fails this suite. |
| BR-039 | Define smoke-tested memo-strong-tree candidate | 25,000 | 260 | 10 | 25,000 | OPEN | - | agent_hunt_pipeline/scala/PosixCubicSmoke.scala:StrongDeferredMemo;agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1;FBound.thy:strong_deferred_span_value,strong_deferred_span_value_THE_lexer,strong_deferred_memo_budget,strong_deferred_original_raw_row_norm_closed_memo_cubic_interface | ScalaSmoke+Isabelle:Posix | Main route is now `bsimpStrong` as the small recognition tree plus original-regex span/memo POSIX value reconstruction. Default smoke route is `strong-memo`, which checks exact POSIX values and Chapter 7 memo traces. `bsimpCubic` emitted-tree work is historical/negative evidence after the graphs; do not optimize it further unless a future candidate beats the thesis baseline and preserves POSIX values. |
| BR-040 | Prove memo-strong-tree POSIX and cubic interface | 8,000 | 180 | 9 | 8,000 | OPEN | - | FBound.thy:strong_deferred_span_value_iff_lexer,strong_deferred_memo_exact_value_budget,strong_deferred_original_memo_budget,strong_deferred_original_raw_row_norm_closed_memo_cubic_interface,strong_deferred_original_raw_row_norm_same_suffix_memo_cubic_interface,strong_deferred_original_raw_row_norm_active_suffix_memo_cubic_interface,strong_deferred_original_raw_row_norm_active_suffix_memo_POSIX_contract,strong_deferred_original_sizeNregex_memo_cubic_interface;GeneralRegexBound.thy:rflts_sizeNregex_closed,raw_shared_prune_closed,raw_shared_prune_pair_closure,raw_shared_prune_suffix_key,raw_shared_prune_same_suffix_pairs,raw_shared_prune_suffix_bucket,raw_shared_prune_same_suffix_closure,raw_shared_prune_closed_iff_same_suffix_closure_subset,card_raw_shared_prune_same_suffix_closure_member_bucket_bound,raw_shared_prune_active_suffix_keys,raw_shared_prune_active_suffix_bucket,raw_shared_prune_active_suffix_pairs,raw_shared_prune_active_suffix_closure,raw_shared_prune_active_suffix_pair_budget,raw_shared_prune_active_suffix_keys_mono,raw_shared_prune_active_suffix_bucket_mono,raw_shared_prune_active_suffix_pairs_mono,raw_shared_prune_active_suffix_closure_mono,raw_shared_prune_active_suffix_pair_budget_mono,raw_shared_prune_active_suffix_pair_budget_bucket_bound,raw_shared_prune_closedI_active_suffix_closure_subset,card_raw_shared_prune_active_suffix_pairs_le_pair_budget,card_raw_shared_prune_active_suffix_closure_pair_budget_bound,card_raw_shared_prune_active_suffix_closure_member_bucket_bound,card_raw_shared_prune_active_suffix_closure_member_pair_budget_bound,card_raw_shared_prune_active_suffix_closure_member_pair_budget_card_bound,path9_atom_frontier_not_raw_shared_prune_closed,carry9_atom_frontier_not_raw_shared_prune_closed,raw_shared_prune_bad_result_in_path9_pair_closure,raw_shared_prune_bad_result_in_carry9_pair_closure,raw_shared_prune_bad_result_in_path9_same_suffix_closure,raw_shared_prune_bad_result_in_carry9_same_suffix_closure,rsizes_rpders_strong1_rows_raw_norm_same_suffix_cubic_universe_boundI | Isabelle:Posix | Prove the checked handoff from the smoke-tested `StrongDeferredMemo` route to a concrete cubic raw/shared universe. Already checked: exact POSIX value extraction from the strong nullable gate plus span/memo table, POSIX/lexer equivalence, nullable recognition gate, quadratic memo-state budget, cubic split-probe budget, conditional row-universe interface, direct active-suffix POSIX contract, and a concrete `sizeNregex N` finite-universe fallback. Also checked-false: directly reusing current path9/carry9 atom-frontier universes for raw strong shared-prune closure; one-step same-suffix closure captures the missing row-difference witness without opening arbitrary global pairs. Current preferred proof contract is `strong_deferred_original_raw_row_norm_active_suffix_memo_POSIX_contract`; latest accounting removes the broad `None` suffix bucket and now exposes the sharper aggregate active pair-budget bridge `card U + P * M`, with key/max-bucket accounting retained as a fallback. |

## Retired / Revoked

| ID | Task | Former Bounty | Status | Date | Reason |
| --- | --- | ---: | --- | --- | --- |
| BR-036 | Close rsimp8/rsimp9 live-row cubic closure | 15,000 | DROPPED | 2026-06-02 | Revoked by admin: proof-first `rsimp9` route failed the smoke-test discipline and must not pay out. Existing lemmas remain historical technical evidence only. |
| BR-037 | Transfer root-safe cubic theorem to annotated lexer | 10,000 | DROPPED | 2026-06-02 | Revoked by admin: old root-safe transfer route is retired until a new simplifier passes A/B/C/D/E/F smoke tests. |

## Open Artifact Notes

- Empty final-active budget bridge: `GeneralRegexBound.thy` and `FBound.thy`
  now check that if the final-active row set is empty, then its row-DAG
  universe is empty and the corresponding key, pair-budget, and max-row-DAG
  metrics are zero. This records the route decision after the graphs:
  emitted-tree `bsimpCubic` is negative evidence, and the active target is
  memo strong tree plus exact POSIX reconstruction and final-active row-DAG
  accounting. This is infrastructure only; no bounty is claimed.
- Final raw DAG handoff: `FBound.thy` now checks
  `strong_deferred_final_raw_dag_size_empty_le_rxsize`,
  `strong_deferred_final_raw_dag_size_singleton_le_rxsize_square`, and
  `strong_deferred_original_final_raw_dag_linear_contract`. This lets BR-040
  target a linear bound on the whole final memo-strong exact DAG
  (`strongMemoDag` in Scala terms), and then obtain exact POSIX reconstruction
  plus all final-active budgets. Follow-up smoke shows small whole-DAG
  constants are not the preferred path: factor `3.0` has a CE with
  `rsize=15`, `strongDag=48`, and `finalRows=0`. Keep final-active row-DAG
  universe as the primary BR-040 target. Infrastructure only; no bounty is
  claimed.
- Memo-strong one-step row-DAG base: `FBound.thy` now checks
  `asize_bder_intern_legacy_le_rxsize_square` and
  `card_strong_deferred_final_active_suffix_row_dag_universe_singleton_le_rxsize_square`.
  This extends the active BR-040 row-DAG universe evidence from empty input to
  one consumed character for legacy roots. It is infrastructure only; no bounty
  is claimed until the arbitrary-input row-DAG/cubic theorem is checked.
- Raw strong normal-form preservation checkpoint: `GeneralRegexBound.thy` now
  checks `row_group_deep_nf_rsimpStrong_raw` through the raw shared-prune
  machinery, and `FBound.thy` lifts it as
  `row_group_deep_nf_rerase_bsimpStrong`. The follow-up derivative-step and
  loop invariants are also checked:
  `row_group_deep_nf_rsimpStrong_raw_rder`,
  `row_group_deep_nf_rerase_bsimpStrong_bder`, and
  `row_group_deep_nf_rerase_bders_simpStrong`. This supports BR-039/BR-040
  but is infrastructure only; no payout is claimed.
- Final-active normal-form bridge: checked
  `legacy_rrexp_rsubterms`, `row_group_deep_nf_legacy_rsubterms`,
  `row_group_deep_nf_strong_deferred_final_raw_nonempty`, and the corresponding
  final-active row/key lemmas. Future BR-040 row-count/member-size proofs can
  now reason directly about deep-normal rows and suffix keys extracted from
  `strong_deferred_final_raw`; this is infrastructure only and claims no
  bounty.
- Final-active row element handles: checked raw and lifted lemmas now expose
  legacy/deep-normal facts for final-active rows, suffix keys, active buckets,
  row-list elements, and row keys. This is the proof-facing entry point for
  the remaining row/member-size bound, but still infrastructure only and no
  bounty is claimed.
- Final-active row subterm/size handles: checked raw and lifted lemmas now
  expose row payloads and row keys as subterms of the final memo-strong raw
  tree, with size bounded by final `rsize`/`asize`. This supports reconstruction
  and future indexed-universe accounting, but the latest Scala scout rejects
  raw row-member tree size as the final linear metric: member factors `1`, `2`,
  and `3` all have counterexamples, while the same cases often have compact
  strong DAGs. Future BR-040 work should target a hash-consed/member-DAG or
  indexed/quotiented final-active universe preserving POSIX values.
- Final-active member-DAG smoke checkpoint: `PosixCubicSmoke.scala` now reports
  exact DAG and shape-DAG sizes for final-active row members, and
  `scala_cubic_smoke.ps1` exposes `-StrongFinalActiveMemberDagFactor` and
  `-StrongFinalActiveMemberShapeDagFactor`. A seed-`20260602` scout with
  rows/pair factors `1.0`, raw member disabled, and DAG/shape-DAG member
  factors `2.0` found no CE in 5,000 random depth-6/input-8 cases. This is
  evidence and tooling for BR-038/BR-039/BR-040, not a bounty payout.
- Isabelle row-DAG universe checkpoint: `GeneralRegexBound.thy` now defines
  `raw_final_active_suffix_row_dag_universe`, and `FBound.thy` lifts it as
  `strong_deferred_final_active_suffix_row_dag_universe`. Checked lemmas show
  every final-active row's exact-DAG cardinality `card (rsubterms q)` is
  bounded by this universe, with final-rsize/final-asize fallback bounds. The
  remaining BR-040 proof target is an original-size bound for this universe
  plus the POSIX reconstruction bridge; no payout is claimed here.
- Row-DAG eliminator checkpoint: checked
  `raw_final_active_suffix_row_dag_universeE` and
  `strong_deferred_final_active_suffix_row_dag_universeE`. These expose any
  row-DAG node as a subterm of a concrete final-active `RSEQ (RALTS rows) k`,
  giving the next structural handle for a root-owned row/DAG universe proof.
  The same checkpoint reran strong-memo smoke and the final-active scout; it
  remains infrastructure only and claims no BR-039/BR-040 payout.
- Final raw DAG metric bridge: checked
  `strong_deferred_final_raw_dag_size`,
  `card_strong_deferred_final_active_suffix_row_dag_universe_le_final_raw_dag_size`,
  and `strong_deferred_final_raw_dag_bound_to_row_dag_universe_bound`.
  This connects a future `strongMemoDag`-style exact-DAG bound for the whole
  memo-strong final recognition tree to the row-DAG universe contract. The
  Chapter 7 report was refreshed for `k=5,8,n<=64`, with `strongMemoDag`
  `72/133` and final max row-DAG `31/61` at `n=64`. This is BR-040
  infrastructure only, not a payout.
- Whole-DAG budget scout: `scala_cubic_smoke.ps1` now exposes
  `-FindStrongMemoDagBudgetCE`, `-StrongMemoDagFactor`, and
  `-StrongMemoDagMinRegexSize`. The scout found no whole-final-DAG CE for
  factors `4` and `3` on recent random grids, but factor `2` shrinks to
  `STAR(NTIMES(STAR(CH(b)),2))` on input `bb` with correct POSIX value
  preservation. Therefore whole-final-DAG constants are diagnostics only; the
  active BR-040 proof target remains the final-active row-DAG universe and its
  POSIX reconstruction contract. No bounty is claimed.
- Final-active route refresh: the default
  `strong_memo_final_active_scout.ps1` three-seed run still finds no CE for
  rows `1.0 * rsize`, pair budget `1.0 * rsize^2`, and exact-DAG/shape-DAG
  member budgets `2.0 * rsize` across seeds `20260602,20260603,20260604`,
  `5,000` cases each at depth `6`, input length `8`. The Chapter 7 comparison
  was refreshed to `n<=80`; final-active max row-DAG stays at `31/61` for
  `k=5/8`. Smoke evidence only; no payout.
- Single row-DAG linear handoff: checked
  `FBound.thy:strong_deferred_original_final_active_single_row_dag_linear_contract`.
  This packages the current BR-040 proof target as one obligation,
  `card strong_deferred_final_active_suffix_row_dag_universe <= K * rxsize r`,
  and then supplies exact POSIX reconstruction plus final rows, pair budget,
  max row-DAG, and row-member exact-DAG budgets. It is proof infrastructure
  only; the original-regex-owned universe bound remains open and no bounty is
  claimed.
- Empty row-DAG base case: checked
  `FBound.thy:card_strong_deferred_final_active_suffix_row_dag_universe_empty_le_rxsize`.
  This proves the single row-DAG universe obligation for empty input with
  `K = 1`, using `bders_simpStrong (intern r) [] = intern r` and
  `rsize (rerase (intern r)) = rxsize r`. It is a real base case for a future
  input-induction proof, but BR-040 remains open and no payout is claimed.
- Row-DAG POSIX handoff checkpoint: checked legacy/deep-normal closure facts
  for the row-DAG universe, plus
  `strong_deferred_memo_tree_value_final_active_row_dag_interface` and
  `strong_deferred_original_final_active_row_dag_linear_contract`. These
  connect a future `K * rxsize r` row-DAG universe bound to exact memo-strong
  POSIX reconstruction and per-row exact-DAG bounds. This narrows BR-040's
  remaining proof obligation but does not itself prove the original-size
  universe bound, so no bounty is claimed.
- Row-DAG finite-universe handoff checkpoint: checked
  `raw_final_active_suffix_row_dag_universe_closed_subsetI`,
  `card_raw_final_active_suffix_row_dag_universe_boundI`, their lifted
  `strong_deferred_*` versions, and
  `strong_deferred_original_final_active_row_dag_finite_universe_contract`.
  The current BR-040 target is therefore not final-tree size accounting, but a
  finite original-regex universe `U` that covers final-active rows, is closed
  under `rsubterms`, and has `card U <= K * rxsize r`. This is still
  infrastructure only and claims no payout.
- Two-universe row-DAG handoff checkpoint: checked
  `card_strong_deferred_final_active_suffix_rows_boundI`,
  `strong_deferred_final_active_suffix_pair_budget_le_bound_square`, and
  `strong_deferred_original_final_active_row_dag_two_universe_contract`.
  Future BR-040 work may separately construct a tight `RowU` for row/pair
  accounting and a closed `DagU` for hash-consed exact-DAG nodes. This keeps
  the memo-strong route aligned with the smoke evidence; no payout is claimed.
- Row-closure DAG handoff checkpoint: checked
  `GeneralRegexBound.thy:rsubterm_closure` with finite/closed/cardinality
  lemmas and
  `FBound.thy:strong_deferred_original_final_active_row_dag_row_closure_contract`.
  The next BR-040 target can focus on a single original-regex-owned `RowU`;
  `DagU` can be instantiated as `rsubterm_closure RowU`. This is still
  infrastructure only and claims no payout.
- Metric-facing row handoff checkpoint: checked
  `FBound.thy:strong_deferred_original_final_active_row_metrics_contract`.
  This is the proof-side version of the Scala final-active row metrics: it
  uses the actual final-active row set, assumes row count `R` and per-row
  exact-DAG size `M`, then yields exact POSIX reconstruction plus pair and
  row-DAG budgets. It narrows BR-040's target but does not prove the
  original-regex-owned `R`/`M` bounds, so no payout is claimed.
- Scalar max-row-DAG handoff checkpoint: checked
  `FBound.thy:strong_deferred_final_active_suffix_max_row_dag` and
  `FBound.thy:strong_deferred_original_final_active_max_row_dag_metrics_contract`.
  This makes the BR-040 proof target match the Scala metric `finalMaxRowDag`
  directly. It is infrastructure only and claims no payout.
- Row-DAG universe to max-row-DAG bridge checkpoint: checked
  `GeneralRegexBound.thy:raw_final_active_suffix_max_row_dag_le_row_dag_universe`,
  `FBound.thy:strong_deferred_final_active_suffix_max_row_dag_le_row_dag_universe`,
  and
  `FBound.thy:strong_deferred_original_final_active_row_dag_universe_metrics_contract`.
  This shows a future row-DAG universe bound is enough to control the scalar
  `finalMaxRowDag` metric. Infrastructure only; no payout is claimed.
- Max-row-DAG fallback checkpoint: checked
  `GeneralRegexBound.thy:raw_final_active_suffix_max_row_dag_le_rsize` and
  `FBound.thy:strong_deferred_final_active_suffix_max_row_dag_le_final_asize`.
  This connects the scalar metric to existing final-tree fallback accounting;
  it is not an original-size theorem and claims no payout.
- Single row-DAG universe contract checkpoint: checked
  `raw_final_active_suffix_rows_subset_row_dag_universe`,
  `strong_deferred_final_active_suffix_rows_bound_by_row_dag_universeI`, and
  `strong_deferred_original_final_active_single_row_dag_universe_contract`.
  This reduces BR-040's accounting interface to one future universe bound.
  Infrastructure only; no payout is claimed.
- Row-DAG decomposition checkpoint: checked
  `raw_final_active_suffix_row_dag_universe_eq_rsubterm_closure`,
  `strong_deferred_final_active_suffix_row_dag_universe_eq_rsubterm_closure`,
  and
  `card_strong_deferred_final_active_suffix_row_dag_universe_le_rows_times_max`.
  This exposes the factorization `row-DAG <= finalRows * finalMaxRowDag`.
  Infrastructure only; no payout is claimed.
- Final-active DAG scout checkpoint: `strong_memo_final_active_scout.ps1`
  now defaults to the metric that BR-040 actually needs: exact-DAG and
  shape-DAG member budgets `2.0 * rsize`, with raw member tree size disabled
  as a failing gate. The default three-seed scout passes with no CE; the
  strongest seed-`20260602` witness has raw member ratio `5.633333` but
  exact-DAG/shape-DAG ratio `1.266667`. This supports the memo/hash-consed
  route and claims no payout.
- Strong `NTIMES` body-normalization checkpoint: `bsimpStrong` now recurses
  into `ANTIMES` bodies, mirrored by `rsimpStrong(_raw)` and the Scala smoke
  model. Checked entry lemmas include
  `row_group_deep_nf_rerase_bsimpStrong_legacy`,
  `row_group_deep_nf_rerase_bders_simpStrong_bsimpStrong_intern`, and
  `row_group_deep_nf_rerase_bders_simpStrong_intern_nonempty`. This removes a
  proof-route precondition but remains BR-039/BR-040 infrastructure only.
- Chapter 7 plotting side task: `agent_hunt_pipeline/scripts/ch7_size_grid.ps1`
  now generates CSV and SVG plots under
  `agent_hunt_pipeline/reports/ch7_size_grid/`, using the Scala smoke model as
  the source of truth. The current default grid compares thesis-style
  `strongTree`, current `cubicTree`, `sharedShapeStatePool`, and
  `langContPruneShapeStatePool` for `k=1..8,n=0..30`. This is BR-038
  visualization/tooling only. It shows current `cubicTree` is not yet as
  strong as thesis Chapter 7 ordinary tree simplification: at `k=5,n=30`,
  `strongTree=958` versus `cubicTree=3245`; at `k=8,n=30`, `strongTree=2747`
  versus `cubicTree=7587`.
- Deferred memo route evidence: the same plotting infrastructure now supports
  `strongMemoTree`, memo-state, and memo-probe metrics, with the report
  `agent_hunt_pipeline/reports/ch7_deferred_memo_grid/`. The dedicated command
  is `agent_hunt_pipeline/scripts/ch7_deferred_memo_grid.ps1`; it also plots
  active-suffix proof-contract metrics (`strongMemoActiveRows`,
  `strongMemoActiveKeys`, `strongMemoActiveMaxBucket`,
  `strongMemoActivePairBudget`). On the default
  `k=1..8,n=0..30` grid, `strongMemoTree` preserves the thesis-style tree
  line (`958` at `k=5,n=30`, `2747` at `k=8,n=30`) while the memo table is
  modest on this family (`strongMemoStates=1703`, `strongMemoSplitProbes=6011`
  at `n=30` for k=5 and k=8). This makes the strong nullable gate plus
  original-regex span/memo reconstruction the leading tree-level route, but it
  is still only tooling/evidence until checked Isabelle reconstruction and
  cubic theorem interfaces are complete.
  The longer `k=5,8,10,12,n<=200` grid strengthens the tree-side evidence
  (`strongMemoTree` peaks at `959`, `3425`, `5940`, and `9686`), but also
  shows that the unquotiented cumulative active prefix pool is not the final
  cubic proof object (`k=12` active pair-budget grows to `262145` at `n=200`).
  This remains diagnostic BR-038/BR-040 infrastructure, not a payout.
  Follow-up final-state metrics are more encouraging: on the same grid,
  `strongMemoFinalActiveRows` maxes at `5`, `9`, `11`, and `13`, while
  `strongMemoFinalActivePairBudget` maxes at `17`, `65`, `101`, and `145`.
  This suggests the next proof should target final-state active rows, not raw
  prefix-pool rows.
- Strong-memo budget scout:
  `agent_hunt_pipeline/scripts/strong_memo_budget_scout.ps1` runs exact POSIX
  `strong-memo` smoke plus `-FindStrongCubicBudgetCE` across deterministic
  seeds and writes
  `agent_hunt_pipeline/reports/strong_memo_budget_scout/summary.md`. The
  current small report (`20260602,20260603`, 2,000 random cases each at depth
  6/input 8, factor `1.0 * rsize^3`) finds no budget CE. This is smoke
  evidence only; BR-039/BR-040 still require a checked final-tree or
  indexed/quotiented universe theorem.
- Strong-memo final-active scout:
  `agent_hunt_pipeline/scripts/strong_memo_final_active_scout.ps1` runs exact
  POSIX `strong-memo` smoke plus `-FindStrongFinalActiveBudgetCE` across
  deterministic seeds and writes
  `agent_hunt_pipeline/reports/strong_memo_final_active_scout/summary.md`.
  The current report (`20260602,20260603,20260604`, 5,000 random cases each at
  depth 6/input 8, `rows <= 1.0 * rsize`, `maxRowSize <= 8.0 * rsize`,
  `pairBudget <= 1.0 * rsize^2`) found no final-active budget CE. A deeper
  seed `20260602` run rejected `4.0 * rsize` with `rsize=30` and
  `maxRowSize=195`, so the checked theorem remains deliberately parameterized
  by `K`; proof work should treat `8.0` as the current smoke-passing candidate,
  not a proven constant. This is smoke evidence for the final-active proof
  route only; no BR-039/BR-040 payout is claimed.
- Member-factor sweep:
  `agent_hunt_pipeline/scripts/strong_memo_final_active_factor_sweep.ps1`
  runs the final-active scout across candidate member factors and keeps
  per-factor reports under
  `agent_hunt_pipeline/reports/strong_memo_final_active_factor_sweep/`. The
  current sweep (`4,6,8`) records `4` and `6` as failed by seed `20260602`,
  case `4784`, and `8` as the current smoke-passing candidate. This is BR-038
  tooling/evidence, not a payout.
- Deeper member-factor smoke:
  `agent_hunt_pipeline/reports/strong_memo_final_active_factor_sweep_deep/`
  records a `8,10,12` sweep over five seeds and `10000` cases per seed at
  depth `7`/input length `10`. `8` still passes with worst observed member
  ratio `6.809524`. This raises confidence in the candidate constant but pays
  no bounty without a checked proof.
- Final-active proof bridge checkpoint: `GeneralRegexBound.thy` now defines
  `raw_final_active_suffix_rows`, `raw_final_active_suffix_keys`, and
  `raw_final_active_suffix_pair_budget`; `FBound.thy` lifts these to the final
  `bders_simpStrong (intern r) s` tree via
  `strong_deferred_final_active_suffix_rows` and packages the checked route in
  `strong_deferred_memo_tree_value_final_active_interface`. This links exact
  POSIX reconstruction, span/split memo budgets, and the final-active row
  bound by final `asize`. It is BR-040 infrastructure only; it does not pay
  until the final-active row/pair-budget cubic theorem or equivalent quotient
  theorem is checked.
- Final-active syntax checkpoint:
  `raw_final_active_suffix_rows_iff`, `raw_final_active_suffix_keys_iff`, and
  `raw_final_active_suffix_bucket_iff` now characterize final-active sets as
  concrete `RSEQ (RALTS rows) k` subterms, with lifted
  `strong_deferred_final_active_suffix_*` versions in `FBound.thy`. This is
  proof infrastructure for BR-040, not a payout.
- Final-active key/bucket checkpoint:
  active keys and buckets now have checked subset, card, and member-size
  support lemmas against the final raw tree. This is useful proof
  infrastructure for the memo strong-tree route, but it is still not the
  original-size cubic theorem and pays no bounty.
- Final-active pair-budget premise reduction:
  `FBound.thy:strong_deferred_final_active_suffix_pair_budget_le_rxsize_square`
  proves that the quadratic pair-budget follows from the linear final-active
  row bound, and
  `strong_deferred_original_final_active_rows_linear_member_cubic_contract`
  records the two-obligation handoff. This removes a proof burden but does not
  itself prove either remaining original-size obligation, so no bounty is
  claimed.
- Original-size final-active contract checkpoint:
  `FBound.thy:strong_deferred_original_final_active_budget_contract_with_member_bound`
  now states the proof target corresponding to the Scala final-active scout.
  For a legacy root, if final-active rows and final-active pair-budget are
  bounded by the original `rxsize r`, and final-active row member size is
  bounded by an explicit `M`, the memo strong-tree route already yields exact
  POSIX `Some`/`None` correctness, `flat v = s`, a legacy final raw recognition
  state, final-active closure size `<= rxsize r + rxsize r * rxsize r * M`,
  and the existing memo-table budgets. The older
  `strong_deferred_original_final_active_budget_contract` remains as the
  special `M = rxsize r` case, but smoke shows that case is too optimistic for
  the current route. The checked
  `strong_deferred_original_final_active_linear_member_cubic_contract` records
  the real target: a proof of `rsize q <= K * rxsize r` for final-active row
  members instantiates the closure bound as
  `rxsize r + K * rxsize r * rxsize r * rxsize r`. This is a checked handoff
  theorem, not a payout; the actual linear member-size bound remains open.
- Final-active pair-budget square checkpoint:
  `raw_shared_prune_active_suffix_pair_budget_eq_pairs` proves the active
  pair-budget is exactly the active pair-relation cardinality, and
  `raw_shared_prune_active_suffix_pair_budget_le_card_square` bounds it by
  `card U * card U`. The final-tree lift
  `strong_deferred_final_active_suffix_pair_budget_le_final_asize_square` is
  now included in `strong_deferred_memo_tree_value_final_active_interface`.
  This is useful fallback accounting, not a cubic theorem payout.
- Strong-memo POSIX contract checkpoint:
  `FBound.thy:strong_deferred_memo_tree_POSIX_correctness`,
  `strong_deferred_memo_tree_POSIX_flat`, and
  `strong_deferred_memo_tree_bounded_contract` now state the live route
  directly: the final strong tree is the nullable gate, exact POSIX values come
  from the span/memo table, and any future final-tree bound `asize <= T`
  immediately yields exact POSIX correctness, `flat v = s`, final active rows
  `<= T`, pair-budget `<= T*T`, and the existing cubic memo-table budgets.
  This is BR-040 infrastructure only; the tree or indexed-universe bound is
  still open.
- Final-active closure contract checkpoint:
  `GeneralRegexBound.thy:raw_final_active_suffix_closure` and
  `FBound.thy:strong_deferred_final_active_suffix_closure` expose the one-step
  active shared-prune closure of the final strong tree's active rows. The
  checked theorem
  `strong_deferred_memo_tree_bounded_active_closure_contract` states that a
  future final-tree bound `asize <= T` plus a final-active member-size bound
  `rsize q <= M` yields
  `card strong_deferred_final_active_suffix_closure <= T + T*T*M`. This is the
  current proof-facing shape for the indexed/final-active universe route, but
  it is still infrastructure until the final tree/member-size bound is checked.
  Follow-up checked lemmas now discharge that member-size premise for the
  final-active closure itself:
  `raw_final_active_suffix_rows_member_size_le_rsize`,
  `card_raw_final_active_suffix_closure_le_rsize_cubic`,
  `strong_deferred_final_active_suffix_rows_member_size_le_final_asize`,
  `strong_deferred_final_active_suffix_closure_le_final_asize_cubic`, and
  `strong_deferred_memo_tree_bounded_active_closure_cubic_contract`. Thus a
  future strong-tree bound `asize <= T` directly gives
  `card strong_deferred_final_active_suffix_closure <= T + T*T*T`. This still
  does not pay BR-040 until the final strong-tree or equivalent indexed
  representation bound is checked.
- Active pair-budget checkpoint: `GeneralRegexBound.thy` now exposes
  `raw_shared_prune_active_suffix_pair_budget` and the checked bridge
  `card_raw_shared_prune_active_suffix_closure_member_pair_budget_bound`.
  It also has monotonicity facts for active keys, buckets, pairs, closure, and
  pair-budget; these are intended for iterative/least-universe constructions.
  The follow-up lemmas
  `raw_shared_prune_active_suffix_pair_budget_bucket_bound` and
  `card_raw_shared_prune_active_suffix_closure_member_pair_budget_card_bound`
  provide the fallback `S * K * K` estimate and the direct `C + P * M`
  closure-cardinality packaging.
  For a finite active universe `U`, it is enough to prove one aggregate
  pair-budget bound `raw_shared_prune_active_suffix_pair_budget U <= P` and
  a member-size bound `rsize q <= M` to get
  `card (raw_shared_prune_active_suffix_closure U) <= card U + P * M`.
  This is the sharper current BR-040 proof contract for memo-strong tree; it
  is infrastructure only until the concrete root-owned active universe and
  its cubic `P`/`M` bounds are checked.
- Checked deferred memo budget: `FBound.thy:strong_deferred_memo_budget`
  now packages the route as a proof-facing interface, and
  `FBound.thy:strong_deferred_original_memo_budget` adds the corresponding
  `legacy_rexp` closure package. They state the nullable gate/unique deferred
  value equivalence, bound the combined accept/value span memo table by
  `2 * rxsize r * Suc (length s)^2`, bound split probes by
  `rxsize r * Suc (length s)^3`, and keep memo/split states inside the
  non-backref fragment when the root is legacy. This is useful BR-040
  infrastructure, but it does not by itself pay a final cubic theorem bounty
  because the tree/share-representation reconstruction theorem is still open.
- Combined row/memo interface:
  `FBound.thy:strong_deferred_original_raw_row_norm_closed_memo_cubic_interface`
  packages the raw strong-row cubic-universe premises together with the
  deferred POSIX value gate, `bders_simpStrong` legacy closure, quadratic memo
  state budget, cubic split-probe budget, and legacy-subterm closure. This is
  the current proof handoff for the leading deferred-memo route. It remains
  conditional infrastructure, not payout, until a concrete raw/shared universe
  with the required cubic bound is checked.
- Direct k/n derivative-size compare side task:
  `agent_hunt_pipeline/scripts/ch7_derivative_size_compare.ps1` generates
  `agent_hunt_pipeline/reports/ch7_derivative_size_compare/index.html`.
  The default report overlays thesis `strongTree` and deferred
  `strongMemoTree` on one plot per `k`; `cubicTree` remains available only as
  an explicit opt-in negative-evidence metric. Older generated summaries showed
  the baseline ratios directly:
  at k=5,n=30, `cubicTree=3245` versus `strongTree=958` (`3.387x`);
  at k=8,n=30, `cubicTree=7587` versus `strongTree=2747` (`2.762x`).
  This is visualization/tooling under BR-038, not a theorem payout.
- Direct-DAG shared smoke prototype: `PosixCubicSmoke.scala` now has an
  optional direct hash-consed derivative/simplifier path, exposed by
  `-SharedDirectDag` / `-ScalaSmokeSharedDirectDag`. The optional
  `-SharedDirectCompareTree` / `-ScalaSmokeSharedDirectCompareTree` gate checks
  every prefix derivative root for exact syntactic equality with the existing
  tree-step reference algorithm. It preserves exact POSIX values for
  value-safe no-reassociation modes in the current exhaustive and random smoke,
  and reports both final reachable DAG size and prefix `statePool`. The
  optional `-SharedStatePoolCubicFactor` /
  `-ScalaSmokeSharedStatePoolCubicFactor` gate now fails the smoke if
  `statePool` exceeds the configured multiple of `rsize(r)^3` above the size
  floor, while `-SharedStatePoolCubicTop` reports the highest-ratio witnesses.
  The long-tail `-SharedPlateauMaxLength` /
  `-ScalaSmokeSharedPlateauMaxLength` gate defaults to `shapeStatePool`, the
  erased/shape prefix-pool metric closest to the current raw proof side. Use
  `-SharedPlateauProgress` / `-ScalaSmokeSharedPlateauProgress` for long runs;
  short `0..30` traces are not payout evidence unless the metric actually
  stops strictly increasing. Current evidence is not sufficient for a payout:
  direct `expanded-keyed-no-reassoc` has `k=5` stopping at `n=124`, but `k=8`
  remains strictly increasing through `n=500`. The experimental
  `unary-cover-no-reassoc` mode also stops on `k=5` (`shapeStatePool 337 ->
  337` at `n=124`) but is still strictly increasing on `k=8` at `n=624`
  (`shapeStatePool=2568`) before the current direct-DAG dedup runs out of heap.
  The narrower `unaryModShapeStatePool` and `unaryPruneShapeStatePool`
  diagnostics do not repair this: the modulo metric is still `2552` and
  increasing at `k=8,n=624`, and the shallow pruning traversal matches it on
  the checked `k=8,n=160` prefix. The next payable candidate needs
  continuation-aware row-set coverage, not another shallow unary child rewrite.
  The first such diagnostic, `contPruneShapeStatePool`, improves smaller roots
  (`k=3` stops at `n=12`; `k=5` stops at `n=68`) but still matches the
  modulo metric at `k=8,n=624` (`2552`) and remains strictly increasing, so it
  is not a BR-039 payout either. The newer
  `langContPruneShapeStatePool` diagnostic is stronger on `k=8`: with
  metric-only bit erasure and step `64`, it first stops increasing at `n=960`
  (`885 -> 885`). But a `k=10` run sampled every `128` characters timed out at
  `n=1664` while still strictly increasing (`1731`), so this is still
  diagnostic evidence only. It does not pay BR-039/BR-040 unless it is replaced
  by a checked POSIX-safe indexed/periodic row universe or reconstruction
  theorem.
  Current Chapter 7 evidence suggests `shapeStatePool`, not the raw total
  allocation pool or exact annotated `statePool`, is the closest smoke proxy
  for the proof-facing erased shared universe. This is BR-038/BR-039 tooling
  evidence only, not a payout.
- Concrete raw shared-prune sanity universe: `GeneralRegexBound.thy` now has
  `raw_shared_prune_closed_sizeNregex`, supported by raw size/legacy lemmas.
  This proves that the raw delayed shared-prune result stays inside every
  coarse legacy size-bounded universe `sizeNregex N`. It is useful evidence
  that the shared-prune obligation is locally well behaved, but it is not a
  BR-039/BR-040 payout because `sizeNregex N` is not a root-owned cubic
  cardinality universe.
- Raw shared-prune closure predicate: `GeneralRegexBound.thy` now has
  `raw_shared_prune_closed`, which weakens the shared closure obligation to
  the case where both `RSEQ (RALTS lrs) k` and `RSEQ (RALTS rrs) k` are already
  in the candidate universe. `FBound.thy` exposes the corresponding
  `strong_deferred_original_raw_row_norm_closed_cubic_universe_interface`.
  This is a closer BR-040 proof contract for a concrete raw/shared universe,
  but still not a payout before that universe and its cubic bounds are checked.
- Raw one-step closure split: `GeneralRegexBound.thy` now splits the raw
  `rpder_strong_rows_raw` closure proof into local `flat_closed`, `norm`, and
  `shared` obligations, with the shared obligation targeting the raw delayed
  prune result `rsimp7_SEQ_atom (rsimp_ALTs (rprune_eq_against lrs rrs)) k`.
  `FBound.thy` exposes this as
  `strong_deferred_original_raw_row_norm_later_shared_cubic_universe_interface`.
  This is useful BR-040 infrastructure, not a payout before a concrete
  cubic raw/shared universe is checked.
- Raw-row universe interface: `GeneralRegexBound.thy` now has finite-universe
  subset/distinct/length/`rsizes` bookkeeping for `rpders_strong_rows_raw`.
  `FBound.thy` adds `strong_deferred_original_raw_row_cubic_universe_interface`,
  which transfers a raw one-step closure premise for
  `rpder_strong_rows_raw` to the annotated `bpders_strong1_rows` size bound,
  exact `map rerase` equality, and deferred POSIX value gate. This is the
  preferred BR-040 proof interface for the next closure attempt, but it is not
  a payout until a concrete cubic raw/shared universe is checked.
- Raw strong skeleton bridge: `GeneralRegexBound.thy` now has
  `rsimpStrong_raw` and raw strong row derivative entry points that mirror the
  annotated delayed-normalization shape. `FBound.thy` proves exact erasure
  bridges from annotated `bsimpStrong`/`bpder_strong_rows` to this raw layer,
  including `rerase_bsimpStrong_raw` and
  `map_rerase_bpders_strong1_rows_raw`. This repairs the usable erased-carrier
  interface after the normalized exact-erasure counterexample, but remains
  infrastructure only; it is not a BR-039 or BR-040 payout.
- Strong prune exact-erasure caveat: `FBound.thy` now has the checked
  counterexample `rerase_bsimpStrong_prune_pair_not_exact`. It shows that
  annotated `bsimpStrong_prune_pair` does not syntactically erase to
  `rsimpStrong_prune_pair`, because the annotated side keeps bit/value-carrying
  row syntax while the skeleton side normalizes duplicate/nested pruned rows
  internally. Future BR-039/BR-040 work must not rely on a naive exact
  `map rerase` bridge for strong pruning; it needs a language/coverage
  universe argument or a checked shared-row reconstruction layer.
- Original-entry strong-row cubic interface: `FBound.thy` now has
  `strong_deferred_original_row_cubic_universe_interface`. It states the
  current checked contract from an original `legacy_rexp r`: a finite erased
  row universe with one-step `bpder_strong_rows` closure and card/member-size
  bounds gives a product bound for
  `bpders_strong1_rows (intern r) s`, while preserving the nullable-row iff
  unique deferred POSIX value gate and the `rxsize` alignment of `intern`.
  This is BR-040 infrastructure only. It does not pay until the actual cubic
  row universe construction/closure theorem is checked.
- Strong-tree route clarification: the currently viable way to preserve the
  `bsimpStrong` tree plateau while getting exact POSIX values is the
  deferred/span-memo route. `StrongFullCert` is retained as a CE-mining tool,
  but the `bba` greedy-sequence CE shows that local final-state
  `Val => Option[Val]` reconstruction is not enough by itself. The optional
  `-CheckStrongDeferredMemo` smoke now includes the known CE grid and must
  remain green before any BR-039/BR-040 claim can use this route.
- Strong cubic frontier reporting: optional `-StrongCubicTop` /
  `-ScalaSmokeStrongCubicTop` reports multiple high-ratio size-pressure
  witnesses for the strong-deferred CEGAR loop. The report also includes a
  distinct-regex frontier so repeated inputs for one regex do not hide other
  structural pressure families. This is diagnostic tooling only; it does not
  by itself satisfy BR-039 or BR-040.
- Checked original-value bridge: `FBound.thy` now has
  `rexp_span_posix` and the root bridge
  `bnullable_bders_simpStrong_intern_iff_rexp_span_posix_root`, plus a
  uniqueness theorem for the root span POSIX entry. This is useful BR-040
  proof infrastructure only; it does not pay until constructor-level
  reconstruction correctness is checked.
- Strong-deferred reconstruction package: `FBound.thy` now also has
  `strong_deferred_reconstruction_budget`, packaging the nullable gate,
  unique deferred value, bounded POSIX value table, and bounded split-probe
  table for the current span/memo route. This is BR-040 infrastructure only;
  the regex-size cubic tree/share bound remains open.
- Original non-backref fragment bridge: `RegLangs.thy` now has `legacy_rexp`,
  and `FBound.thy` has `legacy_rerase_intern`,
  `legacy_rexp_rerase_bders_simpStrong_intern`, and
  `strong_deferred_original_legacy_budget`. Future original-file cubic
  statements can use the premise `legacy_rexp r` directly. This is BR-040
  infrastructure only and does not count as a bounty payout.
- Deferred span fragment closure: `FBound.thy` now also proves that
  `rexp_subterms`, span states, split probes, POSIX span entries, and POSIX
  span states all remain `legacy_rexp` when the root is `legacy_rexp`.
  `strong_deferred_original_legacy_budget` includes this closure for the value
  and split-probe tables. This supports BR-040 but remains infrastructure, not
  a payout.
- Strong row gate bridge: `FBound.thy` now connects
  `bpders_strong1_rows (intern r) s` to the current deferred-value route:
  under `legacy_rexp r`, existence of a nullable strong row is equivalent to
  existence of the unique `strong_deferred_span_value r s`. The same checkpoint
  adds `asize_intern` and `rsize_rerase_intern`, aligning annotated/skeleton
  size with original `rxsize`. This supports the Antimirov row-universe cubic
  route but remains infrastructure, not a payout.
- Checked original split probes: `FBound.thy` now also has
  `rexp_span_split_probes`, `rexp_span_all_split_probes`, their cardinality
  bounds, and one-directional original POSIX constructor rules for `ONE`, `CH`,
  `ALT`, `SEQ`, `STAR`, and `NTIMES`. This supports the current CEGAR route:
  keep the `bsimpStrong` tree as the nullable gate, mine local-certificate CEs,
  and prove exact values through bounded original-root span reconstruction.
  It is still infrastructure, not a BR-039/BR-040 payout.
- Countdown universe fix: original `rexp_subterms` is now reconstruction-aware
  for `NTIMES`, containing every countdown state `NTIMES r k` with `k <= n`.
  This is required for span reconstruction of counted repetitions; plain
  syntactic subterms are too weak. `rexp_span_posix_ALT1E`,
  `rexp_span_posix_ALT2E`, and `rexp_span_posix_SEQE` are checked inversion
  infrastructure only.
- StrongFull known-CE guard: optional smoke gate `-CheckStrongFullKnownCE`
  checks that the minimal greedy-boundary case still blocks local
  `StrongFullCert` reconstruction while `StrongDeferredMemo` matches baseline.
  This prevents accidental payout or proof work on the old local-certificate
  route. It is a diagnostic guard only.
- Checked span constructor support now includes alternatives, unit/empty,
  nonempty star, and counted-repetition intro rules:
  `rspan_accepts_RALTSI`, `rspan_accepts_RONE_emptyI`,
  `rspan_accepts_RSTAR_stepI`, `rspan_accepts_RNTIMES_zeroI`, and
  `rspan_accepts_RNTIMES_SucI`. These are infrastructure only, not a payout
  until an actual POSIX reconstruction relation is checked.
- Admin revocation note: all later mentions of `BR-036`, `BR-037`, `rsimp9`,
  `norm19`, or `path9` in these notes are historical diagnostics only. They are
  not active bounty targets, cannot be locked, and cannot be collected. New
  cubic work must pass the BR-038 smoke suite before any proof-oriented bounty
  can be attempted.
- BR-038/BR-039 now have a stronger Scala-gated smoke checkpoint, still not a
  payout: `PosixCubicSmoke.scala` checks exact POSIX value preservation on
  bounded generated regexes/inputs and the Chapter 7 `k=5` family at derivative
  lengths `4`, `8`, `12`, `16`, and `20` under the same `bsimpCubic`
  candidate. The broad grid belongs in Scala, not in Isabelle `eval` lemmas.
  `thesis_cubic_counterexample_G` and `thesis_cubic_counterexample_H` check
  that `bsimpCubic` is not merely a `bsimpStrong` wrapper because it cleans
  counted repetitions (`ANTIMES`) that `bsimpStrong` leaves untouched. The
  erased-language bridges `L_bsimpCubic`, `RL_rerase_bsimpCubic`, and
  `RL_rerase_bders_simpCubic` are checked support facts only; the full cubic
  theorem and POSIX/bitcode-preserving route remain open.
- BR-039/BR-040 payout is explicitly blocked by the optional deterministic
  random smoke diagnostic until repaired. With seed `20260602`, random case
  `99` finds a POSIX value mismatch for
  `STAR (ALT ONE (STAR (STAR (STAR (STAR (STAR (CH a)))))))` on input `aaa`.
  Default CI keeps random smoke off to preserve a green integration branch, but
  any proof/bounty attempt must run it and resolve this class of bitstream
  mismatch first.
- New diagnostic localization: the value mismatch is tied to destructive
  sequence reassociation in `bsimpCubic_ASEQ_atom`. Mode `no-reassoc` passes
  the tested random value smoke but fails the Chapter 7 threshold; mode
  `full` passes the threshold but fails random value smoke; mode
  `reassoc-nonnullable-left` still fails random value smoke. Therefore BR-039
  cannot pay for a simplifier that emits reassociated sequence syntax unless it
  also supplies a checked bitcode/value reconstruction theorem.
- New route evidence: the Scala harness now reports exact DAG and shape-DAG
  sizes for Chapter 7. Value-safe `no-reassoc` has large tree size but compact
  shared structure (`k=8`, length `32`: tree `18643`, exact DAG `547`,
  shape DAG `312`). This supports a future hash-consed row-universe or delayed
  linear-form bounty route, but it is not itself a payout because BR-039 still
  asks for a smoke-tested candidate with an explicit POSIX-value story.
- Stronger route evidence: diagnostic mode `expanded-keyed-no-reassoc` indexes
  virtual expanded rows such as `a.c` and `b.c` from `(a+b).c` for pruning while
  keeping the emitted syntax `no-reassoc` shaped. It passes the current
  exhaustive depth `2`/input `3` smoke (`84,300` pairs) and deterministic random
  smoke (`2,000` cases, seed `20260602`). On Chapter 7 `k=8`, length `128`, it
  improves plain `no-reassoc` final sizes from tree/exact-DAG/shape-DAG
  `48077/1721/718` to `34581/1465/462`, with a slightly larger shared pool
  `11170 -> 11810`. This is a promising BR-039 design lead, not a payout.
- Thesis Figure 7.6 `k=5` caveat: `bsimpStrong` remains the route that gives
  hundreds-scale ordinary tree size (`n=16` is `820`, matching checked Isabelle
  facts). `expanded-keyed-no-reassoc` at `n=30` still has ordinary tree size
  `3849`, despite compact exact DAG/shape-DAG `276/132`. Therefore no bounty may
  describe this diagnostic as a tree-level reproduction of thesis
  `strongBlexer`; any payout must either recover a value-safe tree simplifier or
  state and prove a shared-representation reconstruction theorem.
- New optional smoke gate `-CheckStrong` blocks a naive tree-level
  `strongBlexer` payout: current `bsimpStrong` fails exact POSIX value
  preservation on `STAR (STAR (CH a))` with input `a`, because nested-star value
  structure is collapsed. This is an expected diagnostic failure, not a default
  CI failure. BR-039 may not use `bsimpStrong` as-is without a checked
  value-reconstruction theorem or a repaired value-safe strong simplifier.
- CE-driven safe-output diagnostic: `bsimpStrongSafe` repairs the first wave of
  value counterexamples by disabling nested-star collapse, nonempty right-unit
  deletion, star absorption, and sequence reassociation in the emitted regex.
  It passes exact POSIX smoke through random depth `5`/input `6`, seed
  `20260602`, but does not preserve the thesis tree-size plateau (`k=5,n=30`
  tree `5133`). It is therefore route evidence only. A payable tree-level
  strong candidate must keep the small `bsimpStrong` regex and add checked
  value transformers/reconstruction for those rewrites, or find a different
  value-safe pruning rule with comparable size.
- CE-driven strong-reconstruction sketch: `scala_cubic_smoke.ps1
  -TraceStrongRecon` now checks local transformer equations for the first
  strong CE witnesses while retaining the actual small `bsimpStrong` output.
  It also checks annotated-value local certificate laws for those rewrite
  classes over small input grids. This is positive route evidence, not a bounty
  claim; payout still requires a compositional derivative-time certificate or
  theorem.
- Strong core certificate prototype: `scala_cubic_smoke.ps1
  -CheckStrongCoreCert` checks the sequence/star core certificate on derivative
  expressions. Current smoke covers `84,300` exhaustive derivative expressions
  plus `3,000` deterministic random expressions with seed `20260602`.
  Alternation flatten/distinct is now included. This is still not a payout
  artifact because the Isabelle proof-facing story remains open.
- Certified-core size trace before row pruning was k=5,n=30 at `2342` versus
  thesis `bsimpStrong` at `958`; this identified row pruning as the next target.
- Certified row-pruning prototype: the direct shared-suffix pattern is now
  certificate-smoked in the surrounding `AALTs` context. The new k=5,n=30
  certified-core size is `678`, with `84,300` exhaustive derivative-expression
  checks and `3,000` deterministic random checks passing.
- Derivative-loop certificate smoke: `scala_cubic_smoke.ps1
  -CheckStrongCoreLoop` now composes `bder`, `bsimpStrongCoreCert`, `injectA`,
  and the accumulated continuation across the whole input. It matches
  `baselineValue` on `84,300` exhaustive pairs and `3,000` deterministic random
  cases. This upgrades the route from local certificates to whole-lexer Scala
  evidence, but Isabelle proof-facing invariants are still required before
  payout.
- Full strong-tree certificate diagnostic: `scala_cubic_smoke.ps1
  -CheckStrongFullLoop -FindStrongFullCE -TraceStrongFullLoop` keeps the
  `bsimpStrong`-scale tree and currently passes exhaustive depth `2`/input `3`
  plus `10,000` deterministic random cases at depth `6`/input `7`. It also
  reproduces the Chapter 7 `k=5` plateau with max state `721`. This does not
  pay BR-039: depth `7`/input `8`, seed `20260602`, case `622` shrinks to
  `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`, where the current
  certificate gives the final `a` to the right star instead of the left POSIX
  greedy star. This CE must be repaired or bypassed by a checked span/memo
  reconstruction theorem before any full-strong candidate can pay out.
- Checked span-universe support: `GeneralRegexBound.thy` now contains
  `rspan_states`, `rspan_split_probes`, and subset/cardinality bounds matching
  the Scala memo reconstruction accounting (`rsize(r) * (|s|+1)^2` states and
  `rsize(r) * (|s|+1)^3` split probes). This is proof infrastructure for
  BR-040-style reconstruction interfaces, not a payout by itself: the actual
  POSIX reconstruction relation still needs to prove that its memo table and
  split probes are subsets of these universes and agree with the existing
  POSIX value relation.
- Checked memo-table specifications: `rspan_accepts` and
  `rspan_all_split_probes` now give concrete table targets for the span route,
  with checked subset/cardinality bounds inherited from the universes. This is
  stronger than raw universe accounting, but still not a bounty payout until a
  reconstruction correctness relation is proved.
- Checked span algebra: `rslice_append`, `rspan_accepts_root_iff`,
  `rspan_accepts_RSEQI`, and `rspan_accepts_RSTAR_emptyI` now provide the first
  constructor rules for the memo-table correctness proof. These are
  infrastructure only; missing constructor/extraction rules and POSIX value
  reconstruction still block payout.
- Proof-facing bridge: `CERTIFIED_STRONG_CORE.md` records the intended
  `cert_recon` relation, loop invariant, certificate constructors, and
  loop-size trace. This is planning evidence, not payout.
- BR-036/BR-037 route correction: a proof based only on `rsimp9`/`bsimp9`
  does not address the thesis Chapter 7 three-star evil family
  `STAR (STAR (ALTs [a*, (aa)*, ...]))`. That family is designed to require
  shared-suffix row pruning such as `(a + b).c + (a + d).c ->
  (a + b).c + d.c`. Future payout for the cubic-bound tranche must therefore
  close the strong-row route (`rsimpStrong`/`bsimpStrong`,
  `rpder_strong_rows`/`bpder_strong_rows`) or prove an equivalent pruning
  theorem. The existing `rsimp9`/path9 material remains useful scaffold for
  tail/countdown normalization and diagnostics, but an `rsimp9`-only closure is
  not sufficient for this bounty.
- BR-036 now has explicit checked regression sanity lemmas for the thesis
  cubic-bound examples: `thesis_cubic_evil3_aaa_norm19_rows_cubic` for the
  Chapter 6 evil shape `(a* + (aa)* + (aaa)*)*` after `aaa`, with
  `thesis_cubic_small_alt3_aaa_norm19_rows_cubic` retained only as a cheap
  contrast for the non-starred variant, and
  `thesis_cubic_ntimes_countdown_norm9_no_zero_counter` plus
  `thesis_cubic_ntimes_countdown_norm19_rows_cubic` for the `(a){3}`
  countdown. These confirm the candidate route on the motivating examples but
  do not settle BR-036. The thesis Chapter 7 stronger simplification/pruning
  idea is not yet a checked production simplifier and remains a design gap.
- BR-036/BR-037 now have checked negative/diagnostic evidence in `FBound.thy`
  for the Chapter 7 example: `thesis_ch7_evil5_bders_simp_size_16` records
  production `bders_simp` size `14876` on `a^16`, while
  `thesis_ch7_evil5_bders_simp8_size_16` records `1308` for the root-safe
  `bsimp8` variant and `thesis_ch7_evil5_bpders_norm17_row_size_16` records
  `645` for the row-list route. The checked overlap-prune facts
  `thesis_ch7_bsimp_misses_overlap_prune`,
  `thesis_ch7_overlap_pruned_smaller`, and
  `thesis_ch7_overlap_pruned_same_language` show why a real
  `bsimpStrong`/`prune` design is still needed: current `bsimp` leaves the
  `(a + b + d).c + (a + c + e).c` overlap untouched, while the pruned erasure
  is language-equivalent and smaller. This is not a bounty payout.
- BR-037 has a first checked executable prototype, not a payout:
  `bsimpStrong`, `bsimpStrong_prune_rows`, and
  `bders_simpStrong` now live in `BlexerSimp.thy` on the original `arexp`
  datatype. The generic lemma `L_prune_eq1_against_AALTs` checks the
  erasure-language basis for deleting later alternatives covered by earlier
  alternatives under `eq1`. The concrete Chapter 7 facts
  `thesis_ch7_bsimpStrong_prunes_overlap`,
  `thesis_ch7_bsimpStrong_overlap_smaller`, and
  `thesis_ch7_bsimpStrong_overlap_same_language` show that the prototype
  performs the missing `(a + b + d).c + (a + c + e).c` prune. Remaining
  bounty requirements: POSIX/bitcode preservation, derivative-size regression
  on the full evil family, and integration without weakening existing lexer
  theorems.
- BR-037 now has the first full evil-family size regression for that prototype:
  `thesis_ch7_evil5_bders_simpStrong_lt_simp8_size_16` and
  `thesis_ch7_evil5_bders_simpStrong_size_16_under_825` show
  `bders_simpStrong` below `825` on `k=5, a^16`, while
  `thesis_ch7_evil5_bders_simpStrong_size_16_not_under_812` gives a checked
  lower-bound sanity check. This confirms the Chapter 7 prune is active beyond
  the toy overlap, but it is still only progress:
  row-list normalization remains smaller (`645`), and no general cubic theorem
  or POSIX/bitcode preservation theorem has been awarded.
- BR-037 also has the checked erasure-language theorem `L_bsimpStrong`,
  proving the executable prototype preserves the language after erasure. This
  is still only a support theorem: a bounty payout needs the POSIX/bitcode
  preservation route and production integration, not erased-language safety
  alone.
- BR-036 now also has the checked norm9-specific scaffold
  `rpath9_atom_frontier_acc`, `rpath9_atom_frontiers`,
  `partial_derivative_path9_atom_frontier_universe`,
  `finite_rpath9_atom_frontier_acc`, `finite_rpath9_atom_frontiers`,
  `finite_partial_derivative_path9_atom_frontier_universe`, and
  `path9_atom_frontier_avoids_old_atom_explosion`. The raw-tail bridge
  `rpath9_tail`, `rsize_rpath9_tail_le`,
  `rfrontier_rpath9_tail_member_size_le`,
  `rfrontier_rsimp7_SEQ_atom_rsimp9_rpath9_tail_member_size_le`, and
  `rfrontier_rpath9_tail_RSEQ_member_size_le` is also checked; it is progress
  toward the remaining linear member-size premise, not a payout claim. The
  generic frontier helper `rfrontier_rsimp7_SEQ_atom_rsimp9_member_size_le`
  and the `RCHAR` raw-tail base cases
  `rpath9_atom_frontier_acc_RCHAR_rpath9_tail_member_size_le` and
  `rpath9_atom_frontier_acc_RCHAR_rpath9_tail_RSEQ_member_size_le` are
  checked as the first leaves for that induction. The carried-constructor
  raw-tail handoffs
  `rpath9_atom_frontier_acc_RSEQ_rpath9_tail_member_sizeI`,
  `rpath9_atom_frontier_acc_RSTAR_rpath9_tail_member_sizeI`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_rpath9_tail_member_sizeI` are also
  checked. The top-level raw-tail member-size interfaces
  `rpath9_atom_frontiers_RSEQ_member_size_rpath9_tailI`,
  `rpath9_atom_frontiers_RSTAR_member_size_rpath9_tailI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_size_rpath9_tailI` are also
  checked, exposing the `RSEQ ... RONE` outer frontier cases through
  `rpath9_tail`. The checked counterexample
  `rpath9_tail_prefix_continuation_bound_counterexample` rules out using a
  continuation-only budget for long prefixes; the checked parent-budget
  interfaces
  `rpath9_atom_frontiers_RSEQ_member_size_rpath9_tail_parentI`,
  `rpath9_atom_frontiers_RSTAR_member_size_rpath9_tail_parentI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_size_rpath9_tail_parentI`
  are the intended next interface for the remaining linear member-size proof.
  The checked counterexamples
  `path9_frontiers_not_subset_norm9_frontier_universe` and
  `path9_frontiers_not_subset_original_frontier_universe` rule out reusing the
  old frontier universe as a direct superset of path9 frontiers.
  The checked budget layer
  `rpath9_member_budget`, `rpath9_member_budget_list`,
  `rpath9_atom_frontier_acc_rpath9_tail_member_budget`, and
  `rpath9_atom_frontiers_member_budget` now packages the accumulator
  member-size recursion, but
  `rpath9_member_budget_nested_star_not_linear` shows this raw budget is too
  coarse for the final linear bound. The tighter checked layer
  `rpath9_tight_member_budget`, `rpath9_tight_member_budget_list`,
  `rpath9_tight_member_budget_le_member_budget`,
  `rpath9_atom_frontier_acc_rpath9_tail_tight_member_budget`,
  `rpath9_atom_frontiers_tight_member_budget`, and
  `rpath9_tight_member_budget_nested_star_linear_sanity` is the current route
  for the remaining linear member-size premise. The checked
  `rpath9_tight_member_budget_nested_star_less_raw` witness records that the
  tight budget strictly improves the raw budget on the nested-star obstruction.
  The checked splitter layer
  `rpath9_tail_RSEQ_size_le`,
  `rpath9_tight_member_budget_list_boundI`,
  `rpath9_tight_member_budget_RALTS_boundI`,
  `rpath9_tight_member_budget_RSEQ_boundI`,
  `rpath9_tight_member_budget_RSTAR_boundI`, and
  `rpath9_tight_member_budget_RNTIMES_nonzero_boundI` is progress toward that
  premise only; it isolates the constructor obligations for the required
  root-owned/carried-continuation induction and is not a BR-036 payout claim.
  The one-step closure interface now also includes
  `rpder_norm9_path9_atom_frontier_step_RALTS_selfI` and
  `rpder_norm9_path9_atom_frontier_step_RSEQ_selfI`; the latter packages the
  nullable right-child lift and leaves only the left carried-continuation
  bridge as the explicit `RSEQ` blocker.
  The first checked slice of that blocker is now
  `rder_path_continuations_acc_RCHAR_left_path9_stable`, with checked stable
  right-tail constructor leaves
  `rder_path_continuations_acc_RCHAR_left_path9_RZERO`,
  `rder_path_continuations_acc_RCHAR_left_path9_RONE`,
  `rder_path_continuations_acc_RCHAR_left_path9_RCHAR`,
  `rder_path_continuations_acc_RCHAR_left_path9_RSTAR`, and
  `rder_path_continuations_acc_RCHAR_left_path9_RNTIMES`. These facts expose
  the exact norm-tail stability assumptions needed for `RALTS` and nested
  `RSEQ`; they are progress evidence only and do not close BR-036.
  The carried-continuation splitter layer now also includes
  `rder_path_continuations_acc_RCHAR_frontierI`,
  `rder_path_continuations_acc_RALTS_carriedI`,
  `rder_path_continuations_acc_RSEQ_carriedI`,
  `rder_path_continuations_acc_RSTAR_carriedI`, and
  `rder_path_continuations_acc_RNTIMES_carriedI`. These are
  universe-parametric scaffold facts for the path9 one-step closure and are
  not a payout claim.
  The first checked one-step leaves built on this layer are
  `rpder_norm9_path9_atom_frontier_step_RSEQ_RCHAR_stable` with
  `RZERO`/`RONE`/`RCHAR`/`RSTAR`/`RNTIMES` right-tail instances, plus
  `rpder_norm9_path9_atom_frontier_step_RSTAR_RCHAR` and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_RCHAR`. These close the
  character-body base leaves for the path9 induction; the general
  `RALTS`/nested-`RSEQ` cases remain open.
  The
  checked accounting
  interface adds
  `partial_derivative_path9_atom_frontier_universe_card_le`,
  `partial_derivative_path9_atom_frontier_universe_member_size_boundI`,
  `partial_derivative_path9_atom_frontier_universe_member_size_linearI`, and
  `rsizes_distinct_path9_atom_frontier_universe_cubicI`. This is progress
  evidence, not a payout claim. The newer tight-budget bridge
  `rpath9_atom_frontiers_tight_member_budget_linearI`,
  `partial_derivative_path9_atom_frontier_universe_member_size_tight_budgetI`,
  and `rsizes_rpders_norm19_rows_rsimp9_path9_tight_budget_cubicI` reduces
  the remaining member-size premise to the single top-level tight-budget
  inequality, while preserving the separate one-step `rpder_norm9_list`
  closure obligation for the smaller universe. The first checked
  closure-plumbing facts are
  `rsubterms_rsimp_ALTs_member`, `set_rflts_singleton_map_member`,
  `rflts_singleton_rsimp9_path9_atom_frontier`,
  `rflts_map_rsimp9_path9_atom_subsetI`,
  `rflts_rsimp9_alt_child_path9_atom_subset`, and
  `rpder_norm9_path9_atom_frontier_step_RZERO/RONE/RCHAR`. The checked
  `RALTS`/`rsimp_ALTs` layer adds `set_rflts_map_member_exists`,
  `set_rflts_map_memberE`, `rflts_map_rsimp9_alt_path9_atom_subset`,
  `rflts_map_rsimp9_rsimp_ALTs_path9_atom_subset`,
  `rpath9_atom_frontiers_alt_child_subset`,
  `rpath9_atom_frontiers_alt_child_universe`,
  `rpder_norm9_path9_atom_frontier_step_RALTS_parentI`, and
  `rpder_norm9_path9_atom_frontier_step_rsimp_ALTs_parentI`. The carried
  constructor parent-inclusion facts are
  `rpath9_atom_frontiers_universe`,
  `rpath9_atom_frontiers_seq_left_subset`,
  `rpath9_atom_frontiers_seq_left_universe`,
  `rpath9_atom_frontiers_seq_right_subset`,
  `rpath9_atom_frontiers_seq_right_universe`,
  `rpath9_atom_frontiers_star_body_subset`,
  `rpath9_atom_frontiers_star_body_universe`,
  `rpath9_atom_frontiers_ntimes_body_subset`, and
  `rpath9_atom_frontiers_ntimes_body_universe`. The checked parent-target
  derivative splitters are
  `rpder_norm9_path9_atom_frontier_step_RSEQ_parentI`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_parentI`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_parentI`. The direct carried
  variants
  `rpder_norm9_path9_atom_frontier_step_RSEQ_directI`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_directI`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_directI` are also checked;
  they reduce the remaining carried branch work to singleton
  `set (rflts [rsimp9 p])` obligations. The nullable
  sequence right-branch lift is also checked:
  `rnullable_rsimp9`,
  `rsubterms_rsimp9_RSEQ_right_nullable_universe`,
  `partial_derivative_path9_atom_frontier_universe_RSEQ_right_nullable_subset`,
  and `rpder_norm9_path9_atom_frontier_step_RSEQ_parent_childI`.
  The normalized-alternative child lifts are checked:
  `partial_derivative_path9_atom_frontier_universe_RALTS_flat_child_subset`,
  `rsubterms_nonalt_flattened_subterms`,
  `rsubterms_rsimp9_alt_child_nonalt_path9_atom_subset`,
  `partial_derivative_path9_atom_frontier_universe_RALTS_nonalt_child_member`,
  `rpder_norm9_path9_atom_frontier_step_RALTS_childI`, and
  `rpder_norm9_path9_atom_frontier_step_rsimp_ALTs_childI`.
  The first direct accounting split for `rpath9_atom_frontiers` is checked:
  `plus2_square_plus_plus3_square_le`,
  `sum_list_rsize_plus2_square_le_rsizes_plus3_square`,
  `card_rpath9_atom_frontier_acc_list_le`,
  `card_rpath9_atom_frontiers_RALTS_le`, and
  `card_rpath9_atom_frontiers_RALTS_quadraticI`. The matching `RALTS`
  member-size split is checked as
  `rpath9_atom_frontiers_RALTS_member_sizeI`.
  The base accounting facts for `RZERO`, `RONE`, `RCHAR`, and zero-count
  `RNTIMES` are checked via
  `card_rpath9_atom_frontiers_RZERO_quadratic`,
  `card_rpath9_atom_frontiers_RONE_quadratic`,
  `card_rpath9_atom_frontiers_RCHAR_quadratic`,
  `rpath9_atom_frontiers_RZERO_member_size`,
  `rpath9_atom_frontiers_RONE_member_size`,
  `rpath9_atom_frontiers_RCHAR_member_size`,
  `card_rpath9_atom_frontiers_RNTIMES_zero_quadratic`, and
  `rpath9_atom_frontiers_RNTIMES_zero_member_size`.
  The next carried-continuation accounting helpers are also checked:
  `rfrontier_member_size_le_rsize`, `card_rfrontier_rsimp7_SEQ_atom_le`, and
  `rfrontier_rsimp7_SEQ_atom_member_size_le`.
  The first path9 accounting constructor splitters are checked:
  `card_rpath9_atom_frontiers_RSEQ_le`,
  `card_rpath9_atom_frontiers_RSTAR_le`,
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_le`,
  `rpath9_atom_frontiers_RSEQ_member_sizeI`,
  `rpath9_atom_frontiers_RSTAR_member_sizeI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_sizeI`.
  The conditional quadratic constructor layer is checked:
  `seq_component_product_plus_child_square_le`,
  `component_product_le_square`,
  `card_rpath9_atom_frontiers_RSEQ_quadraticI`,
  `card_rpath9_atom_frontiers_RSTAR_quadraticI`, and
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_quadraticI`; the remaining
  cardinality obligation is the carried collector product bound.
  Tail-normalization frontier bounds are checked:
  `rsize_rsimp4_SEQ_atom_RONE_le`,
  `rsize_rsimp7_SEQ_atom_RONE_le`,
  `rsize_rsimp7_SEQ_atom_rsimp9_RONE_le`,
  `card_rfrontier_rsimp7_SEQ_atom_RONE_le`,
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RONE_le`,
  `rfrontier_rsimp7_SEQ_atom_RONE_member_size_le`, and
  `rfrontier_rsimp7_SEQ_atom_rsimp9_RONE_member_size_le`.
  The carried-collector base cases are checked:
  `card_rpath9_atom_frontier_acc_RZERO_product`,
  `card_rpath9_atom_frontier_acc_RONE_product`,
  `card_rpath9_atom_frontier_acc_RCHAR_le`,
  `rpath9_atom_frontier_acc_RCHAR_member_size_le`,
  `card_rpath9_atom_frontier_acc_RCHAR_rsimp9_RONE_product`, and
  `rpath9_atom_frontier_acc_RCHAR_rsimp9_RONE_member_size`.
  The carried-collector constructor splitters are checked:
  `sum_list_map_rsize_mult_right`,
  `card_rpath9_atom_frontier_acc_RALTS_productI`,
  `rpath9_atom_frontier_acc_RALTS_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RSEQ_le`,
  `rpath9_atom_frontier_acc_RSEQ_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RSTAR_le`,
  `rpath9_atom_frontier_acc_RSTAR_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_le`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_member_sizeI`.
  The product-introduction layer is also checked:
  `card_rpath9_atom_frontier_acc_RSEQ_productI`,
  `card_rpath9_atom_frontier_acc_RSTAR_productI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_productI`,
  `card_rpath9_atom_frontier_acc_RBACKREF4_productI`,
  `rpath9_atom_frontier_acc_RBACKREF4_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RHALF_productI`,
  `rpath9_atom_frontier_acc_RHALF_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RRESIDUE_product`, and
  `rpath9_atom_frontier_acc_RRESIDUE_member_size`.
  The normalized nested-tail budget facts are checked:
  `rsize_rsimp7_SEQ_atom_rsimp9_nested_RONE_le`,
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_nested_RONE_le`, and
  `rfrontier_rsimp7_SEQ_atom_rsimp9_nested_RONE_member_size_le`.
  The corresponding `RCHAR` accumulator instances are checked:
  `card_rpath9_atom_frontier_acc_RCHAR_rsimp9_nested_RONE_product` and
  `rpath9_atom_frontier_acc_RCHAR_rsimp9_nested_RONE_member_size`.
  The `RSEQ` normalized-tail handoff is checked:
  `card_rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_productI` and
  `rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_member_sizeI`.
  The `RSTAR`/`RNTIMES` normalized-tail handoffs are checked:
  `card_rpath9_atom_frontier_acc_RSTAR_rsimp9_RONE_productI`,
  `rpath9_atom_frontier_acc_RSTAR_rsimp9_RONE_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_productI`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_member_sizeI`.
  The budget-compatible variants are checked:
  `card_rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_balanced_productI`,
  `rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_balanced_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_outer_productI`,
  and `rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_outer_member_sizeI`.
  The top-level path9 frontier cardinality bound is now checked:
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RSTAR_le`,
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RNTIMES_le`,
  `sum_list_rsize_times_rsize_plus_le`, `seq_frontier_acc_card_arith`,
  `card_rpath9_atom_frontier_acc_le_size_frontier`, and
  `card_rpath9_atom_frontiers_quadratic`. The relaxed top-level interfaces
  `card_rpath9_atom_frontiers_RSEQ_quadratic_seq_RONEI`,
  `card_rpath9_atom_frontiers_RSTAR_quadratic_seq_RONEI`, and
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_quadratic_seq_RONEI` are also
  checked. Remaining BR-036 proof debt is linear member-size for the path9
  frontier universe and one-step `rpder_norm9_list` closure.
  The cubic interface now consumes the checked card theorem directly via
  `rsizes_distinct_path9_atom_frontier_universe_cubic_member_sizeI`,
  `rsizes_rpders_norm19_rows_path9_atom_frontier_universe_cubic`, and
  `rsizes_rpders_norm19_rows_rsimp9_path9_atom_frontier_cubicI`; future work
  only needs the linear member-size premise and the one-step path9 closure.
  The current left-continuation bridge has a checked stable-tail helper layer:
  `rsimp4_SEQ_atom_RONE_stable_rsimp7_SEQ_atom`,
  `rsimp4_SEQ_atom_RONE_stable_rsimp_ALTs`, and
  `rsimp4_SEQ_atom_RONE_stable_rdistinct`. These do not collect BR-036, but
  they are the next modular interface for closing `RALTS`/nested-`RSEQ`
  carried-tail cases without broad slow automation.
  The stable-tail left bridge now also has a checked `RALTS`-of-`RCHAR`
  package: `rpath9_atom_frontiers_seq_alt_left_subset`,
  `rpath9_atom_frontiers_seq_alt_left_universe`,
  `rder_path_continuations_acc_RALTS_RCHARs_left_path9_stable`, and
  `rpder_norm9_path9_atom_frontier_step_RSEQ_RALTS_RCHARs_stable` with
  `RZERO`/`RONE`/`RCHAR`/`RSTAR`/`RNTIMES` right-tail instances. This is
  checked progress toward one-step closure, not a BR-036 payout claim.
  The same character-alternative body shape is now checked for `RSTAR` and
  `RNTIMES` via
  `rder_path_continuations_acc_RALTS_RCHARs_root_path9_RSTAR`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_RALTS_RCHARs`,
  `rder_path_continuations_acc_RALTS_RCHARs_root_path9_RNTIMES`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_RALTS_RCHARs`. The counted
  proof explicitly splits the zero-predecessor case, where `RONE` is admitted
  by the universe rather than by a body-frontier inclusion.
  The normalized alternative shape is also bridged by
  `rpder_norm9_path9_atom_frontier_step_RSEQ_rsimp_ALTs_RCHARs_stable`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_rsimp_ALTs_RCHARs`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_rsimp_ALTs_RCHARs`, which
  split `rsimp_ALTs` into empty, singleton-character, and genuine-`RALTS`
  cases. This is still only checked progress toward BR-036.
  Character-only alternatives now survive the literal `rsimp9 (RALTS rs)`
  normalizer path via `rflts_RCHARs_eq`, `RCHARs_rflts`,
  `RCHARs_rflts_map_rsimp9`, `RCHARs_rdistinct`, and
  `RCHARs_rdistinct_rflts_map_rsimp9`. The direct closure packages
  `rpder_norm9_path9_atom_frontier_step_RSEQ_rsimp9_RALTS_RCHARs_stable`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_rsimp9_RALTS_RCHARs`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_rsimp9_RALTS_RCHARs` are
  checked for that exact normalized shape.

## Completed

| ID | Task | Bounty | Est. Lines | Difficulty | Est. USD | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |
| BR-001 | Language nullable/derivative pilot | 200 | 80 | 6 | 200 | DONE | Codex | BackRefLang.thy:BL_BBACKREF_empty,xnullable_correctness,xder_correctness,xders_correctness | Isabelle:BackRefPilot | PR #1, merged |
| BR-002 | Value/Prf/flat correspondence pilot | 160 | 60 | 6 | 160 | DONE | Codex | BackRefValues.thy:BL_flat_BPrf | Isabelle:BackRefPilot | `BackRefValues.thy`, build passes |
| BR-003 | Add `bmkeps` for pilot nullable values | 80 | 20 | 4 | 80 | DONE | Codex | BackRefValues.thy:bmkeps | Isabelle:BackRefPilot | `bmkeps` in `BackRefValues.thy` |
| BR-004 | Prove `bmkeps` flat/prf correctness | 120 | 30 | 5 | 120 | DONE | Codex | BackRefValues.thy:bmkeps_flat,bmkeps_BPrf | Isabelle:BackRefPilot | `bmkeps_flat`, `bmkeps_BPrf` |
| BR-005 | Draft `binjval` statement blueprint | 500 | 30 | 5 | 500 | DONE | Opus | BackRefValues.thy:binjval | Isabelle:BackRefPilot | Commit `b9da0e1` |
| BR-006 | Add guard scripts for bounty/role checks | 60 | 10 | 3 | 60 | DONE | Codex | agent_hunt_pipeline/scripts/backref_bounty_guard.py;agent_hunt_pipeline/scripts/backref_role_guard.py | LocalGuards | `backref_bounty_guard.py`, `backref_role_guard.py` |
| BR-007 | Generalized four-language backreference blueprint | 160 | 20 | 5 | 160 | DONE | Codex | BackRefLang.thy:backref_lang4,backref_lang_as_backref_lang4 | Isabelle:BackRefPilot | `backref_lang4`, `backref_lang_as_backref_lang4` |
| BR-008 | Draft derivative story for generalized `backref_lang4` | 800 | 60 | 6 | 800 | DONE | Codex | BackRefLang.thy:backref_lang4I,Der_backref_lang4 | Isabelle:BackRefPilot | Derivative splits prefix, capture-with-accumulator, and post-capture tail |
| BR-009 | Local and GitHub Isabelle CI with anti-cheat gate | 260 | 15 | 4 | 260 | DONE | Codex | agent_hunt_pipeline/scripts/isabelle_ci.ps1;agent_hunt_pipeline/scripts/backref_no_cheat_guard.py;agent_hunt_pipeline/scripts/write_ci_certificate.py;.github/workflows/isabelle.yml | Isabelle:Posix+BackRefPilot | CI certificate only after both sessions pass |
| BR-010 | Reproduce recurring tmux prompt loop | 90 | 10 | 3 | 90 | DONE | Codex | agent_hunt_pipeline/scripts/backref_idle_watch.sh;agent_hunt_pipeline/scripts/test_tmux_recurring_prompt.sh;agent_hunt_pipeline/WINDOWS_RUNBOOK.md | WSL:tmux-recurring-test | Same paper prompt injected repeatedly |
| BR-011 | Prove `bflat (binjval r c v) = c # bflat v` | 1,000 | 40 | 6 | 1,000 | DONE | Opus | BackRefValues.thy:binjval_flat | Isabelle:BackRefPilot | Commit `6dc8e03` |
| BR-012 | Prove `BPrf (binjval r c v) r` when `BPrf v (xder c r)` | 1,200 | 50 | 7 | 1,200 | DONE | Opus | BackRefValues.thy:binjval_BPrf | Isabelle:BackRefPilot | Commit `6dc8e03` |
| BR-013 | Define and prove `blexer` for pilot `brexp` | 1,500 | 80 | 7 | 1,500 | DONE | Opus | BackRefValues.thy:blexer,blexer_BPrf,blexer_flat,blexer_correct_None,blexer_correct_Some | Isabelle:BackRefPilot | Commit `2e8c45a` |
| BR-014 | Prove `blexer` correctness for pilot `brexp` | 2,000 | 100 | 8 | 2,000 | DONE | Opus | BackRefValues.thy:blexer_correctness,BPosix_binjval,blexer_POSIX,blexer_POSIX_iff | Isabelle:BackRefPilot | Cursor proof lane, Codex stabilization/build verification |
| BR-015 | POSIX value ordering for backreferences | 2,500 | 120 | 8 | 2,500 | DONE | Codex | BackRefValues.thy:BPosix_determ | Isabelle:BackRefPilot | Codex-B lane; uses `BSEQ_split_unique`, nullable empty-value uniqueness, and `BPosix_BBACKREF_value_unique` |
| BR-016 | Generalized `backref_lang4` value pilot | 1,500 | 70 | 7 | 1,500 | DONE | Codex | BackRefLang4Values.thy:bval4,bflat4,BPrf4,backref_lang4_flat_BPrf4,backref_lang_flat_BPrf4_special | Isabelle:BackRefPilot | Explicit value-evidence blueprint before datatype migration |
| BR-017 | Bitcoded backreference lexer definition | 2,500 | 100 | 8 | 2,500 | DONE | Codex | BackRefBlexer.thy:bbit,barexp,berase,bfuse,baintern,bbnullable,bbmkeps,bbder,bblexer | Isabelle:BackRefPilot | Separate pilot file; erase/nullable/derivative checks included |
| BR-018 | Bitcoded backreference lexer correctness | 3,000 | 150 | 9 | 3,000 | DONE | Codex | BackRefBlexer.thy:bbder_bretrieve,bblexer_blexer_retrieve | Isabelle:BackRefPilot | Derivative retrieval transport plus bitcoded output matches `bretrieve (baintern r)` of `blexer` value |
| BR-019 | Bounded fragment theorem for backreferences | 4,000 | 200 | 9 | 4,000 | DONE | Codex | BackRefBoundedBlueprint.thy:BL_bound_BBACKREF_derivative_family_card_bound,GBL_bound_GBACKREF4_derivative_family_card_bound | Isabelle:BackRefPilot | Constructor-specific bounded-fragment derivative families land in finite bounded-string universes with explicit cardinal bounds |
| BR-020 | Simplification rules for backreference lexer | 2,000 | 90 | 7 | 2,000 | DONE | Codex | BackRefBlexer.thy:bbsimp,bblexer_simp_correctness,bblexer_step_simp_correctness | Isabelle:BackRefPilot | Post-derivative and per-step simplified loops preserve `bblexer` |
| BR-021 | Cursor/Opus loop startup kit | 140 | 15 | 4 | 140 | DONE | Codex | .cursor/hooks/posix_loop.ps1;.cursor/hooks/posix_loop.sh;agent_hunt_pipeline/projects/posix-backref/loop-config.cursor-opus.json;agent_hunt_pipeline/projects/posix-backref/SLEEP_RUNBOOK.md | CursorHook:posix-loop | Supplemental robust hook and sleep runbook |
| BR-022 | Bounded-fragment statement blueprint | 1,200 | 60 | 7 | 1,200 | DONE | Codex | BackRefBoundedBlueprint.thy:bounded_GBACKREF4_finite_derivative_languages | Isabelle:BackRefPilot | Semantic bounded-language blueprint for finite derivative-language families; no production bounds or closed forms touched |
| BR-032 | Define stronger cubic-bound simplifier | 25,000 | 260 | 10 | 25,000 | DONE | Codex | BasicIdentities.thy:rsimp7_SEQ_atom,rsimp7_SEQ,rsimp7,RL_rsimp7;BlexerSimp.thy:bsimp7_ASEQ_atom,bsimp7_ASEQ,bsimp7,bpder_norm7_list,bp_der_norm7,bpder_norm7_rows;GeneralRegexBound.thy:rpder_norm7_list,rpd_der_norm7,rpder_norm7_rows,rpders_norm17_rows,RLS_rpders_norm17_rows,RL_rders_pder_norm7;FBound.thy:bsimp7_rerase,bp_der_norm7_rerase,rpders_norm17_rows_rerase,RL_rerase_bders_pder_norm7 | Isabelle:Posix | Checked `rsimp7`/`bsimp7` adds prefix star absorption `r*.(r*.k)=r*.k` over Antimirov row lists; final repeated-row cubic closure remains BR-033 |
| BR-035 | Define root-safe cubic simplifier | 25,000 | 260 | 10 | 25,000 | DONE | Codex | BasicIdentities.thy:rsimp8,rders_simp8,RL_rsimp8,RL_rders_simp8;BlexerSimp.thy:bsimp8,bders_simp8;FBound.thy:bsimp8_rerase,rders_simp8_size,RL_rerase_bders_simp8;GeneralRegexBound.thy:rsize_rsimp8_le,rsizes_rpders_norm17_rows_rsimp8_live_row_cubicI | Isabelle:Posix | New 50k cubic tranche: checked root normalizer preserves language and erasure while avoiding `rsimp7` root-size blow-up; conditional cubic interface is w.r.t. original `rsize r` |

## Effort Estimate Key

Every bounty must include an effort estimate before it can be locked:

- **Est. Lines**: approximate lines of a textbook proof for this result.
- **Difficulty**: formalization difficulty on a 1-10 scale (1 = trivial, 10 = research-level).
- **Est. USD**: approximate cost assuming $100/hour of expert Isabelle work.

Estimates assume all previous results in the dependency chain are already proved.

## Locks

| Lock ID | Task ID | Agent | Deposit | Branch | Expires UTC | Status |
| --- | --- | --- | ---: | --- | --- | --- |
| - | - | - | 0 | - | - | RELEASED |
| L-OPUS-015 | BR-015 | Opus | 250 | codex/backref-values | 2026-05-27T07:38:41Z | RELEASED |
| L-CODEX-B-015 | BR-015 | Codex | 250 | codex/backref-values | 2026-05-27T15:44:00Z | COLLECTED |
| L-CODEX-A-022 | BR-022 | Codex | 120 | codex/backref-values | 2026-05-27T15:44:01Z | COLLECTED |
| L-CODEX-017 | BR-017 | Codex | 250 | codex/backref-values | 2026-05-27T09:35:51Z | COLLECTED |
| L-CODEX-A-019 | BR-019 | Codex | 400 | codex/backref-values | 2026-05-27T18:46:17Z | COLLECTED |

## Lock Rules

- Lock deposit: 10% of bounty, rounded up.
- Maximum **10** active locks per agent.
- Locks expire after **24 hours**.
- Push locks immediately if multiple agents are active.
- Lock-or-lose: if someone else proves a locked theorem, bounty goes to locker.
- A lock does not authorize statement changes.
- Admin can clear stale locks.
- Expired lock deposit is forfeited (not refunded).

## Ledger

| Time UTC | Agent | Action | Task ID | Amount | Balance After | Notes |
| --- | --- | --- | --- | ---: | ---: | --- |
| 2026-05-22T14:00:00Z | Codex | COLLECT | BR-001 | 200 | 200 | Language nullable/derivative pilot merged in PR #1 |
| 2026-05-22T14:20:00Z | Codex | COLLECT | BR-002 | 160 | 360 | Value/Prf/flat correspondence |
| 2026-05-22T14:28:00Z | Codex | COLLECT | BR-003 | 80 | 440 | `bmkeps` definition |
| 2026-05-22T14:28:00Z | Codex | COLLECT | BR-004 | 120 | 560 | `bmkeps` flat and Prf correctness |
| 2026-05-25T16:24:31Z | Opus | COLLECT | BR-005 | 500 | 500 | `binjval` definition |
| 2026-05-24T02:58:00Z | Codex | COLLECT | BR-006 | 60 | 620 | Bounty and role guard scripts |
| 2026-05-24T02:58:00Z | Codex | COLLECT | BR-007 | 160 | 780 | Generalized `backref_lang4` blueprint |
| 2026-05-25T03:40:00Z | Codex | COLLECT | BR-009 | 260 | 1,040 | Local and remote Isabelle CI gates |
| 2026-05-25T04:22:00Z | Codex | COLLECT | BR-010 | 90 | 1,130 | Recurring tmux prompt reproduction |
| 2026-05-25T15:24:00Z | Codex | COLLECT | BR-021 | 140 | 1,270 | Cursor/Opus loop startup kit |
| 2026-05-25T23:24:27Z | Opus | COLLECT | BR-011 | 1,000 | 1,500 | `binjval_flat` |
| 2026-05-25T23:24:27Z | Opus | COLLECT | BR-012 | 1,200 | 2,700 | `binjval_BPrf` |
| 2026-05-25T23:37:17Z | Opus | COLLECT | BR-013 | 1,500 | 4,200 | pilot `blexer` definition and language correctness |
| 2026-05-26T03:58:00Z | Opus | COLLECT | BR-014 | 2,000 | 6,200 | `blexer_correctness`, `BPosix_binjval`, `blexer_POSIX`, `blexer_POSIX_iff`; Codex stabilized build |
| 2026-05-26T07:38:41Z | Opus | LOCK | BR-015 | 250 | 5,950 | Lock L-OPUS-015 for POSIX value ordering / `BPosix_determ` |
| 2026-05-26T09:15:17Z | Codex | COLLECT | BR-008 | 800 | 2,070 | `backref_lang4I`, `Der_backref_lang4`; BackRefPilot passed |
| 2026-05-26T09:35:51Z | Codex | LOCK | BR-017 | 250 | 1,820 | Lock L-CODEX-017 for bitcoded backreference lexer definitions |
| 2026-05-26T09:42:18Z | Codex | COLLECT | BR-017 | 2,500 | 4,320 | `BackRefBlexer.thy` definitions plus erase/nullable/derivative checks; BackRefPilot passed |
| 2026-05-26T10:57:17Z | Codex | COLLECT | BR-018 | 3,000 | 7,320 | `bbder_bretrieve`, `bblexer_blexer_retrieve`; BackRefPilot passed |
| 2026-05-26T11:46:37Z | Codex | COLLECT | BR-020 | 2,000 | 9,320 | `bblexer_simp_correctness` and per-step `bblexer_step_simp_correctness`; BackRefPilot passed |
| 2026-05-26T11:57:08Z | Codex | COLLECT | BR-016 | 1,500 | 10,820 | `backref_lang4_flat_BPrf4`; BackRefPilot passed |
| 2026-05-26T15:43:53Z | Opus | RELEASE | BR-015 | 250 | 6,200 | Cursor/Opus retired because reconnect stalls made overnight work unreliable |
| 2026-05-26T15:44:00Z | Codex | LOCK | BR-015 | 250 | 10,570 | Codex-B takes over POSIX value ordering |
| 2026-05-26T15:44:01Z | Codex | LOCK | BR-022 | 120 | 10,450 | Codex-A takes non-conflicting bounded-fragment statement blueprint lane |
| 2026-05-26T16:06:05Z | Codex | COLLECT | BR-022 | 1,200 | 11,650 | `BackRefBoundedBlueprint.thy` semantic bounded-language finite derivative blueprint; BackRefPilot passed |
| 2026-05-26T18:16:47Z | Codex | COLLECT | BR-015 | 2,500 | 14,150 | `BackRefValues.thy:BPosix_determ`; BackRefPilot passed |
| 2026-05-26T18:46:17Z | Codex | LOCK | BR-019 | 400 | 13,750 | Codex-A locks bounded-fragment theorem packaging |
| 2026-05-26T18:46:18Z | Codex | COLLECT | BR-019 | 4,000 | 17,750 | `BackRefBoundedBlueprint.thy` constructor-specific derivative-family universe/card bounds; BackRefPilot passed |
| 2026-05-31T02:35:36Z | Codex | COLLECT | BR-032 | 25,000 | 42,750 | `rsimp7`/`bsimp7` prefix-star absorption definitions plus norm7 row drivers and erasure/language transfer; Posix and BackRefPilot passed |
| 2026-05-31T03:57:03Z | Codex | COLLECT | BR-035 | 25,000 | 67,750 | `rsimp8`/`bsimp8` root-safe simplifier, erasure/language bridge, size non-increase, and original-size conditional cubic interface; Posix and BackRefPilot passed |

## Sub-Bounty Rules

An agent may offer a sub-bounty from their own balance to request help:

1. Create a new task in Active with `Sub-bounty of BR-XXX` in Notes.
2. Record a `SUB_OFFER` ledger entry deducting from the offering agent.
3. Sub-bounty follows normal completion and guard rules.
4. Cancellation: `SUB_CANCEL` entry refunds the offering agent.

## Early-Finish Bonus

If the entire allocated bounty board is completed before the admin-set
deadline, 10% of the remaining unallocated pool is distributed equally among
agents who completed at least one bounty.

Run the full local CI before collecting or pushing:

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin
```
