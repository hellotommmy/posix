# POSIX Backreference Progress

Last updated: 2026-06-07 (corrected Antimirov frontier route is default)

## Corrected Antimirov Frontier Budget Update (2026-06-08)

- The corrected stage-one theorem now has a checked size/cardinality budget.
  The theorem is still about the normal derivative first, then the normal
  Antimirov frontier splitter:

  ```text
  rfrontier (rders_pder_norm r s) subset apder_frontier r
  rsize_set (rfrontier (rders_pder_norm r s))
    <= (apder_awidth r + rsize r + 3)^3
  card (rfrontier (rders_pder_norm r s))
    <= (apder_awidth r + rsize r + 3)^3
  ```

  Checked theorem names:
  `rfrontier_rders_pder_norm_subset_apder_frontier`,
  `rfrontier_rders_pder_norm_expanded_cubic_size_bound`, and
  `rfrontier_rders_pder_norm_expanded_cubic_card_bound`.
- `apder_awidth` is an expanded alphabetic width: counted repetition
  contributes `n * apder_awidth body`.  This is deliberate.  Empirical
  checks found nested `RNTIMES` can make the whole-residual frontier grow
  exponentially relative to the current compressed `rsize` if the counted
  repetitions are not first normalized/flattened.  Do not claim a cubic
  theorem in the compressed `rsize` metric from this stage-one result alone.
- Guard examples remain checked:
  `apder_frontier_keeps_whole_residuals_a_aa` keeps `a(aa)`, `aa`, `a`,
  and `1`; `apder_frontier_keeps_whole_residuals_a_alt_tail` keeps the whole
  `a(b+b+b)` residual and `b`, and does not pretend that `a` is a frontier
  residual.
- The next stage is not `row_dlforms subset apder_frontier`.  That inclusion
  is false in general: `row_dlforms`/linear forms may split `(a+b)c` into
  forms such as `ac` and `bc`, while the stage-one whole-residual frontier
  stores `(a+b)c` and `c`.  The second-stage route must use a same-front
  linear-form universe or a generated linear-form closure with its own cubic
  budget, then apply `row_dlform_canonical_rows`/strong-row canonicalization.
- Added the first checked second-stage scaffold:
  `apder_lfrontier r = Union q in apder_rows r. row_lforms q`.
  The checked inclusion is

  ```text
  alform_front r s subset apder_lfrontier r
  ```

  under `apder_nf r`, with theorem
  `alform_front_subset_apder_lfrontier`.  This deliberately counts linear
  forms in their own generated universe instead of forcing them into
  `apder_frontier`.
- Added the support budget
  `rsize_set_row_lforms_le_square` and the coarse universe bound
  `rsize_set_apder_lfrontier_le_square_rows`:

  ```text
  rsize_set (row_lforms q) <= (rsize q)^2
  rsize_set (apder_lfrontier r) <= (rsize_set (apder_rows r))^2
  ```

  This is only scaffolding.  It is not the final same-front cubic bound; the
  next proof step should avoid mixing all derivative fronts into one global
  square bound.
- `AntimirovNormalFrontier.thy` now records the corrected stage-one theorem in
  a dedicated file and has checked guard examples in that same file:
  `normal_derivative_frontier_subset`,
  `normal_derivative_frontier_cubic_size`,
  `normal_factored_rows_contract`,
  `normal_frontier_keeps_whole_residuals_a_aa`, and
  `normal_frontier_keeps_whole_residuals_a_alt_tail`.
- 2026-06-08 checked update: the pure normal/factored derivative route now has
  a regex-level cubic theorem.  The new definition is

  ```text
  normal_canonical_derivative r s =
    rsimp_ALTs
      (normal_frontier_canonical_rows (afactored1 r s))
  ```

  The theorem `normal_canonical_derivative_cubic_contract` proves

  ```text
  RL (normal_canonical_derivative r s) = Ders s (RL r)
  rfrontier (normal_canonical_derivative r s)
    subset normal_antimirov_frontier r
  rsize (normal_canonical_derivative r s)
    <= Suc ((apder_awidth r + rsize r + 3)^3)
  ```

  under `legacy_rrexp r` and `apder_nf r`.  The theorem
  `normal_canonical_derivative_exact_frontier_contract` proves the exact
  canonical/no-duplicate statement:

  ```text
  rfrontier (normal_canonical_derivative r s)
    = set (normal_frontier_canonical_rows (afactored1 r s))
  distinct (normal_frontier_canonical_rows (afactored1 r s))
  card (rfrontier (normal_canonical_derivative r s))
    <= (apder_awidth r + rsize r + 3)^3
  ```

  This completes the pure Antimirov/factored canonical derivative theorem; it
  is separate from the still-open final strong/memo POSIX route.
- 2026-06-08 follow-up: the same-front part is now explicit, not just
  implicit in the set inclusion.  Checked theorem names:

  ```text
  normal_canonical_derivative_frontier_eq_ader_front
  normal_frontier_canonical_rows_same_front
  normal_canonical_derivative_same_front_row
  normal_canonical_derivative_equiv_rders_pder_norm
  normal_canonical_derivative_main_cubic_bound
  rsimpStrong_raw_normal_canonical_derivative_cubic_contract
  ```

  In formulas, the key new equality is

  ```text
  rfrontier (normal_canonical_derivative r s) = ader_front r s
  ```

  so the canonical rows are exactly the normal Antimirov frontier for the
  current derivative string `s`.  This records the intended "same derivative
  front" invariant and avoids the earlier invalid split-atom interpretation.
- 2026-06-08 checked wrapper: applying the strong raw simplifier after the
  normal canonical derivative preserves the same cubic regex-size bound:

  ```text
  RL (rsimpStrong_raw (normal_canonical_derivative r s))
    = RL (rders_pder_norm r s)
  RL (rsimpStrong_raw (normal_canonical_derivative r s))
    = Ders s (RL r)
  rsize (rsimpStrong_raw (normal_canonical_derivative r s))
    <= Suc ((apder_awidth r + rsize r + 3)^3)
  ```

  The checked theorem is
  `normal_canonical_then_strong_main_cubic_bound`.  This closes the clean
  normal-canonical-then-strong-simplify regex route; it is still separate from
  the old raw/memo row pipeline.
- The first strong-row bridge is checked without using the old split-atom
  shortcut:

  ```text
  set (rpder_strong_rows_raw c (afactored1 r s))
    subset normal_strong_scan_owner r

  forall x in that set.
    rsize x <= 2 * (apder_awidth r + rsize r + 3)^3
  ```

  The theorem names are
  `rpder_strong_rows_raw_afactored1_subset_normal_strong_scan_owner`,
  `rpder_strong_rows_raw_afactored1_member_cubic`, and
  `rpder_strong_rows_raw_afactored1_normal_owner_contract`.
- A parameterized total-budget bridge is checked:
  `rpder_strong_rows_raw_afactored1_owner_card_budget_contract`.  It proves
  language correctness plus `length`, `card`, `rlinear_termss`, and `rsizes`
  bounds for raw one-step strong rows from `afactored1 r s`, assuming a
  cardinality bound

  ```text
  card (normal_strong_scan_owner r) <= C
  ```

  This isolates the remaining raw-row counting gap.  Do not replace this
  assumption with `sizeNregex`; that would be finite but far too large.
- The canonical second-stage interface is now checked.  The theorem
  `rpder_strong_dcanon_afactored1_same_front_contract` proves that
  canonical/deep-linear-form strong rows stay in the same derivative front:

  ```text
  same_strong_aseq_front_rows r (s @ [c])
    (rpder_strong_dcanon_rows_raw c (afactored1 r s))

  aseq_termss (rpder_strong_dcanon_rows_raw c (afactored1 r s))
    subset strong_derivative_front_terms r (s @ [c])
  ```

  The same theorem also gives cubic `card` and `rsize_set` bounds for
  `strong_derivative_front_terms r (s @ [c])`.
- The checked conditional cubic theorem for the canonical rows is
  `rpder_strong_dcanon_afactored1_dlform_cubic_interface`.  If

  ```text
  rsize_set (afactored1_strong_dlform_universe r s c)
    <= 2 * (rsize r + 3)^3
  ```

  then the canonical rows
  `rpder_strong_dcanon_rows_raw c (afactored1 r s)` are language-correct,
  `row_dlformss_disjoint`, live, size-paid, preserve the raw rows'
  `row_dlformss`, and satisfy cubic `length`, `card`, `rlinear_termss`, and
  `rsizes` budgets.
- 2026-06-08 checked strengthening of the second-stage inclusion: before
  falling back to the global `apder_strong_dlfrontier`, the one-step raw
  strong rows now have an explicit step-local universe inclusion:

  ```text
  row_dlformss (rpder_strong_rows_raw c (afactored1 r s))
    subset afactored1_strong_dlform_universe r s c
  ```

  The theorem is
  `row_dlformss_rpder_strong_rows_raw_afactored1_subset_strong_dlform_universe`.
  It has no `apder_nf r` premise.  The older theorem into
  `apder_strong_dlfrontier r` now factors through this stronger local result.
- 2026-06-08 follow-up: the same local-universe inclusion is now checked for
  the canonicalized strong rows too:

  ```text
  row_dlformss (rpder_strong_dcanon_rows_raw c (afactored1 r s))
    subset afactored1_strong_dlform_universe r s c
  ```

  The theorem is
  `row_dlformss_rpder_strong_dcanon_rows_raw_afactored1_subset_strong_dlform_universe`.
  This confirms that canonicalization itself is not the source of any
  off-front residuals; the remaining issue is purely the size/counting bound
  for the local universe.
- 2026-06-08 stronger same-front bridge: the local strong universe is now
  checked to sit inside the strong closure of the next normal factored rows:

  ```text
  afactored1_strong_dlform_universe r s c
    subset rsimpStrong_dlform_closure (set (afactored1 r (s @ [c])))
  ```

  The theorems are
  `afactored1_strong_dlform_universe_subset_next_rows_closure`,
  `rsize_set_afactored1_strong_dlform_universe_le_next_rows_closure`, and
  `row_dlformss_rpder_strong_dcanon_rows_raw_afactored1_subset_next_rows_closure`.
  This is the whole-residual/same-front formulation of the second-stage
  target: first keep the normal Antimirov rows for the derivative front
  `s @ [c]`, then allow strong simplification closure over those rows.
- The checked conditional theorem
  `rpder_strong_dcanon_rows_raw_afactored1_next_rows_closure_cubic_contractI`
  now says that if

  ```text
  rsize_set
    (rsimpStrong_dlform_closure (set (afactored1 r (s @ [c]))))
    <= 2 * (rsize r + 3)^3
  ```

  then the old raw strong/dcanon step has the same cubic contract as before.
  Thus the remaining old/raw proof obligation can be stated as a cubic
  total-size bound for a single same-front rows closure, not as an atomized
  `aseq_terms` inclusion.
- 2026-06-08 negative checkpoint: the tempting local monotonicity route is
  formally false.  The checked counterexample
  `rsimpStrong_raw_row_dlforms_cost_not_monotone` has

  ```text
  rsize_set (row_dlforms (rsimpStrong_raw p)) = 12
  rsize_set (row_dlforms p) = 10
  row_dlforms_list_size p = 10
  ```

  and therefore refutes both
  `rsize_set (row_dlforms (rsimpStrong_raw p))
    <= rsize_set (row_dlforms p)` and
  `rsize_set (row_dlforms (rsimpStrong_raw p))
    <= row_dlforms_list_size p`.
  Do not try to close the old/raw route by proving one-step
  `row_dlforms` cost nonincrease; the proof must use global same-front
  structure or a stronger whole-residual universe.
- Current remaining second-stage gap: prove the above
  `afactored1_strong_dlform_universe` cubic `rsize_set` estimate from the
  same-front/frontier structure.  Direct subset into `apder_frontier` or
  `partial_derivative_frontier_universe` is false; the checked counterexample
  `afactored1_strong_dlform_universe_not_frontier_subset` must stay visible.
  The right route is a same-front combination/counting argument, not arbitrary
  split-atom closure.
- 2026-06-08 continuation: added checked deep-row accumulator scaffolding for
  that route.  The new increment lemmas
  `rsize_set_row_dlforms_rsimp4_SEQ_atom_diff_le`,
  `rsize_set_row_dlforms_rsimp4_SEQ_atom_le`, and
  `rsize_set_row_dlforms_rsimp4_SEQ_atom_square_le` formalize shared-suffix
  accounting:

  ```text
  rsize_set (row_dlforms (rsimp4_SEQ_atom p k) - row_dlforms k)
    <= rsize p * Suc (rsize p + rsize k)

  rsize_set (row_dlforms (rsimp4_SEQ_atom p k))
    <= rsize_set (row_dlforms k)
       + (rsize p)^2 * Suc (rsize k) + (rsize p + 2)^2
  ```

  Also added `apder_dfrontier_acc_size_budget`, whose equations mirror the
  Antimirov recursion for `apder_terms`, and the checked theorem
  `rsize_set_apder_dfrontier_acc_le_budget`.  This is still scaffolding, not
  the final cubic theorem: the next step is to bound that recursive budget by
  preserving same-front/shared-suffix classes, not by independently squaring
  every generated term.
- 2026-06-08 later continuation: the direct accumulator sum above is now
  superseded by a checked delta scaffold that avoids charging the same suffix
  frontier repeatedly.  New definitions and theorems:

  ```text
  apder_dfrontier_delta_acc r k =
    apder_dfrontier_acc r k - row_dlforms k

  rsize_set (apder_dfrontier_delta_acc r k)
    <= apder_dfrontier_delta_budget r k

  rsize_set (apder_dfrontier_acc r k)
    <= rsize_set (row_dlforms k)
       + apder_dfrontier_delta_budget r k

  rsize_set (apder_deep_frontier r)
    <= rsize_set (row_dlforms r)
       + rsize_set (row_dlforms RONE)
       + apder_dfrontier_delta_budget r RONE
  ```

  This is the preferred route for the final total-size cubic theorem.  Do not
  try to prove cubic by summing `row_dlforms k` at every recursive leaf; that
  loses the shared suffix structure and creates avoidable star/sequence
  over-counting.
- Verification after these additions: Isabelle `Posix` passed, followed by
  `scripts\codex-proof-workers.ps1 -Action Check` reporting no matching
  residual proof-worker processes.

## Correction: Old Split-Atom "Stage One" Is Retracted (2026-06-07)

- The previously recorded first-step claim based on `aseq_terms` is not the
  user's requested Antimirov/linear-form decomposition.  `aseq_terms` opens
  every `RSEQ`, so it over-splits product structure: for example it treats
  `a(aa)` as only the atom `{a}`, whereas the Antimirov derivative frontier
  must keep whole residual terms such as `a(aa)`, `aa`, and `a`.
- The checked `aseq_terms` lemmas remain valid only as auxiliary split-atom
  inclusions.  They must not be described as completing stage one, and they
  are not enough to prove a regex-size cubic bound.
- The corrected stage-one target is now checked: after computing the normal
  partial derivative first, decomposing it by the normal Antimirov frontier
  splitter (not by `aseq_terms`) stays inside the root-owned Antimirov residual
  frontier:

  ```text
  rfrontier (rders_pder_norm r s) subset apder_frontier r
  ```

  The theorem is `rfrontier_rders_pder_norm_subset_apder_frontier`, under the
  proof-local normal-form assumption `apder_nf r`.  Its row-level core is
  `afactored1_apder_rows_subset`; the bridge to the existing normal derivative
  remains `rfrontier (rders_pder_norm r s) = ader_front r s`.
- Do not use `row_dlforms` as the stage-one splitter either.  `row_dlforms`
  recursively opens rows such as `RSEQ (RALTS ps) k`; that is useful later for
  canonical/prune accounting, but it is already too fine for the normal
  Antimirov derivative frontier.  The current checked guard examples are
  `apder_frontier_keeps_whole_residuals_a_aa` and
  `apder_frontier_keeps_whole_residuals_a_alt_tail`; they ensure examples like
  `a(aa)` and `a(b+b+b)` keep whole residuals rather than collapsing to atoms.
- The proof must preserve the same-front restriction; plain closure for every
  `q` in a coarse universe is too strong and admits impossible combinations.
  The remaining route is to prove a polynomial budget for this whole-residual
  frontier/canonical row representation, then connect it to the strong
  simplifier rows.

## Cubic Route Checked Update: Deep Rows And Deep Frontier Closure (2026-06-07)

- Added proof-local deep derivative rows:
  `rpder_deep_list`, `rpder_deep_rows`, `rpders_deep_rows`, and
  `rpders_deep1_rows`.  These use the Antimirov one-step generator
  `rpder_norm_list`, then normalize each generated row with `rsimpDeep_raw`,
  filter dead rows, and remove duplicates.
- Checked their core row facts: language correctness
  (`RLS_rpder_deep_rows`, `RLS_rpders_deep_rows`,
  `RLS_rpders_deep1_rows`), legacy preservation, tail normal form,
  distinctness, and `row_group_deep_nf`.
- Checked the generated one-step budgets:
  `rpder_deep_rows_generated_budget` and
  `rpder_deep_rows_generated_budget_contract`.  In particular, for a singleton
  start row,

  ```text
  length (rpder_deep_rows c [r]) <= 2 * (rsize r + 3)^3
  card (set (rpder_deep_rows c [r])) <= 2 * (rsize r + 3)^3
  ```

  This is a one-step generated-front budget, not the final arbitrary-input
  row-level cubic theorem.
- Retracted old first-step target.  The theorem
  `rders_pder_norm_split_aseq_termss_frontier_universe_subset` proves that we
  first compute the completed normal derivative `rders_pder_norm r s`, then
  open it with `row_dlforms`, and only then split products with `aseq_terms`:

  ```text
  (Union x in row_dlforms (rders_pder_norm r s). aseq_terms x)
    subset partial_derivative_frontier_universe r
  ```

  This statement is checked, but it is now classified as an auxiliary
  split-atom fact, not as the completed Antimirov stage-one theorem.

- Added the deep simplifier split-term closure
  `deep_simp_frontier_aseq_universe r =
   rsimpDeep_aseq_closure (partial_derivative_frontier_universe r)`.
  It is finite, has cubic cardinality and cubic `rsize_set` bounds, and every
  member has the same linear size bound as the original frontier terms.
- Added the checked derivative-fuel layer.  The generic
  `rderiv_fuel_closure U` closes a split-term universe under subterms and
  linear continuations.  Checked facts include subterm closure,
  star-body closure, `RNTIMES` body closure, `RNTIMES` predecessor closure,
  member-size preservation, and

  ```text
  card (rderiv_fuel_closure U) <= 2 * rsize_set U
  ```

  This is the key accounting improvement: fuel closure is charged to
  `rsize_set`, not to `card U * max_size`.
- Added the concrete cubic fuel universes
  `deep_simp_frontier_subterm_universe r` and
  `deep_simp_frontier_fuel_universe r`.  In particular,
  `card_deep_simp_frontier_fuel_universe_cubic` proves:

  ```text
  card (deep_simp_frontier_fuel_universe r) <=
    4 * (rsize r + 2)^3
  ```

  It also has checked zero/one, subterm, star-body, `RNTIMES` body,
  `RNTIMES` predecessor, and linear member-size facts.
- Added the fuel-style derivative induction interface:
  `rpder_norm_list_aseq_terms_fuel_subsetI`,
  `aseq_termss_rpders_deep_rows_fuel_closed_subsetI`, and
  `aseq_termss_rpders_deep1_rows_fuel_closed_subsetI`.  These prove arbitrary
  many deep-row steps stay in a chosen `U` once `U` has fuel closure and
  `rsimpDeep_raw` maps split terms back into `U`.
- Instantiated the raw-generation half for the concrete deep fuel universe:
  `aseq_termss_concat_map_rpder_norm_list_deep_fuel_subsetI` proves that the
  unsimplified `rpder_norm_list` frontier stays inside
  `deep_simp_frontier_fuel_universe r`; and
  `aseq_termss_rpder_deep_rows_deep_fuel_closureI` proves one full
  `rpder_deep_rows` step lands in
  `rsimpDeep_aseq_closure (deep_simp_frontier_fuel_universe r)`.
- Added the idempotent-return interface:
  `rsimpDeep_aseq_closure_subset_idemI`,
  `aseq_terms_rsimpDeep_raw_idem_closed_subsetI`, and
  `aseq_termss_rpders_deep_rows_deep_fuel_idem_subsetI`.  These show that if
  every member of `deep_simp_frontier_fuel_universe r` is already an
  `rsimpDeep_raw` fixed point, then arbitrary many `rpders_deep_rows` steps
  stay inside that same cubic fuel universe.
- Checked the normal-derivative/deep-simplifier bridge:
  after computing `rders_pder_norm r s`, applying `rsimpDeep_raw`, opening by
  `row_dlforms`, and splitting by `aseq_terms`, all split atoms land in
  `deep_simp_frontier_aseq_universe r`.
- The deep simplifier-return step is now checked.  The theorem
  `rsimpDeep_raw_deep_simp_frontier_fuel_universe_idem` proves, for legacy
  roots, that every member of `deep_simp_frontier_fuel_universe r` is already
  an `rsimpDeep_raw` fixed point:

  ```text
  p in deep_simp_frontier_fuel_universe r
  ==> rsimpDeep_raw p = p
  ```

- Consequently the arbitrary non-empty deep-row split-term bound is checked:
  `card_aseq_termss_rpders_deep1_rows_nonempty_cubic` proves

  ```text
  card (aseq_termss (rpders_deep1_rows r (c # s))) <=
    4 * (rsize r + 2)^3
  ```

  This is still a split-term theorem, not the final concrete row/DAG theorem.
- The analogous raw-strong fixed-point route is false for the current
  simplifier.  The diagnostic `rsimpStrong_raw_not_idempotent` proves a small
  checked counterexample where
  `rsimpStrong_raw (rsimpStrong_raw t) != rsimpStrong_raw t`.  Therefore the
  second stage must not try to discharge the strong fuel theorem by proving
  `rsimpStrong_raw` fixed on the whole fuel universe.
- Verification: Isabelle `Posix` passed after these changes.

## Cubic Route Checked Update: Deep Canonical Sequence Probe (2026-06-07)

- Added checked diagnostics showing why the current second-stage proof cannot
  simply assert pure-front closure for `rsimpStrong_raw`:
  `pure_adlform_front_not_closed_under_rsimpStrong_raw` proves that
  `a.(0)*` has pure next-front row `(0)*`, while `rsimpStrong_raw ((0)*) = 1`,
  so the pure `adlform_front` is not closed under strong simplification.
- Added `rsimpStrong_dlform_closure` plus basic finite/card lemmas, then
  checked a stronger negative diagnostic:
  `rsimpStrong_raw_seq_alt_dlform_closure_counterexample`.  The current
  `rsimpStrong_raw` can produce the deep row form `a.(a*.a*)` from a case where
  the old row-form strong closure only contains `a.a*`.  This exposes the
  exact sequence-recursion gap: `rsimpStrong_raw` calls `rsimp7_SEQ_atom` once,
  but the recursive reassociation inside `rsimp4_SEQ_atom` does not preserve
  star-aware absorption.
- Added a local canonical probe:
  `rsimpDeep_SEQ_atom`, which recursively reassociates sequence products while
  keeping the `rsimp7` star-absorption rules active at every join.  Checked
  facts now include `RL_rsimpDeep_SEQ_atom`,
  `rsize_rsimpDeep_SEQ_atom_le`, and
  `aseq_terms_rsimpDeep_SEQ_atom_subset`.
- Added `rsimpDeep_raw`, a proof-local normalizer using
  `rsimpDeep_SEQ_atom` for sequence and ordinary distinct/flatten cleanup for
  alternatives.  Checked facts:
  `RL_rsimpDeep_raw`, `rsize_rsimpDeep_raw_le`, and the sanity theorem
  `rsimpDeep_raw_repairs_seq_alt_dlform_counterexample`, which confirms that
  the old `a.(a*.a*)` counterexample normalizes back to `a.a*`.
- This is not the final theorem.  It establishes that the old
  `rsimpStrong_raw` canonicality route has a real checked obstruction, and
  that the deep-sequence canonicalizer repairs that obstruction while
  preserving language and size.  The remaining work is to connect this
  normalizer, or an equivalent strengthening of `rsimpStrong_raw`, to the
  front-indexed derivative-row induction and row-prune/cubic accounting.
- Verification: Isabelle `Posix` and `BackRefPilot` passed with
  `-SkipScala -SessionTimeoutSeconds 240` after these changes.

## Cubic Route Checked Update: Deep Row Split-Atom Closure (2026-06-07)

- Added checked deep-row splitter support in `AntimirovFactoredTransition.thy`:
  `row_dlforms_aseq_terms_subset` and `row_dlformss_aseq_terms_subset`.
  These prove that after a row is opened by `row_dlforms`, splitting any
  resulting deep linear form with `aseq_terms` does not introduce atoms outside
  the original row/row-list split atoms.
- Added the checked deep same-front scaffold requested by the user:
  `adlform_front`, `same_dlfront_row`, and `same_dlfront_rows`.  The key
  one-step Antimirov-front theorem is
  `row_dlforms_rpder_norm_list_afactored1_subset`: if
  `q in afactored1 root front` and
  `p in rpder_norm_list c q`, then
  `row_dlforms p subset adlform_front root (front @ [c])`.
  This pins the "same derivative front" invariant to a concrete Isabelle
  definition for deep linear forms.
- Added checked deep-front cleanup preservation:
  `same_dlfront_rows_rflts`, `same_dlfront_rows_rdistinct`,
  `same_dlfront_rows_rprune_eq_against`, and
  `same_dlfront_row_rsimp_ALTs`.  These are the deep analogues of the earlier
  shallow `same_lfront_*` transport lemmas and will be used to connect the
  front invariant through scan/prune cleanup.
- Connected that support to the completed normal derivative:
  `row_dlforms_rders_pder_norm_split_terms_frontier_universe_subset` and
  `row_dlforms_rders_pder_norm_split_terms_frontier_universe_contract` prove
  that if `x` is obtained by first computing `rders_pder_norm r s` and only
  then opening it with `row_dlforms`, then

  ```text
  aseq_terms x subset partial_derivative_frontier_universe r
  ```

  with the same quadratic card bound and linear member-size bound for those
  split atoms.
- Connected the same interface to raw strong multi-step rows:
  `row_dlformss_rpders_strong1_rows_raw_split_terms_frontier_universe_subsetI`
  and
  `row_dlformss_rpders_strong1_rows_raw_split_terms_frontier_universe_contractI`.
  These are conditional on the existing `rsimpStrong_raw` frontier-preserving
  norm premise and prove the same atom-level frontier contract for every
  `x in row_dlformss (rpders_strong1_rows_raw r s)`.
- Important limitation: these theorems prove
  `aseq_terms x subset partial_derivative_frontier_universe r`, not
  `x in partial_derivative_frontier_universe r`.  For product rows
  `x = RSEQ p k`, the latter is strictly stronger and requires the
  front-indexed/same-front combination invariant from the user's sketch.
  Existing diagnostics already show that whole residual rows may need
  path/carry continuations rather than the smaller frontier universe.
- Verification: Isabelle `Posix` and `BackRefPilot` passed with
  `-SkipScala -SessionTimeoutSeconds 240` after these changes.

## Cubic Route Checked Update: Linear-Form Accounting and Payload Stability (2026-06-07)

- Added raw multi-step language correctness for raw strong rows:
  `RLS_rpders_strong_rows_raw` and `RLS_rpders_strong1_rows_raw`.
- Added the conditional row-level cubic bridge:
  `rpders_strong1_rows_raw_canonical_lforms_cubic_contractI`.  It proves the
  raw multi-step correctness plus all four row budgets from these explicit
  canonical hypotheses on `rpders_strong1_rows_raw r s`:
  `row_lformss_disjoint`, all rows live, all rows are size-paid by their
  linear forms, and all row linear forms lie in the chosen cubic lform
  universe.
- Added checked linear-form accounting lemmas:
  `rsizes_rows_canonical_strong_simp_lforms_cubic` and
  `rsizes_row_nf_distinct_strong_simp_lforms_cubic`.  These reduce row-size
  cubicity to `rsize_set` cubicity of the row linear-form universe.
- Added checked raw-prune lform monotonicity under the new payload canonical
  condition:

  ```text
  row_payload_lform_stable p =
    row_lforms_tail_stable p and
    (forall k. row_lforms_suffix_stable p k)
  ```

  Main bridge lemmas:
  `row_lforms_rsimpStrong_prune_pair_raw_subset_later_payload_stableI`,
  `row_lformss_rsimpStrong_prune_rows_raw_subset_pairI`, and
  `row_lformss_rpder_strong_rows_raw_subset_generated_payload_stableI`.
  In words: if the payloads of a shared-suffix later row are stable, raw
  scan/prune deletes linear forms but does not create new ones.
- Added diagnostics showing why weaker normal forms are insufficient:
  `row_nf_does_not_imply_tail_stable` and
  `rtail_nf_does_not_imply_tail_stable`.  The first catches left-nested
  sequence reassociation; the second catches nested group rows used as
  payloads.
- Current remaining blocker: prove that actual generated group payloads are
  `row_payload_lform_stable`, or strengthen the simplifier so that generated
  payloads satisfy this condition.  This is now the named second-stage
  canonical gap.
- Verification: Isabelle `Posix` and `BackRefPilot` passed with
  `-SkipScala -SessionTimeoutSeconds 240` after these changes.  Scala smoke
  was not rerun for this proof-only update.

## Cubic Route Checked Update: Second-Stage Strong Simplifier Closure (2026-06-07)

- Added the checked simplifier-side split-term closure
  `strong_simp_frontier_aseq_universe r`, defined as
  `rsimpStrong_aseq_closure (partial_derivative_frontier_universe r)`.
  It is finite, every member has size at most `Suc (rsize r + rsize r)`,
  and its cardinality is bounded by:

  ```text
  card (strong_simp_frontier_aseq_universe r) <=
    2 * (rsize r + 2)^3
  ```

- Proved the corrected normal-derivative-to-strong-simplifier bridge:

  ```text
  aseq_terms (rsimpStrong_raw (rders_pder_norm r s)) subset
    strong_simp_frontier_aseq_universe r
  ```

  The package theorem
  `rsimpStrong_raw_rders_pder_norm_frontier_closure_nf_contract` also gives
  the cubic cardinality bound, the linear member-size bound, and
  `row_group_deep_nf` for the simplified normal derivative.
- Proved one-step raw-strong row bridges from bounded Antimirov states:
  `rpder_strong_rows_raw_rders_pder_norm_frontier_closure_nf_contract` and
  `rpder_strong_rows_raw_afactored1_frontier_closure_nf_contract`.  These show
  that one raw-strong step from either the completed normal derivative row or
  the factored Antimirov rows lands in the same
  `strong_simp_frontier_aseq_universe`, with the same cubic card bound,
  linear member-size bound, and `row_group_deep_nf` rows.
- Added raw strong-row normal-form preservation lemmas:
  `row_group_deep_nf_rpder_strong_list_raw`,
  `row_group_deep_nf_rpder_strong_list_raw_legacy`,
  `row_group_deep_nf_rpder_strong_rows_raw`,
  `row_group_deep_nf_rpder_strong_rows_raw_legacy`,
  `row_group_deep_nf_rpders_strong_rows_raw`, and the non-empty legacy
  variant `row_group_deep_nf_rpders_strong_rows_raw_legacy_Cons`.
- Important limitation: this is still not the final all-input cubic theorem.
  `strong_simp_frontier_aseq_universe` is a split-term/simplifier closure
  universe.  The final memo route still needs a concrete row-level universe
  closed under raw active-suffix/later-shared pruning and subterms, matching
  the interface of
  `strong_deferred_original_raw_row_norm_later_shared_memo_cubic_interface`.
- Verification: full local CI passed after these changes, including Scala
  strong-memo smoke/fuzz and Isabelle `Posix` plus `BackRefPilot`.

## Cubic Route Checked Update: Normal-Derivative Split Terms (2026-06-06)

- Added `AntimirovFactoredTransition.thy` front-indexed linear-form machinery:
  `row_lforms`, `row_lformss`, `alform_front`, `same_lfront_row`, and
  `same_lfront_rows`.
- Earlier split-atom target: the theorem applies to the completed
  normal derivative regex, not only to already-factored rows, but it still
  splits too finely for the user's Antimirov frontier route.  The bridge
  theorem `anorm_der_eq_rders_pder_norm` proves that collapsing the factored
  Antimirov rows with `rsimp_ALTs` is exactly the existing normal derivative
  iterator `rders_pder_norm`.  Therefore
  `rders_pder_norm_aseq_terms_frontier_universe_contract` proves:

  ```text
  aseq_terms (rders_pder_norm r s) subset
    partial_derivative_frontier_universe r
  ```

  with the quadratic card bound and linear member-size bound.  This remains an
  auxiliary split-atom theorem; the corrected whole-residual theorem is
  `rfrontier_rders_pder_norm_subset_apder_frontier`.
- The front-indexed theorem is still checked, but it is now recorded as
  supporting structure rather than the first-step endpoint: every residual
  linear form at a fixed derivative front, when split by `aseq_terms`, lies in
  the original `partial_derivative_frontier_universe`.
  Main theorem:
  `alform_front_aseq_terms_frontier_universe_contract`.
- Added same-front preservation bridges for row cleanup operations:
  `same_lfront_rows_rflts`, `same_lfront_rows_rdistinct`,
  `same_lfront_rows_rprune_eq_against`, and
  `same_lfront_row_rsimp_ALTs`.
- Also checked the lifted same-front contract
  `same_lfront_rows_aseq_terms_frontier_universe_contract`.
- Second-step scaffold added and checked:
  `afactored_steps_append`, `afactored1_snoc`,
  `row_lformss_rflts_eq`, `row_lformss_rdistinct_empty_eq`,
  `row_lformss_afactored_step_eq_generated`, `alform_front_snoc`, and
  `row_lforms_rpder_norm_list_afactored1_subset`.  These make the pure
  Antimirov next-front equality explicit: generating one more derivative from
  `afactored1 root front` lands in `alform_front root (front @ [c])`.
- Added checked diagnostics ruling out two naive second-step invariants:
  `rsimpStrong_raw_aseq_terms_not_monotone` shows strong raw simplification is
  not monotone on `aseq_terms`; and
  `row_lforms_rsimpStrong_prune_pair_raw_not_monotone` shows shared-suffix raw
  pruning is not monotone on `row_lforms`.  The simplifier-side proof must
  therefore use a front-indexed normal/closure invariant that accounts for
  dead branches and simplifier-created constants, not a plain subset argument.
- Current remaining blocker for a final raw strong cubic theorem:
  prove the simplifier-side/canonical side, i.e. discharge the existing
  `rsimpStrong_raw` frontier-universe closure premise or replace it with a
  same-front no-redundancy theorem.  A naive
  `aseq_terms (rsimpStrong_raw p) subset aseq_terms p` is false because star
  bodies can simplify to `RONE`; the needed statement must use the
  front-indexed universe/canonical-normal-form invariant.

## Cubic Route Constraint: Same-Front Antimirov Combinations (2026-06-06)

- User-fixed proof route: do not treat arbitrary subsets of the
  Antimirov/partial-derivative term universe as valid rows.  The derivative
  invariant should be front-indexed:

  ```text
  aseq_terms(row) subset T_r(front)
  ```

  for some derivative-front/residual-front label `front`, where `T_r(front)` is
  the block of original Antimirov terms that can share the same predecessor
  derivative history.
- Intended split of responsibilities:
  - Derivative proof: after any number of derivatives, rows split into
    original Antimirov terms, and each row contains only same-front terms.  This
    proves "no mixed-front combinations".
  - Simplifier proof: `simpStrong` / `rsimpStrong_raw` canonicalizes within an
    already-valid front and removes duplicate/redundant terms.  It should not
    be responsible for proving the Antimirov inclusion invariant.
- Examples to preserve:
  - `(a+b)c` has terms `(a+b)c` and `c`, but they are different-front terms and
    must not be combined.
  - `a*b + a*c` allows `b` and `c` to combine because they can share the same
    consumed-prefix/front history.
  - `(aa)*b + a*c` keeps the same lesson: admissible grouping is based on
    compatible front history, not merely syntactic parent equality.
- This constraint strengthens the already checked plain inclusion theorem
  `afactored1_aseq_terms_frontier_universe_contract`.  Plain inclusion into
  `partial_derivative_frontier_universe r` is useful but too weak for the raw
  regex-size theorem, because it permits arbitrary combinations and loses the
  front discipline needed to bound concrete rows.

## Cubic Route Checkpoint: Antimirov-Style Row Count Scaffold (2026-06-05)

- Final theorem status: **not complete**. This checkpoint proves a one-step
  accounting scaffold in the style of Antimirov linear forms; it does not close
  the all-input memo/DAG bridge theorem.
- Checked Isabelle additions:
  - `GeneralRegexBound.thy:length_le_rsizes`
  - `GeneralRegexBound.thy:card_set_le_rsizes_early`
  - `GeneralRegexBound.thy:length_rflts_le_rsizes`
  - `GeneralRegexBound.thy:length_rpder_norm_list_le_rsize`
  - `GeneralRegexBound.thy:card_set_rpder_norm_list_le_rsize`
  - `GeneralRegexBound.thy:length_concat_map_rpder_norm_list_le_rsizes`
  - `GeneralRegexBound.thy:length_rpder_norm_rows_le_generated_rsizes`
  - `GeneralRegexBound.thy:card_set_rpder_norm_rows_le_generated_rsizes`
  - `GeneralRegexBound.thy:length_rpder_norm_rows_single_cubic`
  - `GeneralRegexBound.thy:card_set_rpder_norm_rows_single_cubic`
  - `GeneralRegexBound.thy:length_rsimpStrong_prune_rows_acc_raw`
  - `GeneralRegexBound.thy:length_rsimpStrong_prune_rows_raw`
  - `GeneralRegexBound.thy:rsize_rsimpStrong_prune_against_rows_raw_le`
  - `GeneralRegexBound.thy:rsizes_rsimpStrong_prune_rows_acc_raw_le`
  - `GeneralRegexBound.thy:rsizes_rsimpStrong_prune_rows_raw_le`
  - `GeneralRegexBound.thy:rsize_rsimpStrong_ALTs_raw_le`
  - `GeneralRegexBound.thy:rsize_rsimpStrong_raw_le`
  - `GeneralRegexBound.thy:length_rpder_strong_rows_le_generated_rsizes`
  - `GeneralRegexBound.thy:card_set_rpder_strong_rows_le_generated_rsizes`
  - `GeneralRegexBound.thy:length_rpder_strong_rows_single_cubic`
  - `GeneralRegexBound.thy:card_set_rpder_strong_rows_single_cubic`
  - `GeneralRegexBound.thy:rsizes_rpder_strong_list_raw_le`
  - `GeneralRegexBound.thy:rsizes_concat_rpder_strong_list_raw_le`
  - `GeneralRegexBound.thy:rsizes_rpder_strong_rows_raw_le`
  - `GeneralRegexBound.thy:length_rpder_strong_rows_raw_le_generated_rsizes`
  - `GeneralRegexBound.thy:card_set_rpder_strong_rows_raw_le_generated_rsizes`
  - `GeneralRegexBound.thy:length_rpder_strong_rows_raw_single_cubic`
  - `GeneralRegexBound.thy:card_set_rpder_strong_rows_raw_single_cubic`
  - `FBound.thy:length_rpder_norm_rows_rerase_intern_single_cubic`
  - `FBound.thy:card_set_rpder_norm_rows_rerase_intern_single_cubic`
  - `FBound.thy:length_rpder_strong_rows_rerase_intern_single_cubic`
  - `FBound.thy:card_set_rpder_strong_rows_rerase_intern_single_cubic`
  - `FBound.thy:length_rpder_strong_rows_raw_rerase_intern_single_cubic`
  - `FBound.thy:card_set_rpder_strong_rows_raw_rerase_intern_single_cubic`
  - `FBound.thy:card_strong_deferred_strong_rows_raw_bridge_rows_le_length`
  - `FBound.thy:card_strong_deferred_strong_rows_raw_bridge_rows_finite_universe_boundI`
  - `FBound.thy:card_strong_deferred_strong_rows_raw_bridge_rows_card_boundI`
  - `FBound.thy:card_strong_deferred_strong_rows_raw_bridge_rows_norm_active_suffix_boundI`
- Meaning:
  - The normalized partial-derivative rows now have explicit length/cardinality
    bounds that factor through the existing cubic total-size theorem for
    `rpder_norm_list`.
  - The strong and raw-strong row accumulators now expose the corresponding
    count metric: pruning preserves raw row-list length, raw simplification is
    size non-increasing, and both `rpder_strong_rows` and
    `rpder_strong_rows_raw` have one-step length/cardinality bounds by
    `2 * (rsize r + 3)^3` for legacy regexes.
  - This aligns the proof surface with Antimirov's linear-form counting
    argument before attempting the harder all-input later-shared/factored-row
    closure proof.
  - The root-level lifted FBound lemmas expose the same one-step count bounds
    directly in terms of original-regex `rxsize r`, via `rerase (intern r)`.
  - The bridge-row set now has a checked multi-step count interface:
    `card (strong_deferred_strong_rows_raw_bridge_rows r s)` is bounded by
    the raw strong-row list length, then by any finite universe closed under
    the raw strong-row step. A norm/active-suffix closure corollary is also
    available for the current memo bridge route.
- Verification:
  - Full local CI PASS:
    `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: scaffold only; no final cubic theorem or bounty is claimed.

## Cubic Route Proof Interface: Strong Row Bridge Owner (2026-06-04)

- Final theorem status: **not complete**. This checkpoint only names and checks
  the next proof interface.
- Checked Isabelle additions:
  - `GeneralRegexBound.thy:rpders_strong_rows_raw_append`
  - `GeneralRegexBound.thy:rpders_strong1_rows_raw_append`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_owner`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_empty`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_cons`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_append`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_subset_owner`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_subterms_subset_owner`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_pruned_rows_subset_owner`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_pruned_rows_subterms_subset_owner`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_owner_subterm_closed`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_closure_member_sizeI`
  - `FBound.thy:card_strong_deferred_strong_rows_raw_bridge_closure_boundI`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_closure_pair_budget_boundI`
  - `FBound.thy:card_strong_deferred_strong_rows_raw_bridge_owner_boundI`
  - `FBound.thy:card_strong_deferred_strong_rows_raw_bridge_owner_from_rows_boundI`
  - `FBound.thy:card_strong_deferred_final_active_suffix_row_dag_universe_bridge_owner_boundI`
  - `FBound.thy:strong_deferred_final_active_suffix_row_dag_universe_bridge_ownerI`
  - `FBound.thy:strong_deferred_final_active_suffix_row_dag_universe_bridge_owner_from_subtermsI`
  - `FBound.thy:strong_deferred_final_active_suffix_row_dag_universe_bridge_owner_from_prunedI`
  - `FBound.thy:strong_deferred_final_active_suffix_rows_empty_bridge_rows_subterms`
  - `FBound.thy:strong_deferred_final_active_suffix_row_dag_universe_empty_bridge_owner`
  - `FBound.thy:strong_deferred_memo_lexer_strong_rows_bridge_owner_linear_contract`
- Meaning:
  - The Scala DAG bridge evidence now has a matching proof-facing owner set:
    rows produced by `rpders_strong1_rows_raw`, closed under raw prune-active
    suffixes and subterms.
  - The bridge route now has a checked contract theorem: bridge-owner coverage
    plus a linear bridge-owner cardinality bound discharges the existing
    memo-strong POSIX/cubic-budget contract.
  - The all-input bridge-inclusion proof is now reduced to a sharper row-level
    obligation: show final active rows are covered by the strong-row list's
    subterm closure, or by one active-suffix prune pass over that closure.
  - The empty-input bridge inclusion is now checked through that same row-level
    route: empty final active rows are covered by the initial strong-row
    subterm closure. The all-input bridge inclusion remains the main open proof
    obligation.
  - The append facts expose the intended induction shape for the strong-row
    side:
    `rpders_strong_rows_raw rs (s @ t) =
     rpders_strong_rows_raw (rpders_strong_rows_raw rs s) t`.
  - The owner cardinality side is no longer opaque: the bridge owner is bounded
    from the bridge rows' cardinality and member sizes via subterm closure,
    active-suffix pair budget, and one final subterm closure. This does not
    prove the desired linear bound yet, but it isolates the remaining accounting
    premises to strong-row count/member-size control.
  - The final cubic route is reduced to two explicit remaining obligations:
    show
    `strong_deferred_final_active_suffix_row_dag_universe r s` is included in
    this bridge owner, then prove a linear original-regex-size bound on the
    bridge owner.
- Verification:
  - `isabelle build -v -d . Posix` PASS under Isabelle2025-2.
- Bounty status: interface only; no final cubic theorem or bounty is claimed.

## Cubic Route Probe: DAG Strong Row-List Bridge Long Tail (2026-06-04)

- Final theorem status: **not complete**. This checkpoint removes a tooling
  bottleneck around the bridge probe; it is not the all-input cubic proof.
- Tooling addition:
  - `agent_hunt_pipeline/scala/PosixCubicSmoke.scala` now accepts
    `POSIX_SMOKE_STRONG_ROWS_BRIDGE_DAG=1`.
  - The new path mirrors `bsimpStrong`, `bpderStrongRows`, active-row
    factoring, and bridge coverage inside `DagStore` with `eraseBits = true`.
    This avoids constructing the huge ordinary annotated `bdersStrong` tree
    and irrelevant bit lists when probing Chapter 7 long-tail coverage.
  - For Ch7 DAG bridge runs, value comparison is deliberately skipped because
    the old `baselineValue` call itself constructs the exploding raw tree.
    Exhaustive and random DAG bridge runs still check row-gated memo POSIX
    values against the baseline.
- Probe result:
  - Exhaustive depth `2` / input length `3`: DAG bridge coverage `832/832`,
    matching the old annotated bridge, with row-gated memo POSIX values
    checked.
  - Random depth `7` / input length `10`, seed `20260604`, `1000` cases:
    DAG bridge coverage `118/118`, with row-gated memo POSIX values checked.
  - Chapter 7 `k=5`, lengths `16,20`: DAG bridge coverage `10/10`.
  - Chapter 7 `k=5`, lengths `24,28,32`: DAG bridge coverage `14/14`.
  - Chapter 7 `k=8`, lengths `16,32`: DAG bridge coverage `18/18`.
- Meaning:
  - The previous Ch7 bridge OOM is now localized to the old annotated/baseline
    tree probe, not to a discovered coverage counterexample.
  - The active proof route is still to turn this bridge shape into an Isabelle
    owner theorem for
    `strong_deferred_final_active_suffix_row_dag_universe`, then discharge the
    linear/cubic bound premise of
    `strong_deferred_memo_lexer_final_active_row_dag_linear_contract`.
- Verification:
  - Full local CI PASS:
    `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: smoke/proof-route evidence only; no final cubic theorem or
  bounty is claimed.

## Cubic Route Checkpoint: Final Row-DAG Owner Closure (2026-06-04)

- Final theorem status: **not complete**. The remaining priority theorem is
  still the all-input original-regex cubic/linear owner bound for the
  memo-strong final row-DAG table.
- Checked Isabelle additions:
  - `GeneralRegexBound.thy:raw_final_active_suffix_row_dag_universe_subterm_closed`
  - `GeneralRegexBound.thy:raw_final_active_suffix_alt_owner_subset_row_dag_universe`
  - `FBound.thy:strong_deferred_final_active_suffix_row_dag_universe_subterm_closed`
  - `FBound.thy:strong_deferred_final_active_suffix_alt_owner_subset_row_dag_universe`
- Meaning:
  - The final-active row-DAG universe is now explicitly named as
    `rsubterms`-closed at both raw and lifted levels.
  - The sharp BR-040 owner set
    `payload_roots ∪ suffix_keys ∪ alt_nodes` is now explicitly covered by
    that row-DAG universe. This keeps the next proof focused on constructing a
    concrete original-regex-owned linear universe, rather than rediscovering
    basic closure/coverage facts around each contract.
- Verification:
  - Full local CI PASS:
    `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: proof-surface cleanup only; no final cubic theorem or bounty
  is claimed.

## Cubic Route Probe: Strong Row-List Bridge Coverage (2026-06-04)

- Final theorem status: **not complete**. This is smoke evidence for a
  possible Antimirov-style owner invariant, not a proof.
- Tooling addition:
  - `agent_hunt_pipeline/scala/PosixCubicSmoke.scala` now accepts
    `POSIX_SMOKE_STRONG_ROWS_BRIDGE_ONLY_CH7=1`, letting the bridge probe run
    only the Chapter 7 grid instead of first consuming memory on the exhaustive
    and random checks.
- Probe result:
  - Exhaustive depth `2` / input length `3` bridge coverage passed:
    final-active coverage `832/832`, with row-gated memo POSIX values matching
    the baseline.
  - Random depth `7` / input length `10`, seed `20260604`, `1000` cases also
    passed: final-active coverage `121/121`.
  - Chapter 7 `k=5`, lengths `4,8,12` passed with coverage `15/15`.
  - Chapter 7 `k=5`, lengths `16,20` still OOM in the bridge probe because it
    constructs the ordinary annotated `bdersStrong` tree and large bit lists.
    The existing deferred-memo trace handles these lengths, so the next
    tooling/proof step should move the bridge coverage predicate onto the
    deferred/memo final-root representation instead of treating this as a
    coverage counterexample.
- Bounty status: smoke/proof-route evidence only; no final cubic theorem or
  bounty is claimed.

## Cubic Route Checkpoint: Fresh-Key DAG Closure Is Too Coarse (2026-06-04)

- Final theorem status: **not complete**. The priority theorem remains the
  all-input original-regex bound for the final memo-strong row-DAG owner table.
- Checked Isabelle additions in `GeneralRegexBound.thy`:
  - `raw_shared_prune_active_suffix_closure_key_dag_universe`
  - `raw_final_active_suffix_closure_key_dag_universe`
  - `card_raw_shared_prune_active_suffix_closure_key_dag_universe_boundI`
  - `card_raw_shared_prune_active_suffix_closure_key_dag_universe_member_pair_budget_bound`
  - `card_raw_shared_prune_active_suffix_closure_key_dag_universe_member_pair_budget_card_bound`
  - `card_raw_final_active_suffix_closure_key_dag_universe_member_pair_budget_bound`
  - `card_raw_final_active_suffix_closure_key_dag_universe_member_pair_budget_card_bound`
  - `card_raw_final_active_suffix_closure_key_dag_universe_le_rsize_cubic_times_rsize`
- Meaning:
  - The previous checkpoint bounded the number of fresh continuation keys
    created by active closure. This checkpoint also charges the `rsubterms`
    DAG of those keys.
  - The generic bound is `(card U + P * M) * M`: key cardinality times
    key-subterm/member size.
  - Instantiated to final-active rows, the naive key-DAG closure gives
    `(rsize r + rsize r * rsize r * rsize r) * rsize r`, not a cubic
    original-regex bound. This is useful negative evidence: the final proof
    cannot simply close all fresh key subterms after active-prune expansion.
    It must keep using the tighter final row-DAG/hash-cons owner route.
- Verification:
  - Focused `isabelle build -v -d . Posix` PASS.
- Bounty status: obstacle/accounting infrastructure only; no final cubic
  theorem or bounty is claimed.

## Cubic Route Checkpoint: Fresh-Key Cardinality Accounting (2026-06-04)

- Final theorem status: **not complete**. This checkpoint controls the fresh
  continuation keys exposed by active-suffix closure, but the original-regex
  cubic owner theorem is still open.
- Checked Isabelle additions in `GeneralRegexBound.thy`:
  - `card_raw_shared_prune_active_suffix_closure_keys_le_closure`
  - `card_raw_shared_prune_active_suffix_closure_keys_member_pair_budget_bound`
  - `card_raw_shared_prune_active_suffix_closure_keys_member_pair_budget_card_bound`
  - `card_raw_final_active_suffix_closure_keys_member_pair_budget_bound`
  - `card_raw_final_active_suffix_closure_keys_member_pair_budget_card_bound`
  - `card_raw_final_active_suffix_closure_keys_le_rsize_plus_square_member`
  - `card_raw_final_active_suffix_closure_keys_le_rsize_cubic`
- Meaning:
  - Since active closure can introduce fresh keys, the proof route now accounts
    for them by cardinality rather than trying to preserve the seed key set.
  - For any finite seed universe `U`, keys of
    `raw_shared_prune_active_suffix_closure U` are bounded by the closure size,
    hence by `card U + P * M` when the active pair budget is `P` and every seed
    member has size at most `M`.
  - Instantiated to final-active rows, this gives a checked cubic bound in the
    size of the already-produced final raw tree. The remaining hard theorem is
    still to replace that final raw size by an original-regex-owned linear or
    cubic owner universe.
- Verification:
  - Focused `isabelle build -v -d . Posix` PASS.
  - Full local CI PASS:
    `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 600`.
- Bounty status: proof accounting infrastructure only; no final cubic theorem
  or bounty is claimed.

## Cubic Route Checkpoint: Fresh Continuation Keys Exposed (2026-06-04)

- Final theorem status: **not complete**. This checkpoint rules out a tempting
  but false invariant; it does not prove the cubic bound.
- Checked Isabelle additions in `GeneralRegexBound.thy`:
  - `raw_shared_prune_suffix_key_rsubterms`
  - `raw_shared_prune_active_suffix_keys_member_size_bound`
  - `raw_shared_prune_active_suffix_closure_keys_member_size_bound`
  - `raw_shared_prune_active_suffix_closure_can_introduce_fresh_key`
- Meaning:
  - Active-suffix closure can introduce a fresh continuation key. A later row
    whose payload is itself `RSEQ (RALTS ...) k2`, when pruned and sequenced
    with the outer key `k`, can expose the new key `k2 . k`.
  - Therefore the next owner-universe proof cannot assume suffix-key
    preservation under active closure. It needs a continuation-owner/cardinality
    argument.
  - The positive replacement fact is still useful: every suffix key in the
    active closure has size bounded by the closure member-size bound, because a
    suffix key is a subterm of its owning row.
- Verification:
  - Focused `isabelle build -v -d . Posix` PASS.
  - Full local CI PASS:
    `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 600`.
- Bounty status: route-sharpening proof infrastructure only; no final cubic
  theorem or bounty is claimed.

## Cubic Route Checkpoint: Shared-Prune Closure Preserves Member Size (2026-06-04)

- Final theorem status: **not complete**. The first-priority theorem is still
  the all-input cubic/linear-owner bound for the final memo-strong
  simplification route, not another conditional handoff.
- Checked Isabelle additions in `GeneralRegexBound.thy`:
  - `raw_shared_prune_pair_outputs_member_size_le_later_size`
  - `raw_shared_prune_pair_closure_member_size_bound`
  - `raw_shared_prune_same_suffix_closure_member_size_bound`
  - `raw_shared_prune_active_suffix_closure_member_size_bound`
- Meaning:
  - The raw strong shared-prune closure cannot create members larger than the
    existing universe member-size bound. Pair outputs are bounded by the
    `later` input row, and pair/same-suffix/active-suffix closures inherit the
    original member bound `M`.
  - This supports the owner-universe construction route: closure may increase
    cardinality, but it no longer threatens the `member_size` premise needed by
    the active-suffix cubic row-universe interface.
- Verification:
  - Full local CI PASS:
    `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 600`.
  - Scala exact POSIX smoke still checks the default strong-memo route before
    Isabelle (`84,300` exhaustive regex/input pairs plus known CE and Chapter
    7 k=5 trace).
- Bounty status: proof infrastructure only; no final cubic theorem or bounty is
  claimed.

## Cubic Route Checkpoint: Final Row-DAG Base Case (2026-06-04)

- Final theorem status: **not complete**. The first-priority missing theorem is
  still a concrete all-input bound of the form
  `card (strong_deferred_final_active_suffix_row_dag_universe r s) <=
   K * rxsize r` for legacy/non-backref regexes.
- Checked Isabelle additions in `FBound.thy`:
  - `nat_square_le_cube_if_pos`
  - `nat_le_cube_if_pos`
  - `card_strong_deferred_final_active_suffix_row_dag_universe_length_le_one_cubic`
- Meaning:
  - The final-active row-DAG universe is now cubically bounded for `length s <=
    1`. The proof uses the existing empty-input linear bound and singleton
    quadratic bound, then pads them to `rxsize r ^ 3`.
  - This is a real checked base case for a future induction/decomposition
    proof, not a bounty claim and not the final cubic theorem.
- Verification:
  - Full local CI PASS:
    `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`.
  - Scala exact POSIX smoke still checks 84,300 exhaustive regex/input pairs
    at depth 2/input length 3, plus the known CE grid and Chapter 7 k=5
    strong-memo trace.

## Cubic Route Checkpoint: Component-Union Memo Owner Gate (2026-06-04)

- Route status:
  - Emitted-tree `bsimpCubic` remains retired as a proof target.
  - The active route is memo strong tree: `bders_simpStrong` supplies the
    nullable recognition tree, while `strong_deferred_memo_lexer` /
    `strong_deferred_span_value` supplies exact POSIX values.
- Checked Isabelle additions in `FBound.thy`:
  - `strong_deferred_final_active_suffix_component_union`
  - `card_strong_deferred_final_active_suffix_row_dag_universe_le_component_union`
  - `card_strong_deferred_final_active_suffix_component_union_shared_component_boundI`
  - `card_strong_deferred_final_active_suffix_component_union_closed_root_boundI`
  - `card_strong_deferred_final_active_suffix_component_union_closed_root_linearI`
- Meaning:
  - The proof side now names the Scala `componentUnionSize` metric:
    rows + alt nodes + shared payload/key DAG nodes as one hash-consable set.
  - Under a finite `rsubterms`-closed owner/root universe `U` covering
    final-active payload roots and suffix keys, the component union is bounded
    by `2 * rows + card U`; this is sharper than the separate-sum
    `decomp_bound`, which gives `2 * rows + 2 * card U`.
- Pipeline changes:
  - Added `POSIX_SMOKE_STRONG_FINAL_ACTIVE_COMPONENT_UNION_FACTOR` and the
    matching PowerShell parameters to the Scala smoke, local CI, value gate,
    final-active scout, and factor sweep.
  - Default local CI now gates row-DAG universe, component union, and decomp
    bound at factor `3 * rsize(r)` on the default strong-memo smoke.
- Verification:
  - Focused `isabelle build -v -d . Posix` PASS.
  - Full local CI PASS:
    `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`.
  - Scala exact POSIX smoke checked 84,300 exhaustive regex/input pairs at
    depth 2/input length 3, plus known CE grid and Chapter 7 k=5 trace.
  - Chapter 7 k=5 final metrics for n=4,8,12,16,20: final component union
    stays `36`, final decomp bound stays `46`, and final row-DAG universe is
    `44,41,41,44,41`.
- Bounty status: proof/smoke infrastructure only; no cubic theorem or bounty is
  claimed.

## Cubic Route Checkpoint: Isabelle Decomp Metric Named (2026-06-04)

- Added the Isabelle-side metric
  `FBound.thy:strong_deferred_final_active_suffix_decomp_bound`, matching the
  Scala smoke metric
  `finalRows + finalAltNodes + finalPayloadDag + finalKeyDag`.
- Checked that this metric bounds the final-active row-DAG universe:
  `card_strong_deferred_final_active_suffix_row_dag_universe_le_decomp_bound`.
- Added linear component bridges:
  `strong_deferred_final_active_suffix_decomp_bound_rows_boundI` and
  `strong_deferred_final_active_suffix_decomp_bound_linearI`.
- Added final memo-lexer handoff theorems
  `strong_deferred_memo_lexer_final_active_decomp_bound_contract` and
  `strong_deferred_memo_lexer_final_active_decomp_linear_contract`.
  These connect the smoke-gated decomp metric directly to exact POSIX
  correctness, `lexer` equality, `flat`, and the row-DAG bound.
- Focused verification: `isabelle build -v -d . Posix` passed. This is
  BR-040 proof infrastructure only; the actual component bounds remain open
  and no bounty is claimed.

## Cubic Route Checkpoint: Memo-Strong Decomp Smoke Gate (2026-06-04)

- Accepted the route decision from the latest plots: direct emitted-tree
  `bsimpCubic` is not the active cubic-bound path.
- Strengthened the smoke pipeline so the default `strong-memo` route now
  reports and gates the proof-facing final-active decomposition metric
  directly: `strongMemoFinalActiveDecompBound =
  finalRows + finalAltNodes + finalPayloadDag + finalKeyDag`.
- Added `StrongFinalActiveDecompBoundFactor` /
  `POSIX_SMOKE_STRONG_FINAL_ACTIVE_DECOMP_BOUND_FACTOR` to
  `scala_cubic_smoke.ps1`, `isabelle_ci.ps1`,
  `strong_memo_value_gate.ps1`, `strong_memo_final_active_scout.ps1`, and the
  factor-sweep wrapper.
- Promoted `decompBoundRatio` to a first-class Scala frontier, so scout
  reports now show the worst final-active decomp-bound witnesses alongside
  row, member-DAG, row-DAG-universe, and pair-budget witnesses.
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including exact `strong-memo` Scala smoke, `Posix`, and
  `BackRefPilot`.
- Infrastructure only; no BR-039/BR-040 bounty is claimed. The next proof work
  should target the component linear bounds behind the memo-strong
  final-active decomp metric, not emitted `bsimpCubic` trees.

## Cubic Route Checkpoint: Decomposition Linear Hook Checked (2026-06-04)

- Added the checked Isabelle lemma
  `FBound.thy:card_strong_deferred_final_active_suffix_row_dag_universe_decomp_linearI`.
- It formalizes the current proof-facing metric: if final-active rows,
  final-active payload-DAG universe, and final-active suffix-key-DAG universe
  are each linear in `rxsize r`, then the final-active row-DAG universe is
  linear with factor `2 * R + P + Q`.
- This exactly matches the Scala `DecompBound` instrumentation:
  `rows + altNodes + payloadDag + keyDag`, using the checked
  `altNodes <= rows` fact on the Isabelle side.
- Verification: focused `isabelle build -v -d . Posix` passed. No bounty is
  claimed; the remaining hard work is proving the three component linear
  bounds for the memo-strong final derivative family.

## Cubic Route Checkpoint: Memo-Strong Owner Decomposition Metrics (2026-06-04)

- Accepted the plot evidence that direct `bsimpCubic` emitted-tree bounds are
  not the current proof route. It remains a negative/regression target.
- Extended `agent_hunt_pipeline/scala/PosixCubicSmoke.scala` so active and
  final strong rows now report component owner metrics:
  `altNodes`, `payloadRoots`, `payloadDagUniverse`, `keyDagUniverse`, and
  both `componentUnionSize` and the proof-facing `decompBoundSize`.
- Updated the Chapter 7 deferred-memo grid defaults so plots include
  `strongMemoFinalActiveRowDagUniverse`,
  `strongMemoFinalActiveDecompBound`,
  `strongMemoFinalActiveComponentUnion`,
  `strongMemoFinalActivePayloadDag`, and
  `strongMemoFinalActiveKeyDag`, along with the existing row/pair/memo metrics.
- Quick smoke passed with exact POSIX value reconstruction enabled. On the
  thesis Chapter 7 `k=5` trace, final row-DAG universe stayed at `44,41` for
  `n=4,8`; the corresponding decomposition bound stayed at `46,46`
  (`rows + altNodes + payloadDag + keyDag`), while the emitted strong tree was
  already `474,730`. This supports the current proof target: a hash-consed
  final-active row-DAG bound, not emitted tree size.
- Generated the focused owner-decomposition report at
  `agent_hunt_pipeline/reports/ch7_memo_strong_owner_decomp/index.html` for
  `k=5,8`, `n=0..80`. At `n=80`, `k=5` has final decomposition bound `46`,
  final component union `36`, final row-DAG universe `41` (max `44`), and
  strong tree `957` (max `959`); `k=8` has final decomposition bound `87`,
  final component union `71`, final row-DAG universe `91` (max `97`), and
  strong tree `3233` (max `3245`).
- Verification:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 300`
  passed, including exact strong-memo Scala smoke, `Posix`, and
  `BackRefPilot`.
- No BR-039/BR-040 bounty is claimed. The remaining proof obligation is still
  a checked linear bound for
  `strong_deferred_final_active_suffix_row_dag_universe`.

## Cubic Route Checkpoint: Linear Row-DAG Target Named (2026-06-04)

- Added the checked theorem
  `FBound.thy:strong_deferred_memo_lexer_final_active_row_dag_linear_contract`.
- This is the current proof-facing target for the memo-strong route. It says:
  if the final-active row-DAG universe satisfies
  `card (strong_deferred_final_active_suffix_row_dag_universe r s)
   <= K * rxsize r`, then the named `strong_deferred_memo_lexer` has exact
  POSIX `Some`/`None` correctness, equals `lexer`, preserves `flat`, and gets
  row, pair, row-DAG, max-row-DAG, root/key coverage, and span/split budgets.
- The remaining hard theorem is now sharply isolated: construct or characterize
  the final-active hash-consed owner table and prove its `K * rxsize r` bound.
  This is stronger and more useful than proving a bound on the emitted
  `bsimpStrong` or retired `bsimpCubic` tree.
- Updated `agent_hunt_pipeline/scripts/strong_memo_final_active_scout.ps1`
  and the factor sweep wrapper so their reports explicitly parameterize and
  display `Row-DAG universe budget`. This keeps the smoke pipeline aligned
  with the Isabelle theorem target.
- Verification so far: focused Isabelle `Posix` build passed; script self-test
  wrote an ignored report under `agent_hunt_pipeline/run/`.

## Cubic Route Checkpoint: Memo-Strong Single Dag Owner Contract (2026-06-04)

- After the derivative-size graphs, the direct emitted-tree `bsimpCubic`
  route is treated as negative evidence. The active proof target is now:
  keep the thesis-style `bsimpStrong` recognition tree, reconstruct exact
  POSIX values from the original regex/string, and prove size through a
  hash-consed final-active row-DAG owner table.
- Added the checked Isabelle theorem
  `FBound.thy:strong_deferred_memo_lexer_final_active_dag_owner_contract`.
  It exposes this target directly through the named
  `strong_deferred_memo_lexer`.
- Under `legacy_rexp r` and a finite `DagU` containing
  `strong_deferred_final_active_suffix_row_dag_universe r s` with
  `card DagU <= D`, the theorem gives:
  exact `Some`/`None` POSIX correctness for `strong_deferred_memo_lexer`,
  equality with `lexer`, `flat`, legacy preservation, payload/root/key
  coverage into `DagU`, row count `<= D`, pair budget `<= D * D`,
  row-DAG/max-row-DAG `<= D`, and the existing span/split memo budgets.
- Design consequence: the remaining main proof can focus on constructing a
  concrete owner table `DagU` and proving its size. It no longer has to talk
  about the hopeless emitted `bsimpCubic` tree as the output value carrier.
- Verification: focused Isabelle `Posix` build passed. Infrastructure only;
  no BR-039/BR-040 bounty is claimed.

## Cubic Route Smoke: Memo-Strong Recognition Gate Hardened (2026-06-04)

- Strengthened `agent_hunt_pipeline/scala/PosixCubicSmoke.scala` so the
  `strong-memo` route now checks two properties independently:
  - the strong nullable gate
    `bnullable (bdersStrong (intern r) s)` agrees with baseline acceptance;
  - the reconstructed memo value agrees with the baseline POSIX value.
- This closes a testing blind spot: before this checkpoint, a false-positive
  strong gate could still reconstruct `None` from the original regex and
  silently match a rejecting baseline. The new
  `checkStrongMemoRecognitionGate` catches that case directly and prints the
  final strong tree/DAG in the failure report.
- Re-ran
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\strong_memo_value_gate.ps1`.
  It passed `84,300` exhaustive regex/input pairs, `15` known counterexample
  cases, and `2,000` random depth-`7`/input-`8` cases with seed `20260602`.
  Chapter 7 `k=5,n<=80` remained stable with final-active row-DAG universe
  in `40..44`.
- This is smoke hardening for BR-039/BR-040. No bounty is claimed.

## Cubic Route Checkpoint: Named Memo-Strong POSIX Candidate (2026-06-04)

- Accepted the graph evidence that emitted-tree `bsimpCubic` is not the cubic
  proof candidate. It remains only negative evidence and a regression source.
- Added the checked Isabelle definition
  `FBound.thy:strong_deferred_memo_lexer`. This names the actual current
  candidate:
  run `bders_simpStrong (intern r) s` as a nullable recognition gate, then
  return the unique original-regex `strong_deferred_span_value` when the gate
  accepts.
- Checked the exact value bridge:
  - `strong_deferred_memo_lexer_eq_lexer`;
  - `strong_deferred_memo_lexer_POSIX_correctness`;
  - `strong_deferred_memo_lexer_flat`;
  - `strong_deferred_memo_lexer_Some_iff_span_value`;
  - `strong_deferred_memo_lexer_defined_iff`;
  - `strong_deferred_memo_lexer_exact_value_budget`.
- Added `agent_hunt_pipeline/scripts/strong_memo_value_gate.ps1`, a dedicated
  smoke command for this route. It runs the `strong-memo` Scala route with
  exact POSIX value checks, known counterexamples, deterministic random cases,
  and the final-active row-DAG universe gate.
- Fresh run:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\strong_memo_value_gate.ps1`.
  It passed `84,300` exhaustive regex/input pairs, `15` known counterexample
  cases, and `2,000` random depth-`7`/input-`8` cases with seed `20260602`.
  On Chapter 7 `k=5,n<=80`, final-active row-DAG universe stayed in
  `40..44` while exact POSIX values were preserved.
- This is BR-039/BR-040 infrastructure and route cleanup, not a final cubic
  theorem payout.

## Cubic Route Checkpoint: RowU + DagU Owner Contract (2026-06-04)

- Added the checked theorem
  `FBound.thy:strong_deferred_original_final_active_rowU_dag_owner_contract`.
- The proof interface now separates the two objects that match the memoized
  implementation picture:
  - `RowU` covers final-active rows and controls row count/pair budget;
  - `DagU` is any finite owner table containing
    `strong_deferred_final_active_suffix_row_dag_universe r s`.
- Under `card RowU <= R` and `card DagU <= D`, the theorem yields exact
  memo-strong POSIX `Some`/`None`, `flat`, legacy preservation, row budget
  `<= R`, pair budget `<= R * R`, row-DAG/max-row-DAG bounds `<= D`, and the
  payload/key root plus payload/key DAG coverage facts into `DagU`.
- Design meaning: future work can prove a hash-consed over-approximation
  `DagU` directly. It does not need to prove `DagU` is syntactically
  subterm-closed, as long as it contains the final row-DAG table.
- Verification: focused Isabelle `Posix` build passed.

## Cubic Route Checkpoint: Row-DAG Owns Roots/Keys (2026-06-04)

- Added raw and lifted coverage lemmas showing that the final-active row-DAG
  universe already contains the roots/keys needed by the root-owned handoff:
  - `raw_final_active_suffix_payload_roots_subset_row_dag_universe`;
  - `raw_final_active_suffix_payload_dag_universe_subset_row_dag_universe`;
  - `raw_final_active_suffix_keys_subset_row_dag_universe`;
  - `raw_final_active_suffix_key_dag_universe_subset_row_dag_universe`;
  - lifted `strong_deferred_final_active_suffix_*_subset_row_dag_universe`
    variants in `FBound.thy`.
- Also added the packaged union facts
  `*_roots_keys_subset_row_dag_universe` and
  `*_payload_key_dag_universe_subset_row_dag_universe`.
- Design meaning: the memo-strong route can treat
  `strong_deferred_final_active_suffix_row_dag_universe r s` as the canonical
  hash-consed proof object. Any future bounded universe containing that row-DAG
  table automatically covers the payload roots, suffix keys, and their DAG
  nodes required by the newer `RowU/root-U` contract.
- Verification: focused Isabelle `Posix` build passed.

## Cubic Route Checkpoint: RowU + RootU Memo-Strong Contract (2026-06-04)

- After reviewing the derivative-size graphs, the emitted-tree `bsimpCubic`
  route is treated as negative evidence rather than an active proof candidate.
  It is too weak to justify the cubic theorem over its output tree.
- The active theorem route is memo strong tree:
  `bders_simpStrong (intern r) s` is the small nullable recognition tree, and
  exact POSIX values are reconstructed from the original regex/string via
  `strong_deferred_span_value`.
- Added the checked theorem
  `FBound.thy:strong_deferred_original_final_active_rowU_shared_root_universe_contract`.
  It separates the two remaining finite-universe obligations:
  - final-active rows are covered by some finite `RowU` with `card RowU <= R`;
  - payload roots and suffix keys are covered by a finite subterm-closed `U`
    with `card U <= D`.
- Under those assumptions the theorem yields exact `Some`/`None` POSIX
  correctness, `flat v = s`, legacy preservation, the row-DAG containment fact,
  row budget `<= R`, pair budget `<= R * R`, and final row-DAG/max-row-DAG
  bounds `<= 2 * R + D`.
- Design meaning: future proof work should prove the actual memo table/root
  universe bounds, not optimize or prove over the old `bsimpCubic` emitted
  tree. No BR-039/BR-040 bounty is claimed yet.
- Verification: focused Isabelle `Posix` build passed.

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

## Cubic Bound Research Checkpoint: Memo-Strong Closed Root Decomp Bridge (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Route decision:
  - The plotted derivative-size evidence makes emitted-tree `bsimpCubic`
    historical/negative evidence. The active route is memo strong tree:
    `bders_simpStrong` is the small nullable recognition tree, and exact POSIX
    values are reconstructed through the checked `strong_deferred_span_value`
    / `strong_deferred_memo_lexer` layer.
- Checked proof additions in `FBound.thy`:
  - `strong_deferred_final_active_suffix_payload_key_dag_universe_subset_closed_root_universe`
  - `strong_deferred_final_active_suffix_decomp_bound_shared_root_boundI`
  - `strong_deferred_final_active_suffix_decomp_bound_shared_root_linearI`
- Design result:
  - If a finite owner/root universe `U` contains final-active payload roots and
    suffix keys and is closed under `rsubterms`, then it also contains both
    payload-DAG and key-DAG universes.
  - The smoke-gated decomposition metric
    `rows + altNodes + payloadDag + keyDag` is therefore bounded by
    `2 * rows + 2 * card U`. The factor `2 * card U` is intentional: this
    metric sums payload-DAG and key-DAG sizes separately. A future
    component-union metric could target `2 * rows + card U`, but it would be a
    different statement and would need its own checked POSIX handoff.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.
- Bounty status: infrastructure only; no bounty is claimed.

## Cubic Bound Research Checkpoint: Component-Union Handoff (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof addition in `FBound.thy`:
  - `strong_deferred_memo_lexer_final_active_component_union_bound_contract`
- Scala smoke addition:
  - `componentUnionRatio` is now a first-class final-active frontier metric,
    reported separately from row-DAG universe and decomp-bound ratios.
- Design result:
  - A linear bound on the final-active component union now directly yields the
    memo-strong lexer/POSIX correctness handoff and the corresponding row-DAG
    universe linear bound, via the checked subset
    `row_dag_universe <= component_union`.
  - This keeps the active proof route aligned with the hash-cons owner-table
    evidence: component union is a sharper metric than the older decomp sum,
    while still being connected to exact POSIX value reconstruction.
- Build: focused Isabelle `Posix` PASS; light Scala strong-memo smoke PASS.
- Bounty status: infrastructure only; no bounty is claimed.

## Cubic Bound Research Checkpoint: Closed-Root Component Contract (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof addition in `FBound.thy`:
  - `strong_deferred_memo_lexer_final_active_component_union_closed_root_linear_contract`
- Design result:
  - The current proof target is now packaged in the sharp owner-universe form:
    prove final rows are linear, and prove a finite `rsubterms`-closed universe
    `U` of owner roots covers all final-active payload roots and suffix keys.
  - Under those assumptions, Isabelle derives exact `strong_deferred_memo_lexer`
    POSIX correctness plus
    `component_union <= (2 * R + C) * rxsize r` and the corresponding row-DAG
    universe bound.
  - This narrows the remaining non-backref cubic work to the real hard lemma:
    construct/prove the general linear owner-root universe, rather than
    repeatedly reproving lexer correctness.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.
- Bounty status: infrastructure only; no bounty is claimed.

## Cubic Bound Research Checkpoint: Component Union Equals Row DAG (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `GeneralRegexBound.thy:raw_final_active_suffix_alt_nodes_subset_row_dag_universe`
  - `FBound.thy:strong_deferred_final_active_suffix_alt_nodes_subset_row_dag_universe`
  - `FBound.thy:strong_deferred_final_active_suffix_component_union_subset_row_dag_universe`
  - `FBound.thy:strong_deferred_final_active_suffix_component_union_eq_row_dag_universe`
  - `FBound.thy:card_strong_deferred_final_active_suffix_component_union_eq_row_dag_universe`
  - `FBound.thy:card_strong_deferred_final_active_suffix_component_union_le_final_asize`
- Scala smoke alignment:
  - `agent_hunt_pipeline/scala/PosixCubicSmoke.scala` now computes
    `componentUnionSize` with the erased alt root's DAG subterms. This matters
    because Scala erases `AALTs` to binary `ALT` trees, while Isabelle's raw
    row metric uses n-ary `RALTS`.
  - The smoke tool now fails fast if `componentUnionSize` and
    `rowDagUniverseSize` diverge, mirroring the checked Isabelle equality.
- Design result:
  - The final-active `component_union` metric is not merely an upper frontier:
    it is exactly the existing final-active row-DAG universe. The missing piece
    was the small `alt_nodes <= row_dag_universe` inclusion.
  - This reduces the live cubic proof surface: future work can prove the
    row-DAG/final-strong-tree bound and get the component-union bound for free,
    or use component-union smoke evidence as direct evidence for the same
    Isabelle metric.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.
- Bounty status: still infrastructure only; the final cubic theorem remains
  unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Final Rows by Suffix Buckets (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `GeneralRegexBound.thy:raw_final_active_suffix_rows_bucket_union`
  - `GeneralRegexBound.thy:card_raw_final_active_suffix_rows_bucket_boundI`
  - `FBound.thy:strong_deferred_final_active_suffix_rows_bucket_union`
  - `FBound.thy:card_strong_deferred_final_active_suffix_rows_bucket_boundI`
- Design result:
  - Final-active rows are now decomposed by their `raw_shared_prune_suffix_key`.
    Isabelle proves that the row set is the union of its active suffix buckets,
    and that `card rows <= card keys * max bucket width`.
  - This is the next useful accounting bridge for the memo-strong route: a
    future proof can close final-row linearity by separately bounding the
    number of suffix keys and the per-key bucket width.
  - During CI a broad `simp` over the bucket union was found to run for over
    a minute. The proof was rewritten with direct `rule`/`arg_cong` steps, in
    line with the proof-performance rule that slow automation must be split.
- Build: full local CI PASS: Scala strong-memo smoke, `Posix`, and
  `BackRefPilot`.
- Bounty status: infrastructure only. The final non-backref cubic theorem is
  still open; no BR-039/BR-040 payout is claimed.

## Cubic Bound Research Checkpoint: Bucket-Linear Memo Contract (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions in `FBound.thy`:
  - `card_strong_deferred_final_active_suffix_rows_bucket_linearI`
  - `strong_deferred_final_active_suffix_pair_budget_bucket_linearI`
  - `strong_deferred_memo_lexer_final_active_bucket_component_union_contract`
- Design result:
  - The bucket decomposition is now connected to the memo-strong POSIX handoff.
    If final suffix keys are linear in the original regex size, each active
    suffix bucket has a uniform width bound, and the final payload roots/keys
    live in a linear closed owner universe, then Isabelle derives exact
    `strong_deferred_memo_lexer` POSIX correctness, `lexer` equality, `flat`,
    final rows bounded by `(K * B) * rxsize r`, and final row-DAG/component
    union bounded by `(2 * (K * B) + C) * rxsize r`.
  - This sharpens the remaining BR-040 obligation: prove the key-count,
    bucket-width, and owner-universe bounds from the non-backref `legacy_rexp`
    invariant, rather than rebuilding the correctness bridge.
- Build: full local CI PASS: Scala strong-memo smoke, `Posix`, and
  `BackRefPilot`.
- Bounty status: infrastructure only. The final theorem is still unproved; no
  BR-039/BR-040 payout is claimed.

## Cubic Bound Research Checkpoint: Bucket Width via Alt Nodes (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `GeneralRegexBound.thy:card_raw_final_active_suffix_bucket_le_alt_nodes`
  - `FBound.thy:card_strong_deferred_final_active_suffix_bucket_le_alt_nodes`
- Design result:
  - For a fixed suffix key `k`, Isabelle now proves that the active bucket
    `{RSEQ (RALTS rows) k}` injects into the final-active `RALTS rows` nodes
    by forgetting the shared suffix. This rewrites one remaining BR-040
    obligation from a vague bucket-width bound into a concrete alt-node/owner
    accounting problem.
  - This is intentionally not a payout theorem. It does not prove the final
    cubic bound relative to the original regex size; it only makes the next
    non-circular owner-universe obligation sharper.
- Build: full local CI PASS: Scala strong-memo smoke, `Posix`, and
  `BackRefPilot`.
- Bounty status: infrastructure only. The final non-backref cubic theorem is
  still unproved; no BR-039/BR-040 payout is claimed.

## Cubic Bound Research Checkpoint: Linear Buckets Give Cubic Handoff (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions in `FBound.thy`:
  - `card_strong_deferred_final_active_suffix_component_union_closed_root_quadraticI`
  - `card_strong_deferred_final_active_suffix_rows_bucket_quadraticI`
  - `strong_deferred_memo_lexer_final_active_bucket_component_union_quadratic_contract`
- Design result:
  - The previous bucket handoff required a uniform constant bucket width to get
    a linear final row-DAG bound. That is stronger than the current cubic goal
    needs and does not match the Chapter 7 evidence as naturally as a linear
    bucket bound.
  - Isabelle now checks the more realistic accounting route:
    if final suffix keys are linear in `rxsize r`, each final active suffix
    bucket is also linear in `rxsize r`, and the final payload roots/keys are
    covered by a linear `rsubterms`-closed owner universe, then
    `strong_deferred_memo_lexer` keeps exact POSIX correctness and the final
    component-union/row-DAG universe is quadratic, hence also cubic, in the
    original regex size.
  - This is a stronger fit for the actual target than the constant-bucket
    contract, but it is still conditional. The remaining substantive theorem
    is to prove the key-count, bucket-width, and owner-universe premises for
    all non-backref inputs.
- Build: full local CI PASS: Scala strong-memo smoke, `Posix`, and
  `BackRefPilot`.
- Bounty status: infrastructure only. The final non-backref cubic theorem is
  still unproved; no BR-039/BR-040 payout is claimed.

## Cubic Bound Research Checkpoint: Rows from Keys and Alt Nodes (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof addition in `FBound.thy`:
  - `card_strong_deferred_final_active_suffix_rows_keys_alt_nodes_quadraticI`
- Design result:
  - Combining the fixed-key bucket injection with bucket-union accounting gives
    a more concrete row-count target: if final suffix keys are linear and
    final-active alt nodes are linear in the original regex size, then final
    active rows are quadratic.
  - This removes the need to prove a separate per-key bucket-width theorem in
    the main BR-040 route. The next hard proof can focus on linear bounds for
    final suffix keys, final-active `RALTS` nodes, and the closed owner
    universe for payload roots/keys.
- Build: full local CI PASS: Scala strong-memo smoke, `Posix`, and
  `BackRefPilot`.
- Bounty status: infrastructure only. The final non-backref cubic theorem is
  still unproved; no BR-039/BR-040 payout is claimed.

## Cubic Bound Research Checkpoint: Alt-Owner Cubic Handoff (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions in `FBound.thy`:
  - `card_strong_deferred_final_active_suffix_component_union_alt_owner_boundI`
  - `card_strong_deferred_final_active_suffix_component_union_alt_owner_quadraticI`
  - `strong_deferred_memo_lexer_final_active_alt_owner_quadratic_contract`
- Design result:
  - The previous owner-universe contracts covered final-active payload roots and
    suffix keys, while final-active `RALTS` nodes were paid for indirectly via
    row accounting. The new contract makes the intended hash-cons table sharper:
    one finite `rsubterms`-closed owner universe `U` must cover payload roots,
    suffix keys, and final-active alt nodes.
  - Under that premise, plus the already checked key/alt-node row bound,
    Isabelle derives exact `strong_deferred_memo_lexer` POSIX correctness,
    exact failure equivalence, `lexer` equality, `flat`, legacy preservation,
    final keys and alt nodes linear in `card U`, final active rows quadratic,
    and final component-union/row-DAG bounds
    `(C * C + C) * rxsize r * rxsize r`, padded to cubic.
  - This is deliberately a handoff, not the final theorem. The first-priority
    remaining task is to construct and prove such a linear owner universe for
    every non-backref input. Until that premise is discharged, the final cubic
    bound for the simplifier is not proved.
- Build: full local CI PASS before this note: Scala strong-memo smoke, `Posix`,
  and `BackRefPilot`. Re-run CI after documentation before committing.
- Bounty status: infrastructure only. The final non-backref cubic theorem is
  still unproved; no BR-039/BR-040 payout is claimed.

## Cubic Bound Research Checkpoint: Bridge Owner Cubic Accounting (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof addition in `FBound.thy`:
  - `card_strong_deferred_strong_rows_raw_bridge_owner_cubicI`
- Design result:
  - The strong-row bridge owner now has a cubic-shaped accounting handoff:
    if the raw strong-row bridge subterm closure has linear cardinality in
    `rxsize r`, its active-suffix prune pair budget is linear in `rxsize r`,
    and every closure member has linear size in `rxsize r`, then Isabelle
    derives
    `card (strong_deferred_strong_rows_raw_bridge_owner r s) <=
      (A * M + P * M * M) * rxsize r * rxsize r * rxsize r`.
  - This is closer to the desired final theorem than the earlier
    row-count/member-size handoff because it isolates the exact remaining
    linear obligations for the bridge-owner route. It is still conditional:
    the final cubic theorem also needs the all-input coverage
    `strong_deferred_final_active_suffix_row_dag_universe r s <=
      strong_deferred_strong_rows_raw_bridge_owner r s`.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash after adding the
  lemma. Re-run full CI before committing the checkpoint.
- Bounty status: accounting infrastructure only. The final non-backref cubic
  theorem remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Strong ALTs Row-DAG Coverage (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions in `GeneralRegexBound.thy`:
  - `raw_final_active_suffix_row_dag_universe_rsimp_ALTs_subset`
  - `raw_final_active_suffix_row_dag_universe_rsimp_ALTs_rdistinct_rflts_subset`
  - `raw_final_active_suffix_row_dag_universe_rsimpStrong_ALTs_raw_subset`
- Design result:
  - The final `rsimp_ALTs`/`rdistinct`/`rflts` normalization layer used by
    `rsimpStrong_ALTs_raw` is now known not to create active suffix row-DAG
    nodes outside the subterm closure of its input rows.
  - This is one local bridge-coverage block for the final cubic theorem: it
    reduces the last ALTs layer to accounting for
    `rsimpStrong_prune_rows_raw`. The theorem still needs the harder
    all-input coverage from the actual strong-row derivative process into a
    cubic-size owner universe.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Strong ALTs Closed-Owner Rule (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions in `GeneralRegexBound.thy`:
  - `raw_final_active_suffix_row_dag_universe_rsimp_ALTs_rdistinct_rflts_closed_subsetI`
  - `raw_final_active_suffix_row_dag_universe_rsimpStrong_ALTs_raw_closed_subsetI`
  - `raw_final_active_suffix_row_dag_universe_rsimpStrong_ALTs_raw_prune_closed_subsetI`
  - `raw_final_active_suffix_row_dag_universe_rsimpStrong_ALTs_raw_active_suffix_closed_subsetI`
- Design result:
  - The final `rsimpStrong_ALTs_raw` layer can now be absorbed by any owner
    universe that is subterm-closed and closed under the shared-prune operation
    used by `rsimpStrong_prune_rows_raw`.
  - Equivalently, if an owner is a fixed point of
    `raw_shared_prune_active_suffix_closure`, Isabelle can derive active
    row-DAG coverage for the whole prune+ALTs layer directly.
  - This is a local coverage rule for the final theorem, not a final theorem:
    the hard remaining task is still to construct a linear-size
    continuation-owner universe for arbitrary non-backref inputs.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Least Active-Suffix Owner (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions in `GeneralRegexBound.thy`:
  - `raw_shared_prune_active_suffix_owner`
  - `raw_shared_prune_active_suffix_owner_extensive`
  - `raw_shared_prune_active_suffix_owner_active_suffix_closed`
  - `raw_shared_prune_active_suffix_owner_prune_closed`
  - `raw_shared_prune_active_suffix_owner_minimal`
  - `raw_final_active_suffix_row_dag_universe_rsimpStrong_ALTs_raw_owner_subsetI`
  - `raw_shared_prune_active_suffix_closure_sizeNregex_subset`
  - `raw_shared_prune_active_suffix_owner_sizeNregex_subset`
  - `finite_raw_shared_prune_active_suffix_owner_sizeNregex`
- Design result:
  - The continuation-owner target is now an explicit least fixed-point-style
    Isabelle object: the smallest set containing seed rows and closed under
    active same-suffix shared-prune outputs.
  - This owner is closed enough to drive `rsimpStrong_prune_rows_raw`, and if
    the input rows are flattened members of the owner, then the final
    `rsimpStrong_ALTs_raw` active row-DAG is covered by the owner's subterm
    closure.
  - The `sizeNregex` lemmas are only a sanity/fallback result: they show the
    least owner is finite under the coarse legacy size universe. They are not
    the desired cubic bound, because `sizeNregex` is far too large.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Least Owner Bridge (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `GeneralRegexBound.thy:rsubterm_closure_mono`
  - `GeneralRegexBound.thy:set_rflts_single_subset_rsubterm_closure`
  - `GeneralRegexBound.thy:raw_shared_prune_active_suffix_closure_subset_owner`
  - `GeneralRegexBound.thy:raw_final_active_suffix_row_dag_universe_rsimpStrong_ALTs_raw_owner_rsubterm_subsetI`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_owner_subset_least_owner`
- Design result:
  - The strong simplifier proof side now has an explicit bridge from ordinary
    subterm seeds to the least active-suffix owner. If input rows are already
    in a seed subterm closure, the final `rsimpStrong_ALTs_raw` active row-DAG
    is covered by the subterms of the least owner generated from that seed.
  - The existing `strong_deferred_strong_rows_raw_bridge_owner` is also covered
    by the least-owner formulation. This helps consolidate the remaining proof
    obligation around one owner object instead of several ad hoc closure
    interfaces.
  - This is not the final cubic theorem. The first-priority remaining theorem
    is still to bound the relevant least/bridge owner table by a concrete
    cubic function of the original non-backref regex size, and then connect
    that bound to the final `strong_deferred_*` POSIX/memo contract.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Strong-Row Least Owner Target (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `GeneralRegexBound.thy:rsubterms_sizeNregex_closed`
  - `GeneralRegexBound.thy:rsubterm_closure_sizeNregex_subset`
  - `FBound.thy:strong_deferred_strong_rows_raw_least_owner`
  - `FBound.thy:strong_deferred_strong_rows_raw_least_owner_dag`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_subterms_subset_least_owner`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_subset_least_owner`
  - `FBound.thy:strong_deferred_strong_rows_raw_least_owner_prune_closed`
  - `FBound.thy:strong_deferred_strong_rows_raw_least_owner_active_suffix_closed`
  - `FBound.thy:strong_deferred_strong_rows_raw_least_owner_dag_subterm_closed`
  - `FBound.thy:strong_deferred_strong_rows_raw_least_owner_dag_sizeNregex_subset`
  - `FBound.thy:finite_strong_deferred_strong_rows_raw_least_owner_dag_sizeNregex`
  - `FBound.thy:raw_final_active_suffix_row_dag_universe_rsimpStrong_ALTs_raw_bridge_rows_subset_least_owner_dag`
- Design result:
  - The proof now names the least fixed-point active-suffix owner generated by
    the strong raw row-list state, plus its subterm/DAG closure. This is a more
    faithful target for sequential shared-suffix pruning than the earlier
    one-step bridge owner.
  - The new owner is automatically active-suffix/prune closed and contains the
    bridge rows and their subterms. Its DAG closure contains the old one-step
    bridge owner and the final active row-DAG of the row-list strong tree
    `rsimpStrong_ALTs_raw (rpders_strong1_rows_raw ...)`.
  - A coarse `sizeNregex` finite fallback is checked for this owner-DAG. This
    is only a sanity/finiteness fallback, not a cubic bound.
- Remaining first-priority gap:
  - Prove that the actual final `bders_simpStrong` active row-DAG, or an
    equivalent memo/row-list final object accepted by the POSIX contract, is
    covered by this least-owner DAG for all non-backref inputs.
  - Then prove a concrete cubic cardinality bound for that least-owner DAG in
    terms of the original regex size.
- Build: focused Isabelle `Posix` PASS via bundled Cygwin bash. Re-run full CI
  before committing.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Row Gate Least-Owner Handoff (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_subset_least_owner_dag`
  - `FBound.thy:map_rerase_bpders_strong1_rows_intern_subset_least_owner_dag`
  - `FBound.thy:asizes_bpders_strong1_rows_intern_least_owner_dag_boundI`
  - `FBound.thy:rsizes_rpders_strong1_rows_raw_intern_least_owner_dag_boundI`
  - `FBound.thy:strong_deferred_row_gate_least_owner_dag_POSIX_contract`
- Design result:
  - The final checked object is now allowed to be the strong row-list nullable
    gate, not the old emitted `bders_simpStrong` tree. Under finite/cardinality
    and member-size bounds for `strong_deferred_strong_rows_raw_least_owner_dag`,
    Isabelle derives exact POSIX correctness/flatness for the row-gate memo
    lexer and size bounds for both annotated rows and erased raw rows.
  - The final row-list erased rows, and the row-list `rsimpStrong_ALTs_raw`
    active row-DAG, are checked to be covered by the least-owner DAG. This
    removes one handoff gap from the memo-strong proof route.
- Remaining first-priority gap:
  - Prove a concrete original-regex cubic/cardinality theorem for
    `strong_deferred_strong_rows_raw_least_owner_dag`, including a usable
    member-size bound. Until that theorem is checked, the final cubic bound is
    not complete.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Least-Owner Member Size (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `GeneralRegexBound.thy:raw_shared_prune_active_suffix_owner_member_size_bound`
  - `GeneralRegexBound.thy:raw_shared_prune_active_suffix_owner_dag_member_size_bound`
  - `FBound.thy:strong_deferred_strong_rows_raw_least_owner_dag_member_sizeI`
  - `FBound.thy:strong_deferred_row_gate_least_owner_dag_rows_member_POSIX_contract`
- Design result:
  - Active-suffix owner generation is now checked to preserve member size:
    every pruning output is charged to the `later` row, so the least fixed-point
    owner cannot introduce a larger row than the seed bound permits.
  - The least-owner DAG member-size premise in the row-gate POSIX handoff can
    be replaced by a bridge-row member-size premise. This narrows the remaining
    cubic proof: prove original-size cardinality for the least-owner DAG and a
    usable bridge-row member-size bound.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Bridge Rows Finite Discharge (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `FBound.thy:legacy_rerase_bpders_strong1_rows`
  - `FBound.thy:legacy_strong_deferred_strong_rows_raw_bridge_rows`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_subset_sizeNregexI`
  - `FBound.thy:finite_strong_deferred_strong_rows_raw_least_owner_dag_rows_member`
- Design result:
  - Bridge rows are now checked to stay in the legacy raw fragment whenever the
    source regex is legacy. A bridge-row member-size bound therefore implies
    membership in `sizeNregex M`, which in turn discharges finiteness of the
    least-owner DAG.
  - This removes one independent premise from the final cubic route: finiteness
    can be derived from legacy plus bridge-row member size. The hard theorem is
    still open: prove a concrete original-regex cardinality bound for the
    least-owner DAG, and prove a usable bridge-row member-size bound from the
    original regex.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Row Gate Without Finite Premise (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof change:
  - Strengthened
    `FBound.thy:strong_deferred_row_gate_least_owner_dag_rows_member_POSIX_contract`
    by removing its explicit finiteness assumption.
- Design result:
  - The row-gate least-owner handoff now derives finiteness internally from
    `legacy_rexp r` plus the bridge-row member-size premise, using the checked
    bridge-row `sizeNregex` discharge. The remaining external proof obligations
    for this contract are therefore the real ones: a cardinality bound for
    `strong_deferred_strong_rows_raw_least_owner_dag`, a bridge-row member-size
    bound, and the arithmetic product bound.
  - This is a premise-reduction step toward the final theorem, not a separate
    wrapper and not the completed cubic theorem.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Least-Owner Closed Universe Handoff (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `FBound.thy:strong_deferred_strong_rows_raw_least_owner_subset_closed_universeI`
  - `FBound.thy:strong_deferred_strong_rows_raw_least_owner_dag_subset_closed_universeI`
  - `FBound.thy:card_strong_deferred_strong_rows_raw_least_owner_dag_closed_universe_boundI`
- Design result:
  - The least-owner DAG cardinality problem is now reduced to a concrete
    closed-universe construction: if a finite `U` contains the bridge-row
    subterm closure, is subterm-closed, and is closed under active-suffix
    shared pruning, then Isabelle proves
    `strong_deferred_strong_rows_raw_least_owner_dag r s \<subseteq> U` and hence
    `card (strong_deferred_strong_rows_raw_least_owner_dag r s) \<le> card U`.
  - This avoids a meaningless wrapper theorem and isolates the real final
    obligation: define/prove a root-owned non-backref `U` whose cardinality is
    cubic in `rxsize r` and whose members have the required size bound.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Bridge Rows From Active-Suffix Universe (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_norm_active_suffix_subsetI`
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_subterm_closure_norm_active_suffix_subsetI`
  - `FBound.thy:card_strong_deferred_strong_rows_raw_least_owner_dag_norm_active_suffix_universe_boundI`
- Design result:
  - The closed-universe handoff no longer needs bridge-row coverage as a raw
    premise when the candidate universe has the usual derivative-closure shape.
    From `rerase (intern r) \<in> U`, local `rpder_norm_list` closure through
    `rsimpStrong_raw`, `rflts` closure, active-suffix closure, and subterm
    closure, Isabelle proves that the bridge-row subterm closure is inside
    `U`.
  - Consequently `card (strong_deferred_strong_rows_raw_least_owner_dag r s)`
    is bounded by `card U` under those concrete closure premises. This further
    narrows the remaining final theorem to constructing a root-owned non-backref
    `U` with cubic cardinality and member-size control.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Candidate-U Row-Gate Handoff (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof additions:
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_rows_norm_active_suffix_member_sizeI`
  - `FBound.thy:strong_deferred_strong_rows_raw_least_owner_dag_norm_active_suffix_member_sizeI`
  - `FBound.thy:strong_deferred_row_gate_norm_active_suffix_universe_POSIX_contract`
- Design result:
  - The candidate-universe route now carries both cardinality and member-size
    into the row-gate least-owner contract. If `U` contains the initial
    `rerase (intern r)`, is closed under `rflts`, local
    `rpder_norm_list`/`rsimpStrong_raw`, active-suffix pruning, and subterms,
    and has `card U \<le> C` plus `rsize q \<le> M` for all `q \<in> U`, then
    Isabelle derives exact row-gate POSIX correctness/flatness and the
    annotated/raw row-size bounds under `C * M \<le> B`.
  - This is still a proof handoff, not the final theorem. The hard remaining
    work is now isolated to constructing a root-owned non-backref `U` with
    cubic cardinality and suitable member-size control.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Final Theorem Status Reconfirmed (2026-06-04)

- Branch: `codex/backref-values`
- Agent: Codex
- Status:
  - The final theorem is **not** complete. The current preferred candidate is
    still the strong-memo / row-gate route: `bders_simpStrong` is used only as
    the nullable recognition gate, while exact POSIX values are reconstructed
    by `strong_deferred_span_value`.
  - Isabelle currently checks the conditional handoff theorem
    `FBound.thy:strong_deferred_row_gate_norm_active_suffix_universe_POSIX_contract`.
    This says that a finite candidate universe `U`, closed under the relevant
    derivative, flattening, active-suffix pruning, and subterm operations, with
    `card U <= C`, member size `<= M`, and `C * M <= B`, is enough to derive
    row-gate POSIX correctness/flatness and annotated/raw row-size bounds.
  - What remains is the hard constructive proof: build a concrete root-owned
    non-backref `U` for arbitrary input strings and prove its cardinality and
    member-size bounds in terms of the original regex size. Until that theorem
    is checked, BR-039/BR-040 remain unpaid.
- Smoke/tooling note:
  - The Scala Chapter 7 grid now reuses one `StrongDeferredMemoResult` per
    `(k,n)` when multiple `strongMemo*` metrics are requested. This removes
    repeated non-DAG derivative recomputation from the plotting pipeline; it is
    not proof progress and must not be counted as bounty.

## Cubic Bound Research Checkpoint: Bridge-Owner Member Size (2026-06-05)

- Branch: `codex/backref-values`
- Agent: Codex
- Checked proof addition:
  - `FBound.thy:strong_deferred_strong_rows_raw_bridge_owner_member_sizeI`
- Design result:
  - The strong-row bridge owner now has a direct member-size preservation fact:
    if every bridge row has raw size at most `M`, then every expression in
    `strong_deferred_strong_rows_raw_bridge_owner r s` also has raw size at
    most `M`.
  - This is useful for the final route because active-suffix pruning and the
    following subterm closure do not independently inflate member size. It
    removes one possible source of accounting noise from the owner-universe
    proof.
  - This does **not** prove the final cubic theorem. In fact, a naive proof
    that combines a cubic cardinality bound for the bridge owner with a linear
    member-size bound would still give a quartic tree-size bound. The main
    target therefore remains the shared/row-DAG universe cardinality theorem,
    or a sharper root-owned owner bound that avoids this extra multiplication.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Bounty status: proof infrastructure only. The final non-backref cubic theorem
  remains unproved and no bounty is claimed.

## Cubic Bound Research Checkpoint: Final Theorem Still Open, DAG Bridge Smoke Fixed (2026-06-05)

- Branch: `codex/backref-values`
- Agent: Codex
- User-priority clarification:
  - The top priority is the final checked theorem that the final strong
    simplification route satisfies a cubic bound for the non-backref fragment.
    That theorem is **not** complete.
  - Existing Isabelle theorems such as
    `strong_deferred_original_raw_row_norm_active_suffix_memo_POSIX_contract`
    and `strong_deferred_row_gate_norm_active_suffix_universe_POSIX_contract`
    are conditional handoffs. They prove correctness/size bounds from an
    assumed finite closed universe `U`; they do not construct the concrete
    root-owned cubic universe.
- Tooling fix:
  - `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1` now exposes the Scala
    flags `POSIX_SMOKE_STRONG_ROWS_BRIDGE_DAG` and
    `POSIX_SMOKE_STRONG_ROWS_BRIDGE_ONLY_CH7`.
  - This prevents Chapter 7 bridge checks from silently falling back to the
    non-DAG tree path, which previously produced a Java heap OOM.
- Smoke evidence after the fix:
  - Exhaustive depth `2`, input length `3`, DAG bridge:
    `84300` regex/input pairs checked; final-active coverage `832/832`;
    maxRows `3`; maxBridgeRows `15`.
  - Deterministic random depth `5`, input length `6`, seed `20260602`, DAG
    bridge: `1000` cases checked; final-active coverage `72/72`; maxRows `6`;
    maxBridgeRows `71`.
  - Chapter 7 DAG bridge, `k=5`, lengths `4,8,16,32`:
    final-active coverage `19/19`; maxRows `15`; maxBridgeRows `83`.
  - Chapter 7 DAG bridge, `k=8`, lengths `4,8,16,32,64`:
    final-active coverage `41/41`; maxRows `36`; maxBridgeRows `259`.
- Current proof target:
  - Do not add more wrapper-style contracts. The next real theorem must
    construct a concrete original-regex universe closed under local derivative
    normalization, `rflts`, active-suffix pruning, and subterms, and prove its
    cardinality/member-size bounds. Only that closes the cubic-bound gap.
- Bounty status: no cubic bounty claimed. Smoke and wrapper exposure are
  supporting evidence only.

## Cubic Route Tooling Checkpoint: Antimirov Row Diff Fuzz Fixed Point (2026-06-06)

- Branch: `codex/backref-values`
- Agent: Codex
- Final theorem status: **not complete**. This checkpoint is an experimental
  scan/prune-vs-Antimirov comparison harness plus two Scala-side simplification
  improvements. It does not construct the missing Isabelle cubic universe.
- New smoke harness:
  - Added `POSIX_SMOKE_COMPARE_SCAN_ROWS`.
  - For each regex/input prefix, it runs scan/prune strong rows against
    Antimirov strong linear-form rows and records row-count ratio, total row
    tree-size ratio, max-row-size ratio, and structural coverage gaps.
  - The Antimirov side is deliberately not row-pruned; it is only strong
    simplified and fully flattened as linear forms.
- Fuzz-driven fixes:
  - First bad random case had equal row count but scan total size `25` vs
    Antimirov `22`; the scan row retained a duplicated `STAR b` suffix after
    pruning. Fix: after row pruning, run `bsimpStrong` once more and fully
    flatten before distincting rows.
  - Second bad random case had scan row count `5` vs Antimirov `4`; scan had
    split a standalone suffix row away from `SEQ (ALTs ...) suffix`. Fix:
    add a guarded `absorbStandaloneSuffixRows` pass that folds a standalone
    suffix back into an `AONE` branch only when the resulting row list does
    not increase total row size.
  - Coverage comparison was strengthened from single-row coverage to
    row-set coverage via expanded row keys, so factored scan rows can be
    compared against multiple Antimirov terms.
- Smoke evidence:
  - Exhaustive depth `2`, input length `3`: `84300` regex/input pairs checked
    per run, with no scan/prune row observations worse than Antimirov strong
    linear-form rows after the fixes.
  - Random fuzz, seeds `20260607`..`20260611`, depth `8`, input length `12`,
    `10000` cases per seed: no worse observations after the fixes.
  - Deeper random fuzz, seeds `20260612`..`20260614`, depth `10`, input length
    `14`, `20000` cases per seed: no worse observations after the fixes.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Proof follow-up:
  - Port only the proof-relevant pieces carefully. The Scala absorber is a
    useful guide for a row-level lemma, but the checked Isabelle route still
    needs a formal counterpart before it can affect the cubic theorem.
  - The final non-backref cubic theorem remains open.

## Cubic Route Checkpoint: Checked Clean Strong Rows (2026-06-06)

- Branch: `codex/backref-values`
- Agent: Codex
- Final theorem status: **not complete**. This checkpoint ports the first
  fuzz-driven simplification improvement into Isabelle as a new proof-facing
  route, but it still does not construct the missing all-input cubic universe.
- Checked Isabelle additions:
  - `GeneralRegexBound.thy:rpder_strong_rows_clean`
  - `GeneralRegexBound.thy:rpd_der_strong_clean`
  - `GeneralRegexBound.thy:rpders_strong_rows_clean`
  - `GeneralRegexBound.thy:rpders_strong1_rows_clean`
  - `GeneralRegexBound.thy:legacy_rpder_strong_rows_clean`
  - `GeneralRegexBound.thy:legacy_rpders_strong_rows_clean`
  - `GeneralRegexBound.thy:RLS_set_map_rsimpStrong`
  - `GeneralRegexBound.thy:RLS_rpder_strong_rows_clean`
  - `GeneralRegexBound.thy:RL_rpd_der_strong_clean`
  - `GeneralRegexBound.thy:rsizes_map_rsimpStrong_le`
  - `GeneralRegexBound.thy:rsizes_rpder_strong_rows_clean_le`
  - `GeneralRegexBound.thy:length_rpder_strong_rows_clean_le_generated_rsizes`
  - `GeneralRegexBound.thy:card_set_rpder_strong_rows_clean_le_generated_rsizes`
  - `GeneralRegexBound.thy:length_rpder_strong_rows_clean_single_cubic`
  - `GeneralRegexBound.thy:card_set_rpder_strong_rows_clean_single_cubic`
  - `FBound.thy:length_rpder_strong_rows_clean_rerase_intern_single_cubic`
  - `FBound.thy:card_set_rpder_strong_rows_clean_rerase_intern_single_cubic`
- Meaning:
  - `rpder_strong_rows_clean` matches the fuzz fix that applies `rsimpStrong`
    once more after active row pruning. Isabelle now checks that this cleaned
    row route preserves the Antimirov derivative language and keeps the same
    one-step cubic count scaffold.
  - This is intentionally added beside the older `rpder_strong_rows` route
    rather than replacing it, so existing bridge proofs remain stable while
    the cleaned route is available for the next proof step.
- Additional smoke evidence after the proof port:
  - `POSIX_SMOKE_COMPARE_SCAN_ROWS=1`, seeds `20260615` and `20260616`,
    depth `9`, input length `13`, `15000` random cases per seed, plus the
    depth `2`/input `3` exhaustive grid on each run: no scan/prune rows worse
    than Antimirov strong linear-form rows.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.
- Remaining proof gap:
  - The guarded standalone-suffix absorber is still Scala-only. The next
    useful Isabelle step is to formulate it as a row-factor/coverage lemma
    before making it part of a checked route.

## Cubic Route Checkpoint: Standalone-Suffix Absorption Lemma (2026-06-06)

- Branch: `codex/backref-values`
- Agent: Codex
- Final theorem status: **not complete**. This checkpoint proves the core
  semantic and size facts behind the Scala standalone-suffix absorber, but it
  does not yet define a full Isabelle absorber pass.
- Checked Isabelle additions:
  - `GeneralRegexBound.thy:RL_RALTS_absorb_standalone_suffix`
  - `GeneralRegexBound.thy:RL_RALTS_absorb_standalone_suffix_context`
  - `GeneralRegexBound.thy:rsizes_absorb_standalone_suffix_le`
- Meaning:
  - Isabelle now checks the row-factor identity
    `RALTS [RSEQ (RALTS ps) k, k]` has the same language as
    `RALTS [RSEQ (RALTS (ps @ [RONE])) k]`.
  - Isabelle also checks that replacing those two rows by the absorbed one
    does not increase `rsizes`.
  - This is exactly the proof-facing kernel of the fuzz-driven Scala
    `absorbStandaloneSuffixRows` improvement. The remaining work is to lift
    it from a local two-row identity into a list-level guarded normalization
    route.
- Build: full CI PASS via `agent_hunt_pipeline/scripts/isabelle_ci.ps1
  -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240`.

## Cubic Route Checkpoint: Covered-Drop Row Diff Fixed Point (2026-06-06)

- Branch: `codex/backref-values`
- Agent: Codex
- Final theorem status: **not complete**. This checkpoint improves the
  scan/prune-vs-Antimirov row comparison loop and adds proof-facing shrink
  relations, but it still does not construct the missing all-input cubic
  universe.
- Scala row-diff improvements:
  - Added strict secondary reporting via
    `POSIX_SMOKE_COMPARE_SCAN_ROWS_INCLUDE_MAX_ONLY`, so max-row-only losses
    are visible even when row count and total row size improve.
  - Added `POSIX_SMOKE_COMPARE_SCAN_ROWS_DUMP_CASE` to replay a random witness
    and print the actual scan rows and Antimirov strong linear-form rows.
  - Added `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_FIXED_POINT`; when enabled,
    the harness raises an assertion if a run has any `primary` or
    `unexplained` observations.
  - Added `POSIX_SMOKE_COMPARE_SCAN_ROWS_KNOWN_REGRESSIONS` to replay the
    historical Antimirov row-diff witnesses by seed/case and require the same
    fixed-point condition.
  - Wired the known-regression gate into `agent_hunt_pipeline/scripts/isabelle_ci.ps1`:
    the default Scala CI smoke now runs the 6 replayed row-diff witnesses with
    `includeMaxOnly=true`, `top=6`, and `maxNormRows=8192`.
  - Added night-fuzz controls:
    `POSIX_SMOKE_COMPARE_SCAN_ROWS_SKIP_EXHAUSTIVE`,
    `POSIX_SMOKE_COMPARE_SCAN_ROWS_RANDOM_MAX_REGEX_SIZE`, and
    `POSIX_SMOKE_COMPARE_SCAN_ROWS_PROGRESS_EVERY`, so long random sweeps can
    avoid repeating the same exhaustive grid and can heartbeat/skip oversized
    generated regexes without changing default behavior.
  - Added `POSIX_SMOKE_COMPARE_SCAN_ROWS_SEEDS`; this accepts comma-separated
    seeds and inclusive ranges such as `20260654..20260658`, so multi-seed
    Antimirov row-diff fuzz runs in one Scala process instead of recompiling
    once per seed.
  - Tightened row-diff observation ranking: a case now reports primary or
    unexplained observations ahead of explained max-only tradeoffs, so the
    fixed-point gate cannot hide an actionable prefix behind a larger
    `absorbedSuffix` score from the same input.
  - Added scan-row-diff shrinking:
    `POSIX_SMOKE_COMPARE_SCAN_ROWS_SHRINK_CASE` replays a random seed/case,
    `POSIX_SMOKE_COMPARE_SCAN_ROWS_SHRINK_MODE` selects
    `actionable`, `primary`, `unexplained`, or `any`, and the harness dumps the
    rows before and after greedy regex/input shrinking.
  - Added `POSIX_SMOKE_COMPARE_SCAN_ROWS_SHRINK_ON_FAILURE` (default on):
    fixed-point assertion failures now include an auto-shrunk actionable
    witness summary, so night fuzz failures immediately carry a smaller
    regex/input to inspect.
  - Added `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE`: the harness now scans
    one or more random seeds for the first row-diff witness matching
    `actionable`, `primary`, `unexplained`, or `any`, dumps the original
    scan rows vs Antimirov rows, and immediately dumps the greedily shrunk
    witness. This is the forward search loop for comparing where scan/prune
    still differs from partial derivatives.
  - Added an explicit linear-term count to row-diff observations. A plain row
    counts as one term, while a factored row
    `RSEQ (RALTS ps) k` counts as `|ps|` terms. The fixed-point gate now treats
    `termRatio > 1` as primary, and summaries report `terms=m/n`,
    `termRatio`, and `termOnly`, so the accumulator rows can be compared more
    directly with Antimirov linear-form terms.
  - Added row-diff classifications:
    - `absorbedSuffix`: scan folds Antimirov rows
      `RSEQ (RALTS ps) k` and `k` into `RSEQ (RALTS (ps @ [RONE])) k`.
    - `coveredDrop`: scan deletes rows covered by the remaining row set.
  - Strengthened bridge coverage for Antimirov-vs-scan comparison:
    nested right-associated scan rows are compared against Antimirov key
    buckets by stripping a matching sequence-factor suffix and checking the
    remaining prefix payload.
  - Added guarded `pruneCoveredRows`: repeatedly removes one row only when the
    remaining rows cover it; this fixed a primary fuzz witness where scan had
    `8/7` rows and total size `653/573` against Antimirov.
- Checked Isabelle additions:
  - Standalone-suffix relation:
    - `GeneralRegexBound.thy:rlinear_terms`
    - `GeneralRegexBound.thy:rlinear_termss`
    - `GeneralRegexBound.thy:rlinear_terms_le_rsize`
    - `GeneralRegexBound.thy:rlinear_termss_le_rsizes`
    - `GeneralRegexBound.thy:rabsorb_standalone_suffix_step`
    - `GeneralRegexBound.thy:rabsorb_standalone_suffix_terms_step`
    - `GeneralRegexBound.thy:rabsorb_standalone_suffix`
    - `GeneralRegexBound.thy:rabsorb_standalone_suffix_terms`
    - `GeneralRegexBound.thy:rabsorb_standalone_suffix_terms_step_imp`
    - `GeneralRegexBound.thy:rabsorb_standalone_suffix_terms_imp`
    - `GeneralRegexBound.thy:RL_RALTS_rabsorb_standalone_suffix_step`
    - `GeneralRegexBound.thy:rsizes_rabsorb_standalone_suffix_step_le`
    - `GeneralRegexBound.thy:rlinear_termss_rabsorb_standalone_suffix_terms_step_le`
    - `GeneralRegexBound.thy:legacy_rabsorb_standalone_suffix_step`
    - `GeneralRegexBound.thy:RL_RALTS_rabsorb_standalone_suffix`
    - `GeneralRegexBound.thy:rsizes_rabsorb_standalone_suffix_le`
    - `GeneralRegexBound.thy:legacy_rabsorb_standalone_suffix`
    - `GeneralRegexBound.thy:RL_RALTS_rabsorb_standalone_suffix_terms`
    - `GeneralRegexBound.thy:rsizes_rabsorb_standalone_suffix_terms_le`
    - `GeneralRegexBound.thy:rlinear_termss_rabsorb_standalone_suffix_terms_le`
    - `GeneralRegexBound.thy:legacy_rabsorb_standalone_suffix_terms`
  - Generic covered-row drop relation:
    - `GeneralRegexBound.thy:rdrop_covered_step`
    - `GeneralRegexBound.thy:rdrop_covered`
    - `GeneralRegexBound.thy:RL_RALTS_rdrop_covered_step`
    - `GeneralRegexBound.thy:rsizes_rdrop_covered_step_le`
    - `GeneralRegexBound.thy:rlinear_termss_rdrop_covered_step_le`
    - `GeneralRegexBound.thy:legacy_rdrop_covered_step`
    - `GeneralRegexBound.thy:RL_RALTS_rdrop_covered`
    - `GeneralRegexBound.thy:rsizes_rdrop_covered_le`
    - `GeneralRegexBound.thy:rlinear_termss_rdrop_covered_le`
    - `GeneralRegexBound.thy:legacy_rdrop_covered`
  - Clean absorbed/pruned strong rows:
    - `GeneralRegexBound.thy:rpder_strong_rows_clean_absorbed`
    - `GeneralRegexBound.thy:rpder_strong_rows_clean_absorbed_pruned`
    - `GeneralRegexBound.thy:legacy_rpder_strong_rows_clean_absorbed`
    - `GeneralRegexBound.thy:legacy_rpder_strong_rows_clean_absorbed_pruned`
    - `GeneralRegexBound.thy:RLS_rpder_strong_rows_clean_absorbed`
    - `GeneralRegexBound.thy:RLS_rpder_strong_rows_clean_absorbed_pruned`
    - `GeneralRegexBound.thy:rsizes_rpder_strong_rows_clean_absorbed_le`
    - `GeneralRegexBound.thy:rsizes_rpder_strong_rows_clean_absorbed_pruned_le`
    - `GeneralRegexBound.thy:rlinear_termss_rpder_strong_rows_clean_absorbed_le_generated_rsizes`
    - `GeneralRegexBound.thy:rlinear_termss_rpder_strong_rows_clean_absorbed_pruned_le_generated_rsizes`
    - `GeneralRegexBound.thy:length_rpder_strong_rows_clean_absorbed_le_generated_rsizes`
    - `GeneralRegexBound.thy:length_rpder_strong_rows_clean_absorbed_pruned_le_generated_rsizes`
    - `GeneralRegexBound.thy:card_set_rpder_strong_rows_clean_absorbed_le_generated_rsizes`
    - `GeneralRegexBound.thy:card_set_rpder_strong_rows_clean_absorbed_pruned_le_generated_rsizes`
    - `GeneralRegexBound.thy:length_rpder_strong_rows_clean_absorbed_single_cubic`
    - `GeneralRegexBound.thy:length_rpder_strong_rows_clean_absorbed_pruned_single_cubic`
    - `GeneralRegexBound.thy:rlinear_termss_rpder_strong_rows_clean_absorbed_single_cubic`
    - `GeneralRegexBound.thy:rlinear_termss_rpder_strong_rows_clean_absorbed_pruned_single_cubic`
    - `GeneralRegexBound.thy:card_set_rpder_strong_rows_clean_absorbed_single_cubic`
    - `GeneralRegexBound.thy:card_set_rpder_strong_rows_clean_absorbed_pruned_single_cubic`
    - `FBound.thy:length_rpder_strong_rows_clean_absorbed_rerase_intern_single_cubic`
    - `FBound.thy:card_set_rpder_strong_rows_clean_absorbed_rerase_intern_single_cubic`
    - `FBound.thy:rlinear_termss_rpder_strong_rows_clean_absorbed_rerase_intern_single_cubic`
    - `FBound.thy:length_rpder_strong_rows_clean_absorbed_pruned_rerase_intern_single_cubic`
    - `FBound.thy:rlinear_termss_rpder_strong_rows_clean_absorbed_pruned_rerase_intern_single_cubic`
    - `FBound.thy:card_set_rpder_strong_rows_clean_absorbed_pruned_rerase_intern_single_cubic`
  - Term-safe clean absorbed/pruned strong rows:
    - `GeneralRegexBound.thy:rpder_strong_rows_clean_terms_absorbed`
    - `GeneralRegexBound.thy:rpder_strong_rows_clean_terms_absorbed_pruned`
    - `GeneralRegexBound.thy:rpder_strong_rows_clean_terms_absorbed_imp_absorbed`
    - `GeneralRegexBound.thy:rpder_strong_rows_clean_terms_absorbed_pruned_imp_absorbed_pruned`
    - `GeneralRegexBound.thy:legacy_rpder_strong_rows_clean_terms_absorbed`
    - `GeneralRegexBound.thy:legacy_rpder_strong_rows_clean_terms_absorbed_pruned`
    - `GeneralRegexBound.thy:RLS_rpder_strong_rows_clean_terms_absorbed`
    - `GeneralRegexBound.thy:RLS_rpder_strong_rows_clean_terms_absorbed_pruned`
    - `GeneralRegexBound.thy:rsizes_rpder_strong_rows_clean_terms_absorbed_le`
    - `GeneralRegexBound.thy:rsizes_rpder_strong_rows_clean_terms_absorbed_pruned_le`
    - `GeneralRegexBound.thy:rlinear_termss_rpder_strong_rows_clean_terms_absorbed_le`
    - `GeneralRegexBound.thy:rlinear_termss_rpder_strong_rows_clean_terms_absorbed_pruned_le`
    - `GeneralRegexBound.thy:rlinear_termss_rpder_strong_rows_clean_terms_absorbed_le_generated_rsizes`
    - `GeneralRegexBound.thy:rlinear_termss_rpder_strong_rows_clean_terms_absorbed_pruned_le_generated_rsizes`
    - `GeneralRegexBound.thy:length_rpder_strong_rows_clean_terms_absorbed_le_generated_rsizes`
    - `GeneralRegexBound.thy:length_rpder_strong_rows_clean_terms_absorbed_pruned_le_generated_rsizes`
    - `GeneralRegexBound.thy:card_set_rpder_strong_rows_clean_terms_absorbed_le_generated_rsizes`
    - `GeneralRegexBound.thy:card_set_rpder_strong_rows_clean_terms_absorbed_pruned_le_generated_rsizes`
    - `GeneralRegexBound.thy:length_rpder_strong_rows_clean_terms_absorbed_single_cubic`
    - `GeneralRegexBound.thy:length_rpder_strong_rows_clean_terms_absorbed_pruned_single_cubic`
    - `GeneralRegexBound.thy:rlinear_termss_rpder_strong_rows_clean_terms_absorbed_single_cubic`
    - `GeneralRegexBound.thy:rlinear_termss_rpder_strong_rows_clean_terms_absorbed_pruned_single_cubic`
    - `GeneralRegexBound.thy:card_set_rpder_strong_rows_clean_terms_absorbed_single_cubic`
    - `GeneralRegexBound.thy:card_set_rpder_strong_rows_clean_terms_absorbed_pruned_single_cubic`
    - `FBound.thy:length_rpder_strong_rows_clean_terms_absorbed_rerase_intern_single_cubic`
    - `FBound.thy:card_set_rpder_strong_rows_clean_terms_absorbed_rerase_intern_single_cubic`
    - `FBound.thy:rlinear_termss_rpder_strong_rows_clean_terms_absorbed_rerase_intern_single_cubic`
    - `FBound.thy:length_rpder_strong_rows_clean_terms_absorbed_pruned_rerase_intern_single_cubic`
    - `FBound.thy:rlinear_termss_rpder_strong_rows_clean_terms_absorbed_pruned_rerase_intern_single_cubic`
    - `FBound.thy:card_set_rpder_strong_rows_clean_terms_absorbed_pruned_rerase_intern_single_cubic`
- Smoke/fuzz evidence:
  - Regression witnesses:
    - seed `20260623`, case `11701`: before `pruneCoveredRows`, scan had
      row count/size `8/7` and `653/573`; after the fix, primary observations
      are `0`.
    - seeds `20260631` and `20260632`: generalized sequence-factor
      reassociation removed the remaining coverage-only `scanExtra` witnesses.
    - seed `20260630`, case `13766`: classified the remaining max-only
      non-primary witness as `coveredDrop`.
  - Strict fuzz, seeds `20260636`..`20260640`, depth `11`, input length `15`,
    `30000` random cases per seed, plus exhaustive depth `2`/input `3` on each
    run: `primary=0` and `unexplained=0`. Remaining observations are classified
    as `absorbedSuffix` or `coveredDrop`.
  - Extended strict fuzz after the CI pass:
    - seed `20260641`, depth `12`, input length `16`, `5000` random cases,
      `maxNormRows=8192`: `primary=0`, `unexplained=0`.
    - seeds `20260642`..`20260646`, depth `12`, input length `16`, `15000`
      random cases per seed, `maxNormRows=8192`: `primary=0`,
      `unexplained=0`; remaining observations are `absorbedSuffix`, with one
      `coveredDrop` on seed `20260645`.
    - seeds `20260647`..`20260649`, depth `13`, input length `17`, `10000`
      random cases per seed, `maxNormRows=16384`: `primary=0`,
      `unexplained=0`; remaining observations are `absorbedSuffix`, with one
      `coveredDrop` on seed `20260649`.
    - seed `20260650`, fixed-point gate enabled, depth `10`, input length
      `14`, `1000` random cases, `maxNormRows=4096`: assertion gate passed
      with `primary=0`, `unexplained=0`.
    - known-regression gate, 6 replayed seed/case witnesses, `maxNormRows=4096`
      and again with `maxNormRows=8192`: assertion gate passed with
      `primary=0`, `unexplained=0`; the only remaining observations are the
      expected `coveredDrop`/`absorbedSuffix` max-only cases.
    - full CI after wiring the gate into `isabelle_ci.ps1`: the Scala smoke
      log now includes the known row-diff regression replay with
      `primary=0`, `unexplained=0`, followed by successful Isabelle `Posix`
      and `BackRefPilot` builds.
    - capped night-fuzz mode, seeds `20260654`..`20260658`, depth `13`, input
      length `17`, `3000` generated cases per seed, random regex size cap
      `220`, `maxNormRows=8192`: assertion gate passed with `primary=0`,
      `unexplained=0`; remaining observations are all `absorbedSuffix`.
    - batched multi-seed fuzz in one Scala process:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_SEEDS=20260659..20260664`, depth `13`,
      input length `17`, `2000` generated cases per seed, random regex size
      cap `220`, `maxNormRows=8192`: assertion gate passed for every seed with
      `primary=0`, `unexplained=0`; remaining observations are all
      `absorbedSuffix`.
    - shrinker smoke: seed `20260657`, case `2169`, depth `13`, input length
      `17`, `mode=any`, `maxNormRows=8192` shrank an `absorbedSuffix`
      max-only witness from `rsize=26` to `rsize=7` while preserving the row
      diff.
    - first-witness finder calibration:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=any`, seed `20260657`, depth
      `13`, input length `17`, `2200` generated cases, random regex size cap
      `220`, `maxNormRows=8192`: found an explained `absorbedSuffix`
      max-only witness at case `339` and shrank it to
      `STAR(SEQ(ALT(CH(b),ONE),ALT(CH(a),CH(b))))` with input `b`
      (`rsize=8`).
    - first-witness actionable search:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=actionable`, seeds
      `20260659,20260660`, depth `13`, input length `17`, `2000` generated
      cases per seed, random regex size cap `220`, `maxNormRows=8192`:
      no matching primary/unexplained/actionable witness found across `3832`
      checked cases.
    - shrink-on-failure smoke: forcing `maxNormRows=1` on the known-regression
      gate produced an expected fixed-point assertion and included an
      auto-shrunk actionable capped witness with `shrunkRsize=4`.
    - after the actionable-first ranking change, the batched
      `20260659..20260664` depth-`13` run was repeated with the fixed-point
      gate and again passed with `primary=0`, `unexplained=0`.
    - fresh fixed-point fuzz after adding first-witness finder:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_SEEDS=20260665..20260668`, depth `13`,
      input length `17`, `3000` generated cases per seed, random regex size
      cap `220`, `maxNormRows=8192`: assertion gate passed for every seed with
      `primary=0`, `unexplained=0`; all remaining observations were classified
      as `absorbedSuffix`.
    - after adding the linear-term metric, the known-regression gate still
      passed with `primary=0`, `unexplained=0`, and `termOnly=0`. The remaining
      max-only witnesses had smaller/equal term counts, for example
      `terms=5/6` on the `coveredDrop` case and `terms=14/20` on the old
      covered-row primary regression.
    - term-primary fixed-point fuzz:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_SEEDS=20260665..20260668`, depth `13`,
      input length `17`, `3000` generated cases per seed, random regex size
      cap `220`, `maxNormRows=8192`: assertion gate passed for every seed with
      `primary=0`, `unexplained=0`, and `termOnly=0`. The remaining
      `absorbedSuffix` observations had `termRatio <= 1`, often exactly `1`.
    - term-primary actionable finder:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=actionable`, seeds
      `20260669..20260672`, depth `13`, input length `17`, `2500` generated
      cases per seed, random regex size cap `220`, `maxNormRows=8192`:
      no matching primary/unexplained/actionable witness found across `9575`
      checked cases.
    - Isabelle term-metric proof smoke: `isabelle build -D . -o
      document=false Posix` passed after adding `rlinear_terms`, the
      term-safe absorbed-suffix relation, `rdrop_covered` term monotonicity,
      and the absorbed/pruned route `rlinear_termss` cubic lemmas.
    - full CI after the Isabelle term-metric proof port passed via
      `agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -NoCertificate
      -Role admin -SessionTimeoutSeconds 240`; the Scala row-diff
      known-regression replay still reported `primary=0`, `unexplained=0`,
      and `termOnly=0`, followed by successful Isabelle `Posix` and
      `BackRefPilot` builds.
    - failed local-improvement attempt: making `bpderStrongRows` accept an
      absorbed/pruned row set only when row count, total size, and max row size
      all do not increase against the pre-absorption base removed the max-only
      tradeoff but reintroduced the seed `20260623`, case `11701` primary
      regression. The failure auto-shrank to
      `STAR(ALT(SEQ(CH(b),ALT(CH(b),STAR(CH(a)))),
                SEQ(CH(b),ALT(ALT(ONE,CH(b)),CH(a)))))`
      with input `bb`, where scan had `4/3` rows and `67/52` total size.
      Conclusion: the standalone-suffix absorption is sometimes necessary to
      remove true row-count/total-size losses, so the remaining max-row `+1`
      tradeoff should be treated as a secondary/shareable-size issue rather
      than eliminated by a blind local guard.
    - targeted Isabelle build after exposing the term-safe absorbed/pruned
      route passed: `isabelle build -D . -o document=false Posix`.
    - row-diff finder now accepts `termOnly` and `maxOnly` modes, so the fuzz
      loop can search directly for the Antimirov-linear-term metric rather than
      only the coarser actionable/primary modes.
    - actionable finder, seeds `20260640..20260642`, depth `11`, input length
      `15`, `12000` generated cases per seed, random regex size cap `140`,
      `maxNormRows=8192`: no actionable witness across `34070` checked cases.
    - term-only finder, seeds `20260643..20260645`, same depth/input/cap:
      no `termOnly` witness across `34070` checked cases.
    - wider actionable finder, seeds `20260646..20260650`, depth `12`, input
      length `16`, `20000` generated cases per seed, random regex size cap
      `180`, `maxNormRows=8192`: no actionable witness across `95467` checked
      cases.
    - wider term-only finder, seeds `20260651..20260655`, same depth/input/cap:
      no `termOnly` witness across `95457` checked cases.
    - max-only finder calibration, seed `20260657`, depth `13`, input length
      `17`, `2500` generated cases, random regex size cap `220`,
      `maxNormRows=8192`: found the expected secondary `absorbedSuffix`
      witness and shrank it to
      `STAR(SEQ(ALT(CH(b),ONE),ALT(CH(a),CH(b))))` with input `b`. Scan has
      rows `1/2`, terms `3/3`, total size `13/20`, and max row `13/12`, so
      the only remaining loss is one constructor in one merged row.
    - added row-diff DAG diagnostics:
      `dag`, `maxDag`, bit-insensitive `shapeDag`, and `maxShapeDag`, plus
      finder modes `dagOnly`, `shapeDagOnly`, `maxDagOnly`, and
      `maxShapeDagOnly`. These are reported as secondary diagnostics; the
      fixed-point gate still treats rows, linear terms, total tree size, caps,
      and uncovered row relations as the actionable criteria.
    - raw `dagOnly` calibration, seed `20260656`, case `74`, shrank to
      `SEQ(SEQ(ALT(CH(a),CH(b)),CH(b)),CH(b))` with input `a`. The raw DAG
      ratio was `3/2`, but `shapeDag=2/2`; the loss is only POSIX bit
      placement, not constructor shape.
    - `shapeDagOnly` calibration, seed `20260656`, case `247`, shrank to
      `STAR(ALT(SEQ(CH(a),ALT(CH(b),CH(a))),CH(a)))` with input `a`. Scan has
      rows `1/2`, terms `3/3`, total size `13/20`, raw DAG `10/10`, but
      `shapeDag=9/7`; this is an `absorbedSuffix` tradeoff where merging a
      suffix row into the prefix accumulator reduces rows/size while adding a
      larger factored-row shape.
    - failed local-improvement attempt: guarding `bpderStrongRows` so
      absorption/pruning is accepted only when local `shapeDag` does not
      increase preserved `primary=0` but created `5` unexplained known
      row-diff witnesses. The guard was reverted; the better treatment is to
      keep `shapeDagOnly` as a secondary diagnostic, not as the production
      acceptance rule.
    - bridge coverage improvement: `rowKeyCoveredBy` now also compares the
      `bsimpStrong`-normalized key and uses `expandedRowSubsetCoveredBy` as a
      final coverage check. This removed a newly surfaced actionable
      `normExtra` witness that shrank to
      `SEQ(STAR(SEQ(CH(b),ALT(SEQ(CH(b),ALT(CH(a),ONE)),ONE))),
           ALT(CH(a),CH(b)))`
      with input `bb`.
    - post-bridge actionable finder:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=actionable`, seeds
      `20260659..20260661`, depth `12`, input length `16`, `12000` generated
      cases per seed, random regex size cap `180`, `maxNormRows=8192`:
      no actionable witness across `34419` checked cases.
    - post-bridge term-only finder:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=termOnly`, seeds
      `20260662..20260664`, same depth/input/cap: no `termOnly` witness across
      `34387` checked cases.
    - full CI after the DAG/shape diagnostics and bridge coverage improvement
      passed. The known row-diff replay now reports `termOnly=0`, `maxOnly=2`,
      `dagOnly=1`, `maxDagOnly=1`, `shapeDagOnly=3`,
      `maxShapeDagOnly=3`, `primary=0`, and `unexplained=0`, followed by
      successful Isabelle `Posix` and `BackRefPilot` builds.
    - mirrored the bridge coverage improvement into the DAG/id-side
      comparator: `rowKeyCoveredById` now also compares the
      `bsimpStrongId`-normalized key and uses `expandedRowSubsetCoveredById`
      as a final coverage check, matching the tree-side `rowKeyCoveredBy`.
    - DAG bridge-specific smoke:
      `scala_cubic_smoke.ps1 -Route custom -SkipLegacyCubic
      -CheckStrongRowsBridge -RequireStrongRowsBridgeCoverage
      -StrongRowsBridgeDag`, depth `2`, input length `3`, plus `1000` random
      cases at depth `8`/input length `12`, seed `20260665`: exhaustive
      final-active coverage `832/832`; random coverage `184/184`. A larger
      depth-`10`/`3000` random run exhausted the Java heap after the exhaustive
      bridge phase had already passed, so the checked evidence uses the
      smaller random bridge run.
    - DAG Chapter 7 bridge smoke:
      `scala_cubic_smoke.ps1 -Route custom -SkipLegacyCubic
      -CheckStrongRowsBridgeCh7 -RequireStrongRowsBridgeCoverage
      -StrongRowsBridgeDag -StrongRowsBridgeOnlyCh7`, `k=5`,
      lengths `4,8,12,16,20`: passed without coverage failure.
    - fresh post-id-bridge actionable finder:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=actionable`, seeds
      `20260666..20260668`, depth `12`, input length `16`, `12000` generated
      cases per seed, random regex size cap `180`, `maxNormRows=8192`:
      no actionable witness across `34347` checked cases.
    - fresh post-id-bridge term-only finder:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=termOnly`, seeds
      `20260669..20260671`, same depth/input/cap: no `termOnly` witness across
      `34342` checked cases.
    - next fixed-point loop found a new actionable bridge-only witness:
      seed `20260674`, case `256`, depth `12`, input length `16`, shrank to
      `SEQ(STAR(SEQ(CH(b),ALT(SEQ(CH(b),ALT(ONE,CH(a))),ONE))),
           ALT(CH(a),SEQ(CH(a),ALT(ONE,CH(a)))))`
      with input `bb`. Scan still had no primary loss (`rows=2/2`,
      `terms=3/4`, `size=46/48`), but the comparator reported a `normExtra`
      row because top-level key expansion did not recursively split an
      alternative branch containing another sequence/alternative. This is
      exactly a linear-forms correspondence gap, not a scan simplification
      regression.
    - bridge coverage improvement: added deep sequence-key expansion for both
      the tree and DAG/id comparators. `expandedSeqKeysDeep` /
      `expandedSeqKeysDeepId` recursively expand alternatives that occur inside
      a chosen branch, and `rowKeyCoveredBy` / `rowKeyCoveredById` use the
      resulting deep row-key subset check as a bridge-only explanation rule.
      The production `bpderStrongRows` simplifier is unchanged by this rule.
    - added the seed `20260674`, case `256` witness to the known row-diff
      regression replay as "nested alternative branch deep linear coverage".
      The replay now checks `7` cases and reports `scanExtra=0`, `normExtra=0`,
      `termOnly=0`, `primary=0`, and `unexplained=0`.
    - post-deep-bridge actionable finder:
      seed `20260674`, depth `12`, input length `16`, `12000` generated cases,
      random regex size cap `190`, `maxNormRows=8192`: no actionable witness
      across `11574` checked cases.
    - post-deep-bridge fresh actionable finder:
      seeds `20260680..20260682`, same depth/input/cap with `12000` generated
      cases per seed: no actionable witness across `34608` checked cases.
    - post-deep-bridge fixed-point random comparison:
      seeds `20260680..20260682`, depth `12`, input length `16`, `6000`
      generated cases per seed, random regex size cap `190`,
      `maxNormRows=8192`, `RequireFixedPoint=1`: `primary=0`,
      `unexplained=0`, and `termOnly=0` across `17308` checked cases.
    - DAG bridge smoke after the id-side deep expansion:
      exhaustive final-active coverage `832/832` at depth `2`/input `3`, plus
      random DAG bridge coverage `189/189` on `1000` cases at depth `8`/input
      `12`, seed `20260683`. The Chapter 7 DAG bridge smoke with `k=5` and
      lengths `4,8,12,16,20` also passed without coverage failure.
    - deeper post-deep-bridge fuzz:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=actionable`, seeds
      `20260684..20260686`, depth `13`, input length `17`, random regex size
      cap `220`, `maxNormRows=10000`: no actionable witness across `28722`
      checked cases. The matching `primary` finder on seeds
      `20260687..20260689` found no primary witness across `28749` checked
      cases.
    - continued post-deep-bridge fixed-point loop:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=unexplained`, seeds
      `20260690..20260692`, depth `13`, input length `17`, random regex size
      cap `220`, `maxNormRows=10000`: no unexplained bridge witness across
      `34572` checked cases.
    - continued post-deep-bridge term metric loop:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=termOnly`, seeds
      `20260693..20260695`, same depth/input/cap: no linear-term regression
      witness across `34439` checked cases.
    - deeper post-deep-bridge actionable loop:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=actionable`, seeds
      `20260696..20260698`, depth `14`, input length `18`, random regex size
      cap `260`, `maxNormRows=12000`: no actionable witness across `25870`
      checked cases.
    - cap-pressure primary probe:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=primary`, seed `20260699`,
      depth `14`, input length `18`, random regex size cap `280`,
      deliberately lower `maxNormRows=2048`: no primary/capped witness across
      `7731` checked cases. The same probe on seed `20260700` with `5000`
      generated cases found no primary/capped witness across `4842` checked
      cases.
    - high-cap actionable probe:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=actionable`, seeds
      `20260702..20260703`, depth `14`, input length `18`, random regex size
      cap `280`, `maxNormRows=14000`: no actionable witness across `13487`
      checked cases.
    - high-cap fixed-point random comparison:
      seeds `20260702..20260703`, depth `14`, input length `18`, `4000`
      generated cases per seed, random regex size cap `280`,
      `maxNormRows=14000`, `RequireFixedPoint=1`: both seeds report
      `capped=0`, `termOnly=0`, `primary=0`, and `unexplained=0` across
      `7704` checked cases. The remaining observations are secondary
      `absorbedSuffix`/max-row/DAG-shape tradeoffs where scan has no worse
      row/term/total-size metric.
    - proof-facing cubic interface cleanup:
      added combined term-safe cubic bounds
      `rpder_strong_rows_clean_terms_absorbed_single_cubic_bounds` and
      `rpder_strong_rows_clean_terms_absorbed_pruned_single_cubic_bounds`,
      plus the `rerase (intern r)` wrappers in `FBound.thy`. These package the
      three Antimirov-aligned metrics together:
      `length rows`, `card (set rows)`, and `rlinear_termss rows` are all
      bounded by `2 * (|r| + 3)^3` for the term-safe absorbed/pruned route.
      `isabelle build -D . Posix` passed after this proof-facing addition.
    - post-interface focused fuzz:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=unexplained`, seeds
      `20260704..20260705`, depth `14`, input length `18`, random regex size
      cap `280`, `maxNormRows=14000`: no unexplained bridge witness across
      `13520` checked cases. The matching `termOnly` finder on seeds
      `20260706..20260707` found no linear-term regression across `13539`
      checked cases.
    - deep linear-term diagnostic:
      added `rowDeepLinearTermCount` / `rowsDeepLinearTermCount` to the Scala
      row-diff harness. This diagnostic counts the recursive deep row-key
      expansion used by the deep bridge coverage check, filtering out zero
      rows, so the harness can now look for nested-alternative branch-count
      regressions that the shallow `rlinear_terms`-style metric could miss.
      It is reported as `deepTerms=scan/norm` with `deepTermRatio`, and has a
      dedicated finder mode `deepTermOnly`; it remains a diagnostic/fuzz mode,
      not a new Isabelle theorem assumption.
    - known row-diff replay with deep term diagnostics:
      the `7` known cases still report `termOnly=0`, `deepTermOnly=0`,
      `primary=0`, and `unexplained=0`. The nested alternative regression now
      shows `deepTerms=19/23`, confirming that scan is also no worse under the
      deeper branch-count metric.
    - deep-term focused fuzz:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=deepTermOnly`, seeds
      `20260708..20260710`, depth `14`, input length `18`, random regex size
      cap `280`, `maxNormRows=14000`: no deep-term regression witness across
      `28961` checked cases.
    - fixed-point random comparison with deep term diagnostics:
      seeds `20260708..20260709`, depth `14`, input length `18`, `4000`
      generated cases per seed, random regex size cap `280`,
      `maxNormRows=14000`, `RequireFixedPoint=1`: both seeds report
      `termOnly=0`, `deepTermOnly=0`, `primary=0`, and `unexplained=0` across
      `7737` checked cases.
    - deep-term fallback visibility:
      the deep linear-term diagnostic now records whether recursive key
      expansion exceeded `deepLinearTermCountMaxKeys=65536` and had to fall
      back to the shallow term count. The row-diff output reports
      `deepTermCapped=scan/norm`, aggregate comparisons count
      `deepTermCapped`, and the finder accepts `deepTermCapped` /
      `deep-term-capped` mode. This prevents a silent fallback from being
      mistaken for complete deep-term evidence.
    - known row-diff replay after exposing deep-term caps:
      the `7` known cases still report `termOnly=0`, `deepTermOnly=0`,
      `deepTermCapped=0`, `primary=0`, and `unexplained=0`.
    - deep-term cap probe:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=deepTermCapped`, seed
      `20260711`, depth `14`, input length `18`, random regex size cap `280`,
      `maxNormRows=14000`: no deep-term cap witness across `7734` checked
      cases. A split rerun on seed `20260712` found no deep-term cap witness
      across `4839` checked cases.
    - deeper deep-term-only probe:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=deepTermOnly`, seeds
      `20260713..20260714`, depth `15`, input length `18`, random regex size
      cap `320`, `maxNormRows=16000`: no deep-term regression witness across
      `15415` checked cases.
    - fixed-point random comparison with deep-term cap counts:
      seeds `20260711..20260712`, depth `14`, input length `18`, `3000`
      generated cases per seed, random regex size cap `280`,
      `maxNormRows=14000`, `RequireFixedPoint=1`: both seeds report
      `deepTermCapped=0`, `termOnly=0`, `deepTermOnly=0`, `primary=0`, and
      `unexplained=0` across `5818` checked cases.
    - deeper fixed-point finder loop:
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=actionable`, seeds
      `20260715..20260716`, depth `15`, input length `18`, random regex size
      cap `320`, `maxNormRows=16000`: no actionable witness across `11567`
      checked cases. The matching `deepTermCapped` probe on seeds
      `20260717..20260718` found no capped deep-term witness across `11542`
      checked cases. The matching `deepTermOnly` probe on seeds
      `20260721..20260722` found no deep-term regression witness across
      `11550` checked cases; seed `20260722` was rerun standalone after a
      wall-clock timeout interrupted the first combined sweep.
    - deeper fixed-point random comparison:
      seeds `20260719..20260720`, depth `15`, input length `18`, `4000`
      generated cases per seed, random regex size cap `320`,
      `maxNormRows=16000`, `RequireFixedPoint=1`: both seeds report
      `capped=0`, `termOnly=0`, `deepTermOnly=0`, `deepTermCapped=0`,
      `primary=0`, and `unexplained=0` across `7713` checked cases. The
      remaining `210` observations are explained secondary
      absorbed-suffix/covered-row or max/DAG/shape tradeoffs; `scanExtra=0`
      throughout this run.
    - secondary max-only shrink:
      replaying seed `20260719`, case `3403`, with
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_SHRINK_MODE=maxOnly` shrinks the local
      max-row tradeoff to
      `STAR(ALT(SEQ(CH(a),ALT(CH(a),CH(b))),CH(a)))` on input `a`. Scan
      absorbs Antimirov's standalone suffix row into one row, giving
      `rows=1/2`, `terms=3/3`, `deepTerms=3/3`, and `size=13/20`, but the
      largest single row grows from `12` to `13` (`maxDag=11/10`,
      `maxShapeDag=9/7`). This confirms the remaining max-only differences
      are a deliberate total-size/row-count win versus local-peak tradeoff,
      not a row-count or linear-term regression.
    - same-budget DAG-sharing diagnostic:
      a `dagOnly` probe on seed `20260726` found a secondary-only difference
      at case `12`; shrinking gives
      `STAR(ALT(SEQ(STAR(CH(a)),STAR(ZERO)),SEQ(CH(a),CH(b))))` on input
      `a`. Scan and Antimirov have identical rows/terms/deepTerms/total-size
      budgets (`2/2`, `2/2`, `2/2`, `19/19`) and mutually cover each other,
      but scan uses one more cross-row DAG node (`11/10`). The harness now
      classifies this exact pattern as `sameBudgetCover`, requiring equal
      row count, shallow terms, uncapped deep terms, total tree size, and
      bidirectional bridge coverage.
    - known row-diff replay after adding same-budget coverage:
      the known replay now has `8` cases, including the same-budget DAG
      sharing tradeoff. It reports `sameBudgetCover=1`, `scanExtra=0`,
      `normExtra=0`, `termOnly=0`, `deepTermOnly=0`, `deepTermCapped=0`,
      `primary=0`, and `unexplained=0`.
    - post-classification fixed-point fuzz:
      seed `20260727`, depth `15`, input length `18`, `2500` generated cases,
      random regex size cap `320`, `maxNormRows=16000`,
      `RequireFixedPoint=1`: `2411` checked cases with `primary=0`,
      `unexplained=0`, `termOnly=0`, `deepTermOnly=0`, `deepTermCapped=0`,
      and `sameBudgetCover=35`. Follow-up finders found no `actionable`
      witness on seed `20260728` across `4812` checked cases and no
      `deepTermOnly` witness on seed `20260729` across `4810` checked cases.
    - budget-nonworse coverage diagnostic:
      added `budgetNonworseCover` as a row-diff explanation and finder/shrink
      mode. It requires `scanRows <= normRows`, shallow linear terms
      nonincreasing, uncapped deep linear terms nonincreasing, total tree size
      nonincreasing, and bidirectional bridge coverage. This is the diagnostic
      that directly matches the current Antimirov-facing proof budget.
    - known row-diff replay after budget-nonworse coverage:
      the `8` known cases now split as `absorbedSuffix=1`, `coveredDrop=1`,
      `sameBudgetCover=1`, and `budgetNonworseCover=5`, with `scanExtra=0`,
      `normExtra=0`, `termOnly=0`, `deepTermOnly=0`, `deepTermCapped=0`,
      `primary=0`, and `unexplained=0`.
    - budget-nonworse shrink:
      replaying seed `20260631`, case `21040`, with
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_SHRINK_MODE=budgetNonworseCover` shrinks
      the known sequence-factor case to
      `STAR(SEQ(CH(b),ALT(SEQ(CH(b),ALT(ONE,CH(b))),ONE)))` on input `bb`.
      The shrunk budgets are rows `2/2`, shallow terms `3/4`, deep terms
      `4/5`, and total size `30/32`, while secondary DAG/max-shape tradeoffs
      remain (`dag=13/12`, `maxShapeDag=9/8`).
    - post-budget fixed-point fuzz:
      seed `20260730`, depth `15`, input length `18`, `3500` generated cases,
      random regex size cap `320`, `maxNormRows=16000`,
      `RequireFixedPoint=1`: `3362` checked cases with `primary=0`,
      `unexplained=0`, `termOnly=0`, `deepTermOnly=0`, and
      `deepTermCapped=0`. Follow-up finders found no `actionable` witness on
      seed `20260731` across `4812` checked cases and no `deepTermCapped`
      witness on seed `20260732` across `4818` checked cases.
    - proof-facing budget interface:
      added generated-budget lemmas
      `rpder_strong_rows_clean_terms_absorbed_generated_budget` and
      `rpder_strong_rows_clean_terms_absorbed_pruned_generated_budget`.
      These package the four Antimirov-facing budget metrics together:
      `length rows`, `card (set rows)`, `rlinear_termss rows`, and
      `rsizes rows` are all bounded by
      `rsizes (concat (map (rpder_norm_list c) rs))`.
    - proof-facing single-step cubic budget interface:
      added
      `rpder_strong_rows_clean_terms_absorbed_single_cubic_budget_bounds` and
      `rpder_strong_rows_clean_terms_absorbed_pruned_single_cubic_budget_bounds`,
      plus the `rerase (intern r)` wrappers in `FBound.thy`. These extend the
      previous cubic bundle by adding the total-size budget `rsizes rows`.
      `isabelle build -D . Posix` passed after the Isabelle additions.
    - post-interface targeted checks:
      known row-diff replay still reports `absorbedSuffix=1`, `coveredDrop=1`,
      `sameBudgetCover=1`, `budgetNonworseCover=5`, `primary=0`, and
      `unexplained=0`. A `budgetNonworseCover` finder on seed `20260733`,
      depth `15`, input length `18`, random regex size cap `320`,
      `maxNormRows=16000`, found no fresh witness across `3384` checked cases.
    - proof-facing semantics+budget contracts:
      added generated contracts
      `rpder_strong_rows_clean_terms_absorbed_generated_budget_contract` and
      `rpder_strong_rows_clean_terms_absorbed_pruned_generated_budget_contract`.
      They combine `RLS (set rows) = Der c (RLS (set rs))` with the four
      generated-budget bounds. Added single-step cubic contracts
      `rpder_strong_rows_clean_terms_absorbed_single_cubic_budget_contract`
      and
      `rpder_strong_rows_clean_terms_absorbed_pruned_single_cubic_budget_contract`,
      whose semantic conclusion is `RLS (set rows) = Der c (RL r)`.
    - original-regex semantics+budget wrappers:
      added `rerase (intern r)` wrappers in `FBound.thy`:
      `rpder_strong_rows_clean_terms_absorbed_rerase_intern_single_cubic_budget_contract`
      and
      `rpder_strong_rows_clean_terms_absorbed_pruned_rerase_intern_single_cubic_budget_contract`.
      Their semantic conclusion is
      `RLS (set rows) = Der c (RL (rerase (intern r)))`, and all four budget
      metrics are bounded by `2 * (rxsize r + 3)^3`.
    - post-contract targeted checks:
      `isabelle build -D . Posix` passed after adding the contracts. Known
      row-diff replay still reports `absorbedSuffix=1`, `coveredDrop=1`,
      `sameBudgetCover=1`, `budgetNonworseCover=5`, `primary=0`, and
      `unexplained=0`. An `actionable` finder on seed `20260734`, depth `15`,
      input length `18`, random regex size cap `320`, `maxNormRows=16000`,
      found no witness across `4357` checked cases.
    - one-way budget-cover fixed-point refinement:
      a wider `actionable` finder on seed `20260735`, depth `15`, input
      length `18`, random regex size cap `320`, `maxNormRows=16000`, found a
      case at generated case `6959` (`6728` checked) whose scan/prune rows had
      strictly no worse proof-facing budgets than Antimirov: rows `7/9`,
      shallow terms `8/11`, deep terms `67/79`, total size `2403/3036`, DAG
      `110/115`, and shape-DAG `80/80`. The only local regression was
      max-row DAG `98/97`, plus an unclassified `normExtra`; this is not scan
      losing to Antimirov, but Antimirov retaining an extra generated row while
      scan rows are covered by the Antimirov rows and the four proof budgets
      are nonworse. Added the `budgetNonworseOneWayCover` explanation and
      finder/shrink mode for this case class.
    - post-one-way-cover checks:
      known row-diff replay remains `primary=0` and `unexplained=0`, with
      `budgetNonworseOneWayCover=0` on the 8 old regressions. Re-running
      seed `20260735` through generated case `7000` found no `actionable`
      witness across `6766` checked cases; the matching random summary had
      `observations=185`, `normExtra=1`, `budgetNonworseOneWayCover=1`,
      `primary=0`, and `unexplained=0`. Follow-up `actionable` finders on
      seeds `20260736..20260737` found no witness across `13483` checked
      cases, and a `deepTermCapped` finder on seed `20260738` found no witness
      across `2387` checked cases.
    - one-way cover regression replay:
      added seed `20260735`, generated case `6959`, to the known row-diff
      replay. The replay now has 9 cases and reports `scanExtra=0`,
      `normExtra=1`, `capped=0`, `termOnly=0`, `deepTermOnly=0`,
      `deepTermCapped=0`, `absorbedSuffix=1`, `coveredDrop=1`,
      `sameBudgetCover=1`, `budgetNonworseCover=5`,
      `budgetNonworseOneWayCover=1`, `primary=0`, and `unexplained=0`.
    - post-regression-list fuzz:
      `actionable` finders on seeds `20260738..20260739`, depth `15`, input
      length `18`, random regex size cap `320`, `maxNormRows=16000`, found no
      witness across `9597` checked cases. A `deepTermOnly` finder completed
      seed `20260739` with no witness across `3369` checked cases; the same
      two-seed run timed out after entering seed `20260740`, so a shorter
      seed `20260740` slice was replayed and found no witness across `1165`
      checked cases.
    - continued post-regression-list fuzz:
      further `actionable` finders on seeds `20260740..20260741`, depth `15`,
      input length `18`, random regex size cap `320`, `maxNormRows=16000`,
      found no witness across `7709` checked cases. A `deepTermCapped` finder
      on seeds `20260741..20260742` found no witness across `4825` checked
      cases.
    - bounded row-diff shrink probes:
      the unbounded shrink of the one-way budget-cover witness
      `20260735/6959` produced the before-shrink dump but did not finish
      promptly, so the Java process was stopped. Added
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_SHRINK_MAX_PROBES`, default `0` for the
      old unlimited behavior. With a `200`-probe cap, the same witness shrinks
      from `rsize=300` to `rsize=198` while preserving
      `budgetNonworseOneWayCover`; the post-shrink metrics are rows `4/7`,
      shallow terms `5/9`, deep terms `32/49`, total size `879/1588`, DAG
      `82/86`, and max-row DAG `74/73`, with
      `probes=200, exhausted=true`. The finder path was also exercised with a
      `50`-probe cap: it automatically rediscovered seed `20260735`, generated
      case `6959` after `6728` checked cases and stopped with
      `probes=50, exhausted=true`.
    - post-probe fixed-point fuzz:
      random fixed-point comparison on seeds `20260743..20260744`, depth `15`,
      input length `18`, random regex size cap `320`, `maxNormRows=16000`,
      checked `2903 + 2896` cases. Both seeds had `scanExtra=0`,
      `normExtra=0`, `termOnly=0`, `deepTermOnly=0`, `deepTermCapped=0`,
      `primary=0`, and `unexplained=0`.
    - fixed-point shrink guard coverage:
      threaded `POSIX_SMOKE_COMPARE_SCAN_ROWS_SHRINK_MAX_PROBES` through the
      fixed-point failure-summary path as well, so exhaustive/random/known
      row-diff gates use the same bounded auto-shrink behavior when an
      actionable witness is found. A known-regression replay with
      `SHRINK_MAX_PROBES=100` still reports the 9-case split with
      `primary=0` and `unexplained=0`.
    - further targeted finders:
      `actionable` finder on seeds `20260745..20260746`, depth `15`, input
      length `18`, random regex size cap `320`, `maxNormRows=16000`,
      found no witness across `6725` checked cases. `deepTermOnly` finder on
      the same seeds found no witness across `4801` checked cases.
      `deepTermCapped` finder on the same seeds found no witness across
      `3845` checked cases.
    - consolidated budget and directed coverage finders:
      added finder/shrink modes `proofBudgetWorse`, `budgetWorse`,
      `scanCoverageGap`, and `normCoverageGap`. `proofBudgetWorse` searches
      for the Isabelle-facing row/term/total-size budget dimensions;
      `budgetWorse` additionally includes deep expanded term counts and
      capping; the coverage modes separate dangerous scan-only rows from the
      one-way Antimirov-extra-row situation. A `budgetWorse` finder on seed
      `20260747`, depth `15`, input length `18`, size cap `320`,
      `maxNormRows=16000`, found no witness across `3387` checked cases. The
      same two-seed run timed out while processing seed `20260748`, so seed
      `20260748` was replayed as a shorter complete slice and found no
      `budgetWorse` witness across `1634` checked cases. A
      `scanCoverageGap` finder on seed `20260749` found no witness across
      `2406` checked cases. The `normCoverageGap` mode was checked on the
      known one-way witness `20260735/6959`, where it correctly reports
      `scanExtra=<none>`, a `normExtra`, and
      `budgetNonworseOneWayCover`.
    - summary budget/coverage counters:
      exhaustive/random/known row-diff summaries now print
      `proofBudgetWorse`, `budgetWorse`, `scanCoverageGap`, and
      `normCoverageGap` counts directly. Known replay with these counters
      reports `proofBudgetWorse=0`, `budgetWorse=0`, `scanCoverageGap=0`,
      and `normCoverageGap=1`, matching the single one-way Antimirov-extra
      witness. A random fixed-point summary on seed `20260750`, depth `15`,
      input length `18`, size cap `320`, `maxNormRows=16000`, checked `2120`
      cases and reported all four new counters as `0`, with `primary=0` and
      `unexplained=0`.
    - hard fixed-point gates:
      added optional row-diff gates
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_PROOF_BUDGET`,
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_BUDGET`,
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_SCAN_COVERAGE`, and
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_NORM_COVERAGE`. These gates now
      fail the comparison run, choose the matching shrink mode, and use the
      bounded shrink probe cap when the requested fixed-point property is
      violated. Known replay with proof-budget, budget, and scan-coverage
      gates enabled passed on all 9 cases: `proofBudgetWorse=0`,
      `budgetWorse=0`, `scanCoverageGap=0`, `normCoverageGap=1`,
      `primary=0`, `unexplained=0`. The norm-coverage gate is intentionally
      left off for known replay because the one-way budget-cover witness is
      Antimirov-extra, not scan-extra.
    - nonworse fixed-point gate:
      added `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_NONWORSE`, a composite
      gate for the iterative scan-vs-Antimirov loop. It expands to the
      proof-budget, stronger-budget, and scan-coverage gates, so a single
      switch now checks that scan/prune rows are not worse than the
      Antimirov linear-form rows in the proof-facing budgets and do not
      contain an uncovered scan-only row. Explained Antimirov-only rows remain
      allowed; those are tracked separately by `normCoverageGap`.
      New-switch checks passed on known replay (`9` cases, with the known
      `normCoverageGap=1` left as explained one-way cover), on seed
      `20260775` (`2500` random cases, depth `5`, input length `14`), and on
      the small exhaustive depth `2`/input `3` grid (`84300` pairs).
      Added `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=nonworse` as the matching
      targeted finder/shrinker mode; it searches for any stronger-budget
      regression or uncovered scan-only row. Full local CI now runs both the
      known row-diff replay and the small exhaustive row-diff grid with
      `POSIX_SMOKE_COMPARE_SCAN_ROWS=1` and
      `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_NONWORSE=1`.
    - hard-gate fuzz/fixed point:
      random fixed-point gate on seed `20260751`, depth `5`, input length
      `14`, checked `2000` cases and reported `proofBudgetWorse=0`,
      `budgetWorse=0`, `scanCoverageGap=0`, `normCoverageGap=0`,
      `primary=0`, and `unexplained=0`. A three-seed run
      `20260752..20260754` checked `9000` more cases under the same hard
      gates; all three seeds again had the four budget/coverage counters at
      `0`, with only explained `absorbedSuffix`/`sameBudgetCover` secondary
      tradeoffs. Targeted `budgetWorse` finder on seeds
      `20260755..20260758` found no witness across `20000` checked cases, and
      targeted `scanCoverageGap` finder on seeds `20260759..20260762` found
      no witness across another `20000` checked cases. A small exhaustive
      hard-gate run over depth `2`, input length `3` checked `84300`
      regex/input pairs with `observations=0`.
    - proof-facing Antimirov budget contracts:
      added compact semantic+budget contracts for both
      `rpder_strong_rows` and `rpder_strong_rows_raw`. The new contracts
      package the Antimirov-style one-step facts into one theorem:
      `RLS` equals the derivative language, and `length`, `card (set ...)`,
      `rlinear_termss`, and `rsizes` are all bounded by the generated
      `rpder_norm_list` size. Single-root cubic versions are now available
      as `rpder_strong_rows_single_cubic_budget_contract` and
      `rpder_strong_rows_raw_single_cubic_budget_contract`; the
      `rerase (intern r)` wrappers in `FBound.thy` rewrite the bound to
      `2 * (rxsize r + 3) ^ 3`. This makes the row-count/linear-form-count
      correspondence explicit enough to cite as the current Antimirov
      scaffold for scan/prune rows.
    - post-contract verification:
      `isabelle build -D . Posix` passed after the new contracts. Known
      row-diff replay with proof-budget, budget, and scan-coverage hard gates
      still passed on all 9 known cases (`proofBudgetWorse=0`,
      `budgetWorse=0`, `scanCoverageGap=0`, `normCoverageGap=1`,
      `primary=0`, `unexplained=0`). A fresh random hard-gate run on seed
      `20260763`, depth `5`, input length `14`, checked `3000` cases with
      `proofBudgetWorse=0`, `budgetWorse=0`, `scanCoverageGap=0`,
      `normCoverageGap=0`, `primary=0`, and `unexplained=0`.
    - multi-step accumulator budget contracts:
      added `rpders_strong1_rows_raw_budget_from_rsizes_bound`, which turns
      any proved final `rsizes` bound for
      `rpders_strong1_rows_raw r s` into simultaneous bounds for final
      accumulator `length`, `card (set ...)`, `rlinear_termss`, and `rsizes`.
      The generic finite-universe wrapper is
      `rpders_strong1_rows_raw_cubic_universe_budget_contractI`. `FBound.thy`
      now also has later-shared and active-suffix companion contracts for the
      original `rerase (intern r)` route:
      `strong_deferred_original_raw_row_norm_later_shared_accumulator_budget_contract`
      and
      `strong_deferred_original_raw_row_norm_active_suffix_accumulator_budget_contract`.
      These are companion theorems, so they do not change the result order of
      the existing memo cubic interfaces.
      A later pass added the remaining same-shape companion contracts in
      `FBound.thy`:
      `strong_deferred_original_raw_row_accumulator_budget_contract`,
      `strong_deferred_original_raw_row_norm_closed_accumulator_budget_contract`,
      and
      `strong_deferred_original_raw_row_norm_same_suffix_accumulator_budget_contract`.
      These give the same final raw-accumulator package for the generic raw,
      norm-closed, and same-suffix routes:
      `length`, `card (set ...)`, `rlinear_termss`, and `rsizes` are all
      bounded by the same finite-universe budget `B`.
    - post-accumulator-contract checks:
      `isabelle build -D . Posix` passed. A fresh random hard-gate run on seed
      `20260764`, depth `5`, input length `14`, checked `3000` cases and
      again reported `proofBudgetWorse=0`, `budgetWorse=0`,
      `scanCoverageGap=0`, `normCoverageGap=0`, `primary=0`, and
      `unexplained=0`.
    - post-nonworse-gate fuzz:
      seed `20260765`, depth `5`, input length `14`, checked `3000` cases
      under the hard nonworse conditions with
      `proofBudgetWorse=0`, `budgetWorse=0`, `scanCoverageGap=0`,
      `normCoverageGap=0`, `primary=0`, and `unexplained=0`. Seeds
      `20260766..20260768`, depth `6`, input length `16`, checked another
      `12000` cases with the same nonworse counters at `0`. A targeted
      `budgetWorse` finder on seeds `20260769..20260770`, depth `7`, input
      length `18`, found no witness across `14000` checked cases; a targeted
      `scanCoverageGap` finder on seeds `20260771..20260772` found no witness
      across another `14000`; and a targeted `normCoverageGap` finder on
      seeds `20260773..20260774` also found no new witness across `14000`.
      The composite `nonworse` finder on seeds `20260776..20260777`, depth
      `7`, input length `18`, found no witness across `12000` checked cases.
      A deeper composite `nonworse` finder on seeds `20260778..20260779`,
      depth `8`, input length `20`, found no witness across another `10000`
      checked cases. Full local CI passed again after wiring the nonworse
      gate into both default known replay and default exhaustive row-diff
      comparison; the default exhaustive comparison checked `84300`
      regex/input pairs with `observations=0`.
      After the extra `FBound.thy` accumulator contracts,
      `isabelle build -D . Posix` passed again. A further composite
      `nonworse` finder on seeds `20260780..20260781`, depth `8`, input
      length `20`, checked `8000` cases and found no nonworse witness:
      `proofBudgetWorse=0`, `budgetWorse=0`, and `scanCoverageGap=0` on both
      seeds. Seed `20260781` did expose one harmless `normCoverageGap`, so the
      targeted `normCoverageGap` shrinker was run on that seed and reduced it
      to
      `STAR(ALT(CH(a),SEQ(CH(a),SEQ(ALT(CH(a),CH(b)),ALT(CH(a),CH(b))))))`
      on input `aa`. Scan is strictly smaller on the main budgets
      (`rows 1/3`, `terms 3/5`, `deepTerms 6/7`, `size 21/48`) and has no
      scan-only row; the harness classifies the Antimirov-only extra as
      `absorbedSuffix`.
      A still deeper composite `nonworse` finder on seeds
      `20260782..20260785`, depth `9`, input length `22`, checked another
      `20000` random cases and again found no nonworse witness. Per-seed
      summaries had `proofBudgetWorse=0`, `budgetWorse=0`,
      `scanCoverageGap=0`, `normCoverageGap=0`, `primary=0`, and
      `unexplained=0`; the remaining observations were secondary
      `absorbedSuffix`/`sameBudgetCover`/rare `coveredDrop` or
      `budgetNonworseCover` tradeoffs where scan stayed no worse on the main
      row/term/size budgets.
    - final size-universe POSIX accumulator contract:
      added
      `strong_deferred_original_sizeNregex_memo_POSIX_accumulator_budget_contract`
      in `FBound.thy`. This is the current one-stop final interface for the
      `sizeNregex N` route: it includes POSIX correctness/flatness, legacy
      preservation, the row-to-memo gate, the raw/annotated row bridge, the
      span-state probe bounds, and the Antimirov-facing final raw accumulator
      budgets
      `length`, `card (set ...)`, `rlinear_termss`, and `rsizes`, all bounded
      by the same `B`. This does not change the existing
      `strong_deferred_original_sizeNregex_memo_cubic_interface`; it is a
      companion theorem with the extra accumulator metrics exposed.
      `isabelle build -D . Posix` passed after adding it.
    - secondary-tradeoff check after the final contract:
      targeted `maxShapeDagOnly` search on seed `20260782`, depth `7`, input
      length `16`, checked `3000` cases and found no pure max-shape-only
      witness. The top observations were still `absorbedSuffix`: scan merged
      rows and improved total rows/size while a single max row/shape metric
      increased by one constructor. This argues against a simple max-size
      guard on `rsimpStrong_prune_pair(_raw)`, because that guard would throw
      away the main Antimirov-budget improvement.
      A fresh composite `nonworse` finder on seeds `20260786..20260787`,
      depth `8`, input length `20`, checked `8000` cases and again found no
      nonworse witness; per-seed summaries had `proofBudgetWorse=0`,
      `budgetWorse=0`, `scanCoverageGap=0`, `normCoverageGap=0`,
      `primary=0`, and `unexplained=0`.
    - active-suffix POSIX accumulator contract:
      added
      `strong_deferred_original_raw_row_norm_active_suffix_memo_POSIX_accumulator_budget_contract`
      in `FBound.thy`. This is the active-suffix analogue of the final
      `sizeNregex` POSIX accumulator theorem: it preserves the old memo/POSIX
      interface shape as a companion theorem while exposing the raw
      accumulator budgets `length`, `card (set ...)`, `rlinear_termss`, and
      `rsizes` under the same finite-universe `B`. This keeps the actual
      scan/prune path aligned with the Antimirov-style row/linear-term
      metrics, not just the final closed size universe. `isabelle build -D .
      Posix` passed after adding it.
    - post-active-suffix-contract fuzz:
      composite `nonworse` finder on seeds `20260788..20260789`, depth `9`,
      input length `22`, checked `10000` random cases and found no nonworse
      witness. Per-seed summaries had `proofBudgetWorse=0`, `budgetWorse=0`,
      `scanCoverageGap=0`, `normCoverageGap=0`, `primary=0`, and
      `unexplained=0`. The strongest secondary examples were again
      `absorbedSuffix`: scan reduced rows and total size, while a single
      max/DAG/shape metric could grow locally.
    - sizeNregex active-suffix POSIX accumulator route:
      added
      `strong_deferred_original_sizeNregex_active_suffix_memo_POSIX_accumulator_budget_contract`
      in `FBound.thy`. It has the same final POSIX/legacy/bridge/span-state
      and raw accumulator-budget conclusions as the existing
      `strong_deferred_original_sizeNregex_memo_POSIX_accumulator_budget_contract`,
      but the proof explicitly instantiates the active-suffix closure route
      using `raw_shared_prune_active_suffix_closure_sizeNregex_subset`.
      This makes the final size-bounded universe scaffold line up with the
      actual active-suffix scan/prune path rather than only the closed-route
      wrapper. `isabelle build -D . Posix` passed after adding it.
    - post-sizeNregex-active-suffix fuzz:
      composite `nonworse` finder on seeds `20260790..20260791`, depth `9`,
      input length `22`, checked `10000` random cases and found no nonworse
      witness. Per-seed summaries again had `proofBudgetWorse=0`,
      `budgetWorse=0`, `scanCoverageGap=0`, `normCoverageGap=0`,
      `primary=0`, and `unexplained=0`; the strongest secondary examples
      remained `absorbedSuffix`.
    - exact active-suffix sizeNregex budget:
      added
      `strong_deferred_original_sizeNregex_active_suffix_memo_POSIX_accumulator_exact_budget_contract`
      in `FBound.thy`. It removes the explicit `card_bound`/`cubic`
      parameters from the active-suffix `sizeNregex` POSIX accumulator route
      by instantiating the natural budget
      `card (sizeNregex N) * N`. The remaining assumptions are exactly the
      regex legacy/init-size assumptions plus the `rpder_norm_list` closure
      assumption for `sizeNregex N`; the conclusion still exposes POSIX
      correctness/flatness, the memo gate, the raw/annotated row bridge,
      span-state probe bounds, and the final raw accumulator budgets.
      `isabelle build -D . Posix` passed after adding it.
    - post-exact-budget fuzz and shrink:
      composite `nonworse` finder on seeds `20260792..20260793`, depth `9`,
      input length `22`, checked `10000` random cases and found no scan-worse
      witness. Seed `20260792` had one harmless `normCoverageGap`, so the
      targeted shrinker reduced it to
      `STAR(SEQ(ALT(SEQ(ALT(CH(b),ONE),ALT(CH(a),CH(b))),ONE),ALT(CH(a),CH(b))))`
      on input `b`. Scan is strictly smaller on the main budgets
      (`rows 1/3`, `terms 3/5`, `deepTerms 6/7`, `size 23/54`) and has no
      scan-only row; the Antimirov-only extra is classified as
      `absorbedSuffix`.
    - least-owner DAG accumulator bridge:
      added
      `rpders_strong1_rows_raw_intern_least_owner_dag_budget_boundI`,
      `strong_deferred_row_gate_least_owner_dag_accumulator_POSIX_contract`,
      and
      `strong_deferred_row_gate_norm_active_suffix_universe_accumulator_POSIX_contract`
      in `FBound.thy`. These expose the final raw accumulator metrics
      `length`, `card (set ...)`, `rlinear_termss`, and `rsizes` directly
      through the smaller least-owner active-suffix DAG budget
      `card (strong_deferred_strong_rows_raw_least_owner_dag r s) * M`, and
      then through any active-suffix universe `U` whose cardinality/member-size
      bounds are known. This is the closest current Isabelle scaffold to the
      Antimirov linear-form accounting.
    - scan-vs-Antimirov fixed-point refinement:
      the Scala row comparator now uses a structural-safe scan step. Each
      step computes the Antimirov-style linear rows as a fallback, adopts
      pruned/absorbed rows only when total tree/DAG/shape-DAG and max
      tree/DAG/shape-DAG budgets do not increase, canonicalizes harmless bit
      placement before annotated-DAG counting, and suppresses already covered
      budget-nonworse DAG-only noise. The motivating shrinks were
      `STAR(ALT(CH(b),SEQ(CH(b),ALT(CH(a),CH(b)))))` on input `b`
      (`maxOnly` from absorbed suffix, now gone), and
      `STAR(SEQ(ALT(CH(a),STAR(CH(a))),ALT(NTIMES(ONE,0),CH(a))))`
      on input `a` (`shapeDagOnly` from absorbed suffix, now gone).
    - latest fixed-point fuzz:
      after the structural-safe scan refinement, targeted `dagOnly` on seed
      `20260794` and targeted `dagOnly` on seed `20260796` each checked
      `5000` random cases with no witness and `observations=0`. Composite
      `nonworse` fuzz on seeds `20260794..20260795` checked `10000` random
      cases with all hard and soft row-diff counters at `0`; composite
      `nonworse` fuzz on seeds `20260796..20260799` checked another `20000`
      random cases with `observations=0` for every seed. No
      `proofBudgetWorse`, `budgetWorse`, `scanCoverageGap`, primary, or
      unexplained case is currently known.
    - proof-facing choice contract:
      added `rpder_strong_rows_clean_terms_choice` in `GeneralRegexBound.thy`,
      a one-step relation that is either the clean Antimirov-style fallback
      rows or the safe term-absorbed/pruned scan rows. The new contracts
      `rpder_strong_rows_clean_terms_choice_generated_budget_contract` and
      `rpder_strong_rows_clean_terms_choice_single_cubic_budget_contract`
      expose the same correctness, `length`, `card (set ...)`,
      `rlinear_termss`, and `rsizes` budgets as the generated
      `rpder_norm_list` linear-form rows, and hence the same
      `2 * (rsize r + 3)^3` single-step cubic bound. `FBound.thy` also has
      `rpder_strong_rows_clean_terms_choice_rerase_intern_single_cubic_budget_contract`
      for the POSIX `rerase (intern r)` surface with `rxsize`.
    - deeper fixed-point confirmation:
      depth-10/input-24 random row-diff fuzz found no new actionable witness.
      Seed `20260800` checked `2000` cases with `FIND_MODE=any`; seeds
      `20260801..20260804` checked another `8000` cases, all with
      `observations=0`. After the choice-contract Isabelle edits,
      `isabelle build -D . Posix` passed, and full
      `agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -NoCertificate
      -Role admin -SessionTimeoutSeconds 240` passed: known row-diff
      regressions `9` cases `observations=0`, exhaustive depth-2/input-3
      row comparison `84300` pairs `observations=0`, plus `Posix` and
      `BackRefPilot`.
    - proof write-up:
      added `CUBIC_BOUND_PROOF_WRITEUP_2026_06_06.md`, which states the
      checked one-step cubic theorem, the POSIX lift, the finite-universe
      accumulator main interface, the exact `sizeNregex` contract, and the
      remaining universe-cardinality obligation needed for a standalone
      all-input cubic theorem.
    - pure Antimirov/factored transition file:
      added `AntimirovFactoredTransition.thy` and included it in `ROOT`.
      The file defines only the scan-free factored row transition
      `afactored_step`, its multi-step driver `afactored_steps`, and the
      singleton driver `afactored1`. It proves language correctness,
      distinctness, the induction principle
      `afactored_steps_subterm_closed_universe_subsetI`, finite-universe
      accumulator budgets, and the conditional cubic contract
      `afactored1_cubic_universe_contractI`. This separates the Antimirov
      proof object from `rsimpStrong_prune_rows`; the remaining target is now
      exactly the root-derived universe closure assumption in that contract.
    - product-term split closure:
      the same file now defines `aseq_terms` / `aseq_termss`, which split
      top-level alternatives and `RSEQ` products into Antimirov-style terms.
      Checked lemmas include `rpder_norm_list_aseq_terms_subsetI`,
      `afactored_steps_aseq_terms_closed_legacy_subsetI`, and
      `afactored1_aseq_terms_frontier_universe_contract`. The new
      unconditional row-frontier theorem proves that for arbitrary many pure
      Antimirov factored rows from a legacy root `r`, every product-split term
      is in `partial_derivative_frontier_universe r`; the split-term set has
      cardinality at most `(rsize r + 2)^2`, and every split term has size at
      most `Suc (rsize r + rsize r)`. The key closure lemma is
      `partial_derivative_frontier_universe_ntimes_predecessor`, which handles
      the counted-repeat predecessor step `RNTIMES q (Suc n) -> RNTIMES q n`.
      The lemma
      `nested_star_row_not_cubic_but_terms_are_cubic` records the important
      distinction: a whole row can leave the coarse cubic universe while its
      split terms still remain inside the bounded frontier universe. The
      older split-atom normal-derivative endpoint is also checked:
      `anorm_der_eq_rders_pder_norm` and
      `rders_pder_norm_aseq_terms_frontier_universe_contract` prove that after
      computing the ordinary `rders_pder_norm r s` regex and then splitting it,
      all split terms are still in the original frontier universe with the same
      quadratic/linear budgets.  This is auxiliary only. The corrected
      whole-residual normal-frontier endpoint is
      `rfrontier_rders_pder_norm_subset_apder_frontier`, and the remaining
      bridge is to budget that residual frontier and connect it to the concrete
      raw rows produced
      by the strong scanner/pruner, controlling product chains/owners well
      enough to discharge the existing `U`-based accumulator interfaces.
- Meaning:
  - The current row-diff loop has reached a fixed point for the tested metrics:
    no scan/prune row-count, linear-term-count, total-size, or coverage loss
    is currently known against Antimirov strong linear forms.
  - The only strict secondary differences found are explained tradeoffs where
    scan uses a smaller row set/total size and no more linear terms, at the
    cost of a single row growing by one constructor.
  - The Isabelle route now has generic relation scaffolding for both classes:
    absorbed-suffix replacement and covered-row deletion both preserve language,
    preserve legacy, and do not increase `rsizes`, so the one-step cubic count
    scaffold inherits through them. The new term-safe absorbed-suffix relation
    also proves that the accumulator-term count does not increase when the
    absorbed suffix contributes at least one linear term, matching the Scala
    row-diff metric used to compare against Antimirov linear forms.

## Cubic Bound Research: wide row pruning scaffold (2026-06-07)

- Process hygiene:
  - Added a standing rule in `AGENTS.md`: long-running proof/search/fuzz
    commands must use explicit timeouts and then check for leftover
    `python`, `poly`, `polyml`, `isabelle`, and Java worker processes.
  - After each bounded Isabelle build in this slice, `tasklist` checks for
    `python.exe`, `poly.exe`, `polyml.exe`, and `java.exe` reported no matching
    residual tasks.
- Checked obstruction:
  - Added `deep_fixed_rows_do_not_force_dlform_disjoint`, showing that
    `distinct + rsimpDeep_fuel_fixed + nonalt + nonzero` is not enough to imply
    `row_dlformss_disjoint`. This confirms that the second-stage proof really
    needs an explicit canonical/prune argument, not only a fixed-point
    simplifier invariant.
- Checked deep-row invariants:
  - Added `rsimpDeep_fuel_fixed_rpder_deep_list`,
    `rsimpDeep_fuel_fixed_rpder_deep_rows`,
    `rsimpDeep_fuel_fixed_rpders_deep_rows`, and
    `rsimpDeep_fuel_fixed_rpders_deep1_rows_nonempty`. Nonempty deep-row
    derivative states now expose rows that are deep-fuel fixed, non-alt, and
    nonzero.
- New proof-local wide-prune scaffold:
  - Added `row_cover_prefixes`, which treats an earlier row with suffix `k` as
    a set of prefixes covering later rows with the same suffix. It includes the
    important case `earlier = k`, represented by prefix `RONE`, and the
    singleton-prefix case `RSEQ p k`.
  - Added `rsimpWide_prune_pair_raw`,
    `rsimpWide_prune_against_rows_raw`, `rsimpWide_prune_rows_acc_raw`, and
    `rsimpWide_prune_rows_raw`.
  - Design choice: grouped later rows `RSEQ (RALTS rrs) k` still rebuild with
    `rsimp7_SEQ_atom`, matching the existing `row_dlforms` definition. Singleton
    later rows do not rebuild; they become `RZERO` if covered, otherwise remain
    `RSEQ p k`. This avoids letting accumulator history create fresh singleton
    row shapes.
- Checked wide-prune facts:
  - Language preservation:
    `RL_rsimpWide_prune_pair_raw_with_earlier`,
    `RL_rsimpWide_prune_against_rows_raw`, and
    `RL_rsimpWide_prune_rows_raw`.
  - Length preservation:
    `length_rsimpWide_prune_rows_acc_raw` and
    `length_rsimpWide_prune_rows_raw`.
  - Normal-form preservation:
    `rtail_nf_rsimpWide_prune_pair_raw`,
    `rtail_nf_rsimpWide_prune_against_rows_raw`,
    `rtail_nf_rsimpWide_prune_rows_acc_raw`, and
    `rtail_nf_rsimpWide_prune_rows_raw`.
  - Split-term monotonicity:
    `row_dlforms_rsimpWide_prune_pair_raw_subset_later_rtail_nf`,
    `row_dlforms_rsimpWide_prune_against_rows_raw_subset_later_rtail_nf`,
    `row_dlformss_rsimpWide_prune_rows_acc_raw_subset_rtail_nf`, and
    `row_dlformss_rsimpWide_prune_rows_raw_subset_rtail_nf`.
- Current meaning:
  - The proof now has a checked candidate for a safer scanner/pruner layer:
    it preserves row language and provably does not increase the
    `row_dlforms` vocabulary under `rtail_nf`.
  - This is not yet the final cubic theorem. The remaining second-stage
    obligation is to connect this monotone pruning scaffold to a genuine
    canonical/disjoint row invariant, or to replace the production
    `rsimpStrong_prune_rows_raw` path with a checked fixed-point/canonical pass
    that proves `row_dlformss_disjoint`.

## Cubic Bound Research: canonical dlform projection (2026-06-07)

- New checked list interface:
  - Added `row_dlforms_list`, a constructive list version of `row_dlforms`,
    with `set_row_dlforms_list`.
  - Added `row_dlformss_list`, with `set_row_dlformss_list`.
  - Proved language preservation:
    `RL_row_dlforms_UN`, `RL_RALTS_row_dlforms_list`, and
    `RL_RALTS_row_dlformss_list`.  Thus expanding rows into their deep linear
    forms preserves the represented row language.
- New canonical projection:
  - Added `row_dlform_canonical_rows rs =
    rdistinct (row_dlformss_list rs) {}`.
  - Checked `distinct_row_dlform_canonical_rows`,
    `set_row_dlform_canonical_rows`, and
    `RL_RALTS_row_dlform_canonical_rows`.
- Atomicity and disjointness:
  - Proved `row_dlforms_member_atomic_rtail_nf`:
    `rtail_nf r` and `x in row_dlforms r` imply `row_dlforms x = {x}`.
  - Lifted this to row lists with
    `row_dlforms_atomic_row_dlformss_rtail_nf`.
  - Proved `row_dlformss_atomic_eq_set` and
    `row_dlformss_disjoint_atomic_distinct`.
  - Therefore `row_dlformss_disjoint_row_dlform_canonical_rows`:
    if all source rows are `rtail_nf`, the canonical projection is
    row-dlform disjoint.
  - Also proved `row_dlformss_row_dlform_canonical_rows_eq`, so the canonical
    projection preserves exactly the same dlform vocabulary under `rtail_nf`.
- Cubic package theorem:
  - Added `rsizes_row_dlform_canonical_rows_cubic`:
    if all source rows are `rtail_nf` and their `row_dlformss` are included in
    `partial_derivative_frontier_universe root`, then
    `rsizes (row_dlform_canonical_rows rows) <= 6 * (rsize root + 2)^3`.
  - Added `row_dlform_canonical_rows_cubic_contractI`, which packages the
    same assumptions into four checked conclusions: language equivalence,
    `row_dlformss_disjoint`, exact `row_dlformss` preservation, and the cubic
    `rsizes` bound.
- Strong-row normal-form bridge:
  - Added `rtail_nf_rpder_strong_rows_raw`.
  - Added `rtail_nf_rpders_strong_rows_raw`, conditional on the initial row
    list being `rtail_nf`.
  - Added `rtail_nf_rpders_strong1_rows_raw`, conditional on the root itself
    being `rtail_nf`.
  - Added the important nonempty-input variant
    `rtail_nf_rpders_strong1_rows_raw_nonempty`, which is unconditional because
    the first strong step normalizes rows with `rsimpStrong_raw`.
  - Added `RL_RALTS_row_dlform_canonical_rpders_strong1_rows_raw`: wrapping the
    strong raw rows in the canonical dlform projection preserves the derivative
    language `Ders s (RL r)` for legacy roots.
- Current meaning:
  - This formalizes the user's proposed second phase as a proof-level
    canonical target: first show derivatives split into the bounded frontier
    terms, then canonicalize by expanding to dlforms and removing duplicates.
  - It still does not say the production `rsimpStrong` regex simplifier
    computes this canonical projection. The remaining bridge is either to
    connect production rows to this projection, or to introduce a checked
    simplifier/canonical pass that implements it.
- Checked failed shortcut:
  - Added `atomic_rtail_nf_aseq_terms_payment_false`.  Even an atomic
    `rtail_nf` row can hide repeated alternatives inside its right continuation,
    so `aseq_terms` may be too small to pay for the whole row's size.  Therefore
    the canonical cubic proof cannot simply replace direct `row_dlformss`
    universe inclusion with per-dlform `aseq_terms` inclusion unless a stronger
    continuation canonicalization invariant is added.

## Cubic Bound Research: parameterized canonical-row interface (2026-06-07)

- Generalized the canonical projection budget away from the old fixed frontier:
  - `rsizes_rows_canonical_dlforms_rsize_set_boundI` proves that any disjoint,
    live, paid row list whose deep linear forms are contained in a finite
    universe `U` satisfies `rsizes rows <= 3 * rsize_set U`.
  - `rsizes_row_dlform_canonical_rows_rsize_set_boundI` specializes this to the
    canonical projection: if source rows are `rtail_nf` and
    `row_dlformss rows subset U`, then
    `rsizes (row_dlform_canonical_rows rows) <= 3 * rsize_set U`.
  - `rsizes_row_dlform_canonical_rows_self_bound` is the self-paying form:
    `rsizes (row_dlform_canonical_rows rows) <=
    3 * rsize_set (row_dlformss rows)` under `rtail_nf`.
- Connected this parameterized interface to production strong raw rows:
  - `row_dlform_canonical_rpders_strong1_rows_raw_universe_contractI` packages
    language preservation, disjointness, exact `row_dlformss` preservation, and
    the `3 * rsize_set U` bound for
    `row_dlform_canonical_rows (rpders_strong1_rows_raw r s)`, conditional on
    `rtail_nf` rows and `row_dlformss ... subset U`.
  - `row_dlform_canonical_rpders_strong1_rows_raw_nonempty_universe_contractI`
    removes the explicit `rtail_nf` assumption for nonempty inputs using
    `rtail_nf_rpders_strong1_rows_raw_nonempty`.
  - `row_dlform_canonical_rpders_strong1_rows_raw_nonempty_self_contract`
    gives the unconditional nonempty self-paying contract for legacy roots.
  - `Ders_snoc` supplies the right-append derivative identity
    `Ders (s @ [c]) A = Der c (Ders s A)`.
  - `row_dlform_canonical_rpder_strong_rows_raw_self_contract` gives the
    one-step strong raw-row canonical projection contract for an arbitrary
    legacy row list, with exact language `Der c (RLS (set rows))` and
    self budget `3 * rsize_set (row_dlformss (rpder_strong_rows_raw c rows))`.
  - `row_dlform_canonical_rpder_strong_rows_raw_afactored1_self_contract`
    specializes the previous theorem to the Antimirov front `afactored1 r s`,
    yielding exact language `Ders (s @ [c]) (RL r)`, disjoint canonical
    dlforms, exact `row_dlformss` preservation, and the same self budget.
  - `same_dlfront_rows_row_dlform_canonical_rows` proves that the canonical
    dlform projection itself preserves the same-front invariant whenever the
    source rows are `rtail_nf`.
  - `row_dlform_canonical_rpders_strong1_rows_raw_nonempty_same_dlfront_self_contractI`
    packages the nonempty strong-row path with the intended responsibility
    split: assuming only a one-step same-front closure condition for
    `rsimpStrong_raw`, the canonical projection denotes `Ders (c # s) (RL r)`,
    remains in the same deep front `(c # s)`, is dlform-disjoint, preserves the
    raw rows' exact `row_dlformss`, and self-pays by `3 * rsize_set` of that
    exact dlform vocabulary.
  - `row_dlform_canonical_rpder_strong_rows_raw_generated_dlforms_contract`
    strengthens the one-step payment interface: the canonical projection over
    `rpder_strong_rows_raw c rows` is paid not just by its own dlforms but by
    the explicit generated universe
    `row_dlformss (concat (map (rpder_strong_list_raw c) rows))`.
  - `row_dlform_canonical_rpder_strong_rows_raw_afactored1_generated_dlforms_contract`
    specializes that generated-universe payment to the Antimirov front
    `afactored1 r s`, with exact language `Ders (s @ [c]) (RL r)`.
- Meaning:
  - The canonical/no-duplicate side is now isolated as a checked reusable
    theorem.  The remaining mathematical obligation is to construct the right
    original-regex-owned same-front / later-shared universe `U` and prove a
    cubic `rsize_set U` bound plus `row_dlformss` inclusion for the actual
    strong scan/prune rows.
  - After the latest bridge, the proof split is sharper: canonical projection
    preserves same-front, so the remaining hard step is not deduplication but
    the relaxed same-front universe/closure theorem for the actual strong
    simplifier outputs.
  - The new generated-dlform contract gives a concrete intermediate target for
    the next proof step: bound the generated dlform vocabulary by a cubic
    original-regex-owned universe, rather than paying only by the already
    cleaned rows.
  - The latest checked refinement introduces
    `afactored1_strong_dlform_universe`, defined as the
    `rsimpStrong_dlform_closure` of the one-step Antimirov generated normal
    rows
    `set (concat (map (rpder_norm_list c) (afactored1 r s)))`.
    New checked lemmas:
    `row_dlformss_concat_rpder_strong_list_raw_subset_dlform_closure`,
    `row_dlformss_concat_rpder_strong_list_raw_afactored1_subset_universe`,
    `afactored1_strong_dlform_universe_aseq_subset`, and
    `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_contract`.
    The packaged contract pays the canonicalized one-step strong rows by
    `3 * rsize_set (afactored1_strong_dlform_universe r s c)`, while also
    recording that every deep form in this universe has `aseq_terms` contained
    in `strong_simp_frontier_aseq_universe r`.
    The follow-on skeleton
    `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_cubic_contractI`
    proves that a future
    `rsize_set (afactored1_strong_dlform_universe r s c) <=
    2 * (rsize r + 3)^3` lemma immediately yields the one-step canonical
    strong-row size bound `6 * (rsize r + 3)^3`.
  - This makes the remaining second-stage obligation sharper:
    prove a cubic `rsize_set` bound for
    `afactored1_strong_dlform_universe r s c`, or replace it by an even
    smaller same-front/later-shared universe with the same inclusion property.
  - New checked size-payment refinement:
    `rsize_set_rsimpStrong_dlform_closure_le_sum` and
    `rsize_set_afactored1_strong_dlform_universe_le_sum` show that the
    simplifier-closure universe can be paid by the sum of
    `rsize_set (row_dlforms (rsimpStrong_raw p))` over the generated normal
    rows `p`.  The wrapper
    `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_sum_cubic_contractI`
    proves that the one-step canonical strong-row cubic bound follows from
    this exact sum being at most `2 * (rsize r + 3)^3`.
  - New checked executable-cost refinement:
    `row_dlforms_list_size r = sum_list (map rsize (row_dlforms_list r))`
    records the full list-expanded cost of opening a row into dlforms, before
    duplicate elimination.  The lemmas
    `rsize_set_row_dlforms_le_row_dlforms_list_size`,
    `sum_rsize_set_row_dlforms_rsimpStrong_raw_le_list_size`, and
    `rsize_set_afactored1_strong_dlform_universe_le_list_size` prove that this
    executable cost pays the previous set-sum obligation.  The wrapper
    `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_list_cubic_contractI`
    now states the next proof target in the most concrete form:
    if the list-expanded cost over generated normal rows is at most
    `2 * (rsize r + 3)^3`, then the same one-step canonical strong-row cubic
    conclusion follows.
    This target is also named by
    `afactored1_strong_dlform_list_cost`; the checked wrapper
    `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_named_list_cubic_contractI`
    says that
    `afactored1_strong_dlform_list_cost r s c <= 2 * (rsize r + 3)^3`
    is sufficient.
    The supporting simp equations for `row_dlforms_list_size` expose the exact
    recursion through `RZERO`, `RALTS`, and `RSEQ (RALTS ps) k`, so future
    same-front accounting can work directly over the suffix-copying cases.
  - New checked obstruction:
    `row_dlforms_suffix_copy_rsize_set_not_paid_by_row_size` shows why the
    next step cannot simply claim
    `rsize_set (row_dlforms row) <= rsize row`: splitting an
    `RSEQ (RALTS [...]) k` copies the suffix into multiple dlforms.  The
    remaining proof therefore has to use the user's same-front/later-shared
    accounting, not a naive per-row-size payment.
  - This is still not the final cubic theorem for production `rsimpStrong`.
- Verification:
  - Full `Posix` Isabelle build passed after the new lemmas, including the
    `afactored1_strong_dlform_universe` contract, the new sum-cubic wrapper,
    and the list-expanded cost wrappers/simp equations.
  - Post-build residual process checks reported no `python.exe`, `poly.exe`,
    `polyml.exe`, or `java.exe` tasks.

## Cubic Route Checked Update: Same-Front Strong Closure (2026-06-07)

- Process hygiene was tightened in `AGENTS.md`: use stable proof wrappers and
  bounded commands, then check for leftover proof/search/fuzz workers.
- Terminology correction:
  - The split-atom theorem is not the first-stage theorem requested by the
    user.  The corrected first-stage theorem is
    `rfrontier_rders_pder_norm_subset_apder_frontier`: compute the normal
    derivative first, then split only by the normal Antimirov frontier
    `rfrontier`; the resulting whole residual frontier is contained in
    `apder_frontier r`, assuming `apder_nf r`.
  - The old facts based on `row_dlforms`/`aseq_terms` remain useful auxiliary
    split-atom inclusions, but they must not be used to claim that normal
    Antimirov residuals have been bounded.
  - The still-missing `U` is a second-stage row/dlform payment universe,
    written here as `U_row`, whose job is to contain whole `row_dlformss`
    combinations for the concrete strong scan/prune or dcanon rows and to have
    a cubic size/cardinality bound.  A separate polynomial budget for
    `apder_frontier r` or an equivalent path-frontier universe is the next
    natural first-stage budget task.
- Added an explicit front-term block:
  `derivative_front_terms r s = aseq_termss (afactored1 r s)`.
  This names the user's "same predecessor/front derivative string" term block.
- Checked normal-derivative bridge:
  `row_dlforms_rders_pder_norm_same_frontier_contract` proves that after
  computing `rders_pder_norm r s` and only then opening/splitting a deep form
  `x`, the split atoms are not merely in the global original universe; they
  are contained in the concrete front block `derivative_front_terms r s`, and
  that block is contained in `partial_derivative_frontier_universe r`.
- Added cleanup support for the front block:
  `aseq_termss_rdistinct_empty_eq`,
  `aseq_termss_rflts_insert_zero_superset`,
  `aseq_termss_generated_subset_afactored_step_insert_zero`, and
  `derivative_front_terms_snoc_generated_insert_zero`.  These record that the
  pure Antimirov row cleanup can only lose split atom `RZERO`.
- Added the strong same-front block:
  `strong_derivative_front_terms r s =
   rsimpStrong_aseq_closure (insert RZERO (derivative_front_terms r s))`.
  The inserted `RZERO` is needed because `rsimpStrong_raw` can create/drop dead
  branches while simplifying inside a front.
- Checked same-front strong-generation bridges:
  `row_dlforms_rsimpStrong_raw_rpder_norm_list_afactored1_same_strong_front`,
  `row_dlformss_concat_rpder_strong_list_raw_afactored1_same_strong_front`,
  `row_dlformss_rpder_strong_rows_raw_afactored1_same_strong_front`, and
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_same_strong_front`.
  These prove that generated, cleaned, and canonicalized one-step strong rows
  do not mix derivative fronts at the split-atom level:

  ```text
  x in row_dlformss (rpder_strong_rows_raw c (afactored1 r s))
  ==> aseq_terms x subset strong_derivative_front_terms r (s @ [c])
  ```

- Also checked
  `strong_derivative_front_terms_subset_strong_simp_frontier`, so for legacy
  roots each same-front strong block remains inside the old global
  `strong_simp_frontier_aseq_universe r`.  The proof has therefore strengthened
  the inclusion invariant from "global universe" to "current-front strong
  closure".
- Added per-front budget wrappers:
  `card_strong_derivative_front_terms_cubic`,
  `rsize_set_strong_derivative_front_terms_cubic`,
  `strong_derivative_front_terms_member_size_linear`, and
  `row_dlformss_rpder_strong_rows_raw_afactored1_same_strong_budget_contract`.
  Thus each current strong-front block has the same checked cubic card and
  `rsize_set` budgets as the global strong frontier, while preserving the
  front-indexed/no-mixed-front statement for actual strong rows.
- Lifted the bridge from individual deep forms to the canonical row list:
  `same_strong_aseq_front_rows`,
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_same_strong_front_rows`,
  and
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_same_strong_budget_contract`.
  The canonical rows for one actual strong step now carry a checked list-level
  invariant:

  ```text
  aseq_termss (row_dlform_canonical_rows
    (rpder_strong_rows_raw c (afactored1 r s)))
    subset strong_derivative_front_terms r (s @ [c])
  ```

  plus cubic budgets for that same front block.
- Added the front-specific split-payment conditional theorem:
  `rsizes_aseq_terms_paid_strong_derivative_front_cubic` and the packaged
  one-step contract
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_same_strong_aseq_paid_cubic_contractI`.
  This says that if the canonical rows for
  `rpder_strong_rows_raw c (afactored1 r s)` satisfy the second-stage
  disjoint/live/paid obligations inside their current
  `strong_derivative_front_terms r (s @ [c])` block, then their `rsizes` are
  bounded by `6 * (rsize r + 2)^3` while preserving the derivative language and
  exact `row_dlformss`.
- Added checked boundary lemma `rtail_nf_does_not_atomize_row_lforms`.
  Even an `rtail_nf` row of the form `RSEQ (RALTS [a,b]) c` opens under
  `row_lforms` to rows such as `RSEQ a c`, so `row_lforms row <> {row}`.
  Therefore the lform canonical-row contracts cannot drop their explicit
  atomic premise.  The second-stage proof should keep using the checked
  `row_dlform_canonical_rows` projection, or introduce a stronger same-front
  representation that proves the needed atomic/no-redundant payment property.
- Added a multi-step deep-canonical strong scaffold for
  `rpders_strong_dcanon_rows_raw`.  New checked lemmas:
  `legacy_rpders_strong_dcanon_rows_raw`,
  `row_dlformss_disjoint_rpders_strong_dcanon_rows_raw_nonempty`,
  `row_dlforms_live_paid_rpders_strong_dcanon_rows_raw_nonempty`,
  `rsizes_rpders_strong_dcanon_rows_raw_nonempty_rsize_set_boundI`, and
  `rpders_strong_dcanon_rows_raw_nonempty_rsize_set_budgetsI`.
  The singleton-root packaged interfaces
  `rpders_strong_dcanon1_rows_raw_nonempty_universe_contractI` and
  `rpders_strong_dcanon1_rows_raw_nonempty_universe_cubic_contractI` add
  derivative-language correctness and turn the finite `U` premise into the
  final nonempty dcanon row budgets.
  The generic bridge `rsize_set_le_card_times_bound` /
  `rsize_set_le_card_member_budgetI`, plus
  `rpders_strong_dcanon1_rows_raw_nonempty_card_member_cubic_contractI`, lets
  active-suffix-style `card U` and member-size bounds feed the same dcanon
  cubic conclusion without first proving a bespoke `rsize_set U` theorem.
  For any nonempty input, the dcanon transition output is already
  `row_dlformss_disjoint`, live, and paid by its own deep linear forms; if its
  `row_dlformss` are included in any finite universe `U`, all four row budgets
  are bounded by `3 * rsize_set U`.  This isolates the remaining obligation to
  constructing a cubic original-regex-owned `U`.
- Added a checked list-cost payment wrapper for the current one-step
  `U_row` candidate `afactored1_strong_dlform_universe`:
  `row_dlforms_member_size_le_list_size`,
  `rsimpStrong_dlform_closure_member_list_size_bound`,
  `afactored1_strong_dlform_universe_member_size_le_list_cost`, and
  `afactored1_strong_dlform_universe_list_cost_budget`.  Thus the same named
  cost `afactored1_strong_dlform_list_cost r s c` pays both
  `rsize_set (afactored1_strong_dlform_universe r s c)` and every member size
  of that universe.  This is a verified scaffold for the second-stage
  accounting target; it is not yet a proof that the named list cost is cubic.
- Added a checked card/generated-size payment interface for the same
  `U_row` candidate:
  `rsize_set_afactored1_strong_dlform_universe_card_generated_boundI`,
  `rsize_set_afactored1_strong_dlform_universe_card_generated_cubicI`,
  `rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_card_generated_cubic_contractI`,
  and
  `rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_card_generated_cubic_budgetsI`.
  This packages the next target exactly: prove
  `card U_row <= C`,
  `rsizes (concat (map (rpder_norm_list c) (afactored1 r s))) <= M`, and
  `C * M <= 2 * (rsize r + 3)^3`; then the one-step dcanon transition gets
  derivative-language correctness, exact `row_dlformss` preservation,
  disjoint/live/paid rows, and all four cubic row budgets.  This is the
  current clean second-stage interface after the completed first-stage
  `U_term` theorem.
- Attempted but did not keep a shrink of the `aseq_terms_live` assumption in
  the existing split-payment contract.  The naive proof route
  `row_dlforms_live -> aseq_terms_live` is too broad for the generalized
  datatype and a later `legacy + rtail_nf` variant must be split into small
  constructor lemmas rather than discharged by broad `fastforce`.
- Remaining theorem gap: this still does not prove the final regex-size cubic
  bound.  The next obligation is the user's second-stage canonical/payment
  side: show that the simplifier/canonical representation does not keep
  redundant combinations inside one allowed same-front block, or define a
  checked canonical pass with that property.  Existing obstructions still show
  that plain `aseq_terms` payment is too fine for row size.
- Verification: bounded `Posix` Isabelle builds passed after the new front-block
  and strong-front lemmas, and after the
  `rtail_nf_does_not_atomize_row_lforms` boundary lemma; another bounded build
  passed after the nonempty dcanon budget scaffold and packaged universe
  contracts; another bounded build passed after the card/member-size bridge.
  Another bounded build passed after the list-cost member-size/budget wrapper,
  and another passed after the card/generated-size dcanon wrappers.
  During the discarded live-assumption shrink attempt, one timed-out build left
  two PolyML proof workers from this run, which were terminated by PID.  The
  final bounded build passed and the final proof-worker check found no
  matching residual processes.
- Added the corrected deep same-front Antimirov frontier object
  `apder_dlfrontier`:

  ```text
  apder_dlfrontier r = UNION q in apder_rows r. row_dlforms q
  ```

  Checked lemmas:
  `finite_apder_dlfrontier`,
  `adlform_front_subset_apder_dlfrontier`,
  `row_dlforms_rders_pder_norm_subset_apder_dlfrontier`, and
  `rsize_set_row_dlforms_rders_pder_norm_le_apder_dlfrontier`.
  This is the precise first-stage version of the user's "same derivative
  front" plan: compute the normal Antimirov derivative first, then fully open
  only grouped rows of the form `RSEQ (RALTS ps) k` along that same front.
  It does not replace the whole-residual `rfrontier` theorem, and it does not
  use `aseq_terms` as the counted row vocabulary.  The new checked statement is:

  ```text
  row_dlforms (rders_pder_norm r s) subset apder_dlfrontier r
  ```

  under `apder_nf r`.
- Current next proof target after `apder_dlfrontier`: prove a closure/budget
  lemma for this same-front universe, ideally
  `apder_dlfrontier r subset partial_derivative_frontier_universe r` or a
  direct `rsize_set (apder_dlfrontier r)` cubic bound.  The key subgoal is:
  if `q` is a front-owned `rtail_nf` row, then `row_dlforms q` stays in the
  original-root front universe.  This requires continuation closure; do not
  shortcut it by counting `aseq_terms`.
- Worker hygiene checkpoint after this update: bounded `Posix` build passed,
  and `scripts\codex-proof-workers.ps1 -Action Check` reported no residual
  proof-worker processes.

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

## 2026-06-08 Normal Antimirov Checkpoint

- Added `AntimirovNormalFrontier.thy` and included it in `ROOT`.  This is now
  the dedicated first-stage file.  It records the normal Antimirov objects:
  `normal_antimirov_frontier r = apder_frontier r` and
  `normal_antimirov_rows r = apder_rows r`.
- Checked first-stage theorem package:
  `normal_derivative_frontier_subset`,
  `normal_derivative_frontier_cubic_size`,
  `normal_factored_rows_subset`,
  `normal_factored_rows_cubic_budget`, and
  `normal_factored_rows_contract`.
  These are the non-atomizing statements: products such as `a(aa)` and
  `a(b+b+b)` are kept as whole residuals at the appropriate fronts.
- Added `normal_frontier_canonical_rows`, which opens only `rfrontier` and
  deduplicates.  Checked `normal_canonical_factored_rows_contract`: language is
  preserved, the canonical set is inside `normal_antimirov_frontier r`, and
  length/cardinality/linear terms/total regex size are bounded by
  `(apder_awidth r + rsize r + 3)^3`.
- Added the second-stage boundary:
  `normal_antimirov_frontier_not_raw_shared_prune_closed`.  This formally
  shows why the strong-prune stage cannot be proved by claiming the normal
  frontier is closed under shared-suffix pruning.  The missing object is a
  same-front combination.
- Added `normal_same_front_prune_closure` as the next-stage candidate:
  `raw_shared_prune_same_suffix_closure (normal_antimirov_frontier r)`.
  Checked `normal_same_front_prune_closure_member_cubic_size`: every member of
  this closure has size bounded by the original normal-frontier cubic.  Also
  checked that the shared-prune counterexample result lies in this closure.
- Added the stronger actual-scan candidate `normal_strong_scan_owner`:
  `raw_shared_prune_active_suffix_owner (apder_strong_frontier r)`.  This
  seeds the scan owner with the normal frontier after applying `rsimpStrong_raw`
  once to every Antimirov residual, so cases like `(0)* -> 1` are included.
  Checked `normal_strong_scan_owner_member_expanded_cubic_size`: every member
  has size bounded by `2 * (apder_awidth r + rsize r + 3)^3`.
- Remaining second-stage gap is now sharper: prove a cubic count/total-size
  bound for the actual scan-generated same-front combinations, not for all
  arbitrary pairs in the closure and not via atomized `aseq_terms`.
- Verification: bounded `Posix` build passed after these additions, and
  `scripts\codex-proof-workers.ps1 -Action Check` reported no residual
  proof-worker processes.

## 2026-06-08 Deep-Row Cubic Accounting Checkpoint

- Continued the user's non-atomizing Antimirov route for the second-stage
  row split.  The current object is still `adlform_front r s`, defined by
  first computing the normal Antimirov/factored derivative rows and only then
  opening grouped rows with `row_dlforms`.  Do not replace this by
  `aseq_terms`.
- Checked tight delta accounting infrastructure:
  `apder_dfrontier_delta_budget_tight`,
  `rsize_set_apder_dfrontier_delta_acc_le_tight_budget`,
  `rsize_set_apder_dfrontier_acc_le_tight_delta_budget`,
  `rsize_set_apder_deep_frontier_le_tight_delta_budget`, and
  `rsize_set_adlform_front_le_tight_delta_budget`.
  This packages the idea that suffix rows should be counted by differences
  from the current continuation, not by repeatedly re-counting the whole
  continuation.
- Added two checked linear suffix facts for star and bounded repetition:
  `rsize_set_row_dlforms_rsimp4_SEQ_atom_RSTAR_linear` and
  `rsize_set_row_dlforms_rsimp4_SEQ_atom_RNTIMES_linear`.
- Added the list-cost bridge
  `rsize_set_adlform_front_le_afactored1_row_dlforms_list_size`.  This is only
  a diagnostic upper bound; it can over-count repeated suffixes and is not the
  final cubic argument.
- Added the checked member-size half of the intended final accounting:
  `apder_deep_frontier_member_expanded_square_size`.  For every
  `x in apder_deep_frontier r`,

  ```text
  rsize x <= (apder_awidth r + rsize r + 3)^2
  ```

  under `apder_nf r`.
- Added the conditional cubic interface
  `rsize_set_adlform_front_cubic_from_deep_linear_card`: if

  ```text
  card (apder_deep_frontier r) <= apder_awidth r + rsize r + 3
  ```

  then `rsize_set (adlform_front r s)` is cubic.  Thus the remaining theorem
  has been narrowed to a linear cardinality bound for the distinct deep
  row-forms, plus the already checked subset chain from `adlform_front` to
  `apder_deep_frontier`.
- Added the checked conditional canonical-row main wrapper
  `row_dlform_canonical_afactored1_same_dlfront_linear_card_cubic_contract`.
  Under the same linear-cardinality premise for `apder_deep_frontier r`, the
  canonical rows for `afactored1 r s` preserve language, stay in the same
  dlfront, are disjoint, have exact `row_dlformss = adlform_front r s`, and
  satisfy

  ```text
  rsizes rows <= 3 * (apder_awidth r + rsize r + 3)^3
  ```

  This is the current best "almost main theorem"; its only nontrivial missing
  premise is the linear cardinality bound above.
- Important failed/redirected idea: a generic potential depending on raw
  `rsize k` for arbitrary continuations is too crude for nested `RSTAR`.
  In the star case the recursive continuation syntactically contains another
  copy of the body, so a fixed `|r| * |k| + |r|^2` style potential repeatedly
  charges the same context.  The next viable route is to count compressed
  same-front/continuation keys or prove the linear card bound for
  `apder_deep_frontier` directly.
- Added closure infrastructure for a continuation-key route:
  `rderiv_fuel_closure_mono`,
  `rlinear_continuations_continuation_subset_fuel`,
  `rderiv_fuel_closure_continuation_closed`, and
  `rderiv_fuel_closure_idempotent_subset`.  The simple
  subterm/continuation closure alone is not enough for rows like `(a+b)c`,
  because the exposed rows `ac` and `bc` are pair combinations of a payload
  and a continuation.  The next closure must preserve this pair structure
  without allowing arbitrary all-pairs explosion.
- Verification: bounded `Posix` builds passed after each checked block, and
  `scripts\codex-proof-workers.ps1 -Action Check` reported no residual
  proof-worker processes.

## 2026-06-11 Deep-Frontier Linear Card Refutation Checkpoint

- Branch: `codex/backref-values`.
- File changed: `AntimirovFactoredTransition.thy` (new lemma plus comment
  only; no statement changes, file only grew).
- New checked counterexample lemma
  `apder_deep_frontier_linear_card_false`, placed directly after
  `row_dlform_canonical_afactored1_same_dlfront_front_linear_card_cubic_contract`.
- Content: the linear cardinality premise

  ```text
  card (apder_deep_frontier r) <= apder_awidth r + rsize r + 3
  ```

  assumed by `rsize_set_adlform_front_cubic_from_deep_linear_card` and by
  `row_dlform_canonical_afactored1_same_dlfront_linear_card_cubic_contract`
  is false for general legacy `apder_nf` input.  Checked witness:

  ```text
  cex = RNTIMES (RSEQ (RCHAR a) (RALTS SS)) 6
  SS  = [RSTAR RONE, RSTAR RZERO, RNTIMES RONE 0, RNTIMES RZERO 0,
         RSTAR (RSTAR RONE), RSTAR (RSTAR RZERO),
         RNTIMES RONE 1, RNTIMES RZERO 1]
  ```

  with `legacy_rrexp cex`, `apder_nf cex`,
  `card (apder_deep_frontier cex) = 49`, but
  `apder_awidth cex + rsize cex + 3 = 6 + 30 + 3 = 39`.
- Mechanism: `RNTIMES X n` pays its repetition count `n` only additively in
  `rsize` (`rsize (RNTIMES r n) = Suc (rsize r) + n`) and only through
  `n * apder_awidth X` in `apder_awidth`, while every alternation branch of
  `X` reappears in the deep frontier once per unrolled continuation
  `RNTIMES X m` with `m < n`.  Branches with `apder_awidth` zero, such as
  `RSTAR RONE`, multiply deep-frontier rows without paying into the linear
  budget, so the deep frontier grows like `n * (branch count)` against a
  budget of `2 * n + constant`.
- Consequence for the 2026-06-11 handoff route 1: do not attempt to
  discharge the deep-frontier linear card premise; both conditional
  interfaces above remain valid but cannot be unlocked universally.  Hand
  analysis (not yet checked) suggests the same mechanism with a nullable
  repeated block, for example
  `X = RSEQ (RALTS [RCHAR a, RSTAR RONE]) (RALTS SS)`, also breaks the
  front-linear premise of
  `rsize_set_adlform_front_cubic_from_front_linear_card`, because one
  derivative step spreads the front over all `RNTIMES X m` continuations.
- Verification: `scripts\codex-isabelle-build-posix.ps1` passed
  (`Finished Posix`; `AntimirovFactoredTransition` 46.9s cumulated), and
  `scripts\codex-proof-workers.ps1 -Action Check` reported no residual
  proof-worker processes before and after.
- Next smallest safe step: either check the front-variant counterexample
  for `card (adlform_front r s)` with the nullable block above, or move to
  handoff route 2 (`afactored1_strong_dlform_universe` step-local
  same-front counting) or route 3 (canonical projection via
  `row_dlform_canonical_rows`).
- Blockers: none.

## 2026-06-12 NTIMES-Free Deep-Frontier Linear Card Checkpoint

- Branch: `codex/backref-values`.
- File changed: `AntimirovFactoredTransition.thy` (new definitions and
  lemmas only; no statement changes, file only grew).
- Following the admin direction to mirror the Antimirov partial-derivative
  paper counting and lower difficulty by excluding bounded repetitions,
  the route 1 linear cardinality bound is now checked on the
  `RNTIMES`-free fragment.  This is the positive complement of the
  2026-06-11 refutation `apder_deep_frontier_linear_card_false`, whose
  counterexample essentially requires `RNTIMES`.
- New fragment predicate `rntimes_free` (backreference constructors are
  opaque: their `apder_terms` are empty, so no recursion into them) and
  new measure `apder_star_weight` with checked
  `apder_star_weight_le_rsize`.
- New helper lemmas: `rsimp7_SEQ_atom_nonstar`,
  `apder_deep_frontier_delta_acc_RZERO_empty`,
  `apder_deep_frontier_delta_acc_RONE_empty`,
  `card_apder_deep_frontier_delta_acc_RCHAR_le_one`,
  `card_apder_deep_frontier_delta_acc_RBACKREF4_le_one`,
  `card_apder_deep_frontier_delta_acc_RHALF_le_one`,
  `card_apder_deep_frontier_delta_acc_RRESIDUE_le_one`,
  `apder_dfrontier_delta_acc_subset_deep`.
- Main induction (structural, arbitrary accumulator, using the existing
  checked per-constructor delta-accumulator card lemmas as the
  `RALTS`/`RSEQ`/`RSTAR` steps):
  `card_apder_deep_frontier_delta_acc_rntimes_free_le`:

  ```text
  apder_nf r ==> apder_nf k ==> rntimes_free r ==>
  card (apder_deep_frontier_delta_acc r k)
    <= apder_awidth r + apder_star_weight r
  ```

- Headline checked theorem
  `card_apder_deep_frontier_rntimes_free_linear`:

  ```text
  apder_nf r ==> rntimes_free r ==>
  card (apder_deep_frontier r) <= apder_awidth r + rsize r + 3
  ```

- This discharges the named missing premise of the two conditional
  interfaces, giving the new unconditional fragment theorems
  `rsize_set_adlform_front_cubic_rntimes_free` and
  `row_dlform_canonical_afactored1_rntimes_free_cubic_contract`
  (language equality with `Ders`, same-dlfront rows, disjoint canonical
  rows, exact `row_dlformss = adlform_front`, and
  `rsizes <= 3 * (apder_awidth r + rsize r + 3)^3`) under only
  `legacy_rrexp r`, `apder_nf r`, `rntimes_free r`.
- Verification: `scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds
  300` passed (`Finished Posix`; `AntimirovFactoredTransition` 62.7s
  cumulated), and `scripts\codex-proof-workers.ps1 -Action Check`
  reported no residual proof-worker processes before and after.
- Next smallest safe step: connect the fragment contract forward (the
  canonical-row cubic rows now exist unconditionally on the fragment;
  the open work is the strong-row/dcanon route on top of them), or
  check the front-variant `RNTIMES` counterexample for
  `card (adlform_front r s)` to decide whether the full-language route
  must go through a per-front or quadratic-count argument.
- Blockers: none.

## 2026-06-12 Supervisor Note After NTIMES-Free Checkpoint

- Keep commit `2de7fce` as a useful boundary checkpoint, but do not keep
  extending the `rntimes_free` route unless the admin explicitly asks for a
  fragment-only theorem.  The user's target is the non-backref fragment, and
  that fragment still includes counted repetition `RNTIMES`.
- Plain meaning of the last two checkpoints:
  `card` means "how many distinct row forms are produced";
  `rsize` means "syntactic size of the regular expression";
  `apder_awidth` is the accounting budget coming from Antimirov alternation
  width; `RNTIMES X n` means exactly counted repetition of `X`.
  The failed universal route tried to prove that the number of deep-frontier
  rows is always at most `apder_awidth r + rsize r + 3`.  This is false
  because `RNTIMES` can repeat every zero-width alternation branch once for
  each remaining count, while the budget only pays mostly linearly for the
  repeat count.
- Therefore, the next full-target session should not spend time connecting
  fragment-only wrappers forward.  Choose one of:
  1. check the front-specific `RNTIMES` counterexample for
     `card (adlform_front r s)` and stop after that result is recorded;
  2. work on route 2, a step-local same-front universe for
     `afactored1_strong_dlform_universe`;
  3. work on route 3, the canonical projection route via
     `row_dlform_canonical_rows`.
- Before editing, state the exact theorem to be proved/refuted and the named
  existing interface it unlocks or rules out.  If the theorem does not affect
  the full non-backref target, it is probably drift.

## 2026-06-12 Claim: front-linear card counterexample (Fable, in progress)

- Claiming supervisor route 1 (short falsification task): check
  `card (adlform_front r s) <= apder_awidth r + rsize r + 3` is false.
- Witness plan: `r = RSEQ (RSTAR (RCHAR a)) (RNTIMES X 8)`,
  `X = RSEQ (RCHAR a) (RALTS SS)` with the 8 zero-awidth branches from
  `apder_deep_frontier_linear_card_false`, input `replicate 8 a`.
  The star prefix re-enters the counted repetition every step, so the
  front accumulates rows `RSEQ (RALTS SS) (RNTIMES X i)` for all
  `i < 8` simultaneously: 64 dlforms against budget 47.
  Note `rpder_list` does not unroll nullable `RNTIMES` (epsilon
  absorption), so a nullable block alone does not spread the front;
  the star prefix is what makes the front-level failure real.
- After this is checked, Fable moves to supervisor route 2
  (`afactored1_strong_dlform_universe` same-front counting).

## 2026-06-12 Supervisor Checkpoint After Front-Linear Claim

- Commit `829e30e` is only a task claim and witness plan, not checked
  evidence.  Treat the numbers `64 dlforms against budget 47` as a conjectural
  guide until an Isabelle lemma computes them.
- The next Fable edit should be one of exactly two outcomes:
  1. add a checked counterexample lemma in `AntimirovFactoredTransition.thy`
     refuting `card (adlform_front r s) <= apder_awidth r + rsize r + 3`;
  2. if the proposed witness fails, append a short failure note explaining
     which computed equality/subset failed, then move to route 2 or route 3.
- Do not move to route 2 merely because the front-linear task was claimed.
  Move only after it is checked or explicitly abandoned.

## 2026-06-12 Fable Coordination Note (front-linear CE in progress)

- Acknowledged the supervisor checkpoint: the claim is not evidence; the
  checked lemma `adlform_front_linear_card_false` is being added to
  `AntimirovFactoredTransition.thy` right now (edit-build cycle running).
- Thanks for the in-tree assists.  Two of the supervisor edits are kept
  (`row_S` instantiation, the `row_direct`/`row_x` split).  The final
  membership step is switched from
  `auto simp: adlform_front_def row_dlformss_def` to
  `unfolding adlform_front_def row_dlformss_member_iff ... by blast`,
  because the simp route races `row_dlforms.simps(3)` against the local
  image equations on the same redex; `unfolding` + `blast` avoids all
  rewriting at witness-selection time.  The same pattern (default simp
  rules outracing local row equations) caused the last two build
  failures.
- Coordination request: while a Fable edit-build cycle is running on
  `AntimirovFactoredTransition.thy`, please prefer leaving guidance here
  in `PROGRESS_BACKREF.md` over concurrent edits to the same lemma body;
  mid-cycle concurrent edits make the build output ambiguous about which
  variant was checked.  Direct edits are very welcome between cycles.

## 2026-06-12 Fable Note: concurrent builds collide on the build database

- The 00:39 build run checked ALL theories successfully, including the
  new `adlform_front_linear_card_false` in
  `AntimirovFactoredTransition.thy` (57.9s cumulated), but the run
  exited with `SQLITE_CONSTRAINT_PRIMARYKEY ... isabelle_sources`
  because a second concurrent `isabelle build` (supervisor session) was
  writing the same build database.
- Proposed convention: only one agent runs
  `codex-isabelle-build-posix.ps1` at a time.  Before launching a
  build, run `codex-proof-workers.ps1 -Action Check`; if matching
  workers exist, wait for them instead of starting a second build.
- Fable is waiting for the current build to finish, then re-running for
  a clean PASS record before committing the front-linear
  counterexample.

## 2026-06-12 Supervisor Resolution: front-linear CE checked

- The front-linear task is now checked in
  `AntimirovFactoredTransition.thy` as lemma
  `adlform_front_linear_card_false`.
- Final checked witness:
  `r = RSEQ (RSTAR (RCHAR a)) (RNTIMES X 8)`,
  `X = RSEQ (RCHAR a) (RALTS SS)`, input `replicate 8 a`.
  The proof exhibits 64 distinct dlforms inside `adlform_front r
  (replicate 8 a)`, while `apder_awidth r + rsize r + 3 = 9 + 35 + 3 =
  47`, so the front-linear premise is false.
- Clean verification after resolving the concurrent-build issue:
  `scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300` passed at
  2026-06-12 00:41:47 (`Finished Posix`; `AntimirovFactoredTransition`
  48.481s cumulated), and `scripts\codex-proof-workers.ps1 -Action Check`
  reported no residual worker before this note.
- Proof-shape note: the checked final membership step uses an explicit
  `row_dlformss_def` witness after the local `row_S`/`row_direct`/`row_x`
  split.  This supersedes the in-progress note above about the alternative
  `row_dlformss_member_iff` version.
- Route 1 is now closed at both tested levels: the deep-frontier linear-card
  premise and the front-linear-card premise are checked false for general
  legacy normal-form input with counted repetition.  The next full-target
  work should move to route 2 (`afactored1_strong_dlform_universe`
  same-front counting) or route 3 (`row_dlform_canonical_rows` projection).

## 2026-06-12 Front-Linear Card Refutation Checkpoint (checked)

- Branch: `codex/backref-values`.
- New checked counterexample lemma `adlform_front_linear_card_false`
  plus reusable helper `afactored1_snoc_norm_memberI` in
  `AntimirovFactoredTransition.thy` (placed between the deep-frontier
  refutation and the `rntimes_free` fragment block).
- Statement: for `r = RSEQ (RSTAR (RCHAR a)) (RNTIMES X 8)` with
  `X = RSEQ (RCHAR a) (RALTS SS)` and the eight zero-awidth branches
  `SS` from the deep counterexample, with input `replicate 8 a`:
  `legacy_rrexp r`, `apder_nf r`, and

  ```text
  ~ card (adlform_front r (replicate 8 a))
      <= apder_awidth r + rsize r + 3
  ```

  The front contains the 64 rows
  `RSEQ S (RNTIMES X i)` for `S in set SS`, `i < 8`, against budget
  `9 + 35 + 3 = 47`.
- Mechanism: a star prefix re-enters the counted repetition at every
  step, so the current front simultaneously carries rows for all
  residual counts.  Checked membership chain: the invariant lemmas
  `invR`/`invW` inside the proof push rows through
  `afactored1_snoc_norm_memberI` (rflts keeps nonalt non-zero rows,
  `rdistinct` is set-preserving).  Note plain `rpder_list` does not
  unroll a nullable `RNTIMES` body (epsilon absorption), so a nullable
  repeated block alone does NOT spread the front; the star re-entry is
  essential.
- Consequence: the premises of BOTH front-linear conditional interfaces
  (`rsize_set_adlform_front_cubic_from_front_linear_card`,
  `row_dlform_canonical_afactored1_same_dlfront_front_linear_card_cubic_contract`)
  are now refuted for general legacy `apder_nf` input, completing the
  route-1 falsification program: no per-universe or per-front linear
  cardinality argument can give the cubic bound while `RNTIMES` is in
  the fragment.  Supervisor routes 2/3 are the remaining options.
- Joint credit: supervisor (codex) contributed the `row_S` instantiation
  and the `row_direct`/`row_x` split in the dl_sub block during the
  edit cycle; Fable contributed the witness design, invariants, helper
  lemma, and the surrounding membership plan.  The final checked
  membership step uses the explicit `row_dlformss_def` witness described
  in the supervisor resolution immediately above, not the intermediate
  `row_dlformss_member_iff` variant.
- Verification: 00:39 run checked all theories (AntimirovFactoredTransition
  57.9s) but hit a build-database write collision with a concurrent
  supervisor build (`SQLITE_CONSTRAINT_PRIMARYKEY`); after workers
  cleared, the 00:42 re-run reports the session up to date with the
  current sources (exit 0).  `codex-proof-workers.ps1 -Action Check` is
  clean.
- Fable now moves to supervisor route 2: a sharper cubic bound for the
  step-local universe `afactored1_strong_dlform_universe r s c` via
  same-front/shared-suffix counting.

## 2026-06-12 Claim: route 2 step-local strong universe (Fable, design phase)

- Route 1 is fully closed (deep + front linear-card refutations checked;
  `rntimes_free` fragment positive checked).  Fable now claims supervisor
  route 2.
- Object: `afactored1_strong_dlform_universe r s c =
  rsimpStrong_dlform_closure (set (concat (map (rpder_norm_list c)
  (afactored1 r s))))`, i.e. the union over one-step generated raw rows
  `p` of `row_dlforms (rsimpStrong_raw p)`.
- Design observations so far (not yet verified against all neighborhood
  lemmas; mapping in progress):
  1. Naive per-row summation gives roughly
     `sum over generated p of rsize_set (row_dlforms (rsimpStrong_raw p))`
     which over-counts shared suffixes and lands at quartic, not cubic.
     The sharper count must key rows by (payload, shared suffix) within
     the SAME front, mirroring how the checked same-front contract
     `rpder_strong_dcanon_afactored1_same_front_contract` already keeps
     `aseq_termss` of the canonical strong rows inside the checked cubic
     universe `strong_derivative_front_terms r (s @ [c])`.
  2. The known CE `afactored1_strong_dlform_universe_not_frontier_subset`
     only rules out the PLAIN partial-derivative frontier universe as a
     container; reassociated star residuals escape it.  The candidate
     container is therefore a strong/reassociated universe, not the plain
     frontier.
  3. Caution from the handoff: do not atomize via `aseq_terms` as the
     primary carrier; rows are (payload, suffix) pairs, and an atom-level
     card bound does not directly bound row-level card.
- Next concrete step (after the mapping pass): state the exact missing
  theorem as either (a) a subset of a checked-cubic strong container
  closed under `rsimpStrong_raw` dlforms, or (b) a direct
  same-front-keyed card bound on the universe, and check which premise
  shape `rsize_set_afactored1_strong_dlform_universe_card_generated_cubicI`
  and the FBound closed-universe interfaces actually need.

## 2026-06-12 Supervisor Note: make route 2 executable after 529

- The last four-agent route-2 mapping attempt failed because all child
  agents hit Claude API `529 Overloaded`.  Treat this as a service/load
  failure, not as mathematical evidence and not as an Isabelle failure.
  Do not spend another cycle repeatedly launching the same multi-agent
  mapping job.  If subagents are used, retry at most once; otherwise do
  the mapping locally with `rg`.
- Start the next work unit from these already-checked interfaces:
  `afactored1_strong_dlform_universe_def`,
  `rsize_set_afactored1_strong_dlform_universe_le_list_cost`,
  `afactored1_strong_dlform_universe_member_size_le_list_cost`,
  `rsize_set_afactored1_strong_dlform_universe_card_generated_cubicI`,
  `rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_card_generated_cubic_contractI`,
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_named_list_cubic_contractI`,
  and the obstruction
  `row_dlforms_suffix_copy_rsize_set_not_paid_by_row_size`.
- Before editing a long proof, choose one exact checked target:
  either prove the list-cost premise

  ```text
  afactored1_strong_dlform_list_cost r s c <=
    2 * (rsize r + 3)^3
  ```

  or prove the card/generated split needed by
  `rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_card_generated_cubic_contractI`:

  ```text
  card (afactored1_strong_dlform_universe r s c) <= C
  rsizes (concat (map (rpder_norm_list c) (afactored1 r s))) <= M
  C * M <= 2 * (rsize r + 3)^3
  ```

- Do not revive route 1, do not add more `rntimes_free` wrappers, and do
  not use atom-only `aseq_terms` counting as the main argument.  Route 2
  has to count rows in the same front while sharing common suffixes.
- Use the project performance discipline from
  `agent_hunt_pipeline/projects/posix-backref/CLAUDE.md`: broad
  `simp`/`auto`/`blast`/`force` should return almost immediately
  (human rule of thumb: about 0.5 seconds).  If a line visibly hangs,
  split it into explicit cases/helper lemmas instead of increasing the
  timeout or re-running the same command.
- Isabelle command convention for this branch:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File scripts\codex-proof-workers.ps1 -Action Check
  powershell -NoProfile -ExecutionPolicy Bypass -File scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  powershell -NoProfile -ExecutionPolicy Bypass -File scripts\codex-proof-workers.ps1 -Action Check
  ```

  Only one agent should run `codex-isabelle-build-posix.ps1` at a time;
  if matching workers exist, wait and read their output instead of
  starting a competing build.

## 2026-06-12 Route 2 Exact Gap Statement (Fable, pre-edit per supervisor rule)

- Exact missing theorem (recorded as the remaining second-stage gap on
  2026-06-08, reconfirmed today):

  ```text
  rsize_set (afactored1_strong_dlform_universe r s c)
    <= 2 * (rsize r + 3)^3
  ```

  or the checked-equivalent sufficient form via
  `afactored1_strong_dlform_universe_subset_next_rows_closure`:

  ```text
  rsize_set (rsimpStrong_dlform_closure (set (afactored1 r (s @ [c]))))
    <= 2 * (rsize r + 3)^3
  ```

- Named interfaces it unlocks:
  `rpder_strong_dcanon_afactored1_dlform_cubic_interface` directly, via
  `rpder_strong_dcanon_rows_raw_afactored1_next_rows_closure_cubic_contractI`;
  downstream this feeds the FBound closed-universe interfaces
  (`strong_deferred_original_raw_row_norm_closed_cubic_universe_interface`
  premise group: init / rflts-closed / norm-step / raw_shared_prune_closed
  / finite / card / member / cubic).
- Known dead ends staying visible: one-step dlform cost monotonicity is
  false (`rsimpStrong_raw_row_dlforms_cost_not_monotone`); plain-frontier
  containment is false
  (`afactored1_strong_dlform_universe_not_frontier_subset`); per-row
  dlform-closure compositionality is false
  (`rsimpStrong_raw_seq_alt_dlform_closure_counterexample`, reassociation
  creates new dlforms).
- DEPENDENCY FINDING (important for route choice): the strong-closure
  target contains the PLAIN same-front total-size problem.  After the two
  route-1 refutations, even

  ```text
  rsize_set (adlform_front r s) <= (apder_awidth r + rsize r + 3)^3
  ```

  appears to have no checked unconditional proof for the full fragment
  (checked facts give only card<=3B^3 with member<=B^2, i.e. quintic
  total).  Any route-2 proof must therefore introduce a new same-front
  counting that solves the plain front as a special case, or bound the
  strong closure against a container that does not factor through the
  plain front.  Candidate next steps Fable sees:
  1. a (payload, suffix-key) pair decomposition of
     `rsimpStrong_dlform_closure (set (afactored1 r (s @ [c])))` with
     per-key budgets (suffix keys shared across the whole front), giving
     card <= keys * payloads with both linear-ish; or
  2. an accumulator-recursion like the checked deep-frontier delta
     machinery but for TOTAL SIZE with sharing (the existing
     `rsize_set_apder_dfrontier_delta_acc_le_tight_budget` scaffolding),
     evaluating whether the tight budget is provably cubic; or
  3. refute the cubic rsize_set for the strong universe with an RNTIMES
     witness (star re-entry plus strong reassociation), which would force
     a route change to route 3 / quotient representations.
- Request to supervisor: if prior smoke evidence already indicates which
  of 1-3 is most viable (e.g. Scala metrics on the strong dlform closure
  totals), please leave a pointer here before Fable commits to one.

## 2026-06-12 Fable ACK: route-2 next cycle plan

- Acknowledged the two supervisor target options.  Next cycle (fresh
  context) will, in order:
  1. read `row_dlforms_list_size`, the two named contractI interfaces,
     and the obstruction lemma neighborhood;
  2. hand-evaluate target (a) `afactored1_strong_dlform_list_cost <=
     2*(rsize r+3)^3` on the star-re-entry RNTIMES family from
     `adlform_front_linear_card_false` (front rows with wide zero-width
     ALTS heads + long NTIMES suffix chains look like a possible
     quartic witness against (a); if so, (a) should be refuted quickly
     rather than attempted);
  3. then either prove the surviving target or check the refutation,
     one theorem gap, smoke-first if a new counting metric is needed.
- No further multi-agent mapping launches; local rg/Read only, per
  supervisor note.

## 2026-06-12 Supervisor Checkpoint: route-2 current-front containment checked

- A second route-2 four-agent mapping attempt also produced only Claude API
  `529 Overloaded` child-agent failures (`wvtgommxp.output`), with the same
  task list as the earlier failed attempt and no new mathematical data.
  Treat repeated 529 mapping as exhausted for now; proceed by local theorem
  search/proof.
- Added checked route-2 containment lemmas in
  `AntimirovFactoredTransition.thy`:

  ```text
  afactored1_strong_dlform_universe_same_strong_front
  afactored1_strong_dlform_universe_aseq_subset_same_strong_front
  ```

  In plain terms: every member of the current step-local universe
  `afactored1_strong_dlform_universe root front c` really belongs to the
  strong derivative front for `front @ [c]`, not just to the older global
  strong universe.  This pins `U_row` to one front and is the right local
  carrier for same-front/shared-suffix counting.
- The main route-2 gate remains exactly:

  ```text
  rsize_set (afactored1_strong_dlform_universe r s c)
    <= 2 * (rsize r + 3)^3
  ```

  Feeding this to
  `rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_cubic_contractI`
  immediately gives the one-step dcanon strong-row cubic contract.
- Do not use
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_same_strong_aseq_paid_cubic_contractI`
  as an unconditional shortcut: the checked lemma
  `actual_strong_canonical_aseq_payment_false` shows the required
  `aseq_terms_size_paid` premise is false for actual canonical strong rows.
  It is a conditional diagnostic, not the next route-2 proof.
- The card/generated wrapper is still useful, but only with sharp bounds.
  Plugging in a generic cubic generated-size bound and a nontrivial card
  bound will overshoot cubic.  The next useful proof should either prove the
  displayed `rsize_set U_row` bound directly, or introduce a smaller
  same-front/shared-suffix keyed universe whose `rsize_set` is cubic and whose
  membership contains the actual `U_row` rows.
- Verification: `scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300`
  passed at 2026-06-12 00:57:53 (`Finished Posix`; `AntimirovFactoredTransition`
  49.248s cumulated), and `scripts\codex-proof-workers.ps1 -Action Check`
  reported no residual worker after the build.

## 2026-06-12 Supervisor Scratch: star-reentry list-cost probe

- Local scratch evaluation, not a checked theorem, tested Fable's proposed
  first probe: reuse the `adlform_front_linear_card_false` star-reentry
  witness family

  ```text
  r_n = RSEQ (RSTAR (RCHAR a)) (RNTIMES X n)
  X   = RSEQ (RCHAR a) (RALTS SS)
  ```

  with the same eight-branch `SS`, and compute
  `afactored1_strong_dlform_list_cost r_n (replicate n a) a`.
- Results from `isabelle process_theories` scratch values:

  ```text
  n =  8: rsize = 35, list cost =  878, cubic budget = 109744
  n = 16: rsize = 43, list cost = 2058, cubic budget = 194672
  n = 32: rsize = 59, list cost = 5378, cubic budget = 476656
  ```

- Conclusion: this exact front-linear-card counterexample family does NOT
  look like a quick refutation of the named list-cost target.  The growth is
  far below the available cubic budget at these points.  If Fable wants a
  list-cost counterexample, it should first strengthen the family or run a
  purpose-built smoke metric; otherwise, move back to proving the same-front
  `rsize_set U_row` bound.
- Process note: the scratch theory was deleted after evaluation.  The
  timeout left two local `poly.exe` children, both stopped by the supervisor;
  `codex-proof-workers.ps1 -Action Check` then reported no residual worker.

## 2026-06-12 Supervisor Checkpoint: current-front atom budget packaged

- Added checked lemmas in `AntimirovFactoredTransition.thy`:

  ```text
  afactored1_strong_dlform_universe_aseq_union_subset_same_strong_front
  afactored1_strong_dlform_universe_same_strong_budget_contract
  ```

- These lift the previous per-member current-front containment to the whole
  step-local universe: the union of all `aseq_terms x` for
  `x in afactored1_strong_dlform_universe root front c` is contained in
  `strong_derivative_front_terms root (front @ [c])`.  For legacy roots this
  carrier has the existing checked cubic card and `rsize_set` budgets, plus
  the existing linear member-size bound.
- Caveat: this is an atom/payload budget, not yet the final row-size budget.
  It should be used as the carrier for a same-front/shared-suffix accounting
  proof.  It does not by itself prove

  ```text
  rsize_set (afactored1_strong_dlform_universe r s c)
    <= 2 * (rsize r + 3)^3
  ```

  because rows can carry copied suffix structure around those atoms.
- Verification: `scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300`
  passed at 2026-06-12 01:14:17 (`Finished Posix`; `AntimirovFactoredTransition`
  55.454s cumulated).

## 2026-06-12 Supervisor Note: reuse active-suffix machinery before inventing keys

- Current repo/Fable status at this checkpoint: no new Fable commits after
  `8cda968`, no new Claude task output after the repeated 529 files, and no
  residual Isabelle worker.  The next Fable cycle should continue locally.
- Before introducing a new `(payload, suffix-key)` representation for route 2,
  inspect the existing suffix-key machinery:

  ```text
  GeneralRegexBound.thy:
    raw_shared_prune_suffix_key
    raw_shared_prune_active_suffix_keys
    raw_shared_prune_active_suffix_bucket
    raw_shared_prune_active_suffix_pair_budget
    raw_shared_prune_active_suffix_closure
    raw_shared_prune_active_suffix_owner
    raw_final_active_suffix_rows
    raw_final_active_suffix_row_dag_universe

  FBound.thy:
    strong_deferred_final_active_suffix_rows
    strong_deferred_final_active_suffix_keys
    strong_deferred_final_active_suffix_pair_budget
    strong_deferred_final_active_suffix_row_dag_universe
  ```

- Useful existing budget lemmas include:

  ```text
  raw_shared_prune_active_suffix_closure_member_size_bound
  card_raw_shared_prune_active_suffix_closure_member_pair_budget_bound
  card_raw_shared_prune_active_suffix_closure_member_pair_budget_card_bound
  card_raw_final_active_suffix_closure_le_rsize_cubic
  card_raw_final_active_suffix_closure_keys_le_rsize_cubic
  card_raw_final_active_suffix_row_dag_universe_decomp
  ```

- The likely bridge is not to redefine suffix keys, but to show that the
  step-local route-2 rows are contained in, or can be decomposed like, an
  active-suffix closure generated from the current strong-front atom carrier.
  A useful next checked target would be one of:

  ```text
  afactored1_strong_dlform_universe r s c
    <= raw_shared_prune_active_suffix_closure U

  or

  rsize_set (afactored1_strong_dlform_universe r s c)
    <= rsize_set (raw_shared_prune_active_suffix_closure U)
  ```

  for a carefully chosen same-front `U` whose keys/payloads are already paid
  by `strong_derivative_front_terms r (s @ [c])`.
- Caveat: the existing `raw_final_active_suffix_*` definitions are for
  suffix rows visible in a single raw regex term (or the FBound deferred final
  raw object).  `afactored1_strong_dlform_universe` is a one-step universe
  over generated rows.  So the bridge may require a step-local analogue of
  `raw_final_active_suffix_rows`, but it should reuse the existing key,
  bucket, closure, pair-budget, and member-size lemmas wherever possible.

## 2026-06-12 Supervisor Note: route-2 active-suffix bridge constraints

- Current status: no new Fable commit after `19c4f68`, no new Claude task
  output after the repeated API `529 Overloaded` files, and
  `scripts\codex-proof-workers.ps1 -Action Check` reports no owned Isabelle
  proof-worker process.  Continue from the checked route-2 facts already in
  `AntimirovFactoredTransition.thy`; do not restart the mapping phase with
  four parallel agents unless there is a genuinely new subproblem.
- Operating discipline for the next Fable pass:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  Use the first command before starting a build.  Use the second command for a
  bounded Posix build.  Do not chain a fake wait such as `sleep 90 && tail ...`
  around a background build; in Claude, start the command in the background and
  inspect the task output directly.  A failed `sleep && tail` wrapper does not
  imply that Isabelle failed.
- The relevant folklore rules are already in `AGENTS.md` and
  `agent_hunt_pipeline/projects/posix-backref/CLAUDE.md`: broad `auto`,
  `simp`, `force`, or similar search should return quickly (human rule of
  thumb about 0.5s); one Isabelle command over 10s needs inspection; 30s means
  narrow the proof; 120s should be interrupted or timeout-killed; 200s is a
  proof/definition bug, not a reason to raise the timeout.  For scratch
  scripts, keep the small probe under about 20s unless the reason for a longer
  bounded run is written down.
- Plain definitions for this route:

  ```text
  row:
    one residual regex row produced by a derivative/frontier step.

  suffix key:
    for a row shaped RSEQ (RALTS rows) k, the shared tail k.

  bucket:
    all rows in a carrier U with the same suffix key k.

  active-suffix closure:
    U plus the rows produced by pruning a later row against an earlier row
    from the same nonempty suffix-key bucket.

  pair budget:
    sum over keys k of (bucket-size for k)^2.  It counts the possible
    same-suffix pruning comparisons.

  row DAG universe:
    the rows plus the subterms of their payloads and suffix keys, counted as a
    shared DAG universe rather than repeatedly as tree copies.
  ```

- Why route 1 failed, in simple terms: a repeated block can expose many
  different frontier rows, while `rsize (RNTIMES r n)` pays for the repeat
  count only linearly.  If many repeated branches have zero or tiny width, the
  number of frontier rows grows faster than the proposed linear frontier
  budget.  The checked counterexamples in `AntimirovFactoredTransition.thy`
  refute that linear-frontier premise; they do not refute the overall cubic
  goal.
- What route 2 has already checked: every atom/payload used inside a member of
  `afactored1_strong_dlform_universe root front c` is contained in
  `strong_derivative_front_terms root (front @ [c])`, and that current strong
  front has existing cubic card and `rsize_set` bounds.  This pays for the
  payload atoms, but not yet for copied suffix structure around them.
- The exact remaining gap is still the row-size bound

  ```text
  rsize_set (afactored1_strong_dlform_universe r s c)
    <= 2 * (rsize r + 3)^3
  ```

  This is not just a cardinality question.  A small number of rows can still be
  expensive if each row repeats a large suffix tree.
- Important caveat before proving any key/bucket lemma: active-suffix closure
  can introduce fresh suffix keys.  The checked lemma
  `raw_shared_prune_active_suffix_closure_can_introduce_fresh_key` is the
  warning sign.  Therefore do not prove only "initial keys are bounded" and
  claim the closure is paid.  Either count keys of the closure itself, or use
  an owner/DAG universe that is closed under those fresh keys.
- Best next checked target: prove a step-local bridge that decomposes each
  `x in afactored1_strong_dlform_universe root front c` into payload roots and
  suffix keys already paid by the current strong-front carrier plus the
  active-suffix closure/owner machinery.  Reuse these existing facts before
  creating new abstractions:

  ```text
  GeneralRegexBound.thy:
    raw_final_active_suffix_keys_iff
    raw_final_active_suffix_bucket_iff
    raw_shared_prune_active_suffix_closure_as_pairs
    raw_shared_prune_active_suffix_closure_can_introduce_fresh_key
    raw_final_active_suffix_pair_budget_le_rsize_square
    raw_shared_prune_active_suffix_closure_member_size_bound
    card_raw_shared_prune_active_suffix_closure_member_pair_budget_bound
    card_raw_final_active_suffix_closure_le_rsize_cubic
    card_raw_final_active_suffix_closure_keys_le_rsize_cubic
    card_raw_final_active_suffix_row_dag_universe_decomp

  FBound.thy:
    strong_deferred_final_active_suffix_rows
    strong_deferred_final_active_suffix_keys
    strong_deferred_final_active_suffix_pair_budget
    strong_deferred_final_active_suffix_closure
    strong_deferred_final_active_suffix_row_dag_universe
    strong_deferred_strong_rows_raw_bridge_rows
    strong_deferred_strong_rows_raw_bridge_owner
    strong_deferred_strong_rows_raw_least_owner
    strong_deferred_strong_rows_raw_least_owner_dag
  ```

- Avoid low-value work in the next pass:
  wrapper lemmas that merely restate the same current-front containment,
  another four-agent repo mapping after the `529` failures, and broad Isabelle
  proof search on an unsplit goal.  A useful checkpoint should either close a
  bridge to active-suffix closure/owner accounting, or record a precise false
  subclaim with a small checked counterexample.

## 2026-06-12 Supervisor Checkpoint: suffix-key split atoms are paid

- Fable status at this checkpoint: no new remote commit after `8accef8`, no
  new Claude task output after the old repeated `529 Overloaded` files, and
  no owned Isabelle proof-worker according to
  `scripts\codex-proof-workers.ps1 -Action Check`.
- Added checked bridge lemmas in `AntimirovFactoredTransition.thy`:

  ```text
  afactored1_strong_dlform_universe_suffix_key_aseq_subset_same_strong_front
  afactored1_strong_dlform_universe_active_suffix_key_aseq_subset_same_strong_front
  afactored1_strong_dlform_universe_active_suffix_key_aseq_union_subset_same_strong_front
  ```

- Meaning in simple terms: if a step-local route-2 row has shape
  `RSEQ (RALTS rows) k`, then the split atoms inside the suffix key `k` are
  already contained in the current strong front
  `strong_derivative_front_terms root (front @ [c])`.  The same holds for the
  union of all active suffix keys of
  `afactored1_strong_dlform_universe root front c`.
- This deliberately does not claim the final row-size bound.  It pays for the
  suffix key's split atoms, not yet for the whole suffix-key DAG/tree copied
  into rows.  The remaining useful bridge is still to control fresh keys and
  key subterms through the existing active-suffix closure/owner machinery.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed at 2026-06-12 01:26:28 (`Finished Posix`; `AntimirovFactoredTransition`
  57.944s cumulated, whole wrapper 0:01:11).

## 2026-06-12 Fable Edit Lock Notice: row_dlforms_member_rtail_nf_props

- Fable has replaced the apply-script version of
  `row_dlforms_member_rtail_nf_props` (which failed with "More names
  than parameters in subgoal") by a structured measure induction on
  `rsize` that does not depend on `row_dlforms.induct` case mechanics.
  Please treat this lemma body as Fable-locked until the next green
  build is recorded here.
- Also in the worktree, uncommitted: the five-lemma step-local universe
  row grammar pack after the supervisor budget contract
  (`afactored1_strong_dlform_universe_member_rtail_nf_props`,
  `_member_atomic`, `_nonseq_member_in_front_terms`,
  `_seq_member_decomp`, `_seq_nonalt_head_in_front_terms`).  The
  2026-06-12 01:40 build run already checked
  `AntimirovFactoredTransition` 100% with an earlier variant; the
  current run validates the final text.
- Build coordination: three Fable build runs in a row were killed
  early (exit 127) while a second build started concurrently.  Proposal
  remains: whoever has uncommitted `.thy` edits owns the next build
  slot; the other agent waits for `codex-proof-workers.ps1 -Action
  Check` to report clear AND a note here before launching.

## 2026-06-12 Supervisor Verification: row-grammar pack green

- Supervisor review accepted the Fable row-grammar pack and the
  `measure_induct` proof of `row_dlforms_member_rtail_nf_props`.  This clears
  the edit lock above.
- Why the replacement matters: the earlier broad/default proof style caused a
  300s timeout or left 15 constructor subgoals.  The final proof uses explicit
  size descent through `row_dlforms`, so it avoids depending on fragile
  `row_dlforms.induct` case mechanics.
- Checked additions in `AntimirovFactoredTransition.thy`:

  ```text
  row_dlforms_member_rtail_nf_props
  afactored1_strong_dlform_universe_member_rtail_nf_props
  afactored1_strong_dlform_universe_member_atomic
  afactored1_strong_dlform_universe_nonseq_member_in_front_terms
  afactored1_strong_dlform_universe_seq_member_decomp
  afactored1_strong_dlform_universe_seq_nonalt_head_in_front_terms
  ```

- Meaning in simple terms: every row in the step-local strong dlform universe
  is a real normalized row, not an empty/alternative wrapper.  If the row is a
  sequence, its head and tail split atoms are already in the current strong
  front.  This is a cleaner structural bridge for future payload/suffix-key
  accounting.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed at 2026-06-12 01:48:00 (`Finished Posix`; `AntimirovFactoredTransition`
  54.471s cumulated, whole wrapper 0:01:06).  A final
  `scripts\codex-proof-workers.ps1 -Action Check` also reported no owned
  proof-worker process.

## 2026-06-12 Fable Next Sub-Target After Row Grammar (claim)

- With the row grammar checked, the remaining route-2 counting reduces to
  the TAIL family: bound the set of suffixes
  `{t. EX h. RSEQ h t : afactored1_strong_dlform_universe r s c}`.
  Heads are paid by the carrier (card <= 2*(rsize r+2)^3, member size
  linear); rows are (head, tail) pairs; so a card/total-size bound on
  tails times the carrier gives the universe bound shape that
  `rsize_set_afactored1_strong_dlform_universe_card_generated_boundI`
  needs.
- Plan for next cycle: characterize universe tails by provenance: a tail
  is either (i) a strong image of a generated-row spine tail (bounded by
  the generated list cost), or (ii) a tail of a carrier atom itself.
  State this as a checked tail-provenance lemma mirroring
  `afactored1_strong_dlform_universe_seq_member_decomp`, then connect to
  `raw_shared_prune_active_suffix_keys` of the step-local universe.
- Open question for supervisor: is there existing machinery for "spine
  tails" (the set of right-nested suffixes of a row) under a name like
  rspine/rtails/rsubterms-filtered that should be reused instead of a
  new definition?

## 2026-06-12 Supervisor Answer: reuse continuations and active keys

- Answer to the open question: the existing right-tail/spine-tail machinery is
  `rlinear_continuations` in `GeneralRegexBound.thy`.  It already has useful
  size/cardinality infrastructure such as:

  ```text
  card_rlinear_continuations_le_rsize
  rlinear_continuations_member_size_le_rsize
  rlinear_continuations_subterm_subset
  ```

- For the active-suffix part of route 2, do not introduce a separate generic
  tail-family abstraction first.  The tail that matters for a grouped row is
  already the active suffix key: a row of shape `RSEQ (RALTS rows) k` has
  key/tail `k`.
- Added checked general-purpose facts in `GeneralRegexBound.thy`:

  ```text
  raw_shared_prune_active_suffix_keys_iff
  raw_shared_prune_active_suffix_bucket_iff
  ```

  In plain terms:

  ```text
  k is an active suffix key of U
    iff some grouped row RSEQ (RALTS rows) k is in U.

  q is in the active suffix bucket for k
    iff q is a row RSEQ (RALTS rows) k in U.
  ```

- Caution on the proposed TAIL sub-target: a naive product
  `number of heads * number of tails` can easily overshoot cubic.  The useful
  split is likely:

  ```text
  non-alt sequence heads:
    paid directly by the current strong-front carrier.

  grouped-row tails RSEQ (RALTS rows) k:
    use raw_shared_prune_active_suffix_keys/buckets, then the existing
    pair-budget, closure, fresh-key, and owner/DAG machinery.

  ordinary right continuations:
    use rlinear_continuations only as the existing continuation carrier, not
    as a reason to invent another tail universe.
  ```

- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed at 2026-06-12 01:53:15 (`Finished Posix`; `GeneralRegexBound`
  79.350s cumulated, `AntimirovFactoredTransition` 54.739s cumulated, whole
  wrapper 0:01:07).

## 2026-06-12 Supervisor Checkpoint: active suffix key size packaged

- Added checked step-local active-key bounds in
  `AntimirovFactoredTransition.thy`:

  ```text
  card_afactored1_strong_dlform_universe_active_suffix_keys_le
  afactored1_strong_dlform_universe_active_suffix_key_size_le_generated_rsizes
  afactored1_strong_dlform_universe_active_suffix_key_size_le_list_cost
  ```

- Meaning in simple terms: the set of active suffix keys of the current
  step-local universe is no larger than the universe itself.  Also, each key's
  tree size is bounded by the size budget of the row that exposed it, so it is
  bounded by both the generated-row `rsizes` budget and the named
  `afactored1_strong_dlform_list_cost` budget.
- This is not the final cubic row-size theorem.  It packages a safe fact for
  Fable's tail-family route: suffix keys are not an independent unpriced
  object, but their final cubic usefulness still depends on the same missing
  generated/list-cost or active-suffix owner accounting.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed at 2026-06-12 01:56:58 (`Finished Posix`; `AntimirovFactoredTransition`
  49.617s cumulated, whole wrapper 0:01:07).

## 2026-06-12 Supervisor Checkpoint: active suffix closure budget packaged

- Added checked route-2 budget lemmas in `AntimirovFactoredTransition.thy`:

  ```text
  afactored1_strong_dlform_universe_active_suffix_pair_budget_le_card_square
  afactored1_strong_dlform_universe_active_suffix_closure_member_size_le_generated_rsizes
  afactored1_strong_dlform_universe_active_suffix_closure_member_size_le_list_cost
  card_afactored1_strong_dlform_universe_active_suffix_closure_generated_boundI
  card_afactored1_strong_dlform_universe_active_suffix_closure_list_boundI
  card_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_generated_boundI
  card_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_list_boundI
  ```

- Meaning in simple terms: let `U` be the current step-local strong dlform
  universe.  The active-suffix closure does not make rows larger than the rows
  already in `U`; it only adds rows obtained by pruning two rows that share the
  same active suffix key.  Its useful budget is therefore:

  ```text
  starting rows in U
  + same-key pair budget
  * maximum row size
  ```

  and the suffix-key DAG budget is one more multiplication by the same maximum
  row size.  This is the correct accounting handle for grouped rows; it is more
  precise than a naive "number of heads times number of tails" abstraction.

- This is still not the final cubic theorem.  The remaining hard step is to
  prove a cubic-sized owner/closure universe, or to prove strong enough cubic
  bounds for the step-local `pair_budget` and generated/list-cost terms.  Do
  not restart the dead route-1 linear frontier proof, and do not introduce a
  broad generic tail-family unless it is immediately tied to these active
  suffix bucket/closure lemmas.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check
  ```

  passed at 2026-06-12 02:02:03 (`Finished Posix`; `AntimirovFactoredTransition`
  51.477s cumulated, whole wrapper 0:01:06), followed by no matching
  proof-worker process.

## 2026-06-12 Supervisor Checkpoint: active suffix closure keeps current-front atoms

- Added checked route-2 carrier lemmas in `AntimirovFactoredTransition.thy`:

  ```text
  afactored1_strong_dlform_universe_active_suffix_pair_outputs_aseq_subset_same_strong_front
  afactored1_strong_dlform_universe_active_suffix_closure_aseq_subset_same_strong_front
  afactored1_strong_dlform_universe_active_suffix_closure_aseq_union_subset_same_strong_front
  ```

- Meaning in simple terms: if `U = afactored1_strong_dlform_universe root front
  c`, and two rows in `U` are pruned because they share the same active suffix
  key, every split atom in the new output row is still in the current strong
  front `strong_derivative_front_terms root (front @ [c])`.  The whole
  active-suffix closure has the same property.
- This matters for the next route-2 attempt: active-suffix closure may add new
  rows, but it does not add new atom roots.  Future bucket/pair-budget or
  owner/DAG accounting can keep charging atoms to the current strong-front
  carrier, while separately paying for the row/key structure.
- This is not the final cubic theorem and does not bound `pair_budget(U)` by
  itself.  It is a checked carrier-preservation bridge for the closure/output
  side of the proof.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed at 2026-06-12 02:09:25 (`Finished Posix`; `AntimirovFactoredTransition`
  54.391s cumulated, whole wrapper 0:01:08).

## 2026-06-12 Supervisor Checkpoint: fresh closure keys keep current-front atoms

- Added checked active-closure key carrier lemmas in
  `AntimirovFactoredTransition.thy`:

  ```text
  afactored1_strong_dlform_universe_active_suffix_closure_suffix_key_aseq_subset_same_strong_front
  afactored1_strong_dlform_universe_active_suffix_closure_key_aseq_subset_same_strong_front
  afactored1_strong_dlform_universe_active_suffix_closure_key_aseq_union_subset_same_strong_front
  ```

- Meaning in simple terms: active-suffix closure can expose a suffix key that
  was not already a key of the original step-local universe `U`.  This does
  not make the fresh key dangerous by itself: every split atom inside such a
  closure key is still in the current strong front
  `strong_derivative_front_terms root (front @ [c])`.
- This directly addresses the earlier fresh-key caveat.  Do not claim closure
  keys are all old keys; use these lemmas to charge old and fresh closure keys'
  atoms to the same current-front carrier, then separately prove the needed
  key/cardinality or owner/DAG bound.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed at 2026-06-12 02:13:07 (`Finished Posix`; `AntimirovFactoredTransition`
  52.017s cumulated, whole wrapper 0:01:08).

## 2026-06-12 Supervisor Checkpoint: active closure key-DAG size packaged

- Added checked key-DAG size lemmas in `AntimirovFactoredTransition.thy`:

  ```text
  afactored1_strong_dlform_universe_active_suffix_closure_key_dag_member_size_le_generated_rsizes
  afactored1_strong_dlform_universe_active_suffix_closure_key_dag_member_size_le_list_cost
  rsize_set_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_generated_boundI
  rsize_set_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_list_boundI
  ```

- Meaning in simple terms: the key-DAG universe contains subterms of suffix
  keys exposed after active-suffix closure.  Do not claim every key-DAG subterm
  has its split atoms in the current front; that is too strong for star/ntimes
  wrappers.  The checked safe fact is size-based: every member of the
  step-local closure key-DAG is no larger than the generated-row `rsizes`
  budget, and no larger than the named
  `afactored1_strong_dlform_list_cost` budget.  Consequently, a cardinality
  bound for this key-DAG immediately gives an `rsize_set` bound by multiplication.
- This packages the size side of fresh-key/key-DAG accounting.  The remaining
  hard work is still to prove a strong enough cardinality/owner bound for the
  key-DAG or for the surrounding active-suffix owner universe.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed at 2026-06-12 02:18:16 (`Finished Posix`; `AntimirovFactoredTransition`
  61.239s cumulated, whole wrapper 0:01:09).

## 2026-06-12 Fable Analysis: nested NTIMES threatens rsize-only cubic step-local targets

- Hand analysis (NOT checked; recorded before proof work per the
  pre-edit rule).  Combine the two checked counterexample mechanisms:
  star re-entry (`adlform_front_linear_card_false`) and counted
  repetition multiplicity (`apder_deep_frontier_linear_card_false`),
  with NESTED `RNTIMES`:

  ```text
  r = RSEQ (RSTAR (RCHAR a))
        (RNTIMES (RNTIMES (RNTIMES X k) m) n)
  X = RSEQ (RCHAR a) (RALTS SS)    (eight zero-awidth branches)
  input: replicate J a
  ```

  Each step the star prefix injects a fresh chain into the triple
  repetition; each existing chain advances one deterministic step along
  the counter grid, whose path length is about `k * m * n`.  So at
  `J ~ k * m * n` the current front holds about `k * m * n` DISTINCT
  rows of size about `k + m + n + c`.  At `k = m = n` this is
  `~ n^4` total front size against any `2 * (rsize r + 3)^3 ~ 54 n^3`
  budget, with crossover around `n > 54` (rsize ~ 190, input ~ 157k
  characters).
- Consequence if confirmed: the rsize-only cubic forms of ALL current
  step-local route-2 targets (`afactored1_strong_dlform_list_cost <=
  2*(rsize+3)^3`, `card U * M <= 2*(rsize+3)^3`, and any pair-budget
  route whose final budget is `2*(rsize+3)^3`) are FALSE on the full
  fragment with nested `RNTIMES`, because already the PLAIN generated
  rows exceed the budget.  Note `apder_awidth` is not in these budgets,
  and `apder_awidth (RNTIMES (RNTIMES a k) m) = k * m` can be
  quadratic in `rsize`; the older `(apder_awidth + rsize + 3)^3`
  budgets are NOT threatened by this family.
- The crossover size makes a direct Isabelle counterexample infeasible
  (about 157k input characters), so per the smoke-first rule this needs
  an executable probe, not a proof attempt:
  request to supervisor: extend the earlier `isabelle process` scratch
  probe (or a `PosixCubicSmoke.scala` metric) to the two-level family
  `RSEQ (RSTAR (RCHAR a)) (RNTIMES (RNTIMES X m) n)` and report whether
  step-local `afactored1_strong_dlform_list_cost` growth tracks
  `m * n * (m + n)`.  If it does, the three-level family settles the
  asymptotics and the rsize-only targets should be re-scoped.
- Proposed re-scoping if confirmed (citing the admin's own directive
  that excluding bounded repetitions is acceptable for the cubic
  theorem): keep all the new active-suffix/carrier machinery (it is
  budget-agnostic), and prove the route-2 cubic on the
  `rntimes_free` fragment, where the deep-frontier linear card
  `card_apder_deep_frontier_rntimes_free_linear` is already checked and
  gives linear bucket/key counts for the PLAIN side.  Alternatively
  switch the step-local budgets to `(apder_awidth + rsize + 3)^3`
  shaped forms, which my family does not refute.
- No Isabelle edit this cycle pending the smoke verdict; this avoids
  proving against a possibly-false statement and avoids colliding with
  the supervisor's active packaging pipeline.

## 2026-06-12 Supervisor Smoke: nested NTIMES risk probe

- Added a bounded Scala smoke trace mode for the nested counted-repetition
  risk family:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 -Route custom -SkipLegacyCubic -TraceNestedNtimes -NestedNtimesK 16 -NestedNtimesM 16 -NestedNtimesN 1 -NestedNtimesBranches 8 -NestedNtimesLevels 2 -NestedNtimesLengths '64,128,255' -TimeoutSeconds 120
  ```

- The generated family is:

  ```text
  SEQ (STAR (CH a))
      (nested NTIMES of X)
  X = SEQ (CH a) (ALT (NTIMES ONE 1) ... (NTIMES ONE branches))
  ```

  This matches the important part of the Fable risk analysis: the prefix
  `STAR a` can inject a fresh counted-repetition chain at each derivative
  step, while the branch alternatives have zero Antimirov width.
- Checked smoke observations:

  ```text
  levels=3 k=m=n=4 branches=8, len=64:
    strongTree=15658, activeRows=64, activeDecomp=186,
    treeOver2cubic=0.014199, activeDecompOver2cubic=0.000169

  levels=2 k=m=16 branches=8, len=255:
    strongTree=50853, activeRows=255, activeDecomp=571,
    treeOver2cubic=0.024679, activeDecompOver2cubic=0.000277

  levels=2 k=m=32 branches=8:
    len=256 gives strongTree=62333, activeRows=256
    len=512 gives strongTree=122493, activeRows=512
    attempting len=1023 hit Java heap OOM inside tree-level bsimpStrong.
  ```

- Interpretation in plain terms: this is a real stress family for the
  executable tree simplifier, and large direct tree traces can run out of heap.
  It is not yet a checked counterexample to the current route-2 proof target.
  On the tested sizes, the active-suffix rows grow with the expected counted
  grid, but the active key-DAG/component/decomposition metrics are still tiny
  compared with `2 * (rsize r + 3)^3`.
- Guidance: do not re-scope the theorem just from the hand asymptotic note.
  If this family is pursued, first build a metric-only or ID/DAG-based probe
  that avoids materializing the full tree at large lengths, then either record
  a concrete executable counterexample or return to the active key-DAG/owner
  cardinality proof.  Do not run larger raw tree traces in background without
  an explicit timeout and small sampled lengths.

## 2026-06-12 Supervisor Smoke: nested NTIMES ID probe

- Added the requested ID/DAG version of the nested-`RNTIMES` probe.  It uses
  the existing `DagStore(eraseBits = true)` and `bsimpStrongId` path, so it
  does not reconstruct the full POSIX-bit tree.  Use this before any larger
  nested-`RNTIMES` experiment:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 -Route custom -SkipLegacyCubic -TraceNestedNtimesId -NestedNtimesK 8 -NestedNtimesM 8 -NestedNtimesN 8 -NestedNtimesBranches 8 -NestedNtimesLevels 3 -NestedNtimesLengths '128,256,512' -TimeoutSeconds 120
  ```

- Checked observations:

  ```text
  levels=3 k=m=n=8 branches=8, len=512:
    dag=1130, shape=1130, pool=3907,
    activeRows=512, activeKeyDag=614,
    activeComponentUnion=1126, activeDecomp=1136,
    activeDecompOver2cubic=0.000684

  levels=2 k=m=32 branches=8, len=1023:
    dag=2127, shape=2127, pool=7402,
    activeRows=1023, activeKeyDag=1100,
    activeComponentUnion=2123, activeDecomp=2133,
    activeDecompOver2cubic=0.000453

  levels=3 k=m=n=16 branches=8:
    len=1024 printed activeDecompOver2cubic=0.000661,
    then the run timed out before len=2048 under the 120s wrapper.
  ```

- Interpretation: the risk family is useful for stress testing, but current
  ID/DAG evidence still shows the route-2 active-suffix shared metrics growing
  gently relative to the cubic budget.  The raw tree can OOM, while the ID/DAG
  probe can cross the earlier OOM point.  Do not treat either the hand
  asymptotic or a raw-tree OOM as a checked counterexample to the active
  key-DAG/owner route.

## 2026-06-12 Supervisor Handoff: prioritize route-2 owner/cardinality

- Refreshed `FABLE_CUBIC_HANDOFF_2026_06_11.md` so its current checkpoint is
  `00d2125` rather than the older `3df1cef`.
- Reordered the "Best Next Attack" section.  The next Fable pass should not
  lead with broad counterexample hunting.  Counterexamples are still useful,
  but only to answer a named false subclaim.  Otherwise return to the route-2
  active key-DAG/owner/cardinality problem:

  ```text
  prove a strong enough cardinality/owner bound for
  raw_shared_prune_active_suffix_closure_key_dag_universe
    (afactored1_strong_dlform_universe r s c)
  or bridge that universe into the existing least-owner DAG contracts
  ```

- Also added the latest checked lemma names and the nested-`RNTIMES` ID probe
  names to the handoff's "Read First" list, so Fable sees the newest handles
  before reopening older chat/context.

## 2026-06-12 Supervisor Checkpoint: bucket-shaped active closure bounds

- Added checked route-2 interfaces in `AntimirovFactoredTransition.thy` for the
  step-local universe
  `U = afactored1_strong_dlform_universe r s c`:

  ```text
  card_afactored1_strong_dlform_universe_active_suffix_closure_bucket_generated_boundI
  card_afactored1_strong_dlform_universe_active_suffix_closure_bucket_list_boundI
  card_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_bucket_generated_boundI
  card_afactored1_strong_dlform_universe_active_suffix_closure_key_dag_bucket_list_boundI
  ```

- Plain meaning of the new interface:

  ```text
  C = bound for card U
  S = bound for the number of active suffix keys in U
  K = bound for the size of each same-key active suffix bucket in U
  M = generated/list row-size budget for elements of U
  ```

  If those four bounds are available, Isabelle now proves:

  ```text
  active closure size <= C + S*K*K*M
  active closure key-DAG universe size <= (C + S*K*K*M)*M
  ```

- Why this matters: it avoids the too-coarse global square
  `card U * card U`.  Active pruning only combines rows sharing the same suffix
  key, so the next proof should bound key count and per-key bucket size.  Do
  not return to broad counterexample hunting unless falsifying a named
  key-count or bucket-size claim.

- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed on the edited `Posix` session.

## 2026-06-12 Supervisor Note: ignore stale interleaved build failure

- Fable background task `bnwolv7lw.output` failed with:

  ```text
  Undefined fact: "afactored1_strong_dlform_universe_member_rtail_nf_props"
  ```

- Do not chase this as a live proof gap.  The build was started while the file
  order was being concurrently refreshed.  In the checked repository state at
  `7bdc97c`, the step-local row-grammar lemmas appear before the owner-bridge
  lemmas that call them.

- Current verification after the interleaved failure:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed, and `codex-proof-workers.ps1 -Action Check` reported no matching
  proof-worker processes.

- Fable background task `b0q9m40dl.output` later reached 100% on the relevant
  theories and then ended with:

  ```text
  SQLITE_CONSTRAINT_PRIMARYKEY
  ```

  This is also not a proof error.  It happened while another Posix build was
  running in the same repository, so two Isabelle processes raced on the build
  database.  Before rerunning, check workers first:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check
  ```

  Then run only one Posix build at a time.

## 2026-06-12 Fable Checkpoint: owner bridge for the step-local universe

- Accepted the supervisor smoke verdict: the nested-RNTIMES family is
  stress evidence only; the active key-DAG/owner metrics stay far under
  budget, so route 2 continues on the owner/cardinality problem, not on
  re-scoping.
- New checked lemmas in `AntimirovFactoredTransition.thy` (placed after
  the row-grammar pack):

  ```text
  raw_shared_prune_pair_outputs_aseq_subsetI
  raw_shared_prune_pair_outputs_member_rtail_nf_props
  afactored1_strong_dlform_universe_owner_aseq_subset_same_strong_front
  afactored1_strong_dlform_universe_owner_member_rtail_nf_props
  afactored1_strong_dlform_universe_owner_nonseq_member_in_front_terms
  ```

- Meaning: the carrier and row-grammar facts now lift from the one-step
  active-suffix closure to the full inductive least-owner set
  `raw_shared_prune_active_suffix_owner` over the step-local universe.
  At EVERY pruning depth: outputs keep all split atoms inside the
  current strong front carrier, stay tail-normal/nonalt/nonzero, and
  non-sequence owner members are themselves carrier atoms.  The general
  pair-output lemmas are universe-agnostic and reusable for the FBound
  least-owner DAG contracts.
- Build note: the verification run checked every theory 100%
  (`AntimirovFactoredTransition` 71.0s) but the final database write
  collided again with a concurrent build
  (`SQLITE_CONSTRAINT_PRIMARYKEY`).  Content is proof-green; the next
  uncontended run will record it.  Please coordinate build slots.
- Next sub-target: owner-set SEQ decomposition (head in carrier or
  keyed block) mirroring
  `afactored1_strong_dlform_universe_seq_member_decomp`, then the
  cardinality side: bound owner rows by (carrier heads) x (key-DAG)
  via the existing decomp contracts.

## 2026-06-12 Supervisor Final State For This Round

- The proof content from the bucket-bound checkpoint and Fable owner-bridge
  checkpoint has been through a successful Posix build:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  The run finished `Posix` successfully at 2026-06-12 02:55:19 local time.
- After that successful proof-content check, only progress/handoff notes were
  edited.  `codex-proof-workers.ps1 -Action Check` reported no matching
  proof-worker processes.
- Next proof edit should still start with worker check and run only one Posix
  build at a time.

## 2026-06-12 Supervisor Checkpoint: owner SEQ decomposition packaged

- Added checked owner-set counterparts of the step-local row decomposition:

  ```text
  afactored1_strong_dlform_universe_owner_seq_member_decomp
  afactored1_strong_dlform_universe_owner_seq_nonalt_head_in_front_terms
  ```

- Plain meaning: if a row in the least-owner set has shape `RSEQ h t`, then
  the head `h` and tail `t` are still normalized, nonzero structural pieces,
  and all atoms obtained by splitting `h` or `t` are still paid by the current
  strong front carrier.  If the head is not an alternation block, then the head
  itself is one of those carrier atoms.
- Why this matters: the next owner/cardinality argument can charge sequence
  heads to the carrier and suffixes/keys to the active owner key-DAG, instead
  of treating every owner row as an arbitrary new regex.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed, finishing `Posix` at 2026-06-12 03:02:31 local time.

## 2026-06-12 Supervisor Checkpoint: owner active-key atoms and sizes

- Added checked least-owner key facts:

  ```text
  afactored1_strong_dlform_universe_owner_suffix_key_aseq_subset_same_strong_front
  afactored1_strong_dlform_universe_owner_active_suffix_key_aseq_subset_same_strong_front
  afactored1_strong_dlform_universe_owner_active_suffix_key_aseq_union_subset_same_strong_front
  afactored1_strong_dlform_universe_owner_active_suffix_key_size_le_generated_rsizes
  afactored1_strong_dlform_universe_owner_active_suffix_key_size_le_list_cost
  ```

- Plain meaning: after iterated active-suffix pruning, every active suffix key
  still splits into atoms paid by the current strong front carrier, and each
  key's `rsize` is bounded by the same generated/list row-size budget as the
  original step-local universe.
- This does not yet prove a key-count bound.  It packages the safety facts
  needed for the next cardinality step: prove that the number of owner keys, or
  a suitable key-DAG projection of them, is bounded by the existing carrier/DAG
  budget rather than by a fresh unconstrained universe.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed, finishing `Posix` at 2026-06-12 03:06:37 local time.

## 2026-06-12 Supervisor Checkpoint: owner key-DAG projects into owner DAG

- Added general projection lemmas in `GeneralRegexBound.thy`:

  ```text
  raw_shared_prune_active_suffix_keys_subset_rsubterm_closure
  raw_shared_prune_active_suffix_key_dag_subset_rsubterm_closure
  card_raw_shared_prune_active_suffix_keys_le_rsubterm_closure
  card_raw_shared_prune_active_suffix_key_dag_le_rsubterm_closure
  ```

- Added step-local owner names in `AntimirovFactoredTransition.thy`:

  ```text
  afactored1_strong_dlform_universe_owner_active_suffix_keys_subset_owner_dag
  afactored1_strong_dlform_universe_owner_active_suffix_key_dag_subset_owner_dag
  card_afactored1_strong_dlform_universe_owner_active_suffix_keys_le_owner_dag
  card_afactored1_strong_dlform_universe_owner_active_suffix_key_dag_le_owner_dag
  ```

- Plain meaning: active suffix keys are subterms of the rows that expose them.
  Therefore the key set, and the key-DAG formed from those keys, are already
  inside the owner DAG `rsubterm_closure (raw_shared_prune_active_suffix_owner
  U)`.  This packages the requested key-DAG projection step.
- This does not yet prove the owner DAG itself is cubic.  It reduces owner
  key-count/key-DAG count to the owner-DAG cardinality problem, instead of
  letting keys become a separate unbounded budget.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed, finishing `Posix` at 2026-06-12 03:11:24 local time.

## 2026-06-12 Supervisor Checkpoint: owner DAG size budget packaged

- Added checked step-local owner-DAG member-size and conditional `rsize_set`
  bounds:

  ```text
  afactored1_strong_dlform_universe_owner_dag_member_size_le_generated_rsizes
  afactored1_strong_dlform_universe_owner_dag_member_size_le_list_cost
  rsize_set_afactored1_strong_dlform_universe_owner_dag_generated_boundI
  rsize_set_afactored1_strong_dlform_universe_owner_dag_list_boundI
  ```

- Plain meaning: every node inside the owner DAG has size bounded by the same
  generated/list budget as the original step-local universe.  Therefore, once a
  finite cardinality bound `card owner_dag <= C` is proved, Isabelle now gives
  `rsize_set owner_dag <= C * M`.
- This deliberately does not claim the owner DAG is cubic yet.  It removes the
  separate size-budget obligation so the remaining hard task is the owner-DAG
  finiteness/cardinality argument itself.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed, finishing `Posix` at 2026-06-12 03:15:33 local time.

## 2026-06-12 Supervisor Checkpoint: owner DAG finite via sizeNregex

- Added general owner-DAG/`sizeNregex` closure facts in
  `GeneralRegexBound.thy`:

  ```text
  raw_shared_prune_active_suffix_owner_dag_sizeNregex_subset
  finite_raw_shared_prune_active_suffix_owner_dag_sizeNregex
  ```

- Added step-local names in `AntimirovFactoredTransition.thy`:

  ```text
  rsimpStrong_dlform_closure_member_legacy
  afactored1_strong_dlform_universe_member_legacy
  afactored1_strong_dlform_universe_subset_sizeNregex_generatedI
  afactored1_strong_dlform_universe_subset_sizeNregex_listI
  afactored1_strong_dlform_universe_owner_dag_subset_sizeNregex_generatedI
  afactored1_strong_dlform_universe_owner_dag_subset_sizeNregex_listI
  finite_afactored1_strong_dlform_universe_owner_dag_generatedI
  finite_afactored1_strong_dlform_universe_owner_dag_listI
  ```

- Plain meaning: if the one-step universe `U` consists of old/non-backref
  regexes and all its rows have size at most `N`, then the least owner DAG
  generated from `U` is also contained in the finite set `sizeNregex N`.
  Therefore Isabelle can now discharge finite-owner-DAG side conditions from
  the generated/list row-size budgets.
- This deliberately does not prove the owner DAG has cubic cardinality.
  `sizeNregex N` is a finite but very large ambient set; using
  `card (sizeNregex N)` as the final count would lose the desired cubic
  bound.  The remaining hard task is still to count owner-DAG nodes sharply,
  probably through the owner sequence decomposition and same-key bucket
  structure.
- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed, finishing `Posix` at 2026-06-12 03:23:21 local time.

## 2026-06-12 Fable URGENT: owner closure cardinality is exponential (claim + construction)

- Before more effort goes into "card (owner DAG) <= cubic": the abstract
  least-owner closure `raw_shared_prune_active_suffix_owner U` admits an
  EXPONENTIAL lower bound in `card U`.  Construction (syntactic, uses
  only `rprune_eq_against` equality filtering, verified against the
  definitions at GeneralRegexBound.thy:17015 and 18163):

  ```text
  atoms a_1..a_m, b, c1, c2, k pairwise distinct
  L   = RSEQ (RALTS [a_1, ..., a_m, c1, c2, b]) k
  E_i = RSEQ (RALTS [a_i, b]) k          (i = 1..m)
  U_m = {L, E_1, ..., E_m}               (card U_m = m + 1)
  ```

  Pruning L (or any of its pruned variants, which stay in the owner set)
  against E_i deletes exactly {a_i, b} from the alternative list; the
  reserved c1, c2 keep every variant RALTS-headed with key k.  Chaining
  prunes reaches the filtered row for EVERY nonempty S of {a_1..a_m}:
  2^m - 1 pairwise distinct owner members from m + 1 starting rows.
- Consequence: any owner-DAG cardinality bound parameterized only by
  `card U` and member sizes is false.  A cubic owner bound must either
  (i) exploit step-local provenance that excludes such bucket patterns
  (note dlform splitting CAN produce many same-key rows, so this needs a
  real invariant), or (ii) replace the all-pairs owner closure by a
  smaller object: the order-respecting one-pass pruning closure
  (matching what rsimpStrong_prune_rows_raw actually computes, linear
  output per pass) or the coverage-saturated rows.  This is the same
  "arbitrary all-pairs closure" trap the original route-2 handoff text
  warned about.
- Fable is now adding the checked parametric counterexample
  (`2 ^ m <= Suc (card (raw_shared_prune_active_suffix_owner U_m))`)
  in AntimirovFactoredTransition.thy, then stopping per handoff rule 3.
- Suggested redirect after the check: define the step-local closure as
  the ONE-PASS accumulated pruning (mirroring
  rsimpStrong_prune_rows_acc_raw), whose output count is bounded by the
  input row count, and re-target the FBound closed-universe premise at
  that object; the carrier/grammar/owner-DAG size packaging all reuse.

## 2026-06-12 Supervisor Response: redirect away from generic owner counting

- The Fable construction above is route-relevant: `raw_shared_prune_active_suffix_owner`
  is an abstract transitive all-pairs closure, while the executable simplifier
  performs an accumulated one-pass pruning over a concrete row list.
- Therefore, do not try to prove a generic polynomial/cardinality bound for
  `raw_shared_prune_active_suffix_owner U` from only `card U` and row-size
  budgets.  Such a theorem is now suspect unless the construction is formally
  refuted.
- Viable next steps are narrower:

  ```text
  1. formalize the exponential abstract-owner counterexample and stop;
  2. prove a step-local invariant showing afactored1_strong_dlform_universe
     cannot realize that same-key filtered-subset construction;
  3. replace the abstract owner closure in the route with a one-pass
     accumulated-pruning universe matching rsimpStrong_prune_rows_acc_raw.
  ```

- The Fable handoff has been updated at the top and in "Best Next Attack" so
  this correction is visible before another session starts.

## 2026-06-12 Fable Coordination: duplicate owner-CE implementations in flight

- Fable build at 03:32 failed INSIDE the supervisor uncommitted WIP at
  GeneralRegexBound.thy line ~26145: a lemma applies the rexp-language
  operator `L` to an `rrexp` row (type clash; should be `RL`).  That WIP
  appears to implement the same owner-exponential construction Fable
  claimed in the URGENT note and has now fully written in
  `AntimirovFactoredTransition.thy` (worktree, awaiting a build slot):

  ```text
  theorem raw_shared_prune_active_suffix_owner_exponential
    (parametric m; atoms are RSTAR-towers so no char supply limit;
     shows: 2^m - 1 distinct owner members from m+1 seed rows,
     injection + card facts, card UU <= Suc m)
  ```

- Per the lock-or-lose convention the claim note at 03:25 covers this
  task.  Request: supervisor please either revert/park the
  GeneralRegexBound WIP so the tree parses, or finish it quickly with
  `RL`; Fable cannot build while GeneralRegexBound is broken.  Happy
  for the supervisor version to win instead if it lands first and is
  general (parametric m, not fixed small m) - in that case Fable drops
  the worktree version.

## 2026-06-12 Fable Note: ceding in-flight CE repair to supervisor

- The 04:02 build gave the first real feedback on
  `raw_shared_prune_active_suffix_owner_exponential`: only the final
  rflts-singleton steps in calc_base/calc_step failed (defines
  folding), everything else checked.  The supervisor is already
  mid-rewrite in-tree with the same fix shape (`rowf_flat`).  Fable
  stops editing this theorem now to avoid edit collisions and will
  harvest the result next cycle.  If any remaining step needs the
  original derivation rationale: prune_core needs the pruned list in
  2-cons form (hence the reserved cc1/cc2), and the membership
  induction is finite_ne_induct with EE j as the earlier row at every
  step.

## 2026-06-12 Supervisor Checkpoint: abstract owner exponential CE checked

- Finished and checked Fable's parametric theorem:

  ```text
  raw_shared_prune_active_suffix_owner_exponential
  ```

- Plain meaning: for every `m`, there is a seed set `UU` with
  `card UU <= Suc m` whose abstract active-suffix owner closure contains
  `2^m - 1` distinct filtered rows.  The construction uses RSTAR-tower atoms,
  so it is not limited by the finite `char` supply.
- Also added a small fixed witness in `GeneralRegexBound.thy`:

  ```text
  raw_shared_prune_active_suffix_owner_filtered_subsets_3
  ```

  It shows the same mechanism concretely: four same-key seed rows generate
  seven filtered variants inside the abstract owner closure.
- Consequence: the generic target "prove a cubic/polynomial cardinality bound
  for `raw_shared_prune_active_suffix_owner U`" is dead unless restricted by a
  strong step-local invariant.  The productive route now is either:

  ```text
  1. prove afactored1_strong_dlform_universe cannot realize this same-key
     filtered-subset pattern; or
  2. replace the abstract all-pairs owner closure with a one-pass accumulated
     pruning universe matching rsimpStrong_prune_rows_acc_raw.
  ```

- Verification:

  ```powershell
  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
  ```

  passed, finishing `Posix` at 2026-06-12 04:07:52 local time.

## 2026-06-12 Fable Checkpoint + Claim: one-pass universe design (route-2 option 2)

- Checkpoint: the abstract owner exponential CE is checked and pushed
  (`raw_shared_prune_active_suffix_owner_exponential`, supervisor commit
  `cd1afcc`, joint work: Fable construction/proof skeleton, supervisor
  final repair).  Abstract owner counting is closed as a dead end.
- Claim: Fable takes supervisor option 2, the one-pass accumulated
  pruning universe.  Design, stated before editing:
  1. The production step is already one-pass:
     `rpder_strong_rows_raw c rs = rdistinct (rflts
     (rsimpStrong_prune_rows_raw (rflts (concat (map
     (rpder_strong_list_raw c) rs))))) {}` and
     `rsimpStrong_prune_rows_raw = rsimpStrong_prune_rows_acc_raw []`
     with the checked fact `length (acc_raw seen rs) = length rs`.
  2. New step-local object (AntimirovFactoredTransition.thy):
     `afactored1_strong_one_pass_rows r s c =
        rpder_strong_rows_raw c (afactored1 r s)`
     and its set/universe.  No closure is taken: counting flows from
     the generated-row count of the current front, so the exponential
     owner trap cannot arise by construction.
  3. First brick lemmas: (a) card (set one_pass) <= length of the
     pruned generated list, via rdistinct/rflts/length lemmas; (b)
     carrier: aseq atoms of every member stay in
     strong_derivative_front_terms r (s @ [c]), reusing
     aseq_termss_rsimpStrong_prune_rows_acc_raw_subsetI and the
     generated-row carrier facts; (c) grammar: members are
     rtail_nf/nonalt/nonzero via the checked pair-output and
     rflts/rfrontier member-props lemmas.
  4. Intended FBound correspondence (statement-level, admin to
     approve): replace the raw_shared_prune_closed U premise group by
     per-step trace bounds on rpders_strong_rows_raw: the universe is
     the union of per-step output sets; the remaining mathematical
     content is the per-step size/count recursion on the honest
     one-pass object, where prune/distinct/flts only shrink and growth
     comes solely from rpder_norm_list, i.e. the same-front budget.
- Next cycle implements brick (a)-(c); supervisor input welcome on
  whether the step-local object should instead be defined directly on
  the strong row trace (rpders_strong_rows_raw) rather than the plain
  front.

## 2026-06-12 Fable Checkpoint: one-pass universe first brick checked

- New checked definitions and lemmas in `AntimirovFactoredTransition.thy`:

  ```text
  afactored1_strong_generated_rows  (rflts of strong-simplified
                                     norm-derivative rows off the front)
  afactored1_strong_one_pass_rows   (= rpder_strong_rows_raw c (afactored1 r s))
  afactored1_strong_one_pass_rows_eq
  length_prune_afactored1_strong_generated_rows
  card_afactored1_strong_one_pass_rows_le
  aseq_termss_afactored1_strong_generated_rows_subset_front
  aseq_termss_afactored1_strong_one_pass_rows_subset_front
  ```

- Meaning: the route-2 step object is now named as the honest one-pass
  pruning output.  Its row count is tied to the generated list length
  (accumulated pruning preserves length; rdistinct only shrinks), and
  ALL atoms of generated and one-pass rows live in the checked cubic
  carrier `strong_derivative_front_terms r (s @ [c])` with no closure
  taken, so the exponential owner trap cannot arise by construction.
- Build: `Finished Posix` at 2026-06-12 05:09:17
  (`AntimirovFactoredTransition` 57.2s cumulated); proof-workers clean.
- Next bricks: (c) member grammar (rtail_nf/nonalt/nonzero) for
  one-pass members via prune-against-rows rtail_nf preservation;
  then the count side: length (afactored1_strong_generated_rows) in
  terms of the front row budget, and the per-step rsizes recursion
  (prune/distinct/flts shrink; growth only from rpder_norm_list).

## 2026-06-12 Fable Checkpoint: one-pass universe member grammar checked

- New checked lemmas in `AntimirovFactoredTransition.thy`:

  ```text
  rflts_singleton_member_rtail_nf_props
  afactored1_strong_generated_rows_member_rtail_nf_props
  afactored1_strong_one_pass_rows_member_rtail_nf_props
  ```

- Meaning: every generated row and every one-pass output row is
  tail-normal, nonalt and nonzero.  Together with the carrier facts
  from the previous brick, the one-pass step object now has the same
  checked grammar as the old dlform universe (head in carrier when
  nonalt, atoms always in carrier) but with construction-level
  immunity to the exponential owner-closure trap.
- Build: `Finished Posix` at 2026-06-12 05:39:10 first try
  (`AntimirovFactoredTransition` 60.7s); proof-workers clean.
- Remaining for the one-pass route: the count side,
  `length (afactored1_strong_generated_rows r s c)` against the front
  row budget (rpder_norm_list lengths under legacy), then the per-step
  rsizes recursion, then the FBound statement-level switch from the
  raw_shared_prune_closed premise group to per-step trace bounds
  (admin approval needed for FBound edits).

## 2026-06-12 Supervisor Note: next one-pass count target

- Fable's new one-pass route is aligned and checked: it is using the actual
  `rsimpStrong_prune_rows_acc_raw` production path, not the dead abstract
  owner closure.
- Small caveat for the next count brick: do not silently treat the final
  `rflts` in

  ```text
  rdistinct (rflts (rsimpStrong_prune_rows_raw generated)) {}
  ```

  as length-shrinking.  The current checked lemma
  `card_afactored1_strong_one_pass_rows_le` only bounds by
  `length (rflts (rsimpStrong_prune_rows_raw generated))`, not yet by
  `length generated`.
- The safer next theorem shape is to charge through frontier/size accounting:

  ```text
  card (set (afactored1_strong_one_pass_rows r s c))
    <= rsizes (afactored1_strong_generated_rows r s c)
  ```

  or an equivalent `rsize_set`/`rfrontiers` version.  Existing handles to try:
  `card_rfrontiers_le_rsizes`, `rfrontiers_rflts`,
  `rsizes_rsimpStrong_prune_rows_raw_le`, and
  `length_prune_afactored1_strong_generated_rows`.
- After that, bound `rsizes (afactored1_strong_generated_rows r s c)` by the
  front-row derivative budget.  Avoid detouring into another finite-universe
  wrapper; the useful unlock is a per-step numeric count/size bound for the
  honest one-pass rows.

## 2026-06-12 Supervisor Checkpoint: one-pass card charged to generated rsizes

- Added and checked:

  ```text
  card_afactored1_strong_one_pass_rows_le_generated_rsizes
  ```

- Meaning: the one-pass output count is now charged through
  `rfrontiers`/`rsizes`, not through the misleading length of the final
  `rflts`.  Formally:

  ```text
  card (set (afactored1_strong_one_pass_rows r s c))
    <= rsizes (afactored1_strong_generated_rows r s c)
  ```

- Proof route: every one-pass output row is already checked nonzero/nonalt, so
  it belongs to its own `rfrontier`; `rfrontiers_rdistinct_empty` and
  `rfrontiers_rflts` erase the final `rdistinct/rflts` wrappers; then
  `card_rfrontiers_le_rsizes` plus `rsizes_rsimpStrong_prune_rows_raw_le`
  charges the count back to generated rows.
- Verification: full `Posix` build passed at 2026-06-12 05:53:01 local time.
- Next brick: bound `rsizes (afactored1_strong_generated_rows r s c)` by the
  derivative/front-row budget for `afactored1 r s`.

## 2026-06-12 Fable Checkpoint: one-pass count side, step 1

- New checked lemmas (AntimirovFactoredTransition.thy), plain meaning:
  every front row is legacy (`legacy_afactored1_rows`), and the total
  size of one derivative step's generated rows is at most the sum of
  `2*(rsize q+3)^3` over the current front rows
  (`rsizes_afactored1_strong_generated_rows_le_front_cubic_sum`).
  Combined with the supervisor's in-tree
  `card_afactored1_strong_one_pass_rows_le_generated_rsizes` (checked
  in the same build), the one-pass row count is now bounded by a sum
  of per-front-row cubes - a purely numeric per-step bound with no
  closure object anywhere.
- Build: `Finished Posix` 05:54:13.
- Continuing immediately (no idle): next is the closed-form version -
  bound the per-row cube sum by front row count times the cube of the
  max row size, then plug the checked front budgets
  (`afactored1_apder_rows_expanded_cubic_budget`) to get a bound in r
  only.  Note the admin added 20k simulated USD to the pool for the
  final cubic theorem and major progress leading to it; board update
  is for the admin/steward to record formally in BACKREF_BOUNTIES.md.

## 2026-06-12 Fable Checkpoint: first unconditional per-step count bound in r only

- New checked lemmas:

  ```text
  sum_front_cubes_le_length_times_total
  card_afactored1_strong_one_pass_rows_root_budget
  ```

- Plain meaning: under legacy + apder_nf, one derivative step of the
  one-pass route produces at most
  `2*B^3 * (2*(2*B^3+3)^3)` distinct rows, where
  `B = apder_awidth r + rsize r + 3`.  This is the first end-to-end
  numeric bound depending only on r, with no closure object and no
  unproved premise.
- Honest assessment: the bound is crude (around B^12).  The loss is in
  one specific step: bounding every front row size by the front TOTAL
  size before cubing.  Tightening means using per-row budgets
  (front members sit in apder_rows r, whose member sizes have checked
  square bounds), which would give roughly B^3 * (B^2+3)^3 ~ B^9, and
  the real cubic target needs the same-front sharing argument on top.
  The chain to tighten is now fully explicit and numeric:
  card one_pass <= rsizes generated <= sum of per-front-row cubes
  <= (count) * (max row)^3.
- Build: `Finished Posix` 05:58:50.  Continuing immediately with the
  per-row tightening (replace total-size by the checked apder_rows
  member square bound).

## 2026-06-12 Supervisor Correction: do not use length-times-total-cube

- The claimed unconditional root-only count bound above is checked, but it is
  not a useful route to the cubic theorem.  The bound is structurally too
  loose: replacing each row size by the total front size before cubing changes
  the target from cubic-size accounting into a high-degree bound.
- Removed `sum_front_cubes_le_length_times_total` and
  `card_afactored1_strong_one_pass_rows_root_budget` from
  `AntimirovFactoredTransition.thy` so future workers do not optimize around
  the wrong numeric shape.
- Added the checked bridge
  `afactored1_strong_one_pass_rows_lform_universe_cubic_contractI`, which says
  the named one-pass object is exactly the existing
  `rpder_strong_rows_raw c (afactored1 r s)` object for purposes of the
  lform-universe cubic contract.
- Plain meaning: one-pass rows should now be bounded by reusing the already
  proven lform/dlform/row-normal cubic interfaces for the production raw row
  pipeline.  Do not try to prove cubic by bounding
  `sum (2*(rsize q+3)^3)` with `length * (total size)^3`; that loses the
  necessary sharing before the proof even reaches the final theorem.
- Verification: full `Posix` build passed at 2026-06-12 06:03:30 local time.

## 2026-06-12 Fable: accepted correction; next gap located (payload stability)

- Accepted the supervisor correction: the length-times-total-cube bound
  was the wrong numeric shape; dropped without protest (reason
  recorded).  The route now runs through the supervisor interface
  `afactored1_strong_one_pass_rows_lform_universe_cubic_contractI`,
  whose open premises are: disjoint / live / paid / lforms-subset /
  cubic rsize_set of `afactored1_strong_lform_universe`.
- Next concrete gap, located: the lforms-subset premise follows from
  `row_lformss_rpder_strong_rows_raw_afactored1_subset_lform_universe_payload_stableI`
  (line ~17252) IF every member of a keyed generated row satisfies
  `row_payload_lform_stable`.  So the next theorem to prove is:
  members of keyed rows output by `rsimpStrong_raw` on generated rows
  are payload-lform-stable (or a checked counterexample if false).
  After that: disjoint/live/paid for one-pass rows, then the remaining
  cubic rsize_set premise (the same-front sharing core).
- Context handover: this Fable session is at its context limit; the
  next session continues from exactly this gap.  Plain summary of the
  day so far: two false inequalities refuted (multiplicative left side
  vs additive right side, NTIMES); the NTIMES-free version proved; the
  abstract owner closure proven exponential; the one-pass object
  defined with checked count/carrier/grammar facts; bounty +20k noted
  for the final theorem.

## 2026-06-12 Supervisor: tight dcanon budget brick

- New checked lemmas:

  ```text
  rsizes_row_dlform_canonical_rows_tight_rsize_set_boundI
  rsizes_rpder_strong_dcanon_rows_raw_tight_rsize_set_boundI
  rsizes_rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_tight
  rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_tight_cubic_contractI
  rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_tight_cubic_budgetsI
  ```

- Plain meaning: after one strong derivative step, the dcanon route
  canonicalizes the row list, meaning duplicates are removed and the list is
  exactly the set of row-dlform pieces.  Therefore its `rsizes` budget is
  paid directly by `rsize_set U`, not by the older coarse `3 * rsize_set U`
  live/paid estimate.
- Concrete payoff: if the remaining universe
  `U = afactored1_strong_dlform_universe r s c` has
  `rsize_set U <= 2 * (rsize r + 3)^3`, then the produced dcanon row list has
  length/card/rlinear/rsizes all bounded by the same
  `2 * (rsize r + 3)^3`.  Earlier dcanon interfaces only exposed a
  `6 * (rsize r + 3)^3` budget from the same premise.
- Guidance for Fable: do not spend more time on all-pairs owner closure,
  length-times-total-cube, or broad lform/dlform wrappers.  The real missing
  statement is still the size of `U`: show the row-dlform universe created by
  this one strong derivative step has cubic `rsize_set`, or find a checked
  counterexample.  The tight dcanon lemmas mean no extra factor is lost after
  that universe bound is proved.
- Verification: full `Posix` build passed at 2026-06-12 06:20:50 local time.

## 2026-06-12 Supervisor: payload-stability caveat hardened

- New checked diagnostics:

  ```text
  row_nf_does_not_imply_payload_lform_stable
  rtail_nf_does_not_imply_payload_lform_stable
  shared_suffix_payload_stability_side_condition_not_shape_automatic
  ```

- Plain meaning: `row_payload_lform_stable p` is not a consequence of
  ordinary row normal form, tail normal form, or merely seeing a later row of
  the shape `RSEQ (RALTS rrs) k`.  It requires a real generated-payload
  invariant.
- Guidance for Fable: do not try to prove the lform-subset premise by
  splitting on row shape plus `row_nf`/`rtail_nf`; that is a checked dead end.
  The lform route is only live if one proves that actual generated payloads
  are produced in a stronger stable form, or changes the simplifier so they
  are.  Otherwise prefer the dcanon/dlform route and attack the remaining
  cubic `rsize_set` bound for `afactored1_strong_dlform_universe`.
- Verification: full `Posix` build passed at 2026-06-12 06:27:14 local time.

## 2026-06-12 Supervisor: tight lform canonical budget brick

- New checked lemmas:

  ```text
  rsizes_row_lform_canonical_rows_tight_rsize_set_boundI
  row_lform_canonical_rpder_strong_rows_raw_afactored1_lform_universe_tight_cubic_contractI
  ```

- Plain meaning: `row_lform_canonical_rows` is also a duplicate-free list whose
  set is exactly `row_lformss`.  Once its lforms lie in a universe `U`, its
  `rsizes` is paid directly by `rsize_set U`; it does not need the older
  live/paid estimate `3 * rsize_set U`.
- Concrete payoff: the canonical lform route now has a checked
  `2 * (rsize r + 3)^3` size contract from the same lform-universe cubic
  premise where the older interface exposed `6 * (rsize r + 3)^3`.
- Verification: full `Posix` build passed at 2026-06-12 06:30:40 local time.

## 2026-06-12 Supervisor Probe: nested-NTIMES one-step dlform size

- Ran a scratch Isabelle `Probe` session (not committed) for
  `X = (a | (1*)).1` and `r = NTIMES (NTIMES X n) n`, measuring:

  ```text
  (rsize, apder_awidth, rsize_set one_step_U, 2*(rsize+3)^3)
  n=2:  (12, 4,   14,   6750)
  n=4:  (16, 16,  20,   13718)
  n=8:  (24, 64,  32,   39366)
  n=16: (40, 256, 56,   159014)
  ```

- Also measured the same `n=16` row after consuming `t` copies of `a`:

  ```text
  (t, rsize, apder_awidth, rsize_set one_step_U, budget)
  t=0:  (0,  40, 256, 56,   159014)
  t=1:  (1,  40, 256, 110,  159014)
  t=2:  (2,  40, 256, 217,  159014)
  t=4:  (4,  40, 256, 582,  159014)
  t=8:  (8,  40, 256, 1860, 159014)
  t=16: (16, 40, 256, 6080, 159014)
  ```

- Interpretation: this cheap nested-NTIMES family does NOT refute the
  rsize-only one-step dlform-universe premise.  The suspicion from missing
  `apder_awidth` remains worth investigating, but it is not yet evidence of a
  false theorem.  Next probe, if needed, should use a family with many
  distinct zero-awidth payload branches and test later positions, not only this
  star-reentry smoke case.

## 2026-06-12 Fable: the remaining premise lacks awidth - suspect, needs one probe

- Target premise: rsize_set (afactored1_strong_dlform_universe r s c)
  <= 2*(rsize r+3)^3.  Note the right side has NO apder_awidth term.
- Simple reason for suspicion: the checked bound on the number of front
  rows is 2*(apder_awidth r + rsize r + 3)^3, and nested RNTIMES makes
  apder_awidth quadratic in rsize (awidth(NTIMES (NTIMES a k) m) = k*m,
  rsize ~ k+m).  So the front feeding one step can be far larger than
  any function of rsize alone, and the step universe contains at least
  one dlform per generated row.  Unless strong simplification collapses
  the row count back below rsize-only cubic, the premise is false on
  the full fragment, for the same multiplicative-vs-additive reason as
  the two refuted inequalities earlier today.
- The existing ID/DAG smoke measured shared/DAG metrics, which can stay
  small while the tree-level rsize_set grows.  Request to supervisor
  (or next Fable cycle): add one metric to the nested-NTIMES probe that
  prints rsize_set of the ONE-STEP dlform universe (sum of distinct
  dlform tree sizes for a single derivative step at several input
  positions) against 2*(rsize+3)^3, on the star-reentry nested-NTIMES
  family with awidth >> rsize (e.g. NTIMES (NTIMES X 16) 16).  If the
  ratio crosses 1, the premise needs an awidth term (interfaces should
  switch to (apder_awidth+rsize+3)^3 shapes) or NTIMES exclusion; if it
  stays low, the collapse mechanism is real and worth finding as the
  proof idea.
- This is one cheap executable check before anyone invests in proving
  or hand-refuting the premise.

## 2026-06-12 Fable: probe trend says keep going - extend t to the full grid

- Thanks for the probe.  The absolute values are small, but the TREND
  is the point: rsize and budget are constant in t (40 / 159014), while
  the one-step universe size grows with every consumed character:

  ```text
  t:        0    1    2    4    8    16
  size:     56   110  217  582  1860 6080   (x2.5-3 per doubling of t)
  ```

  The counter grid for n=16 has path length about n^2 = 256, and t was
  only tested to 16.  Extrapolating the observed growth, the size
  crosses the fixed budget 159014 somewhere around t = 128..256 -
  within the reachable range.  So this family may well refute the
  premise after all; the probe just stopped early.
- Request: rerun the same Probe session with
  t in {32, 64, 128, 192, 256} (and n=16), printing the same tuple.
  Three outcomes: crosses 1 -> premise false as stated, switch budgets
  to awidth form or exclude NTIMES; plateaus below -> the collapse is
  real, and the plateau position tells us what invariant to prove;
  machine cannot reach t=128 -> record the boundary honestly.
- If the supervisor does not rerun within this cycle, Fable will
  reproduce the scratch Probe theory next cycle and run it.
