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

## Retraction: Do Not Treat `aseq_terms` As Stage One

- The old "first-step target" phrasing around
  `rders_pder_norm_split_aseq_termss_frontier_universe_subset` was wrong.
  That theorem is checked, but it proves only a split-atom inclusion after
  opening products with `aseq_terms`.
- `aseq_terms` is too fine for the user's Antimirov decomposition: it opens
  every `RSEQ`.  For examples like `a(aa)` it collapses the relevant whole
  residuals to `{a}`, while the Antimirov frontier must retain terms such as
  `a(aa)`, `aa`, and `a`.
- The corrected first-stage proof obligation is now checked: after normal
  partial derivatives, the normal Antimirov frontier terms themselves lie in
  the root-owned residual frontier
  `apder_frontier r`.  The theorem is
  `rfrontier_rders_pder_norm_subset_apder_frontier`, assuming `apder_nf r`,
  and it uses the checked bridge
  `rfrontier (rders_pder_norm r s) = ader_front r s`.
- Do not use `row_dlforms` as the first-stage splitter either.  It recursively
  opens rows such as `RSEQ (RALTS ps) k`, so it belongs to the later
  canonical/prune accounting, not to the normal derivative frontier theorem.
  The guard examples `apder_frontier_keeps_whole_residuals_a_aa` and
  `apder_frontier_keeps_whole_residuals_a_alt_tail` are checked to prevent
  this mistake from coming back.
- The proof must keep the "same derivative front" restriction; plain closure
  for arbitrary members of a coarse universe is false.
- The next first-stage budget task is polynomial accounting for
  `apder_frontier r` itself, or a checked equivalent path-frontier universe;
  the old `partial_derivative_frontier_universe r` is too small for whole
  multi-suffix residuals such as `b d c`.

### 2026-06-08 Checked Update: Whole-Residual Frontier Budget

- `AntimirovFactoredTransition.thy` now has the checked stage-one budget for
  the corrected whole-residual Antimirov frontier:

  ```text
  rfrontier (rders_pder_norm r s) subset apder_frontier r
  rsize_set (rfrontier (rders_pder_norm r s))
    <= (apder_awidth r + rsize r + 3)^3
  card (rfrontier (rders_pder_norm r s))
    <= (apder_awidth r + rsize r + 3)^3
  ```

  The theorem names are
  `rfrontier_rders_pder_norm_subset_apder_frontier`,
  `rfrontier_rders_pder_norm_expanded_cubic_size_bound`, and
  `rfrontier_rders_pder_norm_expanded_cubic_card_bound`.
- `apder_awidth` expands counted repetition:
  `apder_awidth (RNTIMES r n) = n * apder_awidth r`.  Do not rewrite this
  update as a compressed-`rsize` cubic theorem.  Nested counted repetitions
  can make the unnormalized whole-residual frontier grow too fast relative to
  the current compressed `rsize`.
- The next step is a same-front linear-form/canonical-row bridge.  Do not try
  to prove `row_dlforms subset apder_frontier`: for `(a+b)c`, linear forms can
  produce `ac`/`bc`, while the whole-residual frontier stores `(a+b)c` and
  `c`.
- The first checked bridge for that next step is now present:

  ```text
  apder_lfrontier r =
    Union q in apder_rows r. row_lforms q

  alform_front r s subset apder_lfrontier r
  ```

  under `apder_nf r`.  The theorem is
  `alform_front_subset_apder_lfrontier`.
- Supporting size facts are checked:

  ```text
  rsize_set (row_lforms q) <= (rsize q)^2
  rsize_set (apder_lfrontier r) <= (rsize_set (apder_rows r))^2
  ```

  via `rsize_set_row_lforms_le_square` and
  `rsize_set_apder_lfrontier_le_square_rows`.  This is only a scaffold; it
  mixes all fronts and therefore is too coarse to be the final cubic theorem.
- `AntimirovNormalFrontier.thy` is now the dedicated file for the corrected
  normal-frontier route.  Checked theorem names there include
  `normal_derivative_frontier_subset`,
  `normal_derivative_frontier_cubic_size`,
  `normal_factored_rows_contract`, and the guard examples
  `normal_frontier_keeps_whole_residuals_a_aa` /
  `normal_frontier_keeps_whole_residuals_a_alt_tail`.
- 2026-06-08 checked update: the pure normal/factored route now has a
  regex-level cubic theorem.  The definition
  `normal_canonical_derivative r s` is

  ```text
  rsimp_ALTs
    (normal_frontier_canonical_rows (afactored1 r s))
  ```

  and `normal_canonical_derivative_cubic_contract` proves, under
  `legacy_rrexp r` and `apder_nf r`,

  ```text
  RL (normal_canonical_derivative r s) = Ders s (RL r)
  rfrontier (normal_canonical_derivative r s)
    subset normal_antimirov_frontier r
  rsize (normal_canonical_derivative r s)
    <= Suc ((apder_awidth r + rsize r + 3)^3)
  ```

  `normal_canonical_derivative_exact_frontier_contract` proves the
  no-duplicate/canonical part:

  ```text
  rfrontier (normal_canonical_derivative r s)
    = set (normal_frontier_canonical_rows (afactored1 r s))
  distinct (normal_frontier_canonical_rows (afactored1 r s))
  card (rfrontier (normal_canonical_derivative r s))
    <= (apder_awidth r + rsize r + 3)^3
  ```

  This is the completed pure Antimirov/factored canonical derivative theorem.
  It does not close the final strong/memo POSIX route below.
- 2026-06-08 follow-up: the same-front invariant has also been made explicit.
  New checked theorem names:

  ```text
  normal_canonical_derivative_frontier_eq_ader_front
  normal_frontier_canonical_rows_same_front
  normal_canonical_derivative_same_front_row
  normal_canonical_derivative_equiv_rders_pder_norm
  normal_canonical_derivative_main_cubic_bound
  rsimpStrong_raw_normal_canonical_derivative_cubic_contract
  ```

  The central equality is

  ```text
  rfrontier (normal_canonical_derivative r s) = ader_front r s
  ```

  so the canonical derivative is tied to the single derivative front indexed by
  `s`; it is not an arbitrary subset of the global frontier universe.
- 2026-06-08 checked wrapper: the clean
  normal-canonical-then-strong-simplify route also has a cubic regex bound.
  The theorem is `normal_canonical_then_strong_main_cubic_bound`:

  ```text
  RL (rsimpStrong_raw (normal_canonical_derivative r s))
    = RL (rders_pder_norm r s)
  RL (rsimpStrong_raw (normal_canonical_derivative r s))
    = Ders s (RL r)
  rsize (rsimpStrong_raw (normal_canonical_derivative r s))
    <= Suc ((apder_awidth r + rsize r + 3)^3)
  ```

  This is a completed theorem for the clean canonical derivative route, not
  the final raw/memo strong-row POSIX theorem.
- The first raw strong-row bridge is checked:

  ```text
  set (rpder_strong_rows_raw c (afactored1 r s))
    subset normal_strong_scan_owner r

  forall x in that set.
    rsize x <= 2 * (apder_awidth r + rsize r + 3)^3
  ```

  See `rpder_strong_rows_raw_afactored1_subset_normal_strong_scan_owner`,
  `rpder_strong_rows_raw_afactored1_member_cubic`, and
  `rpder_strong_rows_raw_afactored1_normal_owner_contract`.
- The total raw-row budget is intentionally parameterized:
  `rpder_strong_rows_raw_afactored1_owner_card_budget_contract` proves
  language correctness and `length/card/rlinear_termss/rsizes` bounds assuming

  ```text
  card (normal_strong_scan_owner r) <= C
  ```

  This isolates the raw-row counting gap.  Do not discharge it with
  `sizeNregex`; that is finite but much too large.
- 2026-06-08 checked strengthening: raw strong rows from `afactored1 r s`
  now have a direct step-local deep-linear-form universe inclusion:

  ```text
  row_dlformss (rpder_strong_rows_raw c (afactored1 r s))
    subset afactored1_strong_dlform_universe r s c
  ```

  The theorem is
  `row_dlformss_rpder_strong_rows_raw_afactored1_subset_strong_dlform_universe`;
  it has no `apder_nf r` premise.  The older inclusion into
  `apder_strong_dlfrontier r` now factors through this local theorem.
- The canonical second-stage same-front part is checked:
  `rpder_strong_dcanon_afactored1_same_front_contract` proves

  ```text
  same_strong_aseq_front_rows r (s @ [c])
    (rpder_strong_dcanon_rows_raw c (afactored1 r s))

  aseq_termss (rpder_strong_dcanon_rows_raw c (afactored1 r s))
    subset strong_derivative_front_terms r (s @ [c])
  ```

  and gives cubic card/`rsize_set` bounds for
  `strong_derivative_front_terms r (s @ [c])`.
- The canonical cubic budget is now reduced to one explicit universe estimate.
  `rpder_strong_dcanon_afactored1_dlform_cubic_interface` proves that if

  ```text
  rsize_set (afactored1_strong_dlform_universe r s c)
    <= 2 * (rsize r + 3)^3
  ```

  then `rpder_strong_dcanon_rows_raw c (afactored1 r s)` is language-correct,
  `row_dlformss_disjoint`, live, size-paid, preserves the raw rows'
  `row_dlformss`, and has cubic `length`, `card`, `rlinear_termss`, and
  `rsizes` budgets.
- Remaining focused gap: prove that
  `afactored1_strong_dlform_universe` has the above cubic `rsize_set` bound
  using same-front combination counting.  Direct subset into
  `apder_frontier` or `partial_derivative_frontier_universe` is false; keep
  `afactored1_strong_dlform_universe_not_frontier_subset` visible as a guard.
- 2026-06-08 checked update: the deep-row accumulator now has a delta route
  that subtracts the already-owned suffix frontier before recursing:

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

  This should be the next route for the total-size cubic theorem.  Avoid the
  older direct accumulator sum as the final accounting device; it counts the
  same suffix frontier at multiple leaves and makes the star/sequence
  arithmetic unnecessarily loose.
- Verification: Isabelle `Posix` passed after the new
  `AntimirovNormalFrontier.thy` interfaces; the proof-worker cleanup check
  reported no matching residual workers.

## Latest Checked Deep-Row And Deep-Closure Progress, 2026-06-07

- `AntimirovFactoredTransition.thy` now has proof-local deep derivative rows:
  `rpder_deep_list`, `rpder_deep_rows`, `rpders_deep_rows`, and
  `rpders_deep1_rows`.  They generate one Antimirov step with
  `rpder_norm_list`, normalize each generated row with `rsimpDeep_raw`, filter
  dead rows, and remove duplicates.
- Checked row facts include language correctness
  (`RLS_rpder_deep_rows`, `RLS_rpders_deep_rows`,
  `RLS_rpders_deep1_rows`), legacy preservation, tail normal form,
  distinctness, and `row_group_deep_nf`.
- The one-step generated budget is checked by
  `rpder_deep_rows_generated_budget` and
  `rpder_deep_rows_generated_budget_contract`.  For a singleton input:

  ```text
  length (rpder_deep_rows c [r]) <= 2 * (rsize r + 3)^3
  card (set (rpder_deep_rows c [r])) <= 2 * (rsize r + 3)^3
  ```

  This is not the final arbitrary-input row-level cubic theorem.
- The old split-atom first-step statement is not the requested theorem.  The theorem
  `rders_pder_norm_split_aseq_termss_frontier_universe_subset` proves that
  after first computing the completed normal derivative
  `rders_pder_norm r s`, then opening it with `row_dlforms`, then splitting
  with `aseq_terms`, the resulting atoms are still in the original
  `partial_derivative_frontier_universe r`.  Keep this as an auxiliary fact
  only; do not report it as stage one completion.
- Added the deep simplifier closure universe
  `deep_simp_frontier_aseq_universe r =
   rsimpDeep_aseq_closure (partial_derivative_frontier_universe r)`.
  It has checked finite, cubic cardinality, cubic `rsize_set`, and linear
  member-size bounds.
- Added the generic derivative-fuel closure
  `rderiv_fuel_closure U`, which closes a split-term universe under subterms
  and linear continuations.  Checked facts include subterm closure,
  star-body closure, `RNTIMES` body closure, `RNTIMES` predecessor closure,
  member-size preservation, and:

  ```text
  card (rderiv_fuel_closure U) <= 2 * rsize_set U
  ```

- Added concrete cubic fuel universes:
  `deep_simp_frontier_subterm_universe r` and
  `deep_simp_frontier_fuel_universe r`.  The main checked bound is:

  ```text
  card (deep_simp_frontier_fuel_universe r) <=
    4 * (rsize r + 2)^3
  ```

  `deep_simp_frontier_fuel_universe` also has checked zero/one, subterm,
  star-body, `RNTIMES` body, `RNTIMES` predecessor, and linear member-size
  facts.
- Added the arbitrary-step fuel induction interface:
  `rpder_norm_list_aseq_terms_fuel_subsetI`,
  `aseq_termss_rpders_deep_rows_fuel_closed_subsetI`, and
  `aseq_termss_rpders_deep1_rows_fuel_closed_subsetI`.  These show that
  arbitrary many deep-row steps remain inside a chosen universe `U`, once `U`
  has the fuel facts and `rsimpDeep_raw` maps split terms back into `U`.
- The concrete raw-generation half is checked:
  `aseq_termss_concat_map_rpder_norm_list_deep_fuel_subsetI` keeps the
  unsimplified `rpder_norm_list` frontier inside
  `deep_simp_frontier_fuel_universe r`, and
  `aseq_termss_rpder_deep_rows_deep_fuel_closureI` proves a full
  `rpder_deep_rows` step lands in
  `rsimpDeep_aseq_closure (deep_simp_frontier_fuel_universe r)`.
- Added the idempotent-return interface:
  `rsimpDeep_aseq_closure_subset_idemI`,
  `aseq_terms_rsimpDeep_raw_idem_closed_subsetI`, and
  `aseq_termss_rpders_deep_rows_deep_fuel_idem_subsetI`.  If every member of
  `deep_simp_frontier_fuel_universe r` is already an `rsimpDeep_raw` fixed
  point, these lemmas give arbitrary-step containment in that same cubic fuel
  universe.
- Checked bridge: `rders_pder_norm r s`, followed by `rsimpDeep_raw`, then
  `row_dlforms` and `aseq_terms`, lands inside
  `deep_simp_frontier_aseq_universe r`.
- The deep simplifier-return step is now checked.  The theorem
  `rsimpDeep_raw_deep_simp_frontier_fuel_universe_idem` proves, for legacy
  roots, that every member of the concrete deep fuel universe is an
  `rsimpDeep_raw` fixed point:

  ```text
  p in deep_simp_frontier_fuel_universe r
  ==> rsimpDeep_raw p = p
  ```

- Therefore the arbitrary non-empty deep-row split-term bound is checked by
  `card_aseq_termss_rpders_deep1_rows_nonempty_cubic`:

  ```text
  card (aseq_termss (rpders_deep1_rows r (c # s))) <=
    4 * (rsize r + 2)^3
  ```

  This is a split-term theorem; it is not the final concrete row/DAG theorem.
- The analogous raw-strong fixed-point route is false for the current
  simplifier.  The diagnostic `rsimpStrong_raw_not_idempotent` gives a checked
  counterexample to idempotence:

  ```text
  rsimpStrong_raw (rsimpStrong_raw t) != rsimpStrong_raw t
  ```

  So do not try to finish the strong fuel theorem by proving raw strong
  idempotence on the whole fuel universe.  The next route must either use a
  real fixed-point/canonical simplifier with a termination proof, or prove the
  user's same-front/no-redundant-row invariant directly for the actual row
  representation.
- Verification: Isabelle `Posix` passed after these additions.

## Latest Checked Deep-Canonical Probe, 2026-06-07

- `AntimirovFactoredTransition.thy` now records two checked obstructions to a
  naive second-stage proof for the current `rsimpStrong_raw`.
- First, `pure_adlform_front_not_closed_under_rsimpStrong_raw` shows that pure
  Antimirov fronts are not closed under strong simplification:
  for `a.(0)*`, the pure next-front contains `(0)*`, while
  `rsimpStrong_raw ((0)*) = 1`.
- Second, `rsimpStrong_raw_seq_alt_dlform_closure_counterexample` shows that
  even the stronger closure
  `Union x in row_dlforms r. row_dlforms (rsimpStrong_raw x)` is not enough:
  the current `rsimpStrong_raw` can expose `a.(a*.a*)` where the old closure
  only has `a.a*`.  This is caused by the `RSEQ` branch calling
  `rsimp7_SEQ_atom` once and then falling back to `rsimp4_SEQ_atom` during
  recursive reassociation, losing inner star absorption.
- A proof-local repair probe is checked:
  `rsimpDeep_SEQ_atom` recursively reassociates sequences while keeping the
  `rsimp7` star absorption rules active at every join.  Checked facts:
  `RL_rsimpDeep_SEQ_atom`,
  `rsize_rsimpDeep_SEQ_atom_le`, and
  `aseq_terms_rsimpDeep_SEQ_atom_subset`.
- A proof-local normalizer `rsimpDeep_raw` is also checked.  It uses
  `rsimpDeep_SEQ_atom` for sequence and ordinary flatten/distinct cleanup for
  alternatives.  Checked facts:
  `RL_rsimpDeep_raw`, `rsize_rsimpDeep_raw_le`, and
  `rsimpDeep_raw_repairs_seq_alt_dlform_counterexample`.
- This does not prove the final cubic theorem.  It identifies a checked design
  gap in the existing `rsimpStrong_raw` canonicality route and gives a checked
  candidate sequence canonicalizer that repairs the observed gap.  Next work:
  connect `rsimpDeep_raw` or an equivalent strengthening of `rsimpStrong_raw`
  to the front-indexed derivative-row induction and then to row-prune/cubic
  accounting.

## Latest Checked Front-Indexed Progress, 2026-06-06

- `AntimirovFactoredTransition.thy` now has checked front-indexed linear-form
  definitions:
  `row_lforms`, `row_lformss`, `alform_front`, `same_lfront_row`, and
  `same_lfront_rows`.
- Earlier split-atom normal-derivative closure is checked:
  `anorm_der_eq_rders_pder_norm` bridges the factored Antimirov rows collapsed
  by `rsimp_ALTs` to the existing normal derivative iterator
  `rders_pder_norm`.  The theorem
  `rders_pder_norm_aseq_terms_frontier_universe_contract` then proves that
  after computing the normal derivative regex and only then splitting with
  `aseq_terms`, the terms stay inside the original
  `partial_derivative_frontier_universe`, with the quadratic card bound and
  linear member-size bound.  This is auxiliary only; the corrected
  whole-residual normal-frontier theorem is
  `rfrontier_rders_pder_norm_subset_apder_frontier`.
- Supporting front-indexed closure is also checked:
  `alform_front_aseq_terms_frontier_universe_contract` proves the same
  split-term frontier bound for every linear form at a fixed derivative front.
- Cleanup bridge lemmas are checked:
  `same_lfront_rows_rflts`, `same_lfront_rows_rdistinct`,
  `same_lfront_rows_rprune_eq_against`, `same_lfront_row_rsimp_ALTs`, and
  `same_lfront_rows_aseq_terms_frontier_universe_contract`.
- Second-step scaffolding is checked:
  `afactored_steps_append`, `afactored1_snoc`,
  `row_lformss_rflts_eq`, `row_lformss_rdistinct_empty_eq`,
  `row_lformss_afactored_step_eq_generated`, `alform_front_snoc`, and
  `row_lforms_rpder_norm_list_afactored1_subset`.  These show that pure
  Antimirov generation from `afactored1 root front` advances exactly to
  `alform_front root (front @ [c])`.
- Checked negative diagnostics for the simplifier side:
  `rsimpStrong_raw_aseq_terms_not_monotone` and
  `row_lforms_rsimpStrong_prune_pair_raw_not_monotone`.  Do not try to prove
  the second step by plain `aseq_terms` monotonicity of `rsimpStrong_raw` or
  plain `row_lforms` monotonicity of raw shared-suffix pruning; both are false.
- Full CI after this update passed:
  Scala strong-memo smoke/fuzz on 84,300 depth-2/input-3 pairs plus known
  row-diff regressions, then Isabelle `Posix` and `BackRefPilot`.
- Remaining proof blocker: the simplifier-side theorem is still open.  In
  particular, the existing raw strong theorem still has a norm/closure premise
  for `rsimpStrong_raw`; a naive
  `aseq_terms (rsimpStrong_raw p) subset aseq_terms p` is false because stars
  can simplify to `RONE`.  The next move should prove same-front
  canonical/no-redundancy closure, not collapse back to plain arbitrary-subset
  inclusion.

## Latest Checked Second-Stage Closure, 2026-06-07

- Later on 2026-06-07, the second-stage row accounting was sharpened again.
  The new checked theorem
  `rpders_strong1_rows_raw_canonical_lforms_cubic_contractI` gives raw
  multi-step language correctness plus all four row budgets for
  `rpders_strong1_rows_raw r s`, conditional on an explicit canonical lform
  package: disjoint row linear forms, live rows, row sizes paid by row linear
  forms, and inclusion of all row linear forms in the chosen cubic universe.
- Raw multi-step language correctness itself is checked separately as
  `RLS_rpders_strong_rows_raw` and `RLS_rpders_strong1_rows_raw`.
- The simplifier-side monotonicity target has been made precise.  The new
  payload condition
  `row_payload_lform_stable p` says that payload `p` does not expose new row
  linear forms when used as a tail or under an arbitrary suffix.  Under this
  condition, the checked lemmas
  `row_lforms_rsimpStrong_prune_pair_raw_subset_later_payload_stableI`,
  `row_lformss_rsimpStrong_prune_rows_raw_subset_pairI`, and
  `row_lformss_rpder_strong_rows_raw_subset_generated_payload_stableI` prove
  that raw scan/prune deletes row linear forms but does not create new ones.
- Two negative diagnostics are checked:
  `row_nf_does_not_imply_tail_stable` and
  `rtail_nf_does_not_imply_tail_stable`.  So the next proof step cannot use
  the old weak normal forms alone.  It must either prove that actual generated
  group payloads are `row_payload_lform_stable`, or strengthen the simplifier
  so generated payloads satisfy this condition.
- Isabelle `Posix` and `BackRefPilot` passed with
  `-SkipScala -SessionTimeoutSeconds 240` after this row-accounting update.
  Scala smoke was not rerun for this proof-only update.

- Added `strong_simp_frontier_aseq_universe r`, the checked split-term
  simplifier closure:

  ```isabelle
  strong_simp_frontier_aseq_universe r =
    rsimpStrong_aseq_closure (partial_derivative_frontier_universe r)
  ```

  The theorem `card_strong_simp_frontier_aseq_universe_cubic` proves:

  ```text
  card (strong_simp_frontier_aseq_universe r) <=
    2 * (rsize r + 2)^3
  ```

  and `strong_simp_frontier_aseq_universe_member_size_linear` gives the
  linear member-size bound.
- The corrected normal-derivative + strong-simplifier bridge is checked:
  `rsimpStrong_raw_rders_pder_norm_frontier_closure_nf_contract`.  It proves
  that after first computing `rders_pder_norm r s` and then applying
  `rsimpStrong_raw`, the split terms are inside
  `strong_simp_frontier_aseq_universe r`, with the cubic cardinality bound,
  the linear member-size bound, and `row_group_deep_nf`.
- One-step raw-strong row bridges from Antimirov-bounded states are checked:
  `rpder_strong_rows_raw_rders_pder_norm_frontier_closure_nf_contract` and
  `rpder_strong_rows_raw_afactored1_frontier_closure_nf_contract`.
  These prove the same split-term cubic/linear/NF contract for one
  `rpder_strong_rows_raw` step from the completed normal derivative row or
  from `afactored1 r s`.
- Added raw strong-row NF preservation lemmas, including
  `row_group_deep_nf_rpder_strong_rows_raw_legacy` and
  `row_group_deep_nf_rpders_strong_rows_raw_legacy_Cons`.
- This is still not the final row-level cubic theorem.  The new
  `strong_simp_frontier_aseq_universe` is a split-term/simplifier closure
  universe.  The final memo route still needs a concrete row-level universe
  closed under raw active-suffix/later-shared pruning and subterms, connected
  to `strong_deferred_original_raw_row_norm_later_shared_memo_cubic_interface`.
- Full CI passed after this second-stage update.

## Later Checked Deep-Row Split-Atom Closure, 2026-06-07

- Added checked deep-row splitter lemmas:
  `row_dlforms_aseq_terms_subset` and `row_dlformss_aseq_terms_subset`.
  They say that after `row_dlforms` opens a row into deep linear forms,
  splitting one of those forms with `aseq_terms` is still contained in the
  original row/row-list split atoms.
- Added checked deep same-front definitions:
  `adlform_front`, `same_dlfront_row`, and `same_dlfront_rows`.
  The pure Antimirov front-advance theorem
  `row_dlforms_rpder_norm_list_afactored1_subset` proves that if
  `q in afactored1 root front` and
  `p in rpder_norm_list c q`, then
  `row_dlforms p subset adlform_front root (front @ [c])`.
  This is the concrete deep version of the user's "same derivative front"
  scaffold.
- Added deep-front cleanup preservation:
  `same_dlfront_rows_rflts`, `same_dlfront_rows_rdistinct`,
  `same_dlfront_rows_rprune_eq_against`, and
  `same_dlfront_row_rsimp_ALTs`.
  These are the checked transport lemmas for carrying a fixed deep front
  through flattening, duplicate removal, row pruning, and alternative
  repackaging.
- Added checked normal-derivative bridge:
  `row_dlforms_rders_pder_norm_split_terms_frontier_universe_subset` and
  `row_dlforms_rders_pder_norm_split_terms_frontier_universe_contract`.
  These prove that for
  `x in row_dlforms (rders_pder_norm r s)`,
  `aseq_terms x` stays inside
  `partial_derivative_frontier_universe r`, with the quadratic card bound and
  linear member-size bound.
- Added checked raw-strong multi-step bridge:
  `row_dlformss_rpders_strong1_rows_raw_split_terms_frontier_universe_subsetI`
  and
  `row_dlformss_rpders_strong1_rows_raw_split_terms_frontier_universe_contractI`.
  These are conditional on the existing `rsimpStrong_raw` frontier-preserving
  norm premise and give the same atom-level frontier contract for every
  `x in row_dlformss (rpders_strong1_rows_raw r s)`.
- Do not overclaim this as final inclusion.  The proved shape is:

  ```text
  aseq_terms x subset partial_derivative_frontier_universe r
  ```

  not:

  ```text
  x in partial_derivative_frontier_universe r
  ```

  The gap is exactly the user's same-front combination issue: for
  `x = RSEQ p k`, atom-level inclusion of `p` and `k` does not prove the
  product combination itself is an allowed Antimirov/front residual.
- Isabelle `Posix` and `BackRefPilot` passed with
  `-SkipScala -SessionTimeoutSeconds 240` after this update.

## Fixed Exploration Constraint: Front-Indexed Antimirov Terms

Preserve the user's proof sketch as a fixed route, not a loose analogy:

1. First prove a derivative-side invariant that is stronger than plain term
   inclusion.  For an original regex `r`, let `T_r` be the Antimirov/partial-
   derivative term universe, e.g. the relevant subset of
   `partial_derivative_frontier_universe r`.  The invariant should say that
   after any derivative string `s`, every concrete row can be split into
   Antimirov terms from `T_r`, but the terms in one row are not an arbitrary
   subset of `T_r`.  They must lie in one common derivative front:

   ```text
   aseq_terms(row) subset T_r(front)
   ```

   for some front label `front`.  Equivalently, rows are allowed same-front
   combinations only.

2. Interpret the front label as "possible same predecessor derivative string"
   or the equivalent residual/frontier class.  Two terms may be combined in
   one row only if there exists a shared predecessor/front from which both can
   arise.  This must be formalized separately from the size bound.

3. Examples to preserve:

   - For `(a+b)c`, the relevant terms include `(a+b)c` and `c`, but they do not
     have the same front: `(a+b)c` is at the empty/root front, while `c` is
     reached after `a` or `b`.  Therefore `(a+b)c` must not be combined with
     `c`.
   - For `a*b + a*c`, the terms `b` and `c` can share a front after consuming
     the same `a`-prefix behavior, so their combination is admissible.
   - For `(aa)*b + a*c`, keep the same intended phenomenon: `b` and `c` can
     become same-front terms for compatible consumed-prefix histories, so the
     proof should not rely on syntactic parent equality alone.

4. Then prove the simplifier side separately: `simpStrong` / `rsimpStrong_raw`
   should be shown to normalize or canonicalize rows so that, once rows are
   split, there are no duplicate/redundant same-front terms.  Do not ask
   `simpStrong` to prove the Antimirov inclusion invariant; derivatives prove
   "no mixed-front combinations", while simplification proves "no redundant
   terms inside the allowed front".

5. Do not collapse this route back into plain
   `aseq_terms(row) subset partial_derivative_frontier_universe r`.  That
   inclusion is useful and currently partially checked, but it is too weak for
   the raw regex-size theorem because it permits arbitrary combinations and
   loses the row/front discipline needed to bound concrete row syntax.

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

## Current Antimirov Row-Diff Loop Status

The active proof-facing route now follows the Antimirov linear-forms shape more
directly:

- `GeneralRegexBound.thy` has combined cubic bounds for the term-safe route:
  `rpder_strong_rows_clean_terms_absorbed_single_cubic_bounds` and
  `rpder_strong_rows_clean_terms_absorbed_pruned_single_cubic_bounds`.
- `GeneralRegexBound.thy` also has proof-facing budget bundles:
  `rpder_strong_rows_clean_terms_absorbed_generated_budget`,
  `rpder_strong_rows_clean_terms_absorbed_pruned_generated_budget`,
  `rpder_strong_rows_clean_terms_absorbed_single_cubic_budget_bounds`, and
  `rpder_strong_rows_clean_terms_absorbed_pruned_single_cubic_budget_bounds`.
  These include `rsizes rows` alongside row count, distinct row count, and
  linear-term count.
- `GeneralRegexBound.thy` now also has semantics+budget contracts:
  `rpder_strong_rows_clean_terms_absorbed_generated_budget_contract`,
  `rpder_strong_rows_clean_terms_absorbed_pruned_generated_budget_contract`,
  `rpder_strong_rows_clean_terms_absorbed_single_cubic_budget_contract`, and
  `rpder_strong_rows_clean_terms_absorbed_pruned_single_cubic_budget_contract`.
  These combine the budget facts with `RLS (set rows) = Der c ...`.
- `FBound.thy` has the matching `rerase (intern r)` wrappers:
  `rpder_strong_rows_clean_terms_absorbed_rerase_intern_single_cubic_bounds`
  and
  `rpder_strong_rows_clean_terms_absorbed_pruned_rerase_intern_single_cubic_bounds`.
- `FBound.thy` also has the matching `rerase (intern r)` cubic budget wrappers:
  `rpder_strong_rows_clean_terms_absorbed_rerase_intern_single_cubic_budget_bounds`
  and
  `rpder_strong_rows_clean_terms_absorbed_pruned_rerase_intern_single_cubic_budget_bounds`.
- `FBound.thy` also has the matching `rerase (intern r)` semantics+budget
  contracts:
  `rpder_strong_rows_clean_terms_absorbed_rerase_intern_single_cubic_budget_contract`
  and
  `rpder_strong_rows_clean_terms_absorbed_pruned_rerase_intern_single_cubic_budget_contract`.
- `PosixCubicSmoke.scala` compares scan/prune strong rows against Antimirov
  strong linear-form rows using rows, shallow linear terms, deep expanded
  terms, total tree size, DAG size, shape-DAG size, and max-row variants.
- Known row-diff replay now has 9 cases, including:
  absorbed-suffix, covered-row deletion, reassociation, nested-alternative deep
  linear coverage, same-budget DAG sharing, and one-way budget cover.
- The harness explanations now include `budgetNonworseCover`: scan/prune has
  no larger row count, shallow term count, uncapped deep term count, or total
  tree size than Antimirov, and both row sets bridge-cover each other.
- The harness explanations now also include `budgetNonworseOneWayCover`:
  scan/prune has no larger row count, shallow term count, uncapped deep term
  count, or total tree size than Antimirov, and every scan row is covered by
  the Antimirov rows, but Antimirov may retain an extra row not covered back by
  scan. This is treated as non-actionable because the proof-facing budgets are
  already no worse and semantics are handled separately.

Latest evidence:

- `actionable` finder, seeds `20260715..20260716`, depth 15/input 18/size cap
  320/maxNormRows 16000: no witness across 11567 checked cases.
- `deepTermCapped`, seeds `20260717..20260718`: no witness across 11542 checked
  cases.
- `deepTermOnly`, seeds `20260721..20260722`: no witness across 11550 checked
  cases.
- Fixed-point random comparison, seeds `20260719..20260720`: 7713 checked,
  `primary=0`, `unexplained=0`, `termOnly=0`, `deepTermOnly=0`,
  `deepTermCapped=0`, `scanExtra=0`.
- Post-classification fixed-point run, seed `20260727`: 2411 checked,
  `primary=0`, `unexplained=0`, `termOnly=0`, `deepTermOnly=0`,
  `deepTermCapped=0`, `sameBudgetCover=35`.
- Follow-up finders: no `actionable` witness on seed `20260728` across 4812
  checked cases; no `deepTermOnly` witness on seed `20260729` across 4810
  checked cases.
- Known replay after `budgetNonworseCover`: 8 cases split as
  `absorbedSuffix=1`, `coveredDrop=1`, `sameBudgetCover=1`,
  `budgetNonworseCover=5`, with `primary=0` and `unexplained=0`.
- Post-budget fixed-point fuzz, seed `20260730`: 3362 checked with
  `primary=0`, `unexplained=0`, `termOnly=0`, `deepTermOnly=0`,
  `deepTermCapped=0`. Follow-up finders found no `actionable` witness on seed
  `20260731` across 4812 checked cases and no `deepTermCapped` witness on seed
  `20260732` across 4818 checked cases.
- `isabelle build -D . Posix` passed after adding the generated-budget and
  single-step cubic budget lemmas. Known row-diff replay still reports
  `budgetNonworseCover=5`, `primary=0`, and `unexplained=0`; a
  `budgetNonworseCover` finder on seed `20260733` found no fresh witness across
  3384 checked cases.
- `isabelle build -D . Posix` also passed after adding semantics+budget
  contracts. Known row-diff replay still reports the same 8-case split; an
  `actionable` finder on seed `20260734` found no witness across 4357 checked
  cases.
- A wider `actionable` finder on seed `20260735` exposed a one-way budget-cover
  classification gap at generated case `6959`: scan/norm budgets were rows
  `7/9`, shallow terms `8/11`, deep terms `67/79`, total size `2403/3036`,
  DAG `110/115`, and shape-DAG `80/80`; only max-row DAG was locally larger
  (`98/97`) and the old comparison reported `normExtra`. Added
  `budgetNonworseOneWayCover`; after that, re-running seed `20260735` through
  generated case `7000` found no `actionable` witness across `6766` checked
  cases, and the summary recorded `budgetNonworseOneWayCover=1`,
  `primary=0`, and `unexplained=0`.
- The one-way budget-cover witness is now part of
  `scanRowsKnownRegressions`. Known row-diff replay now reports 9 cases with
  `scanExtra=0`, `normExtra=1`, `budgetNonworseOneWayCover=1`,
  `primary=0`, and `unexplained=0`.
- Follow-up `actionable` finders on seeds `20260736..20260737`, depth 15/input
  18/size cap 320/maxNormRows 16000, found no witness across `13483` checked
  cases. A `deepTermCapped` finder on seed `20260738` found no witness across
  `2387` checked cases.
- Further `actionable` finders on seeds `20260738..20260739` found no witness
  across `9597` checked cases. A `deepTermOnly` finder completed seed
  `20260739` with no witness across `3369` checked cases; a shorter seed
  `20260740` slice found no witness across `1165` checked cases after the
  larger two-seed run timed out on seed `20260740`.
- Further `actionable` finders on seeds `20260740..20260741` found no witness
  across `7709` checked cases. A `deepTermCapped` finder on seeds
  `20260741..20260742` found no witness across `4825` checked cases.
- The unbounded shrink of the one-way budget-cover witness `20260735/6959`
  produced a before-shrink dump but did not finish promptly, so the Java
  process was stopped. `PosixCubicSmoke.scala` now has
  `POSIX_SMOKE_COMPARE_SCAN_ROWS_SHRINK_MAX_PROBES`; default `0` preserves the
  old unlimited behavior. With `200` probes, the same witness shrinks from
  `rsize=300` to `rsize=198` while preserving
  `budgetNonworseOneWayCover`: rows `4/7`, shallow terms `5/9`, deep terms
  `32/49`, total size `879/1588`, DAG `82/86`, max-row DAG `74/73`,
  `probes=200`, `exhausted=true`. The finder path was also exercised with a
  `50`-probe cap and automatically rediscovered seed `20260735` case `6959`
  after `6728` checked cases.
- Post-probe fixed-point fuzz on seeds `20260743..20260744`, depth 15/input
  18/size cap 320/maxNormRows 16000, checked `2903 + 2896` random cases with
  `scanExtra=0`, `normExtra=0`, `termOnly=0`, `deepTermOnly=0`,
  `deepTermCapped=0`, `primary=0`, and `unexplained=0`.
- `POSIX_SMOKE_COMPARE_SCAN_ROWS_SHRINK_MAX_PROBES` is now also threaded
  through fixed-point failure summaries, so exhaustive/random/known row-diff
  gates use bounded auto-shrink when an actionable witness is found. A
  known-regression replay with `SHRINK_MAX_PROBES=100` still reports 9 cases
  with `primary=0` and `unexplained=0`.
- Further targeted finders on seeds `20260745..20260746`, depth 15/input
  18/size cap 320/maxNormRows 16000: no `actionable` witness across `6725`
  checked cases, no `deepTermOnly` witness across `4801` checked cases, and
  no `deepTermCapped` witness across `3845` checked cases.
- Added consolidated row-diff finder modes: `proofBudgetWorse` for the
  Isabelle-facing row/term/total-size budgets, `budgetWorse` for those plus
  deep expanded terms/capping, and directed coverage modes
  `scanCoverageGap`/`normCoverageGap`. `budgetWorse` found no witness on seed
  `20260747` across `3387` checked cases; a two-seed run timed out while
  processing seed `20260748`, so a shorter complete seed `20260748` replay
  found no witness across `1634` checked cases. `scanCoverageGap` found no
  witness on seed `20260749` across `2406` checked cases. `normCoverageGap`
  was checked on known witness `20260735/6959`, where it reports
  `scanExtra=<none>`, a `normExtra`, and `budgetNonworseOneWayCover`.
- Exhaustive/random/known row-diff summaries now print
  `proofBudgetWorse`, `budgetWorse`, `scanCoverageGap`, and
  `normCoverageGap` counts directly. Known replay reports
  `proofBudgetWorse=0`, `budgetWorse=0`, `scanCoverageGap=0`,
  `normCoverageGap=1`. A random fixed-point summary on seed `20260750`,
  depth 15/input 18/size cap 320/maxNormRows 16000, checked `2120` cases and
  reported all four new counters as `0`, with `primary=0` and `unexplained=0`.
- Optional hard gates were added for the row-diff fixed-point loop:
  `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_PROOF_BUDGET`,
  `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_BUDGET`,
  `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_SCAN_COVERAGE`, and
  `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_NORM_COVERAGE`. When a gated counter
  is nonzero, the harness fails and auto-shrinks in the matching mode using
  `POSIX_SMOKE_COMPARE_SCAN_ROWS_SHRINK_MAX_PROBES`.
- Added `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_NONWORSE` as the one-switch
  version of the intended scan-vs-Antimirov fixed point. It expands to the
  proof-budget, stronger-budget, and scan-coverage gates, so it checks that
  scan/prune rows are not worse in the proof-facing budgets and do not have an
  uncovered scan-only row. It intentionally does not reject explained
  Antimirov-only rows; those remain visible as `normCoverageGap`.
  New-switch validation passed on known replay (`9` cases, known
  `normCoverageGap=1` still explained), seed `20260775` (`2500` random cases,
  depth 5/input 14), and exhaustive depth 2/input 3 (`84300` pairs).
  `POSIX_SMOKE_COMPARE_SCAN_ROWS_FIND_MODE=nonworse` is now the matching
  targeted finder/shrinker mode, and default local CI now runs both known
  row-diff replay and the small exhaustive row-diff grid with
  `POSIX_SMOKE_COMPARE_SCAN_ROWS=1` and
  `POSIX_SMOKE_COMPARE_SCAN_ROWS_REQUIRE_NONWORSE=1`.
- Hard-gate replay/fuzz after adding the gates:
  known replay with proof-budget, budget, and scan-coverage gates passed on
  all 9 known cases with `proofBudgetWorse=0`, `budgetWorse=0`,
  `scanCoverageGap=0`, `normCoverageGap=1`, `primary=0`, `unexplained=0`.
  Do not enable the norm-coverage gate for that replay unless the one-way
  Antimirov-extra witness is deliberately reclassified.
- Additional hard-gate fuzz:
  seed `20260751`, depth 5/input 14, checked `2000` random cases with all four
  budget/coverage counters `0`; seeds `20260752..20260754` checked another
  `9000` cases with the same result. Targeted `budgetWorse` finder on seeds
  `20260755..20260758` found no witness across `20000` checked cases, and
  targeted `scanCoverageGap` finder on seeds `20260759..20260762` found no
  witness across another `20000` checked cases. A small exhaustive hard-gate
  run over depth 2/input 3 checked `84300` regex/input pairs and had
  `observations=0`.
- Isabelle proof-facing contracts now mirror the Antimirov budget metrics more
  directly. `GeneralRegexBound.thy` has semantic+budget contracts for
  `rpder_strong_rows` and `rpder_strong_rows_raw`: the produced rows denote
  the derivative language, and `length`, `card (set ...)`, `rlinear_termss`,
  and `rsizes` are bounded by the generated Antimirov `rpder_norm_list` size.
  The single-root cubic entries are
  `rpder_strong_rows_single_cubic_budget_contract` and
  `rpder_strong_rows_raw_single_cubic_budget_contract`; `FBound.thy` adds the
  `rerase (intern r)` wrappers
  `rpder_strong_rows_rerase_intern_single_cubic_budget_contract` and
  `rpder_strong_rows_raw_rerase_intern_single_cubic_budget_contract`, with
  bound `2 * (rxsize r + 3) ^ 3`.
- Post-contract checks:
  `isabelle build -D . Posix` passed. Known row-diff hard-gate replay still
  passed on all 9 cases with `proofBudgetWorse=0`, `budgetWorse=0`,
  `scanCoverageGap=0`, `normCoverageGap=1`, `primary=0`, `unexplained=0`. A
  fresh random hard-gate run on seed `20260763`, depth 5/input 14, checked
  `3000` cases with all budget/coverage counters `0`.
- Multi-step accumulator contracts:
  `GeneralRegexBound.thy` now has
  `rpders_strong1_rows_raw_budget_from_rsizes_bound` and
  `rpders_strong1_rows_raw_cubic_universe_budget_contractI`, turning an
  `rsizes` bound on final raw accumulator rows into simultaneous bounds for
  `length`, `card (set ...)`, `rlinear_termss`, and `rsizes`. `FBound.thy`
  adds companion contracts for the original route,
  `strong_deferred_original_raw_row_norm_later_shared_accumulator_budget_contract`
  and
  `strong_deferred_original_raw_row_norm_active_suffix_accumulator_budget_contract`.
  These are separate companion theorems and do not change the numbered
  conclusions of the existing memo cubic interfaces.
- Additional accumulator companions:
  `FBound.thy` now also has
  `strong_deferred_original_raw_row_accumulator_budget_contract`,
  `strong_deferred_original_raw_row_norm_closed_accumulator_budget_contract`,
  and
  `strong_deferred_original_raw_row_norm_same_suffix_accumulator_budget_contract`.
  They package the final raw accumulator bounds for the generic raw,
  norm-closed, and same-suffix routes: `length`, `card (set ...)`,
  `rlinear_termss`, and `rsizes` are all bounded by the same budget `B`.
- Post-accumulator-contract checks:
  `isabelle build -D . Posix` passed. Fresh random hard-gate run seed
  `20260764`, depth 5/input 14, checked `3000` cases with
  `proofBudgetWorse=0`, `budgetWorse=0`, `scanCoverageGap=0`,
  `normCoverageGap=0`, `primary=0`, `unexplained=0`.
- Follow-up nonworse fuzz:
  seed `20260765`, depth 5/input 14, checked `3000` cases with the nonworse
  counters at `0`; seeds `20260766..20260768`, depth 6/input 16, checked
  `12000` more cases with the same result. Targeted `budgetWorse` finder on
  seeds `20260769..20260770`, targeted `scanCoverageGap` finder on
  `20260771..20260772`, and targeted `normCoverageGap` finder on
  `20260773..20260774` each checked `14000` depth 7/input 18 cases and found
  no witness. The composite `nonworse` finder on seeds `20260776..20260777`,
  depth 7/input 18, checked `12000` more cases and found no witness. A deeper
  composite `nonworse` finder on seeds `20260778..20260779`, depth 8/input
  20, checked `10000` cases and found no witness. Full local CI passed again
  after wiring the nonworse gate into default known replay and default
  exhaustive row-diff comparison; the default exhaustive comparison checked
  `84300` regex/input pairs with `observations=0`.
- Latest post-contract checks:
  after the extra `FBound.thy` accumulator companions,
  `isabelle build -D . Posix` passed. Composite `nonworse` finder on seeds
  `20260780..20260781`, depth 8/input 20, checked `8000` cases and found no
  nonworse witness (`proofBudgetWorse=0`, `budgetWorse=0`,
  `scanCoverageGap=0`). Seed `20260781` had one harmless `normCoverageGap`;
  targeted shrinking reduced it to
  `STAR(ALT(CH(a),SEQ(CH(a),SEQ(ALT(CH(a),CH(b)),ALT(CH(a),CH(b))))))` on
  input `aa`, with scan strictly smaller on the main budgets
  (`rows 1/3`, `terms 3/5`, `deepTerms 6/7`, `size 21/48`) and the
  Antimirov-only extra classified as `absorbedSuffix`.
- Latest deeper fuzz:
  composite `nonworse` finder on seeds `20260782..20260785`, depth 9/input
  22, checked another `20000` random cases and found no nonworse witness.
  Per-seed summaries had `proofBudgetWorse=0`, `budgetWorse=0`,
  `scanCoverageGap=0`, `normCoverageGap=0`, `primary=0`, and
  `unexplained=0`; the remaining observations were secondary
  `absorbedSuffix`/`sameBudgetCover`/rare `coveredDrop` or
  `budgetNonworseCover` tradeoffs.
- Final size-universe POSIX accumulator contract:
  `FBound.thy` now has
  `strong_deferred_original_sizeNregex_memo_POSIX_accumulator_budget_contract`.
  It is a companion to `strong_deferred_original_sizeNregex_memo_cubic_interface`
  and exposes POSIX correctness/flatness, legacy preservation, the row-to-memo
  gate, the raw/annotated row bridge, span-state probe bounds, and the final
  raw accumulator budgets `length`, `card (set ...)`, `rlinear_termss`, and
  `rsizes`, all bounded by the same `B`. `isabelle build -D . Posix` passed
  after adding it.
- Latest secondary-tradeoff check:
  targeted `maxShapeDagOnly` search on seed `20260782`, depth 7/input 16,
  checked `3000` cases and found no pure max-shape-only witness. The top
  observations were still `absorbedSuffix`, where scan improves rows/total
  size but can increase one max row/shape metric by one constructor; do not
  add a simple max-size guard without rechecking the main budgets. Composite
  `nonworse` finder on seeds `20260786..20260787`, depth 8/input 20, checked
  `8000` cases and found no nonworse witness (`proofBudgetWorse=0`,
  `budgetWorse=0`, `scanCoverageGap=0`, `normCoverageGap=0`, `primary=0`,
  `unexplained=0`).
- Active-suffix POSIX accumulator contract:
  `FBound.thy` now has
  `strong_deferred_original_raw_row_norm_active_suffix_memo_POSIX_accumulator_budget_contract`.
  It is the active-suffix analogue of the final `sizeNregex` POSIX
  accumulator theorem: POSIX correctness/flatness, memo gate, raw/annotated
  row bridge, span-state probe bounds, and final raw accumulator budgets
  `length`, `card (set ...)`, `rlinear_termss`, and `rsizes` are all exposed
  under the same finite-universe `B`. `isabelle build -D . Posix` passed after
  adding it.
- Latest post-active-suffix fuzz:
  composite `nonworse` finder on seeds `20260788..20260789`, depth 9/input
  22, checked `10000` random cases and found no nonworse witness. Per-seed
  summaries had `proofBudgetWorse=0`, `budgetWorse=0`, `scanCoverageGap=0`,
  `normCoverageGap=0`, `primary=0`, and `unexplained=0`; the strongest
  secondary examples remained `absorbedSuffix` tradeoffs.
- SizeNregex active-suffix POSIX accumulator route:
  `FBound.thy` now has
  `strong_deferred_original_sizeNregex_active_suffix_memo_POSIX_accumulator_budget_contract`.
  It has the same final POSIX/legacy/bridge/span-state and raw accumulator
  budget conclusions as
  `strong_deferred_original_sizeNregex_memo_POSIX_accumulator_budget_contract`,
  but proves them by explicitly instantiating the active-suffix closure route
  with `raw_shared_prune_active_suffix_closure_sizeNregex_subset`. `isabelle
  build -D . Posix` passed after adding it.
- Latest post-sizeNregex-active-suffix fuzz:
  composite `nonworse` finder on seeds `20260790..20260791`, depth 9/input
  22, checked `10000` random cases and found no nonworse witness. Per-seed
  summaries had `proofBudgetWorse=0`, `budgetWorse=0`, `scanCoverageGap=0`,
  `normCoverageGap=0`, `primary=0`, and `unexplained=0`; the strongest
  secondary examples remained `absorbedSuffix`.
- Exact active-suffix sizeNregex budget:
  `FBound.thy` now has
  `strong_deferred_original_sizeNregex_active_suffix_memo_POSIX_accumulator_exact_budget_contract`.
  It is the same active-suffix POSIX accumulator route with the natural budget
  `card (sizeNregex N) * N`, so callers no longer need to pass separate
  `card_bound`/`cubic` assumptions when that exact budget is enough. The
  remaining substantial assumption is still the `rpder_norm_list` closure for
  `sizeNregex N`. `isabelle build -D . Posix` passed after adding it.
- Latest post-exact-budget fuzz/shrink:
  composite `nonworse` finder on seeds `20260792..20260793`, depth 9/input
  22, checked `10000` random cases and found no scan-worse witness. Seed
  `20260792` had one harmless `normCoverageGap`; targeted shrinking reduced
  it to
  `STAR(SEQ(ALT(SEQ(ALT(CH(b),ONE),ALT(CH(a),CH(b))),ONE),ALT(CH(a),CH(b))))`
  on input `b`, with scan smaller on the main budgets (`rows 1/3`,
  `terms 3/5`, `deepTerms 6/7`, `size 23/54`) and the Antimirov-only extra
  classified as `absorbedSuffix`.
- Least-owner DAG accumulator bridge:
  `FBound.thy` now has
  `rpders_strong1_rows_raw_intern_least_owner_dag_budget_boundI`,
  `strong_deferred_row_gate_least_owner_dag_accumulator_POSIX_contract`, and
  `strong_deferred_row_gate_norm_active_suffix_universe_accumulator_POSIX_contract`.
  These expose the final raw accumulator metrics `length`, `card (set ...)`,
  `rlinear_termss`, and `rsizes` through the smaller least-owner active-suffix
  DAG budget and through any active-suffix universe with cardinality/member-size
  bounds. This is the current proof-facing bridge closest to Antimirov
  linear-form accounting.
- Latest scan-vs-Antimirov fixed-point refinement:
  `PosixCubicSmoke.scala` now computes Antimirov-style linear rows as a local
  fallback and only adopts pruned/absorbed scan rows when total tree/DAG/shape
  and max tree/DAG/shape budgets do not increase. The comparator also
  canonicalizes harmless bit placement before annotated-DAG counting and
  suppresses already covered budget-nonworse DAG-only noise. This removed the
  shrunk `maxOnly` witness
  `STAR(ALT(CH(b),SEQ(CH(b),ALT(CH(a),CH(b)))))` on input `b` and the shrunk
  `shapeDagOnly` absorbed-suffix witness
  `STAR(SEQ(ALT(CH(a),STAR(CH(a))),ALT(NTIMES(ONE,0),CH(a))))` on input `a`.
- Latest fixed-point fuzz:
  targeted `dagOnly` on seeds `20260794` and `20260796` each checked `5000`
  random cases with no witness and `observations=0`. Composite `nonworse` on
  seeds `20260794..20260795` checked `10000` cases with all hard/soft row-diff
  counters at `0`; composite `nonworse` on seeds `20260796..20260799` checked
  another `20000` cases with `observations=0` for every seed. No
  `proofBudgetWorse`, `budgetWorse`, `scanCoverageGap`, primary, or
  unexplained case is currently known.
- Proof-facing choice contract:
  `GeneralRegexBound.thy` now has `rpder_strong_rows_clean_terms_choice`, which
  is either the clean Antimirov-style fallback rows or the safe
  term-absorbed/pruned scan rows. Its generated-budget and single-step cubic
  contracts expose correctness plus `length`, `card (set ...)`,
  `rlinear_termss`, and `rsizes`, bounded first by the generated
  `rpder_norm_list` rows and then by `2 * (rsize r + 3)^3`.
  `FBound.thy` has the matching `rerase (intern r)`/`rxsize` contract for the
  POSIX surface.
- Deeper fixed-point confirmation:
  depth-10/input-24 fuzz found no actionable witness. Seed `20260800` checked
  `2000` cases with `FIND_MODE=any`; seeds `20260801..20260804` checked
  another `8000` cases, all with `observations=0`. After these proof edits,
  `isabelle build -D . Posix` passed, and full CI passed: known row-diff
  regressions `9` cases `observations=0`, exhaustive row comparison `84300`
  pairs `observations=0`, plus `Posix` and `BackRefPilot`.
- Proof write-up:
  `CUBIC_BOUND_PROOF_WRITEUP_2026_06_06.md` summarizes the checked one-step
  cubic theorem, POSIX lift, finite-universe accumulator interface, exact
  `sizeNregex` contract, and the remaining universe-cardinality obligation
  for a standalone all-input cubic theorem.
- Pure Antimirov/factored transition:
  `AntimirovFactoredTransition.thy` is now in `ROOT`. It defines only
  scan-free rows: `afactored_step`, `afactored_steps`, and `afactored1`.
  It proves language correctness, distinctness, induction through a closed
  universe (`afactored_steps_subterm_closed_universe_subsetI`), finite-universe
  row/term/size budgets, and the conditional cubic theorem
  `afactored1_cubic_universe_contractI`. This isolates the proof object from
  `rsimpStrong_prune_rows`; the remaining mathematical obligation is the
  root-derived Antimirov universe closure assumption.
- Product-term split closure:
  `AntimirovFactoredTransition.thy` also defines `aseq_terms` / `aseq_termss`,
  which split top-level alternatives and `RSEQ` products into Antimirov-style
  terms. New checked lemmas include `rpder_norm_list_aseq_terms_subsetI`,
  `afactored_steps_aseq_terms_closed_legacy_subsetI`, and
  `afactored1_aseq_terms_frontier_universe_contract`. The unconditional
  row-frontier theorem proves that, after arbitrary many pure Antimirov
  factored-row derivatives from a legacy root `r`, all product-split terms
  remain in
  `partial_derivative_frontier_universe r`; their set has cardinality at most
  `(rsize r + 2)^2`, and every member has size at most
  `Suc (rsize r + rsize r)`. The key closure lemma is
  `partial_derivative_frontier_universe_ntimes_predecessor`, for the counted
  repeat step `RNTIMES q (Suc n) -> RNTIMES q n`. The lemma
  `nested_star_row_not_cubic_but_terms_are_cubic` documents the key distinction:
  a whole row may leave the coarse cubic universe, while the split terms remain
  in the bounded frontier universe.
- Corrected normal-derivative frontier closure:
  `anorm_der_eq_rders_pder_norm` proves that the collapsed factored transition
  equals the existing normal derivative iterator.  The old
  `rders_pder_norm_aseq_terms_frontier_universe_contract` is only an auxiliary
  split-atom theorem.  The user-requested normal-frontier theorem is now
  `rfrontier_rders_pder_norm_subset_apder_frontier`: compute
  `rders_pder_norm r s` first, then split only with `rfrontier`, and the
  resulting whole residuals stay in `apder_frontier r` under `apder_nf r`.
  The row closure behind it is `afactored1_apder_rows_subset`.
- Second-stage pruning scaffold:
  `AntimirovFactoredTransition.thy` now has a proof-local wide prune candidate:
  `row_cover_prefixes`, `rsimpWide_prune_pair_raw`,
  `rsimpWide_prune_against_rows_raw`, `rsimpWide_prune_rows_acc_raw`, and
  `rsimpWide_prune_rows_raw`.  It treats `earlier = k` as prefix `RONE`, and
  treats `RSEQ p k` as singleton-prefix coverage.  The checked design is
  hybrid: grouped later rows still rebuild with `rsimp7_SEQ_atom`, matching
  `row_dlforms`; singleton later rows only become `RZERO` when covered or stay
  unchanged.  Checked facts include language preservation
  (`RL_rsimpWide_prune_rows_raw`), length preservation, `rtail_nf` preservation,
  and split-term monotonicity
  `row_dlformss_rsimpWide_prune_rows_raw_subset_rtail_nf`.  This is useful
  scaffolding for the canonical/disjoint second stage, not yet a replacement
  theorem for the production strong simplifier.
- Canonical dlform projection:
  `AntimirovFactoredTransition.thy` now also defines `row_dlforms_list`,
  `row_dlformss_list`, and
  `row_dlform_canonical_rows rs = rdistinct (row_dlformss_list rs) {}`.
  Checked facts:
  `set_row_dlforms_list`, `RL_RALTS_row_dlforms_list`,
  `RL_RALTS_row_dlformss_list`, `RL_RALTS_row_dlform_canonical_rows`,
  `row_dlforms_member_atomic_rtail_nf`,
  `row_dlformss_disjoint_row_dlform_canonical_rows`, and
  `row_dlformss_row_dlform_canonical_rows_eq`.
  The packaged theorem `rsizes_row_dlform_canonical_rows_cubic` says: if source
  rows are `rtail_nf` and their `row_dlformss` are included in
  `partial_derivative_frontier_universe root`, then the canonical projection has
  total size at most `6 * (rsize root + 2)^3`.  This formalizes the user's
  second-phase idea at proof-object level: split to bounded frontier terms,
  deduplicate, obtain a disjoint canonical row list.  It still does not prove
  that production `rsimpStrong` computes this projection.
  `row_dlform_canonical_rows_cubic_contractI` packages the same assumptions into
  language equivalence, disjointness, exact dlform preservation, and cubic size.
  Also checked: `rtail_nf_rpder_strong_rows_raw`,
  `rtail_nf_rpders_strong_rows_raw`,
  `rtail_nf_rpders_strong1_rows_raw`, and the unconditional nonempty-input
  bridge `rtail_nf_rpders_strong1_rows_raw_nonempty`.
  `RL_RALTS_row_dlform_canonical_rpders_strong1_rows_raw` proves that the
  canonical projection over strong raw rows still denotes `Ders s (RL r)` for
  legacy roots.
  Failed shortcut now checked as a counterexample:
  `atomic_rtail_nf_aseq_terms_payment_false`.  Even an atomic `rtail_nf` row can
  hide repeated alternatives in its right continuation, so per-dlform
  `aseq_terms` inclusion alone cannot pay for whole-row size without an extra
  continuation canonicalization invariant.
  Another checked boundary is `rtail_nf_does_not_atomize_row_lforms`: an
  `rtail_nf` row `RSEQ (RALTS [a,b]) c` still opens under `row_lforms` to
  rows such as `RSEQ a c`, so `row_lforms row <> {row}`.  Do not remove the
  explicit atomic premise from lform canonical-row contracts; use the checked
  dlform projection or prove a stronger same-front representation invariant.
- Cleanup rule:
  `AGENTS.md` now requires timeouts for long-running proof/search/fuzz commands
  and residual-process checks for `python`, `poly`, `polyml`, `isabelle`, and
  Java workers after interrupted or overnight runs.  In this slice, bounded
  Isabelle builds were followed by `tasklist` checks with no residual
  `python.exe`, `poly.exe`, `polyml.exe`, or `java.exe`.
- Process hygiene rule:
  `AGENTS.md` now also says to use bounded proof/search/fuzz commands, prefer
  the stable proof wrappers, and check for leftover worker processes after
  interrupted or overnight runs.
- Latest checked lform split-atom contract:
  `row_lformss_rpder_strong_rows_raw_afactored1_aseq_subset`,
  `row_lformss_rpder_strong_rows_raw_afactored1_member_sizeI`, and
  `row_lformss_rpder_strong_rows_raw_afactored1_aseq_contract` are now proved.
  For any
  `x in row_lformss (rpder_strong_rows_raw c (afactored1 r s))`, after
  splitting `x` with `aseq_terms`, the atoms lie in
  `strong_simp_frontier_aseq_universe r`, have cubic cardinality
  `<= 2 * (rsize r + 2)^3`, and have linear member-size bound
  `<= Suc (rsize r + rsize r)`.
  This is deliberately weaker than
  `x in strong_simp_frontier_aseq_universe r`; the remaining same-front
  obligation is to show that the product combination `x` itself is an allowed
  front residual, not merely that its atoms are bounded.

## Latest Checked Canonical-Row Parameterization, 2026-06-07

- `AntimirovFactoredTransition.thy` now has a reusable canonical-row budget
  interface parameterized by an arbitrary finite deep-linear-form universe `U`:
  `rsizes_rows_canonical_dlforms_rsize_set_boundI` and
  `rsizes_row_dlform_canonical_rows_rsize_set_boundI`.
- The self-paying form
  `rsizes_row_dlform_canonical_rows_self_bound` proves that, under `rtail_nf`,
  the canonical projection size is bounded by
  `3 * rsize_set (row_dlformss rows)`.
- The production-strong-row bridge is also checked:
  `row_dlform_canonical_rpders_strong1_rows_raw_universe_contractI`,
  `row_dlform_canonical_rpders_strong1_rows_raw_nonempty_universe_contractI`,
  and
  `row_dlform_canonical_rpders_strong1_rows_raw_nonempty_self_contract`.
  These preserve the derivative language, make the canonical projection
  `row_dlformss_disjoint`, preserve exactly the same `row_dlformss`, and bound
  the canonical projection by either `3 * rsize_set U` or its own
  `row_dlformss` set.
- The newest checked bridge is one-step and directly aligned with the user's
  "same derivative front" picture:
  `Ders_snoc`,
  `row_dlform_canonical_rpder_strong_rows_raw_self_contract`, and
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_self_contract`.
  The last theorem says that canonicalizing
  `rpder_strong_rows_raw c (afactored1 r s)` denotes
  `Ders (s @ [c]) (RL r)`, is `row_dlformss_disjoint`, preserves exactly the
  raw rows' `row_dlformss`, and self-pays by
  `3 * rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))`.
- Same-front preservation through canonicalization is now checked:
  `same_dlfront_rows_row_dlform_canonical_rows`.
  The packaged nonempty strong-row theorem
  `row_dlform_canonical_rpders_strong1_rows_raw_nonempty_same_dlfront_self_contractI`
  says that, under a one-step same-front closure premise for
  `rsimpStrong_raw`, canonicalized strong rows denote `Ders (c # s) (RL r)`,
  remain in the deep front `(c # s)`, are dlform-disjoint, preserve exactly the
  raw rows' `row_dlformss`, and self-pay by that vocabulary's `rsize_set`.
- The one-step generated-dlform payment layer is also checked:
  `row_dlform_canonical_rpder_strong_rows_raw_generated_dlforms_contract`
  and
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_generated_dlforms_contract`.
  These replace the self budget by the explicit generated universe
  `row_dlformss (concat (map (rpder_strong_list_raw c) rows))`; the
  `afactored1` version still denotes `Ders (s @ [c]) (RL r)`.
- The latest checked refinement introduces a stronger simplifier-closure
  payment interface:
  `afactored1_strong_dlform_universe r s c =
  rsimpStrong_dlform_closure
    (set (concat (map (rpder_norm_list c) (afactored1 r s))))`.
  New checked lemmas:
  `row_dlformss_concat_rpder_strong_list_raw_subset_dlform_closure`,
  `row_dlformss_concat_rpder_strong_list_raw_afactored1_subset_universe`,
  `afactored1_strong_dlform_universe_aseq_subset`, and
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_contract`.
  The packaged contract proves language correctness, canonical dlform
  disjointness, exact `row_dlformss` preservation, generated-dlform inclusion
  into the new universe, `aseq_terms` containment in
  `strong_simp_frontier_aseq_universe r`, and the size payment
  `rsizes canonical <=
  3 * rsize_set (afactored1_strong_dlform_universe r s c)`.
  The conditional skeleton
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_cubic_contractI`
  proves that a future
  `rsize_set (afactored1_strong_dlform_universe r s c) <=
  2 * (rsize r + 3)^3` lemma immediately gives
  `rsizes canonical <= 6 * (rsize r + 3)^3`.
- New checked sum-payment refinement:
  `rsize_set_rsimpStrong_dlform_closure_le_sum`,
  `rsize_set_afactored1_strong_dlform_universe_le_sum`, and
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_sum_cubic_contractI`.
  These replace the remaining universe-size premise by the more local target
  ```text
  sum p in set (concat (map (rpder_norm_list c) (afactored1 r s))).
    rsize_set (row_dlforms (rsimpStrong_raw p))
    <= 2 * (rsize r + 3)^3
  ```
  which is the current best formal interface for the user's same-front /
  later-shared accounting argument.
- New checked executable-cost refinement:
  `row_dlforms_list_size r = sum_list (map rsize (row_dlforms_list r))`
  and the named aggregate
  `afactored1_strong_dlform_list_cost r s c`,
  with
  `rsize_set_row_dlforms_le_row_dlforms_list_size`,
  `sum_rsize_set_row_dlforms_rsimpStrong_raw_le_list_size`,
  `rsize_set_afactored1_strong_dlform_universe_le_list_size`, and
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_list_cubic_contractI`.
  The named wrapper
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_dlform_universe_named_list_cubic_contractI`
  uses the shorter premise
  `afactored1_strong_dlform_list_cost r s c <= 2 * (rsize r + 3)^3`.
  Supporting checked simp equations unfold `row_dlforms_list_size` over
  `RZERO`, `RALTS`, and `RSEQ (RALTS ps) k`, making the suffix-copying branch
  explicit for the next same-front accounting proof.
  This gives a concrete target that exposes suffix copying directly:
  ```text
  sum_list
    (map (lambda p. row_dlforms_list_size (rsimpStrong_raw p))
      (concat (map (rpder_norm_list c) (afactored1 r s))))
    <= 2 * (rsize r + 3)^3
  ```
  Proving this list-expanded bound is sufficient for the same one-step
  canonical strong-row cubic conclusion.  It is intentionally stronger than
  the set-sum target, but easier to fuzz and to connect to same-front grouping.
- New checked obstruction:
  `row_dlforms_suffix_copy_rsize_set_not_paid_by_row_size`.  It shows that
  `rsize_set (row_dlforms row) <= rsize row` is false in general, because
  splitting `RSEQ (RALTS [...]) k` can copy the suffix `k` into multiple
  dlforms.  Do not try to finish the cubic proof by a naive per-row-size
  argument.
- Interpretation: the canonical/no-redundant-row side is now separated cleanly
  from the universe-construction side.  The first-stage split-term universe is
  already checked: after computing the normal derivative and then opening it
  with `row_dlforms`/`aseq_terms`, the atoms stay in the original
  `partial_derivative_frontier_universe r`.  The remaining proof needs a
  different object, a row/dlform payment universe `U_row`, for the actual
  strong scan/prune rows; prove both `row_dlformss ... subset U_row` and a
  cubic `rsize_set U_row` bound.  A precise immediate target is
  `rsize_set (afactored1_strong_dlform_universe r s c) <= O((rsize r)^3)`.
  Do not claim the final cubic theorem yet.
- Latest checked split-payment scaffold:
  `aseq_termss_disjoint`, `aseq_terms_live`, `aseq_terms_size_paid`, and
  `rsizes_aseq_terms_paid_universe_boundI` are now proved.  This packages the
  user's second-stage route: once canonical/simplified rows are proved to have
  disjoint split atoms and each surviving row is paid by its own split atoms,
  split-atom inclusion into a cubic frontier universe immediately gives an
  `rsizes` cubic bound.
- Latest checked bridge to the actual one-step strong transition:
  `aseq_termss_row_dlform_canonical_rows_subsetI`,
  `rsizes_aseq_terms_paid_strong_simp_frontier_cubic`,
  `aseq_termss_row_dlform_canonical_rpder_strong_rows_raw_afactored1_subset`,
  and
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_aseq_paid_cubic_contractI`.
  These prove that the canonical rows for
  `rpder_strong_rows_raw c (afactored1 r s)` already have the right language
  and split-atom universe, and that the full cubic `rsizes` bound follows as
  soon as the same-front/no-redundant split payment obligations are discharged.
- Latest checked front-linear-form universe scaffold:
  `rsimpStrong_lform_closure` and `afactored1_strong_lform_universe` are now
  defined as the shallow linear-form analogue of the existing deep-form
  closure.  Generated strong rows are connected by
  `row_lformss_concat_rpder_strong_list_raw_subset_lform_closure` and
  `row_lformss_concat_rpder_strong_list_raw_afactored1_subset_universe`.
  Because lforms are not unconditionally monotone through strong pruning, the
  actual raw-row bridge is intentionally conditional:
  `row_lformss_rpder_strong_rows_raw_afactored1_subset_lform_universe_payload_stableI`.
  The new contract
  `rpder_strong_rows_raw_afactored1_lform_universe_cubic_contractI` proves that
  the actual one-step strong rows have the right derivative language and cubic
  `length/card/rlinear_termss/rsizes` as soon as three remaining obligations
  are supplied: lform disjoint/live/paid, payload-stable lform inclusion, and a
  cubic `rsize_set` bound for `afactored1_strong_lform_universe`.
- Checked obstruction for the current canonicalizer:
  `row_dlform_canonical_rows_aseq_payment_false` shows that
  `row_dlform_canonical_rows` being canonical for `row_dlforms` does not imply
  `aseq_terms_size_paid`.  In particular, a row such as
  `RSEQ (RCHAR a) (RALTS [RCHAR b, RCHAR b, RCHAR b, RCHAR b, RCHAR b])`
  is `rtail_nf` and survives as a singleton deep row, but its size is not paid
  by its split atoms.  So the next proof step needs either a genuine
  split-atom canonicalization/merge layer or an additional theorem that the
  actual strong simplifier removes this form of redundancy.
- Strong-normal-form obstruction:
  `rsimpStrong_fixed_aseq_terms_payment_false` shows that even an
  `rsimpStrong_fuel_fixed` non-alt nonzero row can fail the current
  `aseq_terms_size_paid` invariant.  The witness
  `RSEQ (RCHAR a) (RSEQ (RCHAR a) (RCHAR a))` confirms that the current
  `aseq_terms` splitter is too fine for size payment.  Keep it for inclusion
  into the bounded frontier universe, but use the front-indexed
  Antimirov/linear-form terms (`alform_front` / `same_lfront_rows`) as the
  payment units for the user's same-front proof route.
- Verification: direct Isabelle `Posix` build passed after these additions,
  including the `afactored1_strong_dlform_universe` contract and the
  sum-cubic plus list-expanded cost wrappers/simp equations.  A later build
  also passed after the split-payment scaffold and the actual one-step strong
  transition bridge; another build passed after the checked current-canonicalizer
  payment obstruction, and another passed after the strong-normal-form
  obstruction.  A further bounded direct build passed after the
  front-linear-form universe scaffold and actual one-step lform-universe
  contract.  A further bounded direct build passed after
  `rtail_nf_does_not_atomize_row_lforms`.
  Follow-up `tasklist` checks found no residual `python.exe`, `poly.exe`,
  `polyml.exe`, or `java.exe`.
- Process hygiene after the 2026-06-07 restart: prefer the stable repo-local
  wrappers `scripts/codex-isabelle-build-posix.ps1` and
  `scripts/codex-proof-workers.ps1`.  The build wrapper runs a bounded Posix
  Isabelle build; the worker wrapper checks or kills only stale proof-worker
  processes tied to this repo or `C:\Users\Chengsong\Isabelle2025-2`.

## Latest Checked Same-Front Strong Closure, 2026-06-07

- `AGENTS.md` now explicitly records the process hygiene rule: use bounded
  proof/search/fuzz commands, prefer the stable proof wrappers, and check for
  leftover workers after long or interrupted runs.
- `AntimirovFactoredTransition.thy` now names the user's front block directly:

  ```text
  derivative_front_terms r s = aseq_termss (afactored1 r s)
  ```

  and `same_aseq_front_row root front row` means
  `aseq_terms row subset derivative_front_terms root front`.
- Checked normal-derivative front-block theorem:

  ```text
  row_dlforms_rders_pder_norm_same_frontier_contract
  ```

  If `x in row_dlforms (rders_pder_norm r s)`, then `x`'s split atoms are in
  the concrete block `derivative_front_terms r s`; for legacy roots that block
  is contained in `partial_derivative_frontier_universe r`.
- Cleanup facts were added so generated Antimirov rows can be compared to the
  cleaned next front without pretending cleanup preserves every syntactic row:
  `aseq_termss_rflts_insert_zero_superset`,
  `aseq_termss_generated_subset_afactored_step_insert_zero`, and
  `derivative_front_terms_snoc_generated_insert_zero`.  Intuitively, flattening
  and distinct cleanup can only lose the dead split atom `RZERO`.
- The strong-simplifier front block is now explicit:

  ```text
  strong_derivative_front_terms r s =
    rsimpStrong_aseq_closure (insert RZERO (derivative_front_terms r s))
  ```

  This is the current derivative-front block after allowing `rsimpStrong_raw`
  to simplify inside the block.
- Checked one-step same-front strong bridges:

  ```text
  row_dlforms_rsimpStrong_raw_rpder_norm_list_afactored1_same_strong_front
  row_dlformss_concat_rpder_strong_list_raw_afactored1_same_strong_front
  row_dlformss_rpder_strong_rows_raw_afactored1_same_strong_front
  row_dlform_canonical_rpder_strong_rows_raw_afactored1_same_strong_front
  ```

  The key usable shape is:

  ```text
  x in row_dlformss (rpder_strong_rows_raw c (afactored1 r s))
  ==> aseq_terms x subset strong_derivative_front_terms r (s @ [c])
  ```

  and the same is true after `row_dlform_canonical_rows`.
- Also checked
  `strong_derivative_front_terms_subset_strong_simp_frontier`, so the new
  front-indexed strong block refines the older global
  `strong_simp_frontier_aseq_universe r`.
- Added per-front budget wrappers:
  `card_strong_derivative_front_terms_cubic`,
  `rsize_set_strong_derivative_front_terms_cubic`,
  `strong_derivative_front_terms_member_size_linear`, and
  `row_dlformss_rpder_strong_rows_raw_afactored1_same_strong_budget_contract`.
  Each current strong-front block now carries checked cubic card and
  `rsize_set` budgets, plus the linear member-size bound.
- Lifted the bridge to canonical row lists:
  `same_strong_aseq_front_rows`,
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_same_strong_front_rows`,
  and
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_same_strong_budget_contract`.
  The canonical rows for one strong step now satisfy:

  ```text
  aseq_termss (row_dlform_canonical_rows
    (rpder_strong_rows_raw c (afactored1 r s)))
    subset strong_derivative_front_terms r (s @ [c])
  ```

  with cubic budgets for that same front block.
- Added the front-specific split-payment conditional theorem:
  `rsizes_aseq_terms_paid_strong_derivative_front_cubic` and
  `row_dlform_canonical_rpder_strong_rows_raw_afactored1_same_strong_aseq_paid_cubic_contractI`.
  If the canonical rows for one strong step satisfy the remaining
  disjoint/live/paid obligations inside their current
  `strong_derivative_front_terms r (s @ [c])` block, then the theorem yields
  the derivative language, exact `row_dlformss` preservation, and
  `rsizes <= 6 * (rsize r + 2)^3`.
- Multi-step dcanon scaffold now exists for the explicit canonical transition
  `rpders_strong_dcanon_rows_raw`: checked lemmas
  `legacy_rpders_strong_dcanon_rows_raw`,
  `row_dlformss_disjoint_rpders_strong_dcanon_rows_raw_nonempty`,
  `row_dlforms_live_paid_rpders_strong_dcanon_rows_raw_nonempty`,
  `rsizes_rpders_strong_dcanon_rows_raw_nonempty_rsize_set_boundI`, and
  `rpders_strong_dcanon_rows_raw_nonempty_rsize_set_budgetsI`.
  For singleton roots, the packaged interfaces
  `rpders_strong_dcanon1_rows_raw_nonempty_universe_contractI` and
  `rpders_strong_dcanon1_rows_raw_nonempty_universe_cubic_contractI` add
  derivative-language correctness and expose the final theorem shape under a
  finite/cubic `U` premise.
  The bridge lemmas `rsize_set_le_card_times_bound` and
  `rsize_set_le_card_member_budgetI`, together with
  `rpders_strong_dcanon1_rows_raw_nonempty_card_member_cubic_contractI`, allow
  the active-suffix style of proof: prove `row_dlformss ... subset U`,
  `card U <= C`, every member has size `<= M`, and `C * M` is cubic.
  Thus after any nonempty input, the dcanon output is already disjoint/live/paid
  by deep linear forms, and any finite `U` containing its `row_dlformss` gives
  length/card/rlinear_termss/rsizes bounded by `3 * rsize_set U`.
- New checked list-cost payment wrapper:
  `row_dlforms_member_size_le_list_size`,
  `rsimpStrong_dlform_closure_member_list_size_bound`,
  `afactored1_strong_dlform_universe_member_size_le_list_cost`, and
  `afactored1_strong_dlform_universe_list_cost_budget`.  For the one-step
  candidate `U_row = afactored1_strong_dlform_universe r s c`, the named cost
  `afactored1_strong_dlform_list_cost r s c` pays both `rsize_set U_row` and
  every member size of `U_row`.  The remaining task is still to prove that this
  cost, or a smaller same-front/later-shared replacement universe, is cubic.
- New checked card/generated-size payment wrapper:
  `rsize_set_afactored1_strong_dlform_universe_card_generated_boundI`,
  `rsize_set_afactored1_strong_dlform_universe_card_generated_cubicI`,
  `rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_card_generated_cubic_contractI`,
  and
  `rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_card_generated_cubic_budgetsI`.
  The next second-stage target is now explicit: prove
  `card U_row <= C`,
  `rsizes (concat (map (rpder_norm_list c) (afactored1 r s))) <= M`, and
  `C * M <= 2 * (rsize r + 3)^3`.  Those three facts immediately give the
  one-step dcanon language contract, exact `row_dlformss` preservation,
  disjoint/live/paid rows, and all four cubic row budgets.
- Discarded proof attempt to remember: a broad shrink of the
  `aseq_terms_live` assumption was tried and removed.  The naive implication
  `row_dlforms_live -> aseq_terms_live` is too broad for the generalized
  datatype, and the `legacy + rtail_nf` variant should be proved by small
  constructor lemmas, not by broad `fastforce`.
- Current remaining proof gap: the inclusion/no-mixed-front side is now
  stronger and front-indexed for strong rows.  This is the completed first
  stage, not the missing `U`.  The final regex cubic bound still needs the
  second-stage canonical/payment theorem: inside one allowed same-front block,
  prove the simplifier/canonical representation does not keep redundant
  combinations, or define a checked canonical pass that does.  Equivalently,
  construct a cubic row/dlform universe `U_row` for whole `row_dlformss`
  combinations, rather than re-proving split-atom inclusion.
- Verification: bounded `Posix` Isabelle build passed after these additions;
  later bounded builds also passed after `rtail_nf_does_not_atomize_row_lforms`
  and after the nonempty dcanon budget scaffold plus packaged universe
  contracts, after the card/member-size bridge, and after the list-cost
  member-size/budget wrapper, and after the card/generated-size dcanon
  wrappers.  A timed-out discarded live-assumption shrink attempt left two
  PolyML proof workers from this run; they were terminated by PID.  The final
  bounded build passed and the final proof-worker check found no residual
  matching processes.
- New checked deep same-front Antimirov frontier:
  `apder_dlfrontier r = UNION q in apder_rows r. row_dlforms q`.
  Checked lemmas:
  `finite_apder_dlfrontier`,
  `adlform_front_subset_apder_dlfrontier`,
  `row_dlforms_rders_pder_norm_subset_apder_dlfrontier`, and
  `rsize_set_row_dlforms_rders_pder_norm_le_apder_dlfrontier`.
  The key first-stage statement is now:

  ```text
  row_dlforms (rders_pder_norm r s) subset apder_dlfrontier r
  ```

  under `apder_nf r`.  This is the user's same-front split route: first compute
  the normal Antimirov derivative, then open grouped `RSEQ (RALTS ps) k` rows
  along that same front.  It is distinct from both the whole-residual
  `rfrontier_rders_pder_norm_subset_apder_frontier` theorem and the older
  auxiliary `aseq_terms` accounting.  Do not count final rows by raw
  `aseq_terms`.
- Next proof target: either show
  `apder_dlfrontier r subset partial_derivative_frontier_universe r`, or prove
  a direct cubic `rsize_set` bound for `apder_dlfrontier`.  The likely required
  bridge is a continuation-closure lemma of the form: a front-owned `rtail_nf`
  row has all `row_dlforms` inside the original-root universe.  This is the
  nontrivial part; avoid replacing it with split-atom inclusion.

Two useful secondary shrinks:

- Max-only local peak:
  `STAR(ALT(SEQ(CH(a),ALT(CH(a),CH(b))),CH(a)))` on input `a`.
  Scan gives rows/terms/deepTerms/size `1/2`, `3/3`, `3/3`, `13/20`, but max
  row grows `13/12`.
- Same-budget DAG sharing:
  `STAR(ALT(SEQ(STAR(CH(a)),STAR(ZERO)),SEQ(CH(a),CH(b))))` on input `a`.
  Scan and Antimirov have rows/terms/deepTerms/size `2/2`, `2/2`, `2/2`,
  `19/19`, mutually bridge-cover, but scan DAG is `11/10`. The harness labels
  this as `sameBudgetCover`.
- Budget-nonworse cover:
  `STAR(SEQ(CH(b),ALT(SEQ(CH(b),ALT(ONE,CH(b))),ONE)))` on input `bb`.
  Scan and Antimirov have rows/terms/deepTerms/size `2/2`, `3/4`, `4/5`,
  `30/32`, while scan has secondary DAG/max-shape tradeoffs `13/12` and
  `9/8`. The harness labels this as `budgetNonworseCover`.

## Required Check Before Commit

After any meaningful Isabelle change:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240
```

Commit only intentional tracked files. Do not commit the `*.thy~` backups.

## 2026-06-08 Latest Normal-Frontier Update

- New dedicated first-stage theory: `AntimirovNormalFrontier.thy`, included in
  `ROOT`.
- Checked normal Antimirov package:
  `normal_derivative_frontier_subset`,
  `normal_derivative_frontier_cubic_size`,
  `normal_factored_rows_subset`,
  `normal_factored_rows_cubic_budget`,
  `normal_factored_rows_contract`, and
  `normal_canonical_factored_rows_contract`.
- The intended first stage is now explicit and non-atomizing:

  ```text
  rfrontier (rders_pder_norm r s) subset normal_antimirov_frontier r
  set (afactored1 r s) subset normal_antimirov_rows r
  ```

  under `apder_nf r`.  Examples in the file check that whole residuals such as
  `a(aa)`, `aa`, `a`, and `a(b+b+b)` are retained; do not replace this by
  `aseq_terms` splitting.
- Added `normal_frontier_canonical_rows`: it opens only `rfrontier` and
  deduplicates.  The checked contract preserves language and bounds all four
  budgets by `(apder_awidth r + rsize r + 3)^3`.
- Added the checked obstruction
  `normal_antimirov_frontier_not_raw_shared_prune_closed`: the normal frontier
  alone is not closed under `rsimpStrong_prune_pair_raw`.  This is the formal
  reason the second stage must count actual same-front combinations.
- Added `normal_same_front_prune_closure`:

  ```text
  raw_shared_prune_same_suffix_closure (normal_antimirov_frontier r)
  ```

  and checked `normal_same_front_prune_closure_member_cubic_size`: every member
  of this same-front closure has cubic member size.  The current remaining
  target is a cubic cardinality/total-size bound for the actual scan-generated
  combinations, not for arbitrary all-pairs closure and not for atomized
  `aseq_terms`.
- Added the stronger actual-scan owner candidate:

  ```text
  normal_strong_scan_owner r =
    raw_shared_prune_active_suffix_owner (apder_strong_frontier r)
  ```

  This starts from `rsimpStrong_raw` applied to each Antimirov residual, then
  closes under active shared-suffix scan outputs.  Checked
  `normal_strong_scan_owner_member_expanded_cubic_size`: every owner member has
  size at most `2 * (apder_awidth r + rsize r + 3)^3`.  The missing part is a
  cubic count/total-size bound for the actually reachable owner rows or a
  sharper scan-indexed sub-owner.
- Latest bounded `Posix` build passed, followed by
  `scripts\codex-proof-workers.ps1 -Action Check` with no residual workers.

## 2026-06-08 Deep-Row Cubic Accounting Update

- New checked tight-delta bridge in `AntimirovFactoredTransition.thy`:
  `rsize_set_apder_dfrontier_acc_le_tight_delta_budget`,
  `rsize_set_apder_deep_frontier_le_tight_delta_budget`, and
  `rsize_set_adlform_front_le_tight_delta_budget`.
  This is now the preferred scaffold for the second-stage deep-row split.
- New checked member-size half:

  ```text
  apder_deep_frontier_member_expanded_square_size
  ```

  Under `apder_nf r`, every member of `apder_deep_frontier r` has size at most
  `(apder_awidth r + rsize r + 3)^2`.
- New checked conditional final interface:

  ```text
  rsize_set_adlform_front_cubic_from_deep_linear_card
  ```

  If `card (apder_deep_frontier r) <= apder_awidth r + rsize r + 3`, then
  `rsize_set (adlform_front r s)` is cubic.  The remaining hard theorem is now
  the linear cardinality bound for distinct deep row-forms.
- New checked conditional canonical-row wrapper:

  ```text
  row_dlform_canonical_afactored1_same_dlfront_linear_card_cubic_contract
  ```

  Under the same linear-cardinality premise, the canonical rows preserve
  language, stay in the same dlfront, are disjoint, have exact
  `row_dlformss = adlform_front r s`, and satisfy
  `rsizes rows <= 3 * (apder_awidth r + rsize r + 3)^3`.
- New checked diagnostic/list bridge:

  ```text
  rsize_set_adlform_front_le_afactored1_row_dlforms_list_size
  ```

  This is not the final argument; list-cost can over-count repeated suffixes.
- The attempted raw-`rsize k` potential for arbitrary continuations is too
  crude in nested `RSTAR`: the recursive continuation syntactically repeats
  the star body.  Do not spend time trying to force a fixed
  `|r|*|k|+|r|^2` potential unless it uses a compressed continuation measure.
- Added closure lemmas:
  `rderiv_fuel_closure_mono`,
  `rlinear_continuations_continuation_subset_fuel`,
  `rderiv_fuel_closure_continuation_closed`, and
  `rderiv_fuel_closure_idempotent_subset`.
  Plain subterm/continuation closure is still insufficient for rows such as
  `(a+b)c`, because exposed rows like `ac` and `bc` are pair combinations.
  The next closure/universe must include the legitimate same-front
  payload-continuation pairs without allowing arbitrary all-pairs explosion.
- Latest bounded `Posix` build passed after these additions, and
  `scripts\codex-proof-workers.ps1 -Action Check` reported no residual
  proof-worker processes.

## 2026-06-08 Strong Local-Universe Update

- New checked dcanon inclusion:

  ```text
  row_dlformss
    (rpder_strong_dcanon_rows_raw c (afactored1 r s))
    subset afactored1_strong_dlform_universe r s c
  ```

  The theorem is
  `row_dlformss_rpder_strong_dcanon_rows_raw_afactored1_subset_strong_dlform_universe`.
  This shows canonicalization stays inside the same step-local strong dlform
  universe; it does not create an additional off-front problem.
- New checked negative result:

  ```text
  rsimpStrong_raw_row_dlforms_cost_not_monotone
  ```

  There is an `apder_nf` example with
  `rsize_set (row_dlforms (rsimpStrong_raw p)) = 12`, while
  `rsize_set (row_dlforms p) = 10` and `row_dlforms_list_size p = 10`.
  Therefore the raw/strong-dcanon route cannot be closed by proving local
  `row_dlforms` cost nonincrease for `rsimpStrong_raw`.  Continue with a
  global same-front/shared-suffix count or a sharper whole-residual universe.
- New checked same-front rows-closure bridge:

  ```text
  afactored1_strong_dlform_universe r s c
    subset rsimpStrong_dlform_closure (set (afactored1 r (s @ [c])))
  ```

  with the corresponding `rsize_set` monotonic bridge and dcanon inclusion:
  `rsize_set_afactored1_strong_dlform_universe_le_next_rows_closure` and
  `row_dlformss_rpder_strong_dcanon_rows_raw_afactored1_subset_next_rows_closure`.
- New checked conditional wrapper:

  ```text
  rpder_strong_dcanon_rows_raw_afactored1_next_rows_closure_cubic_contractI
  ```

  If the strong dlform closure of the next normal factored row set
  `set (afactored1 r (s @ [c]))` has cubic `rsize_set`, then the old
  raw strong/dcanon step gets the existing language/disjoint/live/paid/cubic
  contract.  This is the current preferred formulation of the remaining
  old/raw obligation.

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
7. AntimirovFactoredTransition.thy around apder_terms, apder_frontier, afactored1_apder_rows_subset, and rfrontier_rders_pder_norm_subset_apder_frontier
8. agent_hunt_pipeline/scala/PosixCubicSmoke.scala around factoredActiveRowsFromRowsId and strongRowsBridgeRowsId

Start with git fetch/status. The old untracked backup files BackRefLang.thy~, BackRefLang4Pilot.thy~, and Lexer.thy~ were intentionally deleted at the user's request; do not resurrect them.

The final cubic theorem is NOT proved. Do not claim BR-039/BR-040 or final cubic bounty. The corrected normal-derivative frontier theorem is now proved: rfrontier_rders_pder_norm_subset_apder_frontier says that after first computing rders_pder_norm r s, splitting only with rfrontier keeps the whole Antimirov residuals inside apder_frontier r, under apder_nf r. Do not replace this by the older aseq_terms/row_dlforms split-atom theorem; that theorem is auxiliary only and over-splits examples like a(aa). The next first-stage budget task is polynomial cardinality/member-size/rsize_set accounting for apder_frontier r, or for a checked equivalent path-frontier universe that keeps whole multi-suffix residuals. The remaining second-stage gap is still the representation bridge from bounded same-front residual vocabularies to the concrete raw rows produced by strong scan/prune. The promising Scala DAG bridge includes iterative factoredActiveRowsFromRowsId, while Isabelle bridge_owner is not the same object. Your priority is to finish the apder/path-frontier budget, then formalize or replace the concrete original-regex-owned factor-row/later-shared universe U, prove the needed closure/cardinality/member-size bounds for raw/factored rows, and connect it to strong_deferred_original_raw_row_norm_later_shared_memo_cubic_interface.

Also read the new wide-prune scaffold in AntimirovFactoredTransition.thy around row_cover_prefixes and rsimpWide_prune_rows_raw. It is checked to preserve language, length, rtail_nf, and row_dlformss subset under rtail_nf. Its hybrid design is deliberate: grouped rows use rsimp7 to align with row_dlforms; singleton rows are only deleted or left unchanged. This is a route toward the canonical/disjoint second stage, not yet the final simplifier theorem.

Then read the canonical dlform projection around row_dlform_canonical_rows. The theorem rsizes_row_dlform_canonical_rows_cubic is checked and packages the user's two-step proof plan for any rtail_nf source rows whose dlforms are already in the original frontier universe. The missing bridge is computational/representational: show the actual strong simplifier rows can be replaced by, or compute, this canonical projection while preserving the required POSIX/value semantics.

Avoid wrappers, rsimp9 revival, broad auto/blast/sledgehammer lines over 1-2 seconds, and Isabelle eval smoke grids. Use Scala for broad smoke. After every meaningful checked checkpoint, run:
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\isabelle_ci.ps1 -SkipFetch -NoCertificate -Role admin -SessionTimeoutSeconds 240

Commit and push only intentional tracked files to origin/codex/backref-values.
```
