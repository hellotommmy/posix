# Posix Backref Design Log

This file records semantic design changes that affect later proofs. It is meant
to be read before continuing long-running agent work.

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
