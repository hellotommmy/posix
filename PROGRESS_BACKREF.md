# POSIX Backreference Progress

Last updated: 2026-05-31 (rsimp9 RNTIMES zero-count repair)

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
