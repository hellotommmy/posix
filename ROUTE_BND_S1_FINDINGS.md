# Route-1 BND lane S1 findings

Date: 2026-06-21

Branch: `card/route1-bnd`
Theory: `r1bnd/Card_Route1_Bnd.thy`
Session: `Posix_Card_Route1_Bnd`

## Current green local helpers

The worktree has green helper edits in `r1bnd/Card_Route1_Bnd.thy`:

- `finite_single_root`
- `finite_single_term`
- `strong_apder_acc_singleton_decomp`
- `boundary_excess` / `root_excess` definitions for the cardinal-only repair
- `card_le_if_missing_in_image`
- `finite_boundary_excess` / `finite_root_excess`
- small constructor subset leaves: `RZERO`, `RONE`, `RCHAR`, and `RALTS` with
  continuation `RZERO` or `RONE`

The session builds green with the private `USER_HOME` heap command from `ROUTE_BND.md`.

## Negative result: [REFUTED helper only] uniform_S_image_boundary_subset

The refuted helper is the stronger image-subset statement:

```isabelle
strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k
  \<subseteq> rsimpStrong_raw ` (single_root t k - strong_apder_acc RONE k)
```

This helper is false.  This does **not** refute the S1 cardinal inequality, and
does **not** refute `boundary_term_absorb`.  A temporary Isabelle lemma, added
only for verification and then removed, proved the following witness under the
private heap build:

```isabelle
fixes a
defines "t \<equiv> RSEQ (RCHAR a) (RALTS [RSEQ (RCHAR a) (RSTAR (RCHAR a))])"
defines "k \<equiv> RSTAR (RCHAR a)"
defines "bad \<equiv>
  RSEQ (RCHAR a)
    (RSEQ (RCHAR a)
      (RSEQ (RSTAR (RCHAR a)) (RSTAR (RCHAR a))))"
shows "bad \<in> strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k"
  and "bad \<notin> rsimpStrong_raw ` (single_root t k - strong_apder_acc RONE k)"
```

The proof script that Isabelle accepted for this temporary witness was:

```isabelle
by (simp_all add: t_def k_def bad_def strong_apder_acc_def single_root_def
    rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
    rsimpStrong_prune_rows_raw_def rsimpStrong_prune_pair_raw_def
    rsimp7_SEQ_atom_def Let_def)
```

Consequently the `rsimpStrong_raw` image route plus `card_image_le` cannot prove S1.
This is a fail-stop result for that skeleton, not a new route.

Important classification: this witness is `RSEQ`-root, since the top constructor of
`t` is `RSEQ`.  Thus it also refutes the proposed RSEQ image branch as stated; this
contradicts any route status claiming that branch is validated for all RSEQ roots.
The exact `t,k` above should be reconciled before the lane spends more proof time on
that image-subset branch.

Final state after removing the temporary witness: `Posix_Card_Route1_Bnd` builds green.

## Cardinal-only repair sanity checks

Temporary Isabelle checks, added only for validation and then removed, were green for:

1. `t = RSEQ (RCHAR a) (RSTAR (RCHAR a))`, `k = RSTAR (RCHAR a)`.
   This is the old plain-subset failure.  The refined missing-row condition
   "X-Y is contained in the `rsimpStrong_raw` image of Y-X" holds on this witness.
2. `t = RSEQ (RCHAR a) (RALTS [RSEQ (RCHAR a) (RSTAR (RCHAR a))])`,
   `k = RSTAR (RCHAR a)`.  The previous `bad` row lies in `X \<inter> Y`, so it
   disappears from `X-Y`; the refined missing-row condition holds on this witness.
3. A non-RSEQ sample `t = RCHAR a`, `k = RSTAR (RCHAR a)`.  Here `X \<subseteq> Y` and
   `X-Y = {}`.

The broad one-shot formalizations were deliberately not kept: both full non-RSEQ
case-simp and arbitrary RSEQ case-simp timed out as proof scripts.  The next proof
step should continue splitting the refined target into small constructor lemmas.
