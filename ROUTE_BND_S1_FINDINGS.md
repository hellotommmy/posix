# Route-1 BND lane S1 findings

Date: 2026-06-21

Branch: `card/route1-bnd`
Theory: `r1bnd/Card_Route1_Bnd.thy`
Session: `Posix_Card_Route1_Bnd`

## Current green local helpers

The worktree has green helper edits in `r1bnd/Card_Route1_Bnd.thy`.
The latest live route is **not** an S-image route; keep these helpers only as
banked finite/subset facts unless a later hand-proof reuses them.

- `finite_single_root`
- `finite_single_term`
- `strong_apder_acc_singleton_decomp`
- `boundary_excess` / `root_excess` definitions for the cardinal-only repair
- `card_le_if_missing_in_image`
- `card_le_of_card_diff_le`
- `term_excess`
- `bnd_spine` / `bnd_profile` / `bnd_key` / `bnd_counts` /
  `bnd_lift_compatible`
- `finite_boundary_excess` / `finite_root_excess` / `finite_term_excess`
- small constructor subset leaves: `RZERO`, `RONE`, `RCHAR`, and `RALTS` with
  continuation `RZERO` or `RONE`
- `RSTAR` equality/subset/missing leaves
- vacuous/subset leaves for `RNTIMES`, `RBACKREF4`, `RHALF`, and `RRESIDUE`

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

## Dead route: missing-image repair

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
step at that time was to split the refined target into small constructor lemmas.

This is now superseded.  A later Secretary/Pro probe refuted the refined
missing-image premise too:

```isabelle
X t k - Y t k \<subseteq> rsimpStrong_raw ` (Y t k - X t k)
```

The cause is that `rsimpStrong_raw` over-collapses the trailing star nest.  A
clean RSEQ-root counterexample is recorded in `ROUTE_BND.md`:
`t=(c+a·b*)·b*`, `k=b*·b*`, with `a·(b*·b*) \<in> X-Y` but not in the
`rsimpStrong_raw` image of `Y-X`.

This refutes only the helper route.  It does **not** refute the S1 cardinal
inequality and does **not** refute `boundary_term_absorb`.

## Live route

The current live target is:

```isabelle
card (X t k - Y t k) \<le> card (Y t k - X t k)
```

via a definable injection from `X-Y` into `Y-X`, using the least-dominator
star-run lift over the `bnd_profile`/`bnd_key`/`bnd_counts` interface.  Do not
formalize `inj_on` yet.  The injection proof waits for the Secretary hand-proof
of:

- `D_nonempty`: every `x \<in> X-Y` has a compatible candidate in `Y-X`.
- `D_chain`: within each key-class, candidates form a chain / unique least.
