# Route-1 BND lane S1 findings

Date: 2026-06-21

Branch: `card/route1-bnd`
Theory: `r1bnd/Card_Route1_Bnd.thy`
Session: `Posix_Card_Route1_Bnd`

## Current green local helpers

The worktree currently has a small helper edit in `r1bnd/Card_Route1_Bnd.thy`:

- `finite_single_root`
- `finite_single_term`
- `strong_apder_acc_singleton_decomp`

The session builds green with the private `USER_HOME` heap command from `ROUTE_BND.md`.

## Negative result: the RSEQ image skeleton is false

The proposed RSEQ half of the S1 skeleton was:

```isabelle
strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k
  \<subseteq> rsimpStrong_raw ` (single_root t k - strong_apder_acc RONE k)
```

This statement is false.  A temporary Isabelle lemma, added only for verification and
then removed, proved the following witness under the private heap build:

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

Final state after removing the temporary witness: `Posix_Card_Route1_Bnd` builds green.
