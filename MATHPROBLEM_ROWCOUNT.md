# Open Problem: Antimirov Row-Count Linearity (the D law)

Status: OPEN, CORRECTED TWICE 2026-06-13.  The original max-1
`apder_zwidth` D law and the first J* numeric invariant are FALSE at depth 5
(see CORRECTION below).  The raw `apder_zw2` law is also FALSE if zero counted
repetitions are allowed in continuations: a checked 04:00 CE uses
`RNTIMES _ 0` alternatives with zero budget but non-`RONE` frontier rows.
The live salvage target for the current cubic chain is therefore the
legacy/non-backref, `rntimes_free` instance of the `apder_zw2` law, or a
future zero-count-aware weight/premise if the admin chooses to reopen the
general NTIMES statement.  Do not try to prove the raw unrestricted `zw2`
law.

## Definitions (all in AntimirovFactoredTransition.thy)

- `apder_term_frontier_acc r k` (line ~1739), written `acc r k` here:
  RZERO/RONE -> {}; RCHAR -> rfrontier k;
  RALTS rs -> union of members; RSEQ r1 r2 ->
  acc r1 (sigma4 r2 k) UNION acc r2 k; RSTAR r ->
  acc r (sigma4 (RSTAR r) k); where sigma4 = rsimp4_SEQ_atom.
- `rfrontier k` (GeneralRegexBound ~3862): RZERO -> {}, RALTS ->
  union of member frontiers, else singleton {k}.
- `apder_zwidth` (landed 2026-06-12, commit 1d0d115): C=1,
  ALTS/SEQ = sum, STAR x = max 1 (zwidth x), RZERO/RONE = 0,
  NTIMES r n = n * max 1 (zwidth r).
- `apder_zw2` (landed 2026-06-13, commit 8a7a370): C=1,
  ALTS/SEQ = sum, STAR x = Suc (zw2 x), RZERO/RONE = 0,
  NTIMES r n = n * Suc (zw2 r).  Checked surface:
  `apder_zwidth_le_apder_zw2` and `apder_zw2_rntimes_free_le_rsize`.
- `apder_nf` (line ~1791): no RZERO/RONE parts in SEQ, nonalt
  alternation members, head of SEQ non-SEQ.

## The law

```
apder_nf r ==> apder_nf k ==>
card (acc r k - rfrontier k) <= apder_zw2 r
```

This unrestricted form is now checked false.  The current proof-useful target
is the rntimes-free form:

```
legacy_rrexp r ==> legacy_rrexp k ==>
apder_nf r ==> apder_nf k ==> rntimes_free r ==> rntimes_free k ==>
card (acc r k - rfrontier k) <= apder_zw2 r
```

## What is known

1. The old zwidth law is FALSE: deep sampling found nested zero-consuming
   star CEs after shallower runs had passed.  The corrected zw2 law passed
   295,551 deep samples in the 2026-06-13 correction run.  Future sampling
   claims must include depth>=5 and directed nested-star/zero-width
   families.
2. awidth instead of zwidth is FALSE: zero-width stars (STAR RONE
   stacks) give frontier rows without letters.
   CE: r = SEQ b (ALTS [a, STAR(RONE), STAR(STAR RONE)]), k=RONE.
3. Falsified strengthenings (do NOT retry):
   - D+ subset discount: +1 discount when rfrontier k nonempty and
     a subset of acc.  CE: r = SEQ a (ALTS [a, STAR(STAR a)]),
     k = RONE (card 3 = zwidth 3, no slack; discount overdraws).
   - intersect discount (acc INT Fk nonempty): same CE.
   - membership companions (rfrontier t SUBSET acc r t under
     zwidth>=1 or awidth>=1): both false; STAR REWRITES leaf
     continuations (acc(STAR a, t) = {RSEQ (STAR a) t}).
   - difference against k only is the law itself; difference against
     the fully-consumed composite was never made precise.
4. Anatomy of the hard case (SEQ r1 r2 with k = RONE): the character
   leaves of r1 see continuation r2 VERBATIM (sigma4(r2,RONE)=r2), so
   one leaf (budget 1) imports the whole frontier F(r2) (W(r2) points).
   The books balance ONLY because F(r2) overlaps acc(r2, RONE) - the
   sibling sum - i.e. inclusion-exclusion across the union
   acc(r1,r2) UNION acc(r2,RONE).  Single-set unary discounts cannot
   see this; the invariant must speak about the OVERLAP
   card(F(r2) INT acc(r2,RONE)) or jointly bound
   card((F(r2) UNION acc(r2,RONE)) - {RONE})  - note the latter as
   stated (<= zwidth r2) is FALSE by the same CE family with the
   singleton F(SEQ) point; some +constant or a structurally smarter
   merge is needed.
5. Raw `apder_zw2` D is FALSE with zero counted repetitions:
   `r = RSEQ (RCHAR c)
     (RALTS [RNTIMES (RCHAR a) 0, RNTIMES (RCHAR b) 0])`,
   `k = RONE`.  Isabelle checks `card(acc r RONE - {RONE}) = 2`
   while `apder_zw2 r = 1`
   (`apder_zw2_D_law_rntimes_zero_alt_false`).  Mechanism: each
   `RNTIMES _ 0` contributes no accumulator rows and no `zw2` budget, but
   remains a distinct frontier atom imported by the preceding character.

## Payoff when landed

- card(apder_rows r) <= zw2 r + 2 (k = RONE instance + insert), once the
  corrected D law lands.
- With apder_rows_member_size_quadratic (checked, ef30819):
  rsizes(afactored1 r s) <= (zw2+2) * quadratic = CUBIC static
  front bound by assembly on the fragment where the zw2 size payoff is
  available.  With Isabelle's current compact `rsize (RNTIMES r n) =
  Suc (rsize r) + n`, the checked payoff is
  `apder_zw2_rntimes_free_le_rsize`; do not cite global
  NTIMES-inclusive `zw2 <= rsize` without a separate theorem/change.

## Suggested next attacks

- Joint induction on (a, c) = (card(acc - Fk), card(acc INT Fk)) with
  a transfer term for sibling overlap.
- A list-version accumulator with explicit duplicate accounting
  (rdistinct-style) so the overlap becomes a computable quantity.
- Prove first for the k-chain fragment (rfrontier k a singleton all
  the way down), then lift over the single degenerate k=RONE layer.
- For the current cubic payoff, prove the rntimes-free D law first.  If
  the general NTIMES target is reopened, add a zero-count frontier slot
  (for example a `max 1`/normalization premise around `RNTIMES _ 0`) before
  attempting induction.

## HISTORICAL BREAKTHROUGH CANDIDATE (REFUTED 2026-06-13 01:05)

The first J* invariant below was validated on 95,510 shallow nf samples
with 55,351 nontrivially-active middle terms, then refuted by the deep
correction run.  Keep it only as possible induction-shape intuition over
zw2 after re-running the equality anatomy; do not try to prove it as
written.

```
J*(r1, r2, k):   [nf r1, nf r2, nf k; r1,r2 not RZERO/RONE; r1 non-SEQ]
  card (acc r1 (sigma4 r2 k) - F(sigma4 r2 k))
+ card ((acc r1 (sigma4 r2 k) INT F(sigma4 r2 k)) - F k - acc r2 k)
+ card (acc r2 k - F k)
  <= zwidth r1 + zwidth r2
```

Plain words: the left accumulator counted away from its OWN composite
frontier, plus the imported composite-frontier points NOT covered by
the sibling, plus the sibling count, fit in the joint budget - with
A1 INT A2 points allowed to be double-counted (this is strictly
stronger than the D law for SEQ nodes, and implies the SEQ branch).

Notes for the prover:
- At k = RONE this is exactly the J balance found from the equality
  anatomy (imported_extra = 0 AND overlap = 0 at every equality case).
- D for SEQ follows since card((A1 UNION A2) - Fk) <= t1 + t2 + t3.
- The induction should prove D and J* simultaneously (J* speaks about
  a SEQ node split; D handles the other constructors where the
  composite collapses).
- Checker: extend scratch_rowcount_check.py with the J* block (code
  in PROGRESS 2026-06-13 00:35 entry).

## CORRECTION (2026-06-13 01:05): zwidth insufficient, use zw2; J* false at depth

- DEEP sampling (285k, depth<=5/4) produced a CE against BOTH the J*
  candidate AND the original D law with the max-1 zwidth:

  ```
  r = SEQ b (ALTS [STAR(STAR a), STAR(STAR b), b]), k = RONE
  card(acc - {RONE}) = 5  >  zwidth = 4
  ```

  Mechanism: a nested zero-consuming star contributes BOTH itself as a
  frontier point AND its unrolled row - each star LAYER needs a slot.
- CORRECTED weight (validated 295,551 deep samples, zero violations):

  ```
  zw2: C=1, ALTS/SEQ=sum, STAR x = 1 + zw2 x, Z=O=0
  card (acc r k - rfrontier k) <= zw2 r        [nf r, nf k]
  ```

  In Isabelle, `apder_zw2_rntimes_free_le_rsize` is checked, so the
  linear-row-count payoff is unchanged on the existing rntimes-free
  fragment.  A global NTIMES-inclusive `zw2 <= rsize` payoff is not
  available with the current compact `RNTIMES` size measure unless a
  separate statement/change lands.
- LESSON: shallow sampling (depth<=4) validated false statements
  (zwidth-D at 200k, J* at 95k).  ALWAYS validate at depth>=5 with
  directed nested-star families before proving.  The J* shape may
  still be the right INDUCTION SKELETON over zw2 - re-derive its
  equality anatomy under zw2 before the Isabelle attempt.

## CORRECTION (2026-06-13 04:00): raw zw2 insufficient with RNTIMES 0

- CHECKED CE:

  ```
  r = RSEQ (RCHAR c)
        (RALTS [RNTIMES (RCHAR a) 0, RNTIMES (RCHAR b) 0])
  k = RONE
  card(acc r k - rfrontier k) = 2
  apder_zw2 r = 1
  ```

  Isabelle lemma:
  `apder_zw2_D_law_rntimes_zero_alt_false`.
- Mechanism: `RNTIMES x 0` is nullable and has empty derivative
  accumulator, but its syntactic frontier is still the atom
  `RNTIMES x 0`; an alternation of two such atoms imports two rows through
  one preceding character slot.
- The legacy/non-backref, rntimes-free payoff route remains viable and is now
  the narrow live target.  Do not attempt the unrestricted raw `zw2` law
  unless the weight or premises are repaired first.
