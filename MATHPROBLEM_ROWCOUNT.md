# Open Problem: Antimirov Row-Count Linearity (the D law)

Status: OPEN. Mirror-validated on >200,000 nf samples, unrefuted.
Four inductive strengthenings falsified with concrete counterexamples.
Landing this in Isabelle makes the entire checked chain for the POSIX
set-ledger cubic gate close to cubic on the nf fragment (see
MAINLINE.md and PROGRESS_BACKREF.md tail of 2026-06-12).

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
- `apder_nf` (line ~1791): no RZERO/RONE parts in SEQ, nonalt
  alternation members, head of SEQ non-SEQ.

## The law

```
apder_nf r ==> apder_nf k ==>
card (acc r k - rfrontier k) <= apder_zwidth r
```

## What is known

1. TRUE empirically: >200k random nf samples at depth <= 5, plus all
   directed adversarial families (zero-width star stacks, star-seq
   towers, wide alternations).  Equality is attained in all root
   constructors (no slack pattern by shape).
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

## Payoff when landed

- card(apder_rows r) <= zwidth r + 2 (k = RONE instance + insert).
- With apder_rows_member_size_quadratic (checked, ef30819):
  rsizes(afactored1 r s) <= (zwidth+2) * quadratic = CUBIC static
  front bound by assembly, replacing the tight-cubic ledger detour,
  and the row-count half of the dynamic front-quadratic conjecture.

## Suggested next attacks

- Joint induction on (a, c) = (card(acc - Fk), card(acc INT Fk)) with
  a transfer term for sibling overlap.
- A list-version accumulator with explicit duplicate accounting
  (rdistinct-style) so the overlap becomes a computable quantity.
- Prove first for the k-chain fragment (rfrontier k a singleton all
  the way down), then lift over the single degenerate k=RONE layer.

## BREAKTHROUGH CANDIDATE (2026-06-13 00:35, angle 10)

The first surviving strengthening, the J* invariant - validated on
95,510 nf samples with 55,351 nontrivially-active middle terms:

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
