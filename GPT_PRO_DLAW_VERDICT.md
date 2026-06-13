# GPT Pro verdict on the D-law: telescoping boundary invariant (T + S)

PROVENANCE: produced by GPT Pro (web, high-reasoning) on 2026-06-13 from the
self-contained bundle (CUBIC_OPEN_PROBLEM + MATHPROBLEM_ROWCOUNT). Surfaced to
all agents by the secretary.

STATUS: DESIGN PROPOSAL — not yet sample-checked, not yet Isabelle-verified.
Before investing Isabelle effort, SAMPLE-CHECK the T and S invariants at
depth >= 5 with directed nested zero-width-star families (extend
scratch_rowcount_check.py). This project has TWICE had a statement pass shallow
sampling and fail at depth 5 (zwidth-D, the first J*). If T and S survive the
deep run, this is the recommended architecture; if a deep CE appears, record it
in SUPER_LINEAR_PATTERNS.md and report.

TL;DR (actionable):
- Replace the unary D target by a TELESCOPING boundary invariant
  T(r,k):  clean r ==> clean k ==> card((F(sigma r k) UNION A r k) - F k) <= W r,
  plus a strict-credit auxiliary
  S(r,k):  clean r ==> clean k ==> 0 < W r ==> Suc(card(A r k - F k)) <= W r.
  D is an immediate corollary of T; J*-zw2 is a SEQ corollary of D(left)+T(right).
- The SEQ overlap DISAPPEARS: F(sigma r2 k) becomes a boundary subtracted on the
  left and paid once on the right — no inclusion-exclusion arithmetic at SEQ.
- CONCRETE GAP IT FOUND in the current plan: E0 must be the EXACT merged-frontier
  T law, NOT the `+1` form. With E0(+1), SEQ telescoping yields W r1 + W r2 + 1,
  leaking one unit already in the ordinary singleton-continuation case
  (r1 = RCHAR a, r2 = RCHAR b, k = RCHAR c). The left character's strict spare
  unit from S(r1, sigma r2 k) is what pays it. The feared k=RONE / right-ALTS
  case is NOT the failing case — it closes cleanly under T.
- Four bridge lemmas (sigma_clean, sigma_RONE_id_nf, clean_zero_budget_root,
  alts_positive_member) + the exact `T_and_S` simultaneous-induction statement
  are at the end of this file.

---
## Verdict

**J*-zw2 has the right SEQ anatomy, but I would not make it the primary induction invariant.** It is better as a corollary of a sharper “boundary telescoping” invariant. The current `(E00-RONE, E0, D)` plan closes **only if E0 is strengthened from a `+1` law to an exact frontier-transport law**. With only `E0-general(+1)`, there is a real proof gap in the ordinary SEQ case where `k ≠ RONE` and `F(σ r2 k)` is a singleton. The **right-ALTS / `k = RONE` degenerate case is not the failing case**; it closes cleanly once the right operand is proved with the exact merged-frontier law.

I’ll use the notation from the attachments: `A r k = acc r k`, `F k = rfrontier k`, `σ r k = sigma4 r k`, and `W r = apder_zw2 r`. The relevant definitions are exactly the ones in the D-law note: `RCHAR` imports `F k`, `SEQ r1 r2` uses `A r1 (σ r2 k) ∪ A r2 k`, `STAR r` uses `A r (σ (STAR r) k)`, and `W` is additive over `SEQ`/`ALTS` with one extra unit per `STAR`. 

---

## The invariant that cracks the overlap

Replace the unary D target by this stronger **telescoping boundary invariant**:

```isabelle
T(r,k):
  clean r ==> clean k ==>
  card ((F (σ r k) ∪ A r k) - F k) <= W r
```

where

```isabelle
clean q ≡ legacy_rrexp q ∧ rntimes_free q ∧ apder_nf q ∧ zero_budget_trivial q
```

and `zero_budget_trivial` is the predicate from the note: every zero-`zw2` subterm is literally `RZERO` or `RONE`. That predicate is exactly what removes the `RNTIMES _ 0` and zero-budget-alternative frontier ghosts. 

The D law is then immediate:

```isabelle
A r k - F k ⊆ (F (σ r k) ∪ A r k) - F k
```

so

```isabelle
card (A r k - F k) <= W r
```

The companion induction invariant needed for the `RALTS` proper-continuation case is a strict drain law:

```isabelle
S(r,k):
  clean r ==> clean k ==> 0 < W r ==>
  Suc (card (A r k - F k)) <= W r
```

This is not an arbitrary strengthening. It says that a positive-budget expression always has one spare slot beyond its already-drained accumulator rows. That spare slot is exactly what pays the **new composite frontier point** introduced by `σ (RALTS rs) k` when `k` is not `RONE` or `RZERO`.

The key insight is that `T` makes the overlap disappear by making `F(σ r2 k)` a **boundary** between the left and right sides of a sequence. In the hard case

```isabelle
r = RSEQ r1 r2
m = σ r2 k
A1 = A r1 m
A2 = A r2 k
```

the exact SEQ target for `T` is covered by

```isabelle
((F (σ r1 m) ∪ A1 ∪ A2) - F k)
⊆
((F (σ r1 m) ∪ A1) - F m)
 ∪
((F m ∪ A2) - F k)
```

The first set is paid by `W r1`; the second is paid by `W r2`. No inclusion-exclusion arithmetic is needed at the SEQ node.

For `k = RONE` and `r2 = RALTS rs`, this is precisely the missing overlap mechanism. A character in `r1` may import the whole wide frontier `F r2`, but in `T(r1,r2)` that frontier is subtracted as the boundary:

```isabelle
T(RCHAR c, r2):
  card ((F (σ (RCHAR c) r2) ∪ F r2) - F r2) <= 1
```

So the character pays only the new row `σ (RCHAR c) r2`, not the whole `F r2`. The wide frontier is then paid once, on the right, by

```isabelle
T(r2, RONE):
  card ((F r2 ∪ A r2 RONE) - {RONE}) <= W r2
```

That is the overlap: `F r2 ∩ A r2 RONE` is counted once because `T` uses a union on the right side, not two separate unary counts. This directly addresses the hard SEQ anatomy described in the note, where a character leaf imports all of `F(r2)` and the budget balances only through overlap with `acc(r2,RONE)`. 

---

## How J*-zw2 falls out

Let

```isabelle
m  = σ r2 k
A1 = A r1 m
A2 = A r2 k
Fm = F m
Fk = F k
```

J*-zw2’s left side is

```isabelle
card (A1 - Fm)
+ card ((A1 ∩ Fm) - Fk - A2)
+ card (A2 - Fk)
```

The second and third terms are disjoint subsets of

```isabelle
(Fm ∪ A2) - Fk
```

Therefore

```isabelle
card ((A1 ∩ Fm) - Fk - A2) + card (A2 - Fk)
<= card ((Fm ∪ A2) - Fk)
```

Then `D(r1,m)` plus `T(r2,k)` gives

```isabelle
card (A1 - Fm)
+ card ((A1 ∩ Fm) - Fk - A2)
+ card (A2 - Fk)
<= W r1 + W r2
```

So **J*-zw2 is a corollary of `D(left)` + `T(right)`**. Since `D` itself follows from `T`, the real induction target should be `T`, with `S` as the auxiliary strict-credit lemma. The revived J*-zw2 statement from the attachment is therefore the right diagnostic shape, but not the cleanest thing to induct on. 

---

## Constructor discharge for `T` and `S`

### `RCHAR`

For `r = RCHAR c`:

```isabelle
A (RCHAR c) k = F k
```

So

```isabelle
(F (σ (RCHAR c) k) ∪ A (RCHAR c) k) - F k
= F (σ (RCHAR c) k) - F k
```

By the definition of `σ`, this set has cardinal at most one:

```isabelle
σ c RZERO = RZERO
σ c RONE  = c
σ c k     = RSEQ c k     otherwise
```

Thus `T` is paid by `W (RCHAR c) = 1`.

For `S`:

```isabelle
A (RCHAR c) k - F k = ∅
Suc 0 <= 1
```

So the strict spare slot is exactly the character’s one unit.

---

### `RALTS`

Let `r = RALTS rs`.

There are three continuation cases.

**1. `k = RONE`.**

Then `σ (RALTS rs) RONE = RALTS rs`, and

```isabelle
F (RALTS rs) ∪ A (RALTS rs) RONE
=
⋃ q∈set rs. (F q ∪ A q RONE)
```

Using the normal-form lemma `apder_nf q ==> σ q RONE = q`, each member contributes by `T(q,RONE)`, and finite-union subadditivity gives

```isabelle
card ((F (RALTS rs) ∪ A (RALTS rs) RONE) - {RONE})
<= sum_list (map W rs)
```

This is the exact `E00-RONE` law, stronger than the `max 1` form except where `W = 0`, where `zero_budget_trivial` reduces the case to `RZERO/RONE`.

**2. `k = RZERO`.**

Then `σ (RALTS rs) RZERO = RZERO`, so the frontier part disappears. The target is bounded by the member D consequences of `T(q,RZERO)`.

**3. Proper continuation: `k ≠ RZERO` and `k ≠ RONE`.**

Now

```isabelle
σ (RALTS rs) k = RSEQ (RALTS rs) k
F (σ (RALTS rs) k) = {RSEQ (RALTS rs) k}
```

So the target is bounded by

```isabelle
1 + card ((⋃ q∈set rs. A q k) - F k)
```

This is where `S` is essential. Because `clean (RALTS rs)` and this is a real `RALTS` node, not a zero-budget ghost, there is some member `q0 ∈ set rs` with `0 < W q0`. Then:

```isabelle
1 + card ((⋃ q∈set rs. A q k) - F k)
<=
1 + card (A q0 k - F k)
  + sum_{q≠q0} card (A q k - F k)
<=
W q0 + sum_{q≠q0} W q
```

The chosen positive member pays the single composite ALTS root via `S(q0,k)`; all other members use `D`, which follows from `T`.

For `S(RALTS rs,k)`, the same list-credit argument applies, but without the ALTS root. Choose one positive-budget member to pay the global `Suc`; the rest use D.

This is the place where the proposed `E0(+1)` is too weak. If the `+1` is kept outside the budget instead of charged to a positive member via `S`, the `RALTS` proper-continuation proof leaks one unit.

---

### `RSTAR`

Let `r = RSTAR p` and

```isabelle
m = σ (RSTAR p) k
A = A p m
```

Then

```isabelle
A (RSTAR p) k = A p m
```

For `T`:

```isabelle
(F m ∪ A) - F k
⊆
(F m - F k) ∪ (A - F m)
```

The first set has cardinal at most one, because `m` is either `RZERO` or a non-`RALTS` atom/sequence/star frontier. The second set is paid by `D(p,m)`, hence by `T(p,m)`. Therefore:

```isabelle
card ((F m ∪ A p m) - F k)
<= 1 + W p
= W (RSTAR p)
```

For `S`, we need

```isabelle
Suc (card (A p m - F k)) <= 1 + W p
```

Equivalently:

```isabelle
card (A p m - F k) <= W p
```

Split

```isabelle
A p m - F k
=
(A p m - F m) ∪ (A p m ∩ (F m - F k))
```

The second component is at most one point. If it is empty, `D(p,m)` pays the first component. If it is nonempty, then the body really hits its boundary frontier; if `W p = 0`, cleanliness forces `p` to be `RZERO` or `RONE`, contradicting the hit. Hence `0 < W p`, and `S(p,m)` pays

```isabelle
Suc (card (A p m - F m)) <= W p
```

which covers the hit plus the outside-boundary rows. The outer star’s `+1` is then the strict spare slot for the whole star. This is exactly why `zw2` needs one unit per star layer; the old max-one zwidth failed on nested zero-consuming stars. 

---

### `RSEQ`

Let `r = RSEQ r1 r2` and

```isabelle
m  = σ r2 k
A1 = A r1 m
A2 = A r2 k
```

For `T`, use the telescoping inclusion:

```isabelle
(F (σ (RSEQ r1 r2) k) ∪ A1 ∪ A2) - F k
=
(F (σ r1 m) ∪ A1 ∪ A2) - F k
⊆
((F (σ r1 m) ∪ A1) - F m)
 ∪
((F m ∪ A2) - F k)
```

The first set is paid by `T(r1,m)`; the second is paid by `T(r2,k)`. Therefore:

```isabelle
card ((F (σ (RSEQ r1 r2) k) ∪ A (RSEQ r1 r2) k) - F k)
<= W r1 + W r2
```

For `S`, use

```isabelle
(A1 ∪ A2) - F k
⊆
(A1 - F m) ∪ ((F m ∪ A2) - F k)
```

Since `apder_nf (RSEQ r1 r2)` forbids `RZERO/RONE` parts, and `zero_budget_trivial` forbids a nontrivial zero-budget left operand, we have `0 < W r1`. Then

```isabelle
Suc (card (A1 - F m)) <= W r1
```

by `S(r1,m)`, while

```isabelle
card ((F m ∪ A2) - F k) <= W r2
```

by `T(r2,k)`. This gives

```isabelle
Suc (card (A (RSEQ r1 r2) k - F k)) <= W r1 + W r2
```

So the SEQ case closes without a bespoke overlap lemma.

---

## Assessment of the current candidate

The revived J*-zw2 invariant is **mathematically aligned with the problem**. It names the three regions that matter: left rows away from the middle frontier, middle-frontier imports not absorbed by the right sibling, and right rows away from the final frontier. The attachment’s observation that J*-zw2 implies the SEQ branch by a three-block covering is correct. 

But the proof architecture should shift:

```text
Do not induct on J* directly.
Prove T + S.
Derive D.
Derive J* as a SEQ corollary when useful.
```

The hidden gap is specifically this: if `E0-general` is only

```isabelle
card ((F (σ r k) ∪ A r k) - F k) <= W r + 1
```

then SEQ telescoping gives `W r1 + W r2 + 1`, not `W r1 + W r2`. The missing unit appears already in the nondegenerate singleton-continuation case:

```isabelle
r1 = RCHAR a
r2 = RCHAR b
k  = RCHAR c

m  = σ r2 k = RSEQ b c
A1 = {m}
A2 = {c}
F m = {m}
F k = {c}
```

`D(r1,m)` and `D(r2,k)` both see zero drained rows, but the whole SEQ has the row `m` outside `F k`. The proof closes only if the left character’s strict spare unit is available. That is exactly what `S(r1,m)` supplies.

By contrast, the feared `k = RONE`, right-`ALTS` case is fine under `T`:

```isabelle
r2 = RALTS rs
m  = σ r2 RONE = r2
```

The left side subtracts `F r2` as its boundary; the right side pays `F r2 ∪ A r2 RONE - {RONE}` once. This is the overlap mechanism the unary strengthenings could not express. The note explicitly warns that single-set discounts cannot see this overlap and that the invariant must account for `F(r2) ∩ acc(r2,RONE)` or jointly bound the merged set; `T` is exactly the merged-set formulation. 

---

## Why this is preferable to list/multiset accounting

The PDF’s refutation of duplicated-list cost shows that any architecture requiring polynomial control of `Dlist` or per-row duplicated multisets is dead: the tower family grows exponentially before set deduplication, while the deduplicated union survives because repeated tails merge. 

`T` stays purely set-based. It does not count duplicates and does not need a multiset ledger. It turns the proof into a **telescoping frontier transport** argument: every constructor pays only for the new frontier it creates after subtracting the incoming boundary. This fits the top-level cubic route, where the page-4 decomposition reduces the remaining gate work to row count times the already-checked quadratic member-size universe. 

---

## Residual Isabelle obligations

I see four concrete bridge lemmas to land before the main induction.

```isabelle
sigma_clean:
  clean r ==> clean k ==> clean (σ r k)
```

Needed for recursive IH calls in `SEQ` and `STAR`.

```isabelle
sigma_RONE_id_nf:
  apder_nf r ==> σ r RONE = r
```

Or at least the frontier version:

```isabelle
apder_nf r ==> F (σ r RONE) = F r
```

Needed for the `RALTS`/`RONE` branch.

```isabelle
clean_zero_budget_root:
  clean r ==> W r = 0 ==> r = RZERO ∨ r = RONE
```

This is the working content of `zero_budget_trivial` at the root. It is what kills `RALTS []`, `RALTS [RONE]`, and `RNTIMES _ 0`-style ghosts as budget-free frontier carriers.

```isabelle
alts_positive_member:
  clean (RALTS rs) ==> 0 < W (RALTS rs) ==>
  ∃q∈set rs. 0 < W q
```

Together with a list-union cardinal lemma that lets one positive member pay the global `Suc` via `S`, while all other members use D.

With those bridges, the main simultaneous induction should be:

```isabelle
lemma T_and_S:
  assumes "clean r" "clean k"
  shows
    "card ((F (σ r k) ∪ A r k) - F k) <= W r"
  and
    "0 < W r ==> Suc (card (A r k - F k)) <= W r"
```

Then the desired D law is a one-line corollary:

```isabelle
lemma D_law_clean:
  assumes "clean r" "clean k"
  shows "card (A r k - F k) <= W r"
  using T_and_S(1)[OF assms]
  by (meson Diff_mono Un_upper2 card_mono finite...)
```

My recommendation is to try this exact `T + S` induction before investing further in direct J*. It preserves the J* overlap insight, but moves the induction boundary to the place where SEQ naturally telescopes.
