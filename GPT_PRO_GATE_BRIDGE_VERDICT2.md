# GPT Pro verdict #2 on the gate-bridge: the continuation-parametric drain potential

PROVENANCE: GPT Pro, 2026-06-14, third pass — after BOTH original-root carriers
(opened-boundary + liveness) were machine-checked FALSE. THIS is the corrected
design and the route to execute. Supersedes the opened-boundary carrier-preservation
step of `GPT_PRO_GATE_BRIDGE_VERDICT.md` (that step is false; the rest of its
potential-charging ideas are reused here).

STATUS: design proposal — SAMPLE-CHECK at depth>=5 before heavy Isabelle: the child
invariant `rsize_set(strong_child_drain p k) <= drain_pot p + drain_w p*(1+rsize k)`
and the cubic `drain_pot r <= rsize r*(rsize r+2)^2`. Constants are tunable;
verdict3's constructor arithmetic shows POSITIVE slack at every node (RCHAR +1,
RSEQ +Wp, RSTAR +W+2), so this is likely to sample clean — but do not skip the
depth>=5 check (twice burned by shallow sampling).

TL;DR (the route to close the §1 gate):
- Carrier over the CURRENT NORMALIZED rows (`S = rsimpStrong_raw`), NOT the original
  root — so the singleton-ALT-collapse CE is HARMLESS (the induction root is `S p`,
  e.g. RSTAR(RCHAR a), not the unsimplified RSTAR(RALTS[RCHAR a])).
- `strong_child_drain p k = strong_opened_live(nseq p k) - strong_opened_live(S k)`
  (drain analogue of subtracting odfront k; pass-through / `1` branches pay ZERO).
- CONTINUATION-PARAMETRIC child invariant (measure = `rsize p` only; the
  continuation `k` may GROW, including the star re-entry `nseq (RSTAR p) k`):
    `rsize_set(strong_child_drain p k) <= drain_pot p + drain_w p * (1 + rsize k)`.
- `drain_pot` = open_pot's strict-crossing shape, named separately; per-constructor
  discharges (RZERO/RONE/RCHAR/RALTS/RSEQ/RSTAR) all close with positive slack.
- Cubic: `drain_pot r <= rsize r*(rsize r+2)^2`, `drain_child_budget r RONE <=
  (rsize r+3)^3`, leaving `5*rsize^2+21*rsize+27` slack for the root wrappers.
- The existing conditional root-cubic wrappers consume `child_ok` (the
  continuation-parametric fact), NOT a coarse child cubic. Final bridge: §7.
  Guard discipline: §8 (rtail_nf for strong-normalized current rows; clean/
  rntimes_free for the original front-budget side). Set-native throughout — no
  list-cost, no square-sum, no rowwise S-monotonicity.

The full memo follows verbatim.

---

## Design memo: replace root-cubic child IH with a continuation-parametric drain potential

The child IH should **not** say “each child gets `2*(rsize child + 3)^3`.” That repeats the failed coarse assembly: it spends the whole parent budget before the `RALTS` or `RSTAR` wrapper gets to pay its constructor/opening obligations. The viable invariant is the same idea as the opened-boundary memo, but moved to the **current strong-normalized row representation** and made **continuation-parametric**. This respects the checked failures: both original-root carriers fail because `rsimpStrong_raw` normalizes singleton alternatives, flattening, deduplication, and pruning, so the carrier must be over the current normalized `afactored1` rows / `strong_opened_live`, not over the original root. 

The invariant to prove is:

```isabelle
rsize_set (strong_child_drain p k)
  ≤ drain_pot p + drain_w p * (1 + rsize k)
```

Here `p` is the **current normalized child row**, `k` is the normalized continuation, and the measure is only `rsize p`. The continuation is allowed to grow, including the star re-entry continuation `p*`; the recursive argument still decreases from `RSTAR p` to `p`.

---

## 1. Normalized child carrier

Use the carrier that is already implemented, `strong_opened_live`, but do not call it on the original root. Introduce a normalized sequencing abbreviation:

```isabelle
abbreviation S where
  "S ≡ rsimpStrong_raw"

definition nseq where
  "nseq p k = S (rsimp7_SEQ_atom (S p) (S k))"
```

If `strong_opened_live` is row-valued in the current development, use it directly. If it is set-valued, read `strong_opened_live x` below as `strong_opened_live {x}`.

```isabelle
definition strong_child_drain where
  "strong_child_drain p k =
     strong_opened_live (nseq p k) - strong_opened_live (S k)"
```

This is the drain analogue of subtracting `odfront k`: the continuation-owned opened forms are removed before charging the child. That is what kills the RONE tower and keeps the proof set-native/deduplicated rather than list- or square-sum based. The gap document explicitly rules out the square-sum and non-deduplicated list routes; the degree has to come from suffix sharing/deduplication. 

The root carrier should then be an abbreviation over current rows, not original roots:

```isabelle
definition strong_root_drain where
  "strong_root_drain p =
     strong_opened_live (S p)"        (* or singleton-set version *)
```

and the already checked actual containment should remain the entry point:

```isabelle
row_dlformss (rpder_strong_rows_raw c (afactored1 r s))
  ⊆ strong_opened_live_current (set (map S (afactored1 r (s @ [c]))))
```

The important point is that the CE

```isabelle
RSTAR (RALTS [RCHAR a])  ↦  RSTAR (RCHAR a)
```

is now harmless: the induction root is `S p = RSTAR (RCHAR a)`, not the unsimplified `RSTAR (RALTS [RCHAR a])`.

---

## 2. Potential and weight

Use the same strict-crossing shape as `open_pot`, but name it separately so it is clear that this is the **drain-child** potential, not the failed original-root carrier potential. The weight can be `apder_zw2`; I write it as `drain_w` only to keep the memo readable.

```isabelle
abbreviation drain_w where
  "drain_w ≡ apder_zw2"
```

```isabelle
fun drain_pot where
  "drain_pot RZERO = 0"
| "drain_pot RONE  = 0"
| "drain_pot (RCHAR c) = 2"

| "drain_pot (RALTS rs) =
     sum_list (map drain_pot rs)"

| "drain_pot (RSEQ p q) =
     drain_pot p
   + drain_pot q
   + drain_w p * (rsize q + 2)"

| "drain_pot (RSTAR p) =
     drain_pot p
   + (drain_w p + 1) * (rsize (RSTAR p) + 2)"

| "drain_pot (RNTIMES p n) =
     n * (drain_pot p + (drain_w p + 1) * (rsize p + 2))"
```

The `RNTIMES` branch is only for totality of the function; the target lemma should be registered and used under `rntimes_free`. The full-gate statement records that non-`rntimes_free` weight arguments are false because `{0}` can carry frontier atoms without paying the plain weight. 

Define the child budget:

```isabelle
definition drain_child_budget where
  "drain_child_budget p k =
     drain_pot p + drain_w p * (1 + rsize k)"
```

The key theorem is:

```isabelle
lemma strong_child_drain_potential:
  assumes nf_p:   "rtail_nf (S p)"          (* or the live strong-row NF predicate *)
      and nf_k:   "rtail_nf (S k)"
      and free_p: "rntimes_free p"
      and free_k: "rntimes_free k"
      and legacy_p: "legacy_rrexp p"
      and legacy_k: "legacy_rrexp k"
  shows
    "rsize_set (strong_child_drain p k)
       ≤ drain_child_budget (S p) (S k)"
```

Equivalently, after rewriting normalized arguments at the call site:

```isabelle
lemma strong_child_drain_potential_normalized:
  assumes nf_p:   "rtail_nf p"
      and nf_k:   "rtail_nf k"
      and free_p: "rntimes_free p"
      and free_k: "rntimes_free k"
      and legacy_p: "legacy_rrexp p"
      and legacy_k: "legacy_rrexp k"
      and norm_p:  "S p = p"
      and norm_k:  "S k = k"
  shows
    "rsize_set (strong_child_drain p k)
       ≤ drain_pot p + drain_w p * (1 + rsize k)"
```

This is the invariant the wrappers should consume.

---

## 3. Induction and measure

Use well-founded induction on the first component only:

```isabelle
measure (λ(p,k). rsize p)
```

or, if the proof is stated as `∀k. P p k`, simply structural induction on `p` with a list induction for `RALTS`.

The continuation is **not** part of the decreasing measure. This is crucial for `RSTAR`: the recursive call is on the smaller body `p`, but with the larger continuation `nseq (RSTAR p) k`.

The size facts needed are the normalized-sequence upper bounds:

```isabelle
lemma rsize_nseq_le:
  "rsize (nseq p k) ≤ rsize p + rsize k + 1"
```

and the star-specialized version:

```isabelle
lemma rsize_nseq_star_le:
  "rsize (nseq (RSTAR p) k) ≤ rsize p + rsize k + 2"
```

These should follow from the existing `rsimp7_SEQ_atom` size lemmas plus `rsimpStrong_raw` size nonincrease. This does **not** use the false rowwise opened-ledger monotonicity of `S`; it only uses syntactic size nonincrease. The false route is assuming simplification shrinks `D` row-by-row, which is explicitly refuted. 

---

## 4. Constructor discharges

### `RZERO` and `RONE`

```isabelle
strong_child_drain RZERO k = {}
strong_child_drain RONE  k = {}
```

`RONE` contributes only the already-owned continuation, removed by subtracting `strong_opened_live (S k)`. This is the drain version of “pass-through contributes zero,” which was the central point of the opened-boundary design. 

So:

```isabelle
0 ≤ drain_pot RONE + drain_w RONE * (1 + rsize k) = 0
```

and similarly for `RZERO`.

### `RCHAR`

Per-constructor containment should be:

```isabelle
strong_child_drain (RCHAR a) k
  ⊆ row_dlforms (nseq (RCHAR a) k)
```

The right side is at most one opened row, and:

```isabelle
rsize_set (row_dlforms (nseq (RCHAR a) k))
  ≤ rsize k + 2
```

The budget is:

```isabelle
drain_pot (RCHAR a) + drain_w (RCHAR a) * (1 + rsize k)
= 2 + 1 * (1 + rsize k)
= rsize k + 3
```

So `RCHAR` closes with one unit of slack.

### `RALTS`

Use the already checked constructor containment, but with normalized rows:

```isabelle
strong_child_drain (RALTS rs) k
  ⊆ ⋃p∈set rs. strong_child_drain p k
```

Then use set-ledger subadditivity:

```isabelle
rsize_set (strong_child_drain (RALTS rs) k)
 ≤ sum_list (map (λp. rsize_set (strong_child_drain p k)) rs)
 ≤ sum_list (map (λp. drain_pot p + drain_w p * (1 + rsize k)) rs)
```

By definition of `drain_pot` and `drain_w` on `RALTS`:

```isabelle
sum_list (map drain_pot rs)
+ sum_list (map drain_w rs) * (1 + rsize k)
=
drain_pot (RALTS rs)
+ drain_w (RALTS rs) * (1 + rsize k)
```

This is the main reason not to use child cubics. The children consume exactly the additive child budget, so the parent’s constructor slack remains available to the existing `RALTS` root-cubic wrapper.

For normalized `RALTS`, the list is already flattened/deduplicated/non-singleton. If the lemma is stated before that normalization, keep the proof as `≤` using `rflts`/`rdistinct`; duplicates only make the list-sum upper bound larger, while the carrier remains set-native.

### `RSEQ`

The containment should be the drain telescoping step:

```isabelle
strong_child_drain (RSEQ p q) k
  ⊆ strong_child_drain p (nseq q k)
   ∪ strong_child_drain q k
```

This is the same middle-boundary cancellation as before: the forms owned by `nseq q k` are subtracted from the left child and supplied by the right child. The previous opened-boundary memo used the same cancellation for `odfront (sigma q k)`. 

Let:

```text
Pp = drain_pot p
Pq = drain_pot q
Wp = drain_w p
Wq = drain_w q
b  = rsize q
m  = rsize k
```

Using `rsize (nseq q k) ≤ b + m + 1`:

```isabelle
rsize_set (strong_child_drain p (nseq q k))
  ≤ Pp + Wp * (1 + rsize (nseq q k))
  ≤ Pp + Wp * (b + m + 2)

rsize_set (strong_child_drain q k)
  ≤ Pq + Wq * (m + 1)
```

So the union is bounded by:

```isabelle
Pp + Pq + Wp * (b + m + 2) + Wq * (m + 1)
```

The parent budget is:

```isabelle
drain_pot (RSEQ p q) + drain_w (RSEQ p q) * (m + 1)
=
Pp + Pq + Wp * (b + 2) + (Wp + Wq) * (m + 1)
=
Pp + Pq + Wp * (b + m + 3) + Wq * (m + 1)
```

So the `RSEQ` case closes with exactly `Wp` slack.

That `Wp * (rsize q + 2)` term is the child-level suffix-crossing charge. It is what the coarse cubic IH fails to expose.

### `RSTAR`

Use the star containment in this form:

```isabelle
strong_child_drain (RSTAR p) k
  ⊆ star_entry p k
   ∪ strong_child_drain p (nseq (RSTAR p) k)
```

where:

```isabelle
definition star_entry where
  "star_entry p k =
     row_dlforms (nseq (RSTAR p) k) - strong_opened_live (S k)"
```

The star entry is a singleton/small opened row after normalization, so:

```isabelle
rsize_set (star_entry p k)
  ≤ rsize p + rsize k + 2
```

Let:

```text
a = rsize p
m = rsize k
W = drain_w p
P = drain_pot p
```

By induction on the body with the re-entry continuation:

```isabelle
rsize_set (strong_child_drain p (nseq (RSTAR p) k))
  ≤ P + W * (1 + rsize (nseq (RSTAR p) k))
  ≤ P + W * (a + m + 3)
```

Adding the star entry gives:

```isabelle
≤ P + W * (a + m + 3) + (a + m + 2)
```

The parent budget is:

```isabelle
drain_pot (RSTAR p) + drain_w (RSTAR p) * (m + 1)
=
P + (W + 1) * (rsize (RSTAR p) + 2) + (W + 1) * (m + 1)
=
P + (W + 1) * (a + 3) + (W + 1) * (m + 1)
=
P + W * (a + m + 4) + a + m + 4
```

The difference is:

```isabelle
[P + W*(a+m+4) + a+m+4]
-
[P + W*(a+m+3) + a+m+2]
=
W + 2
```

So the `RSTAR` case closes with `W + 2` slack.

This is the child-drain analogue of the old `open_pot` “+1 per star”: the `+1` in

```isabelle
drain_w (RSTAR p) = drain_w p + 1
```

pays for the star’s own re-entry edge, while

```isabelle
(drain_w p + 1) * (rsize (RSTAR p) + 2)
```

pays for carrying the body through the `p*` suffix. This is the exact place where a root-only child cubic is too coarse: it gives no continuation-indexed credit for `p` under `p*`.

---

## 5. Cubic arithmetic

The arithmetic lemma to prove for the potential is:

```isabelle
lemma drain_pot_le_cubic_core:
  assumes "rntimes_free r"
  shows
    "drain_pot r ≤ rsize r * (rsize r + 2)^2"
```

Use `drain_w r ≤ rsize r`, already available in the clean/rntimes-free fragment via the `zw2` facts. The roadmap records that the D law and static front use this weight, with `w(r) ≤ |r|`. 

Constructor arithmetic:

For `RALTS`, with `S = sum_list (map rsize rs)` and `N = 1 + S`:

```isabelle
sum_list (map (λp. rsize p * (rsize p + 2)^2) rs)
  ≤ S * (S + 2)^2
  ≤ N * (N + 2)^2
```

For `RSEQ`, with `a = rsize p`, `b = rsize q`, `N = 1 + a + b`:

```isabelle
a*(a+2)^2 + b*(b+2)^2 + a*(b+2)
  ≤ N*(N+2)^2
```

The expanded slack is:

```text
3*a^2*b + 3*a^2 + 3*a*b^2 + 13*a*b + 9*a + 3*b^2 + 11*b + 9
```

For `RSTAR`, with `a = rsize p`, `N = a + 1`:

```isabelle
a*(a+2)^2 + (a+1)*(a+3)
  ≤ (a+1)*(a+3)^2
```

The slack is:

```text
(a + 2) * (2*a + 3)
```

Then the root child budget satisfies:

```isabelle
lemma drain_child_budget_root_cubic:
  assumes "rntimes_free r"
  shows
    "drain_child_budget r RONE ≤ (rsize r + 3)^3"
```

because:

```isabelle
drain_child_budget r RONE
= drain_pot r + drain_w r * (1 + rsize RONE)
= drain_pot r + 2 * drain_w r
≤ rsize r * (rsize r + 2)^2 + 2 * rsize r
≤ (rsize r + 3)^3
```

The final slack is:

```text
(rsize r + 3)^3
- (rsize r*(rsize r+2)^2 + 2*rsize r)
= 5*(rsize r)^2 + 21*rsize r + 27
```

So this child invariant leaves an entire extra cubic for the already checked root-base wrappers. In particular, if a wrapper carries a base term such as `rsize r`, `rsize r + 1`, or even `rsize r^2 + rsize r + 1`, it still fits inside the project target:

```isabelle
rsize r * (rsize r + 2)^2
+ (rsize r)^2
+ 3 * rsize r
+ 1
≤ (rsize r + 3)^3
≤ 2 * (rsize r + 3)^3
```

This is the cubic budget the existing conditional `RALTS`/`RSEQ`/`RSTAR` wrappers should consume.

---

## 6. Wrapper interface to implement

The existing root-cubic wrappers should not ask for:

```isabelle
∀child. rsize_set (strong_opened_live child)
  ≤ 2 * (rsize child + 3)^3
```

They should ask for the continuation-parametric child fact:

```isabelle
definition child_ok where
  "child_ok p ≡
     (∀k. rtail_nf k ⟶ rntimes_free k ⟶ legacy_rrexp k ⟶
        rsize_set (strong_child_drain p k)
          ≤ drain_child_budget p k)"
```

Then the wrapper premises become:

```isabelle
RALTS wrapper:
  (∀p∈set rs. child_ok p)

RSEQ wrapper:
  child_ok p
  child_ok q

RSTAR wrapper:
  child_ok p
```

Inside the `RSTAR` wrapper, instantiate `child_ok p` at:

```isabelle
k = nseq (RSTAR p) RONE
```

or, for the general continuation version:

```isabelle
k = nseq (RSTAR p) k0
```

This is the missing star-compatible edge. The recursive call is on `p`; the continuation contains `RSTAR p`, but the measure ignores the continuation.

---

## 7. Final bridge shape

After the child theorem lands, the bridge should look like this:

```isabelle
lemma strong_opened_live_current_cubic:
  assumes clean: "apder_clean r"
      and nf:    "apder_nf r"
      and free:  "rntimes_free r"
      and legacy:"legacy_rrexp r"
  shows
    "rsize_set
       (strong_opened_live_current
          (set (map S (afactored1 r (s @ [c])))))
     ≤ 2 * (rsize r + 3)^3"
```

Then combine with the checked containment into the current normalized drain carrier:

```isabelle
lemma actual_gate_from_current_drain:
  assumes clean: "apder_clean r"
      and nf:    "apder_nf r"
      and free:  "rntimes_free r"
      and legacy:"legacy_rrexp r"
  shows
    "rsize_set
       (row_dlformss
          (rpder_strong_rows_raw c (afactored1 r s)))
     ≤ 2 * (rsize r + 3)^3"
```

The proof should use the existing fact that the gate rows are contained in the current-row drain carrier, not the old `opened_boundary_forms r RONE` carrier. The old original-root preservation route is machine-checked false, and the live-row-universe route is false for the same normalization reason. 

---

## 8. Guard discipline

Use `apder_clean`, `apder_nf`, `legacy_rrexp`, and `rntimes_free` only to get the current rows and the numeric facts needed by the outer theorem. Do **not** feed strong-normalized rows back into the D-law induction. The prior memo’s `rtail_nf`/`clean` separation is still right in spirit, but the carrier target changes: `rtail_nf` belongs to the strong-normalized current-row side, while `clean/rntimes_free` belongs to the original front-budget side. 

The proposed proof is set-native throughout:

```isabelle
rsize_set (A ∪ B) ≤ rsize_set A + rsize_set B
```

and never uses `Dlist`, list-cost, square-sum as the main bound, or rowwise monotonicity of `rsimpStrong_raw`. The full problem statement records those routes as refuted or degree-losing. 
