<!--
SECRETARY HEADER (2026-06-14). GPT Pro verdict #5 — the PROOF SKELETON for the
deferred #3/#4 cover lemmas (answers the micro-ask in 5_FOLLOWUP_cover_proofs.txt
after the additive acc-split was measured BOXED). The move: a proof-only WEAK
carrier `weak_child_drain` (using the non-collapsing rsimp4 plug) + an INJECTIVE
indexed-slot charge, proven by MUTUAL induction over P (strong cover) and Q (weak
cover). Replaces the boxed split — every parent drain row gets its own paid slot.

STATUS: VALIDATED at depth≥5 (2026-06-14) — 3 harnesses over the faithful model,
~660k checks, 0 in-fragment violations: W1 weak cover (138852), W2/W3 RALTS bridge
(359932), W4/W5 RSTAR bridge + entry cost (164866). Both CEs covered (C-DRAIN-2 tight).

⚠ TWO IMPLEMENTATION CAVEATS (validation-found — get these right or it breaks):
(1) The WEAK carrier's accumulator must use the NON-COLLAPSING rsimp4 plug and must
    NOT apply rsimpStrong_raw (S) inside the weak opening. Concretely the weak acc is
    `⋃ (h,_)∈drain_ctxs p. row_dlforms (rsimp4_SEQ_atom h k)` (S-FREE). If S is applied
    per slot (as §4's wrapped-root LHS `row_dlforms (S (rsimp4 …))` is written), W1
    BREAKS — S collapses `b·a*·a*→b·a*`, the size-4 duplicate competes with the size-7
    row for the same `(b·a*,4)` slot and injectivity fails (measured: 4 in-fragment CEs,
    deficit 1). NB the §4 W3 inclusion keeps S on its LHS wrapped-root (the strong side
    being bounded) and that is fine; it is the weak_child_drain DEFINITION's acc that
    must be S-free.
(2) The lemma guards must include `S p = p` and `S k = k` (strong-normal fixpoint),
    NOT just rtail_nf/nf — nf accepts nested stars (STAR(STAR a)) on which W2/W3/W4
    fail; verdict5 states these (norm/norm_k) — keep them, do not weaken.
(3) W3's LHS subtracts `strong_opened_live (S k)` (the bigger set) while its RHS
    subtracts only `row_dlforms k`; that asymmetry is load-bearing — do not weaken the
    LHS subtraction.
The live work order + lane split is in STEER.md. THIS IS THE ROUTE.
-->

## The missing move: prove a **weak-root cover** simultaneously with the strong cover

Do not try to prove #3/#4 directly from child `strong_child_drain`. Insert one proof-only carrier:

```isabelle
definition wseq where
  "wseq p k = rsimp4_SEQ_atom p k"     (* weak final plug: no guarded star-idempotence *)

definition weak_child_drain where
  "weak_child_drain p k =
     (row_dlforms (wseq p k) ∪ strong_opened_live_row_universe_acc p k)
       - row_dlforms k"
```

This is not a new semantic carrier for the final theorem. It is a proof carrier that says: “open `p` against `k` with the reassociating plug that the parent RALTS/RSTAR opener actually exposes, and subtract only the weak continuation boundary.” The actual drain still remains

```isabelle
strong_child_drain p k =
  strong_opened_live (nseq p k) - strong_opened_live (S k)
```

over the current strong-normalized rows, which is the viable carrier identified after the original-root carriers failed. 

The key point is that the final charging plug for a slot must be `rsimp4_SEQ_atom`, not `raw_plug`/`rsimp7_SEQ_atom`. `ctx_extend` may continue to store the normalized head using `rsimp7`, but the parent RALTS/RSTAR exposed row is charged as the weak append

```isabelle
rsimp4_SEQ_atom h k
```

where `h` is the stored slot head. That is exactly what pays `b·c*·c*`: the child slot head is `h = b·c*`, but the parent row is the weak final plug `rsimp4_SEQ_atom h c*`, not the collapsed strong child plug. The obstruction is precisely the `rsimp7` guarded `a*·a* → a*` rule versus `rsimp4` not collapsing it. 

---

## 1. Use indexed slots, not set membership of slots

Because `drain_ctxs` is a list ledger, use slot positions. Do **not** use `set (drain_ctxs p)` as the injection target, since duplicate context pairs can exist syntactically but still represent separate paid slots.

```isabelle
definition slot_cost where
  "slot_cost p k i =
     snd (drain_ctxs p ! i) + (1 + rsize k)"

lemma ctx_bound_as_slots:
  "ctx_bound (drain_ctxs p) k =
     (∑ i < length (drain_ctxs p). slot_cost p k i)"
  unfolding ctx_bound_def ctx_base_def ctx_count_def slot_cost_def
  by (induction "drain_ctxs p") auto
```

For alternatives, define the offset into the concatenated RALTS slot list:

```isabelle
definition alt_off where
  "alt_off rs i =
     sum_list (map (λq. length (drain_ctxs q)) (take i rs))"

definition alt_slot where
  "alt_slot rs i j = alt_off rs i + j"
```

with the usual `concat` facts:

```isabelle
lemma alt_slot_lt:
  assumes "i < length rs" "j < length (drain_ctxs (rs ! i))"
  shows "alt_slot rs i j < length (concat (map drain_ctxs rs))"

lemma nth_alt_slot:
  assumes "i < length rs" "j < length (drain_ctxs (rs ! i))"
  shows
    "concat (map drain_ctxs rs) ! alt_slot rs i j =
       drain_ctxs (rs ! i) ! j"
```

Then `drain_ctxs (RALTS rs) = concat (map drain_ctxs rs)` gives the parent slot.

---

## 2. The core proof lemma: weak rows have an injective slot charge

Prove this helper by induction on `rsize p`; it is the lemma that makes #3 and #4 short.

```isabelle
lemma weak_child_drain_charge:
  assumes nf_p:     "rtail_nf p"
      and norm_p:   "S p = p"
      and free_p:   "rntimes_free p"
      and legacy_p: "legacy_rrexp p"
      and free_k:   "rntimes_free k"
      and legacy_k: "legacy_rrexp k"
  obtains ch where
    "⋀x. x ∈ weak_child_drain p k
          ⟹ ch x < length (drain_ctxs p)"
    "inj_on ch (weak_child_drain p k)"
    "⋀x. x ∈ weak_child_drain p k
          ⟹ rsize x ≤ slot_cost p k (ch x)"
```

The cost corollary is the version normally consumed:

```isabelle
lemma weak_child_drain_ctx_bound:
  assumes same_guards
  shows
    "rsize_set (weak_child_drain p k)
       ≤ ctx_bound (drain_ctxs p) k"
proof -
  obtain ch where ch_lt: "⋀x. x∈weak_child_drain p k ⟹ ch x < length (drain_ctxs p)"
              and inj:   "inj_on ch (weak_child_drain p k)"
              and cost:  "⋀x. x∈weak_child_drain p k ⟹ rsize x ≤ slot_cost p k (ch x)"
    using weak_child_drain_charge[OF assms] by blast

  have "rsize_set (weak_child_drain p k)
        ≤ (∑x∈weak_child_drain p k. slot_cost p k (ch x))"
    using cost unfolding rsize_set_def by (intro sum_mono) auto
  also have "... = (∑i∈ch ` weak_child_drain p k. slot_cost p k i)"
    using inj by (simp add: sum.reindex)
  also have "... ≤ (∑i<length (drain_ctxs p). slot_cost p k i)"
    using ch_lt by (intro sum_mono2) auto
  also have "... = ctx_bound (drain_ctxs p) k"
    by (simp add: ctx_bound_as_slots)
  finally show ?thesis .
qed
```

This is the replacement for the boxed split. It still uses finite-set subadditivity/reindexing, but only **after** every row has been assigned to a paid context slot. It never creates a free-standing `1 + wrapped_root` summand.

---

## 3. Constructor proof for `weak_child_drain_charge`

The induction is on the first argument only. The continuation may be non-normalized in this helper, because the RSEQ weak case needs the continuation `rsimp4_SEQ_atom q k` to preserve the uncollapsed `c*·c*` row. The cost is syntactic, so this is fine.

### RZERO/RONE

For the weak boundary, RONE is exactly zero:

```isabelle
weak_child_drain RZERO k = {}
weak_child_drain RONE  k = {}
```

because the RONE root contribution is `row_dlforms k`, and `weak_child_drain` subtracts `row_dlforms k`.

### RCHAR

There is one slot:

```isabelle
drain_ctxs (RCHAR c) = [(RCHAR c, rsize (RCHAR c))]
```

The charge map is constant `0`. The local lemma is:

```isabelle
lemma weak_RCHAR_slot_cost:
  "x ∈ weak_child_drain (RCHAR c) k
   ⟹ rsize x ≤ slot_cost (RCHAR c) k 0"
```

This is just the singleton opened row `c·k`, with units/zero cases erased.

### RALTS, weak version

The weak RALTS case is additive and harmless:

```isabelle
lemma weak_child_drain_RALTS_decomp:
  "weak_child_drain (RALTS rs) k
     ⊆ (⋃ q∈set rs. weak_child_drain q k)"
```

Given `x`, choose the least alternative index containing it:

```isabelle
i = Least (λi. i < length rs ∧ x ∈ weak_child_drain (rs ! i) k)
```

Use the child weak charge `ch_i x = j`, and return the global slot

```isabelle
alt_slot rs i j
```

The intervals given by `alt_off` are disjoint, and each child charge is injective, so the global charge is injective. This pays duplicate rows across alternatives automatically: the domain is a set, and `Least` picks one owner.

### RSEQ, weak version

Use the weak reassociation split:

```isabelle
lemma weak_child_drain_RSEQ_decomp:
  "weak_child_drain (RSEQ p q) k
     ⊆ weak_child_drain p (rsimp4_SEQ_atom q k)
      ∪ weak_child_drain q k"
```

Use priority-left ownership:

```isabelle
if x ∈ weak_child_drain p (rsimp4_SEQ_atom q k)
then charge into the left block
else charge into the right block
```

Left block index:

```isabelle
j ↦ j
```

Right block index:

```isabelle
j ↦ length (drain_ctxs p) + j
```

The size conversion for the left block is exactly the declared `ctx_extend` cost:

```isabelle
rsize (rsimp4_SEQ_atom q k) ≤ rsize q + 1 + rsize k
```

so if the child gives

```isabelle
rsize x ≤ snd (drain_ctxs p ! j) + (1 + rsize (rsimp4_SEQ_atom q k))
```

then the parent slot gives

```isabelle
rsize x
≤ snd (drain_ctxs p ! j) + (1 + rsize q) + (1 + rsize k)
= slot_cost (RSEQ p q) k j
```

because the left block of `drain_ctxs (RSEQ p q)` is

```isabelle
map (ctx_extend q) (drain_ctxs p)
```

### RSTAR, weak version

Use:

```isabelle
let j = nseq (RSTAR p) k
```

and split:

```isabelle
lemma weak_child_drain_RSTAR_decomp:
  "weak_child_drain (RSTAR p) k
     ⊆ (row_dlforms (rsimp4_SEQ_atom (RSTAR p) k) - row_dlforms k)
      ∪ weak_child_drain p (nseq (RSTAR p) k)"
```

Charge the entry part to slot `0`:

```isabelle
drain_ctxs (RSTAR p) ! 0 = (RSTAR p, rsize (RSTAR p))
```

and the body part to `Suc (ch_body x)`. The body-slot conversion is:

```isabelle
rsize (nseq (RSTAR p) k) ≤ rsize p + rsize k + 2
```

equivalently,

```isabelle
1 + rsize (nseq (RSTAR p) k)
≤ (1 + rsize (RSTAR p)) + (1 + rsize k)
```

because `rsize (RSTAR p) = rsize p + 1`. This is exactly the cost stored by

```isabelle
ctx_extend (RSTAR p)
```

for every body slot. This is the same star-specialized size fact from the continuation-parametric design. 

---

## 4. The exact RALTS cover lemma #3

First prove the set relation into weak children:

```isabelle
lemma strong_child_drain_RALTS_to_weak_children:
  assumes nf:      "rtail_nf (RALTS rs)"
      and norm:    "S (RALTS rs) = RALTS rs"
      and nf_k:    "rtail_nf k"
      and norm_k:  "S k = k"
      and guards:  "rntimes_free (RALTS rs)" "rntimes_free k"
                   "legacy_rrexp (RALTS rs)" "legacy_rrexp k"
  shows
    "strong_child_drain (RALTS rs) k
       ⊆ (⋃ q∈set rs. weak_child_drain q k)"
```

The root sublemma inside this proof is the one you asked for:

```isabelle
lemma RALTS_wrapped_root_into_weak_slots:
  assumes same_guards
  shows
    "row_dlforms (S (rsimp4_SEQ_atom (RALTS rs) k))
       - strong_opened_live (S k)
     ⊆ (⋃ q∈set rs.
          (row_dlforms (rsimp4_SEQ_atom q k) - row_dlforms k))"
```

This is the precise relation between the wrapped-root opening and child context slots. It is intentionally phrased with `rsimp4_SEQ_atom q k`, not `nseq q k`. The bad row

```isabelle
b·(c*·c*)
```

is in

```isabelle
row_dlforms (rsimp4_SEQ_atom (b·c*) c*)
```

and is charged to the slot

```isabelle
(b·c*, 4)
```

with cost

```isabelle
4 + (1 + rsize c*) = 4 + 3 = 7
```

The corresponding strong child root `nseq (b·c*) c*` may collapse to `b·c*`, and that is exactly why the old child-drain membership proof was false. The weak slot lemma pays the parent row without needing it to be a child-drain member.

Then #3 is short:

```isabelle
lemma strong_child_drain_RALTS_ctx_bound:
  assumes guards
  shows
    "rsize_set (strong_child_drain (RALTS rs) k)
       ≤ sum_list (map (λq. ctx_bound (drain_ctxs q) k) rs)"
proof -
  have incl:
    "strong_child_drain (RALTS rs) k
       ⊆ (⋃ q∈set rs. weak_child_drain q k)"
    by (rule strong_child_drain_RALTS_to_weak_children) fact+

  have "rsize_set (strong_child_drain (RALTS rs) k)
        ≤ rsize_set (⋃ q∈set rs. weak_child_drain q k)"
    using incl by (intro rsize_set_mono) auto
  also have "... ≤ sum_list (map (λq. rsize_set (weak_child_drain q k)) rs)"
    by (rule rsize_set_UNION_list_le_sum)
  also have "... ≤ sum_list (map (λq. ctx_bound (drain_ctxs q) k) rs)"
    using weak_child_drain_ctx_bound by (intro sum_list_mono) auto
  finally show ?thesis .
qed
```

This uses a union bound over alternatives, but not the boxed root-plus-children split. Each alternative contributes one fused weak budget that already includes the wrapped-root row and the recursive acc rows, assigned to the same list of child slots.

---

## 5. The RALTS charging map explicitly

For a row

```isabelle
x ∈ strong_child_drain (RALTS rs) k
```

define:

```isabelle
i x =
  Least (λi. i < length rs ∧ x ∈ weak_child_drain (rs ! i) k)
```

The existence of `i x` is exactly `strong_child_drain_RALTS_to_weak_children`.

Let `chW_i` be the child weak charge from `weak_child_drain_charge` for `rs ! i`. Then:

```isabelle
j x = chW_i x
charge_ALTS x = alt_slot rs (i x) (j x)
```

The map satisfies:

```isabelle
charge_ALTS x < length (drain_ctxs (RALTS rs))
```

and

```isabelle
rsize x
≤ snd (drain_ctxs (RALTS rs) ! charge_ALTS x) + (1 + rsize k)
```

by `nth_alt_slot`.

It is injective on the deduplicated parent drain: if two rows charge to the same global slot, the interval lemma gives the same alternative index, and child injectivity gives the same row. If the same syntactic row is produced by two alternatives, the set has only one copy and `Least` picks one owner.

---

## 6. The exact RSTAR cover lemma #4

Define the entry set:

```isabelle
definition star_entry_drain where
  "star_entry_drain p k =
     row_dlforms (nseq (RSTAR p) k) - strong_opened_live (S k)"
```

Then prove the strong-to-weak-body relation:

```isabelle
lemma strong_child_drain_RSTAR_to_entry_weak_body:
  assumes nf:      "rtail_nf (RSTAR p)"
      and norm:    "S (RSTAR p) = RSTAR p"
      and nf_k:    "rtail_nf k"
      and norm_k:  "S k = k"
      and guards:  "rntimes_free (RSTAR p)" "rntimes_free k"
                   "legacy_rrexp (RSTAR p)" "legacy_rrexp k"
  shows
    "strong_child_drain (RSTAR p) k
       ⊆ star_entry_drain p k
        ∪ weak_child_drain p (nseq (RSTAR p) k)"
```

The proof is by unfolding the RSTAR clause of the live accumulator:

```isabelle
strong_opened_live (nseq (RSTAR p) k)
  ⊆ row_dlforms (nseq (RSTAR p) k)
   ∪ weak_live p (nseq (RSTAR p) k)
```

After subtracting `strong_opened_live (S k)`, root rows go to `star_entry_drain`; body rows either remain in the weak body drain, or if they are in the body weak boundary `row_dlforms (nseq (RSTAR p) k)`, they are paid by the entry set.

The entry cost lemma is:

```isabelle
lemma star_entry_drain_cost:
  assumes guards
  shows
    "rsize_set (star_entry_drain p k)
       ≤ rsize (RSTAR p) + (1 + rsize k)"
```

Use the atomic-star shape of `nseq (RSTAR p) k`:

```isabelle
rsize (nseq (RSTAR p) k) ≤ rsize p + rsize k + 2
```

and `rsize (RSTAR p) = rsize p + 1`, so

```isabelle
rsize (nseq (RSTAR p) k)
≤ rsize (RSTAR p) + 1 + rsize k
= rsize (RSTAR p) + (1 + rsize k)
```

The opened row set is singleton-or-empty for this atomic-left sequence, so the linear row-size bound applies; do not use the generic quadratic `row_dlforms` bound.

Then #4 is:

```isabelle
lemma strong_child_drain_RSTAR_ctx_step:
  assumes guards
  shows
    "rsize_set (strong_child_drain (RSTAR p) k)
       ≤ rsize (RSTAR p) + (1 + rsize k)
         + ctx_bound (drain_ctxs p) (nseq (RSTAR p) k)"
proof -
  let ?j = "nseq (RSTAR p) k"

  have incl:
    "strong_child_drain (RSTAR p) k
       ⊆ star_entry_drain p k ∪ weak_child_drain p ?j"
    by (rule strong_child_drain_RSTAR_to_entry_weak_body) fact+

  have "rsize_set (strong_child_drain (RSTAR p) k)
        ≤ rsize_set (star_entry_drain p k)
          + rsize_set (weak_child_drain p ?j)"
    using incl by (intro rsize_set_subset_union_sum) auto
  also have "... ≤ rsize (RSTAR p) + (1 + rsize k)
                 + ctx_bound (drain_ctxs p) ?j"
    using star_entry_drain_cost weak_child_drain_ctx_bound by auto
  finally show ?thesis .
qed
```

This is the RSTAR analog of the RALTS repair: the body is not charged to the strong child drain, but to the weak child drain under the re-entry continuation.

---

## 7. The RSTAR charging map explicitly

For

```isabelle
x ∈ strong_child_drain (RSTAR p) k
```

let

```isabelle
j = nseq (RSTAR p) k
```

Use priority:

```isabelle
if x ∈ star_entry_drain p k
then charge x = Inl ()
else charge x = Inr (chW p j x)
```

If you want this as a parent-slot map into `drain_ctxs (RSTAR p)`:

```isabelle
charge_STAR x =
  if x ∈ star_entry_drain p k
  then 0
  else Suc (chW p j x)
```

The entry set is singleton-or-empty, so slot `0` is not overused. Body slots are shifted by `Suc`, and `weak_child_drain_charge` gives injectivity on the body. The body cost is later converted into parent-slot cost by:

```isabelle
rsize j ≤ rsize p + rsize k + 2
```

For the tight CE with body

```isabelle
p = (1+a)·c
k = 1
```

the escaping row is charged to the body slot for `c` in `drain_ctxs p`, not to the star entry. Here

```isabelle
j = nseq (RSTAR p) RONE = RSTAR p
```

and the slot is essentially

```isabelle
(RCHAR c, 1)
```

with cost

```isabelle
1 + (1 + rsize j)
```

which is exactly the size of the row `c·j`. That is why the master context cover can be slack-zero on this family: no extra RSTAR correction term is being smuggled in; the body slot itself pays the escaped re-entry row.

---

## 8. Existing facts to lean on

Use these already-green or local facts as the discharge surface:

```isabelle
ctx_bound (drain_ctxs (RALTS rs)) k
= sum_list (map (λq. ctx_bound (drain_ctxs q) k) rs)

rsize (rsimp4_SEQ_atom q k) ≤ rsize q + 1 + rsize k

rsize (nseq (RSTAR p) k) ≤ rsize p + rsize k + 2

drain_ctxs (RSEQ p q)
= map (ctx_extend q) (drain_ctxs p) @ drain_ctxs q

drain_ctxs (RSTAR p)
= (RSTAR p, rsize (RSTAR p))
  # map (ctx_extend (RSTAR p)) (drain_ctxs p)

drain_ctxs (RALTS rs)
= concat (map drain_ctxs rs)
```

Also use the row-opener shape lemmas, not the generic square bound. The full problem statement records that the opener is set-native/deduplicated and that list-cost and rowwise simplification monotonicity routes are refuted, so the local proof should stay with singleton/slot opening facts and finite-set reindexing only. 

The master induction should therefore be over the pair of predicates:

```isabelle
P p ≡ ∀k. strong_child_drain p k ≤ctx ctx_bound (drain_ctxs p) k
Q p ≡ ∀k. weak_child_drain   p k ≤ctx ctx_bound (drain_ctxs p) k
```

with #3 using `Q` on RALTS children and #4 using `Q` on the RSTAR body. The old failed route used `P` on the children and therefore lost the uncollapsed parent row; this route uses `Q`, whose root clause is exactly the weak `rsimp4` plug that the parent opener exposes.
