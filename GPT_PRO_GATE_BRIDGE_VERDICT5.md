<!--
SECRETARY HEADER (2026-06-15). GPT Pro verdict #6 — the corrected GATE ASSEMBLY design after
the scover/master_cover set-containment routes were refuted (they die on the a*·a*→a* strong
collapse). THE MOVE: replace set-containment by a `slot_origin_cover` — an INJECTIVE map from
each strong (collapsed) row to a distinct paid drain_ctxs slot whose weak witness row
`collapses_to` it (`row_dlforms(S y) = {x} ∧ rsize x ≤ rsize y`). The strong row is the theorem
object; the weak row is only a cost witness. Pays b·a* exactly (y = b·(a*·a*)). Reuses the
validated absorbed-B1 bridge + the green ctx ledger; avoids set-cover, B2 equality, S-monotonicity.

STATUS: depth>=5 validation IN PROGRESS (the make-or-break: does an injective slot_origin_cover
actually exist for strong_child_drain — a bipartite matching check — + the per-constructor lift
lemmas). A and all agents HOLD until this is green-lit in STEER. The 7-lemma stack is in §1-7.
-->

## Verdict

Use **candidate 1 as the outer assembly** and **candidate 3 as the induction invariant**. Do **not** try to prove a plain set inclusion into the weak carrier, and do **not** install a global “`S`-image monotonicity” theorem. The obstruction is exactly the already-recorded one: `rsimp7_SEQ_atom` may collapse `a*·a*` while the weak `rsimp4_SEQ_atom` slot still contains the uncollapsed row, so membership is incomparable even when the size charge is valid. The status note says the corrected route is a **size cost-cover over indexed `drain_ctxs` slots**, not set-membership, with RALTS additive and RSTAR adding one entry slot. 

The move is:

```isabelle
strong row x  ≠  weak row y as a set member
strong row x  =  collapse/open(y)
rsize x ≤ rsize y
y is paid by an indexed drain_ctxs slot
```

So the object to prove is not `strong_child_drain p k ⊆ weak_child_drain p k`, but an **injective cost-origin relation** from each strong row to a paid weak slot.

---

## 1. Replace set containment by a slot-origin charge

Keep the existing indexed-slot discipline from verdict5: `drain_ctxs` is a **list ledger**, not a set ledger, because duplicate context pairs may still represent separate paid slots. 

Use these proof-only definitions.

```isabelle
definition slot_cost where
  "slot_cost p k i =
     snd (drain_ctxs p ! i) + (1 + rsize k)"

definition weak_slot_rows where
  "weak_slot_rows p k i =
     row_dlforms
       (rsimp4_SEQ_atom (fst (drain_ctxs p ! i)) k)
       - row_dlforms k"
```

The key new relation is **not** membership of the strong row in the weak slot. It is: the weak slot row collapses/open-normalizes to the strong row and is at least as large.

```isabelle
definition collapses_to where
  "collapses_to y x ⟷
     row_dlforms (S y) = {x} ∧ rsize x ≤ rsize y"
```

If in the local development `row_dlforms (S y)` is awkward because of opener aliases, use the equivalent singleton lemma for the strong opener of a linear row. The important part is that the relation is **functional in `x`**:

```isabelle
lemma collapses_to_functional:
  assumes "collapses_to y x" "collapses_to y x'"
  shows "x = x'"
  using assms unfolding collapses_to_def by auto
```

Now define the actual charge invariant:

```isabelle
definition slot_origin_cover where
  "slot_origin_cover p k X ⟷
    (∃own wit.
        inj_on own X ∧
        (∀x∈X.
            own x < length (drain_ctxs p) ∧
            wit x ∈ weak_slot_rows p k (own x) ∧
            collapses_to (wit x) x))"
```

This is the replacement for every failed set-cover statement. It says: each **deduped strong row** gets one paid slot, and the weak row in that slot is only a **witness of cost**, not a required set equal/member.

The numeric extraction is then mechanical:

```isabelle
lemma weak_slot_rows_cost:
  assumes "i < length (drain_ctxs p)"
      and "y ∈ weak_slot_rows p k i"
  shows "rsize y ≤ slot_cost p k i"
```

This is the per-slot form of the already-green weak carrier charge. The verdict5 weak proof already has the stronger ingredient: an injective charge for `weak_child_drain`, followed by reindexing into the sum over slots. 

```isabelle
lemma slot_origin_cover_ctx_bound:
  assumes "finite X"
      and "slot_origin_cover p k X"
  shows "rsize_set X ≤ ctx_bound (drain_ctxs p) k"
proof -
  obtain own wit where inj: "inj_on own X"
    and lt:  "⋀x. x∈X ⟹ own x < length (drain_ctxs p)"
    and wit: "⋀x. x∈X ⟹ wit x ∈ weak_slot_rows p k (own x)"
    and col: "⋀x. x∈X ⟹ collapses_to (wit x) x"
    using assms unfolding slot_origin_cover_def by blast

  have "rsize_set X ≤ (∑x∈X. slot_cost p k (own x))"
    unfolding rsize_set_def
    using col wit lt weak_slot_rows_cost
    unfolding collapses_to_def
    by (intro sum_mono) fastforce
  also have "... = (∑i∈own ` X. slot_cost p k i)"
    using inj by (simp add: sum.reindex)
  also have "... ≤ (∑i<length (drain_ctxs p). slot_cost p k i)"
    using lt by (intro sum_mono2) auto
  also have "... = ctx_bound (drain_ctxs p) k"
    unfolding slot_cost_def
    by (simp add: ctx_bound_as_slots)
  finally show ?thesis .
qed
```

The target becomes:

```isabelle
lemma strong_child_drain_slot_origin_cover:
  assumes G: "drain_guard p k"
  shows "slot_origin_cover p k (strong_child_drain p k)"
```

and then:

```isabelle
lemma strong_child_drain_ctx_bound:
  assumes G: "drain_guard p k"
  shows "rsize_set (strong_child_drain p k)
       ≤ ctx_bound (drain_ctxs p) k"
  using strong_child_drain_slot_origin_cover[OF G]
        slot_origin_cover_ctx_bound
  by auto
```

Finally:

```isabelle
lemma strong_child_drain_potential:
  assumes G: "drain_guard p k"
  shows "rsize_set (strong_child_drain p k)
       ≤ drain_pot p + drain_w p * (1 + rsize k)"
proof -
  have "rsize_set (strong_child_drain p k)
        ≤ ctx_bound (drain_ctxs p) k"
    by (rule strong_child_drain_ctx_bound[OF G])
  also have "... ≤ drain_pot p + drain_w p * (1 + rsize k)"
    using ctx_bound_le_drain_child_budget G by blast
  finally show ?thesis .
qed
```

Here `drain_guard p k` should bundle your usual assumptions:

```isabelle
definition drain_guard where
  "drain_guard p k ⟷
      rtail_nf p ∧ S p = p ∧ rntimes_free p ∧ legacy_rrexp p ∧
      rtail_nf k ∧ S k = k ∧ rntimes_free k ∧ legacy_rrexp k"
```

Use whatever existing guard bundle you already have.

---

## 2. Induction measure and invariant

Prove `strong_child_drain_slot_origin_cover` by **well-founded induction on `rsize p`**, with the continuation universally quantified.

```isabelle
lemma strong_child_drain_slot_origin_cover:
  assumes "drain_guard p k"
  shows "slot_origin_cover p k (strong_child_drain p k)"
using assms
proof (induction p arbitrary: k rule: rsize_less_induct)
  ...
qed
```

The measure is only the first argument. This is essential: the recursive continuations grow or normalize, for example

```isabelle
j = nseq q k
j = nseq (RSTAR p) k
rsimp4_SEQ_atom q k
```

so an induction on `(p,k)` is the wrong shape. Subterms are strictly smaller in the first coordinate, and continuation closure is discharged by existing `legacy`, `rntimes_free`, `rtail_nf`, and `S`-fixpoint guard-decomposition lemmas.

The induction invariant is **numeric/slot-origin**, not set inclusion:

```isabelle
P p ≡ ∀k. drain_guard p k
          ⟶ slot_origin_cover p k (strong_child_drain p k)
```

A second auxiliary invariant should be proved simultaneously or just before the induction:

```isabelle
B p ≡ ∀k. drain_guard p k
          ⟶ absorbed_B1_slot_origin p k
```

where `absorbed_B1_slot_origin` is the charged form of your validated bridge:

```isabelle
lemma absorbed_B1_slot_origin:
  assumes "drain_guard q cont"
  shows
    "slot_origin_cover q cont
       (strong_opened_live (nseq q cont) - strong_opened_live (S cont))"
```

This lemma is where the validated bridge

```isabelle
SOL (rsimp4_SEQ_atom q cont)
  ⊆ SOL_acc q cont ∪ SOL cont
```

is consumed. The bridge is not used to prove that a strong row is a weak member. It is used to prove that an intermediate continuation-boundary row is either removed by the final boundary or has a weak slot origin in the `q`-ledger.

---

## 3. Why global candidate 2 is too strong

The safe statement is:

```isabelle
rsize_set strong ≤ rsize_set weak
```

**only if** it is derived from an explicit injective origin map:

```isabelle
∃π. inj_on π strong ∧
    (∀x∈strong. π x ∈ weak ∧ rsize x ≤ rsize (π x))
```

Do not prove a general theorem like:

```isabelle
rsize_set (S ` X) ≤ rsize_set X
```

or any rowwise `row_dlforms` monotonicity of `S`. The full gate statement explicitly records that `S` is not pointwise `row_dlforms`-cost monotone, so a generic simplification-shrinks-ledger route is a dead route. 

The usable local fact is weaker and slot-shaped:

```isabelle
weak slot witness y collapses to strong row x
⟹ rsize x ≤ rsize y
```

For the counterexample row, the map is:

```isabelle
x = b·a*
y = b·(a*·a*)
collapses_to y x
rsize x ≤ rsize y
```

The row `x` is not in the weak cover as a member. It is paid by the weak row `y`.

---

## 4. RSEQ discharge

Let:

```isabelle
j = nseq q k
```

Use a three-way proof split, but only two paid blocks.

```isabelle
drain_ctxs (RSEQ p q)
  = map (ctx_extend q) (drain_ctxs p) @ drain_ctxs q
```

The left block pays rows whose origin is in `p` under continuation `j`. The right block pays rows from `q` and rows that were only the intermediate `j`-boundary.

### RSEQ local split

Prove the local classification as a slot-origin statement, not as a weak-set inclusion:

```isabelle
lemma strong_child_drain_RSEQ_slot_origin:
  assumes G: "drain_guard (RSEQ p q) k"
  defines "j ≡ nseq q k"
  shows "slot_origin_cover (RSEQ p q) k
           (strong_child_drain (RSEQ p q) k)"
```

The proof uses:

```isabelle
strong_child_drain (RSEQ p q) k
  ⊆
    left_live p j
  ∪ B1 q k
  ∪ right_live q k
```

where the important conceptual sets are:

```isabelle
left_live p j  = strong_child_drain p j
right_live q k = strong_child_drain q k
B1 q k         = strong_opened_live j - strong_opened_live (S k)
```

Do not try to prove:

```isabelle
left weak rows under j
  ⊆ parent weak rows under k
```

as a set. That is precisely where the `a*·a*` collapse breaks the proof. Instead, lift the **origin witness**.

### Left block

From the IH for `p` at continuation `j`:

```isabelle
slot_origin_cover p j (strong_child_drain p j)
```

take for each left row `x`:

```isabelle
i < length (drain_ctxs p)
yL ∈ weak_slot_rows p j i
collapses_to yL x
```

Let the parent slot be the same index in the left block:

```isabelle
own x = i
```

and replace the witness by the parent weak append:

```isabelle
y =
  rsimp4_SEQ_atom
    (fst (ctx_extend q (drain_ctxs p ! i)))
    k
```

The required local collapse lemma is:

```isabelle
lemma RSEQ_lift_collapses_to:
  assumes "i < length (drain_ctxs p)"
      and "yL ∈ weak_slot_rows p (nseq q k) i"
      and "collapses_to yL x"
      and "drain_guard (RSEQ p q) k"
  shows
    "∃y.
        y ∈ weak_slot_rows (RSEQ p q) k i ∧
        collapses_to y x"
```

This lemma is the corrected replacement for the false bridge

```isabelle
rsimp7_SEQ_atom q cont = S (rsimp4_SEQ_atom q cont)
```

It should not assert equality of plugs. It only asserts that the **parent weak append has the same strong collapsed opened singleton**, possibly after shrinking.

Cost is purely arithmetic:

```isabelle
rsize (nseq q k) ≤ rsize q + 1 + rsize k
```

hence:

```isabelle
slot_cost p j i
≤ slot_cost (RSEQ p q) k i
```

because the left parent slot is `ctx_extend q (drain_ctxs p ! i)`.

### Right block

For right rows, use the IH for `q,k` and shift the slot index:

```isabelle
own x = length (drain_ctxs p) + own_q x
```

The witness is unchanged, but viewed inside the right block of the appended slot list.

The standard append facts discharge lookup and index bounds:

```isabelle
nth_append
length_map
```

### The B1 rows

These are the rows that the left child regards as continuation boundary under `j`, but the parent only subtracts `S k`.

This is exactly where the absorbed bridge is used. Use it in charged form:

```isabelle
lemma RSEQ_B1_absorbed_slot_origin:
  assumes "drain_guard q k"
  defines "j ≡ nseq q k"
  shows
    "slot_origin_cover q k
       (strong_opened_live j - strong_opened_live (S k))"
```

The proof shape is:

```isabelle
x ∈ strong_opened_live (nseq q k) - strong_opened_live (S k)

choose weak predecessor y in SOL (rsimp4_SEQ_atom q k)
with collapses_to y x

by absorbed_B1:
  y ∈ SOL_acc q k ∪ SOL k

if y ∈ SOL k:
   collapses_to y x implies x ∈ strong_opened_live (S k), contradiction
else:
   y ∈ SOL_acc q k, hence y has a q-slot weak origin
```

So the B1 rows are paid by the **right block**, not by a new summand.

This is the key RSEQ repair. The old proof tried to match the collapsed row against an uncollapsed child set. The new proof lets the collapsed row charge to the same slot as the uncollapsed predecessor.

---

## 5. RSTAR discharge

For star, let:

```isabelle
j = nseq (RSTAR p) k
```

and define the entry part:

```isabelle
definition star_entry_drain where
  "star_entry_drain p k =
     row_dlforms (nseq (RSTAR p) k) - strong_opened_live (S k)"
```

The star ledger has exactly the required shape:

```isabelle
drain_ctxs (RSTAR p)
  = (RSTAR p, rsize (RSTAR p))
    # map (ctx_extend (RSTAR p)) (drain_ctxs p)
```

The entry row uses slot `0`; the body rows use shifted body slots.

### Entry slot

Prove the singleton/linear entry lemma:

```isabelle
lemma star_entry_slot_origin:
  assumes "drain_guard (RSTAR p) k"
  shows
    "slot_origin_cover (RSTAR p) k (star_entry_drain p k)"
```

with:

```isabelle
own x = 0
wit x = rsimp4_SEQ_atom (RSTAR p) k
```

or the corresponding opened singleton witness if the local opener formulation needs the element after `row_dlforms`.

The size lemma is the already identified one:

```isabelle
rsize (nseq (RSTAR p) k) ≤ rsize p + rsize k + 2
```

equivalently:

```isabelle
rsize (nseq (RSTAR p) k)
≤ rsize (RSTAR p) + (1 + rsize k)
```

and the entry opener is singleton-or-empty, so no generic quadratic `row_dlforms` bound is needed. verdict5 also flags this exact RSTAR entry-cost shape and warns to use the opener shape lemma rather than the square bound. 

### Body slots

Use the IH for the body at the re-entry continuation:

```isabelle
slot_origin_cover p j (strong_child_drain p j)
```

For each body row `x`, if the IH gives slot `i`, shift:

```isabelle
own x = Suc i
```

The witness is lifted through the parent star context:

```isabelle
y =
  rsimp4_SEQ_atom
    (fst (ctx_extend (RSTAR p) (drain_ctxs p ! i)))
    k
```

with the local lift lemma:

```isabelle
lemma RSTAR_lift_collapses_to:
  assumes "i < length (drain_ctxs p)"
      and "yB ∈ weak_slot_rows p (nseq (RSTAR p) k) i"
      and "collapses_to yB x"
      and "drain_guard (RSTAR p) k"
  shows
    "∃y.
        y ∈ weak_slot_rows (RSTAR p) k (Suc i) ∧
        collapses_to y x"
```

The parent-slot cost conversion is:

```isabelle
1 + rsize (nseq (RSTAR p) k)
≤ (1 + rsize (RSTAR p)) + (1 + rsize k)
```

which is exactly the `ctx_extend (RSTAR p)` budget for every shifted body slot. The verdict5 RSTAR section records this body-slot conversion and the fact that the tight counterexample row is charged to a body slot, not to hidden star slack. 

### Star B1 boundary

The body child `p` at continuation `j` subtracts `strong_opened_live j`, but the parent star only subtracts `strong_opened_live (S k)`. Those lost rows are precisely the star entry boundary:

```isabelle
strong_opened_live j - strong_opened_live (S k)
```

They must not become an extra summand. Prove:

```isabelle
lemma RSTAR_body_B1_is_entry:
  assumes "drain_guard (RSTAR p) k"
  defines "j ≡ nseq (RSTAR p) k"
  shows
    "strong_opened_live j - strong_opened_live (S k)
       ⊆ star_entry_drain p k"
```

or, if the exact `SOL`/`row_dlforms` definitions require the weak predecessor formulation, prove the charged version:

```isabelle
lemma RSTAR_body_B1_entry_slot_origin:
  assumes "drain_guard (RSTAR p) k"
  defines "j ≡ nseq (RSTAR p) k"
  shows
    "slot_origin_cover (RSTAR p) k
       (strong_opened_live j - strong_opened_live (S k))"
```

with all rows charged to slot `0`.

This is where the absorbed-B1 bridge is used in the star case: a body-boundary row is either already in the final continuation boundary and disappears, or it is the star entry and is paid by slot `0`. No extra RSTAR correction term is introduced.

Then the RSTAR numeric conclusion is:

```isabelle
lemma strong_child_drain_RSTAR_ctx_bound:
  assumes "drain_guard (RSTAR p) k"
  shows
    "rsize_set (strong_child_drain (RSTAR p) k)
       ≤ ctx_bound (drain_ctxs (RSTAR p)) k"
proof -
  let ?j = "nseq (RSTAR p) k"

  have entry:
    "rsize_set (star_entry_drain p k)
       ≤ rsize (RSTAR p) + (1 + rsize k)"
    using star_entry_drain_cost assms by blast

  have body:
    "rsize_set (strong_child_drain p ?j)
       ≤ ctx_bound (drain_ctxs p) ?j"
    using IH guard_closure assms by blast

  have body_to_parent:
    "ctx_bound (drain_ctxs p) ?j
       ≤ ctx_bound (map (ctx_extend (RSTAR p)) (drain_ctxs p)) k"
    using rsize_nseq_RSTAR_le by (slotwise_arith)

  have split:
    "strong_child_drain (RSTAR p) k
       ⊆ star_entry_drain p k ∪ strong_child_drain p ?j"
    using RSTAR_body_B1_is_entry by blast

  show ?thesis
    using split entry body body_to_parent
    unfolding drain_ctxs.simps ctx_bound_def
    by (rsize_set_union_arith)
qed
```

If the set split is brittle because of the same collapsed/uncollapsed mismatch, use the `slot_origin_cover` version instead of `⊆`. The arithmetic remains identical.

---

## 6. RALTS discharge

RALTS is the place where a free parent-boundary summand is impossible: the budget is exactly additive over children. The status file explicitly notes that RALTS has zero constructor slack, so adding a full parent opened row as a separate boundary cannot be paid. 

Use indexed alternative slots:

```isabelle
definition alt_off where
  "alt_off rs i =
     sum_list (map (λq. length (drain_ctxs q)) (take i rs))"

definition alt_slot where
  "alt_slot rs i j = alt_off rs i + j"
```

with:

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

The RALTS origin statement should be:

```isabelle
lemma RALTS_strong_rows_have_child_weak_origin:
  assumes "drain_guard (RALTS rs) k"
      and "x ∈ strong_child_drain (RALTS rs) k"
  shows
    "∃i y.
        i < length rs ∧
        y ∈ weak_child_drain (rs ! i) k ∧
        collapses_to y x"
```

Then choose the least owner:

```isabelle
i x = Least (λi.
        i < length rs ∧
        (∃y∈weak_child_drain (rs ! i) k. collapses_to y x))
```

If the child weak charge gives `j`, the parent slot is:

```isabelle
own x = alt_slot rs (i x) j
```

This is exactly where `b·a*` is handled correctly:

```isabelle
x = b·a*
y = b·(a*·a*)
y ∈ weak_child_drain child k
collapses_to y x
rsize x ≤ rsize y
```

No membership claim `b·a* ∈ weak_child_drain child k` is made.

Injection is preserved as follows: if two strong rows charge to the same global RALTS slot, the interval lemma gives the same child index, the child weak charge gives the same weak witness, and `collapses_to_functional` gives the same strong row.

---

## 7. Final assembly path

The proof chain should be:

```isabelle
strong_child_drain_slot_origin_cover
  : slot_origin_cover p k (strong_child_drain p k)

slot_origin_cover_ctx_bound
  : rsize_set (strong_child_drain p k)
      ≤ ctx_bound (drain_ctxs p) k

ctx_bound_le_drain_child_budget
  : ctx_bound (drain_ctxs p) k
      ≤ drain_pot p + drain_w p * (1 + rsize k)
```

So the final target closes by:

```isabelle
lemma strong_child_drain_master_bound:
  assumes "drain_guard p k"
  shows
    "rsize_set (strong_child_drain p k)
       ≤ drain_pot p + drain_w p * (1 + rsize k)"
proof -
  have A:
    "rsize_set (strong_child_drain p k)
       ≤ ctx_bound (drain_ctxs p) k"
    using strong_child_drain_ctx_bound assms by blast
  also have
    "... ≤ drain_pot p + drain_w p * (1 + rsize k)"
    using ctx_bound_le_drain_child_budget assms by blast
  finally show ?thesis .
qed
```

Then your already-green wrappers consume it:

```isabelle
strong_child_drain_potential
actual_gate_from_current_drain
```

The core design principle is: **collapse is allowed to change the row identity, but not the slot budget**. The weak row is used only as a paid witness; the strong row is the actual theorem object.
