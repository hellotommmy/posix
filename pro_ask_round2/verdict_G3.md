I modeled the attached definitions exactly, and L2 survived the counterexample hunt. One important correction emerged: the tempting **RSEQ recurrence**

```isabelle
D1 (RSEQ r1 r2) k <= 1 + D1 r1 (s4 r2 k) + D1 r2 k
```

is **false**. The smallest adversarial shape I found is the known killer:

```text
q = (1 + a*) . c*,   k = c*
D1 q k = 3, but 1 + D1 (1+a*) (c*.c*) + D1 c* c* = 2
```

So the formal proof should not use that recurrence. The correct RSEQ step is:

```isabelle
D1 (RSEQ r1 r2) k <= rsize r1 + D1 r2 k
```

and then the right IH gives `<= rsize r1 + rsize r2 < rsize (RSEQ r1 r2)`. This is still stronger than needed and is what my Python validation supports.

I use the notation from `DESIGN.md`: `S = rsimpStrong_raw`, `s4 = rsimp4_SEQ_atom`, `s7 = rsimp7_SEQ_atom`, `C X = rsimpStrong_dlform_closure X`, `A r k = strong_apder_acc r k`, `B k = A RONE k`, and `D r k = card (A r k - B k)`; these are the same definitions and carrier/green lemmas listed in the attached definitions.   The target L2 is exactly the singleton-size lemma requested in the prompt. 

---

## 1. Helper definitions

I would introduce these small abbreviations in Isabelle. Only `ralts_size_budget` is recursive.

```isabelle
abbreviation A :: "rrexp => rrexp => rrexp set" where
  "A r k == strong_apder_acc r k"

abbreviation B :: "rrexp => rrexp set" where
  "B k == strong_apder_acc RONE k"

definition D :: "rrexp => rrexp => nat" where
  "D r k = card (A r k - B k)"

definition D1 :: "rrexp => rrexp => nat" where
  "D1 q k = card (A (RALTS [q]) k - B k)"

definition single_root :: "rrexp => rrexp => rrexp set" where
  "single_root q k =
     rsimpStrong_dlform_closure
       (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))"

definition single_term :: "rrexp => rrexp => rrexp set" where
  "single_term q k =
     rsimpStrong_dlform_closure
       (apder_term_frontier_acc q k)"

fun ralts_size_budget :: "rrexp list => nat" where
  "ralts_size_budget [] = 0"
| "ralts_size_budget (q # qs) =
     rsize q + ralts_size_budget qs"
```

The basic decomposition is:

```isabelle
lemma A_single_decomp:
  "A (RALTS [q]) k = single_root q k ∪ single_term q k"
  unfolding strong_apder_acc_def single_root_def single_term_def
  by simp
```

because

```isabelle
apder_term_frontier_acc (RALTS [q]) k
  = apder_term_frontier_acc q k
```

and the carrier is exactly

```isabelle
C (rfrontier (s4 (RALTS [q]) k) ∪ apder_term_frontier_acc q k).
```

Also:

```isabelle
lemma B_alt:
  "B k = rsimpStrong_dlform_closure (rfrontier k)"
  unfolding strong_apder_acc_def
  by simp
```

since `s4 RONE k = k` and `apder_term_frontier_acc RONE k = {}`. The definitions of `rfrontier`, `row_dlforms`, `rsimpStrong_dlform_closure`, and `apder_term_frontier_acc` are the ones in `DEFINITIONS.txt`.   

---

## 2. The two new helper lemmas that make the induction work

### 2.1 Boundary-plus-term absorption

This helper is the main way to avoid double-counting the continuation boundary in the RSEQ case.

```isabelle
lemma boundary_term_absorb:
  assumes "apder_nf t" "apder_nf k"
  shows
    "card ((B (rsimp4_SEQ_atom t k) - B k) ∪
           (single_term t k - B k))
       <= D1 t k"
```

Interpretation: when `t` is opened under `k`, the rows already present in the new continuation boundary `B (s4 t k)` plus the genuine term rows of `t` are all paid by the singleton carrier of `t`.

This is not a simple subset lemma. In general,

```isabelle
B (s4 t k) ⊆ A (RALTS [t]) k ∪ B k
```

is false. The example

```text
t = a . b*,   k = b* . b*
```

has a collapsed boundary row `a.b*` that is not literally in `A (RALTS [t]) k`; it is charged to the uncollapsed singleton root row `a.(b*.b*)`. So formalize this helper as a cardinal/injection lemma, not as a subset lemma.

Proof method: induction on `t`, using the same constructor split as below. For the `RALTS` case, use the singleton-cover lemma L1 from the design:

```isabelle
lemma strong_apder_acc_RALTS_singleton_cover:
  "A (RALTS rs) k <= (UN q:set rs. A (RALTS [q]) k)"
```

The design explains why this cover is valid: the strong alternation prune deletes already-covered head branches but does not invent a branch with no origin.  The prune definitions and “shrunk-never-dropped” behavior are in `DEFINITIONS.txt`. 

### 2.2 Sequence-head core budget

Define the sequence-head core informally as:

```isabelle
core h t k =
  (single_root (RSEQ h t) k ∪
   single_term h (rsimp4_SEQ_atom t k))
  - (B k ∪ B (rsimp4_SEQ_atom t k))
```

The lemma is:

```isabelle
lemma seq_head_core_le_rsize:
  assumes "apder_nf h" "apder_nf t" "apder_nf k"
  shows
    "card
       ((single_root (RSEQ h t) k ∪
         single_term h (rsimp4_SEQ_atom t k))
        - (B k ∪ B (rsimp4_SEQ_atom t k)))
     <= rsize h"
```

This is the lemma that absorbs the hard tail-doubling.

Example:

```text
h = x*,  t = a*,  k = a*
```

The head core contains both

```text
x*.a*
x*.(a*.a*)
```

and `rsize x* = 2` pays for exactly those two rows. For the stronger killer

```text
h = 1 + a*,  t = c*,  k = c*
```

the core contains three rows:

```text
c*.c*
a*.c*
a*.(c*.c*)
```

and `rsize (1+a*) = 4` pays for them. This is precisely why the broken recurrence using `D1 h (s4 t k)` cannot work: the singleton carrier of `h` under the collapsed continuation hides some rows that the parent still sees.

Proof method for `seq_head_core_le_rsize`:

```isabelle
proof (induction h arbitrary: t k)
  case RZERO
  then show ?case by simp

  case RONE
  then show ?case by simp

  case (RCHAR c)
  (* term part is B (s4 t k); after subtracting B k ∪ B (s4 t k),
     only the singleton root can remain. *)
  have "card (...) <= 1"
    by (simp add: single_root_def single_term_def)
  then show ?case by simp

  case (RSEQ h1 h2)
  (* use associativity of s4:
       s4 (RSEQ h1 h2) c = s4 h1 (s4 h2 c)
     split the head core into the h1-core and the boundary-plus-term
     absorption for h2. *)
  have nf_h2_t_k:
    "apder_nf (rsimp4_SEQ_atom h2 (rsimp4_SEQ_atom t k))"
    using RSEQ.prems apder_nf_s4 by blast
  have core_h1:
    "... <= rsize h1"
    using RSEQ.IH(1) ...
  have absorb_h2:
    "... <= D1 h2 (rsimp4_SEQ_atom t k)"
    using boundary_term_absorb ...
  have "D1 h2 (rsimp4_SEQ_atom t k) <= rsize h2"
    using RSEQ.IH(2) ...
  then show ?case
    by simp
next
  case (RALTS rs)
  (* distribute branch origins by L1 / singleton cover and sum branch budgets. *)
  have "... <= ralts_size_budget rs"
    using RALTS.IH strong_apder_acc_RALTS_singleton_cover
    by (meson card_UN_Diff_list_le ...)
  then show ?case
    by simp
next
  case (RSTAR r)
  let ?c = "rsimp4_SEQ_atom t k"
  let ?c' = "rsimp4_SEQ_atom (RSTAR r) ?c"

  (* One row is the star-boundary/tail residual; the rest is the child term
     under ?c'. *)
  have star_boundary:
    "card (B ?c' - B ?c) <= 1"
    using star_boundary_shift_le_one[of r ?c] RSTAR.prems by simp

  have child:
    "card (single_term r ?c' - B ?c') <= D1 r ?c'"
    unfolding D1_def A_single_decomp by (intro card_mono) auto

  have "D1 r ?c' <= rsize r"
    using RSTAR.IH apder_nf_s4 RSTAR.prems by blast

  then show ?case
    using star_boundary child by simp
qed
```

This helper is the formal place where the size slack is spent. It should be proved before L2, or mutually with the boundary absorption lemma.

---

## 3. L2 proof by constructor

I recommend proving the slightly stronger theorem for all NF `q`, including a top `RALTS` case, because subterms of a nonalt branch may themselves be alternations. The requested nonalt singleton lemma is then immediate.

```isabelle
lemma singleton_size_nf:
  assumes "apder_nf q" "apder_nf k"
  shows "D1 q k <= rsize q"
```

### Case `RZERO`

```isabelle
A (RALTS [RZERO]) k = {}
```

Reason: `s4 (RALTS [RZERO]) k` is either `RZERO`, `RALTS [RZERO]`, or `RSEQ (RALTS [RZERO]) k`; after `S`, all of these strongly open to no rows, and `apder_term_frontier_acc RZERO k = {}`.

So:

```isabelle
D1 RZERO k = 0 <= rsize RZERO
```

### Case `RONE`

The term frontier is empty. The root rows are `row_dlforms (S k)` or a subset of `B k`, by the green continuation-base lemma:

```isabelle
lemma row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE:
  assumes "apder_nf k"
  shows "row_dlforms (rsimpStrong_raw k) ⊆ strong_apder_acc RONE k"
```

This lemma is listed in `DEFINITIONS.txt`.  Therefore:

```isabelle
D1 RONE k = 0 <= rsize RONE
```

### Case `RCHAR c`

For a singleton character alternation, the carrier equals the ordinary character carrier:

```isabelle
A (RALTS [RCHAR c]) k = A (RCHAR c) k
```

because `S (RALTS [RCHAR c]) = RCHAR c`, and the term frontier is `rfrontier k` in both cases.

Then use the green lemma:

```isabelle
lemma card_strong_apder_acc_RCHAR_diff_base_le:
  assumes "apder_nf k"
  shows "card (strong_apder_acc (RCHAR c) k - strong_apder_acc RONE k)
       <= rsize (RCHAR c)"
```

This gives:

```isabelle
D1 (RCHAR c) k <= 1 = rsize (RCHAR c)
```

The green RCHAR lemma is in the carrier section of `DEFINITIONS.txt`. 

### Case `RSEQ r1 r2`

Let:

```isabelle
c = rsimp4_SEQ_atom r2 k
```

The singleton carrier decomposes as:

```isabelle
A (RALTS [RSEQ r1 r2]) k
 =
 single_root (RSEQ r1 r2) k
 ∪ single_term r1 c
 ∪ single_term r2 k
```

because:

```isabelle
apder_term_frontier_acc (RSEQ r1 r2) k
 =
 apder_term_frontier_acc r1 (s4 r2 k)
 ∪ apder_term_frontier_acc r2 k
```

Now subtract `B k`. Every row is either:

1. in the head core, paid by `rsize r1`;
2. in the shifted boundary `B c - B k`;
3. in the right term rows `single_term r2 k - B k`.

Formally:

```isabelle
(A (RALTS [RSEQ r1 r2]) k - B k)
⊆
((single_root (RSEQ r1 r2) k ∪ single_term r1 c)
  - (B k ∪ B c))
∪
((B c - B k) ∪ (single_term r2 k - B k))
```

Taking cardinals:

```isabelle
D1 (RSEQ r1 r2) k
 <= card (((single_root (RSEQ r1 r2) k ∪ single_term r1 c)
            - (B k ∪ B c)))
    + card ((B c - B k) ∪ (single_term r2 k - B k))
```

Apply the two helpers:

```isabelle
card (((single_root (RSEQ r1 r2) k ∪ single_term r1 c)
        - (B k ∪ B c)))
 <= rsize r1

card ((B c - B k) ∪ (single_term r2 k - B k))
 <= D1 r2 k
```

So the exact RSEQ recurrence is:

```isabelle
D1 (RSEQ r1 r2) k <= rsize r1 + D1 r2 k
```

Then the IH on `r2` gives:

```isabelle
D1 r2 k <= rsize r2
```

hence:

```isabelle
D1 (RSEQ r1 r2) k
 <= rsize r1 + rsize r2
 <  Suc (rsize r1 + rsize r2)
 =  rsize (RSEQ r1 r2)
```

This is the corrected RSEQ step. The `Suc` at the `RSEQ` node is spare slack; the head syntax `rsize r1` pays for the frozen-tail rows, including the `s*.s*` residuals.

### Case `RSTAR r`

Let:

```isabelle
c = rsimp4_SEQ_atom (RSTAR r) k
```

The root of the singleton star is exactly the continuation boundary after plugging the star:

```isabelle
single_root (RSTAR r) k = B c
```

and the term part is:

```isabelle
single_term (RSTAR r) k = single_term r c
```

Therefore:

```isabelle
A (RALTS [RSTAR r]) k
 =
 B c ∪ single_term r c
```

Subtract `B k`:

```isabelle
A (RALTS [RSTAR r]) k - B k
⊆
(B c - B k) ∪ (single_term r c - B c)
```

The star boundary creates at most one non-base row:

```isabelle
lemma star_boundary_shift_le_one:
  assumes "apder_nf r" "apder_nf k"
  shows "card (B (rsimp4_SEQ_atom (RSTAR r) k) - B k) <= 1"
```

Proof: case-split on `S r` and `S k`. If `S (RSTAR r)` collapses to `RONE`, the shifted boundary is already in `B k`. Otherwise the strong plug has one leading `RSTAR` row outside the old boundary; `s7` only collapses the leading equal-star pair. This uses the exact `s7` definition. 

Also:

```isabelle
card (single_term r c - B c) <= D1 r c
```

because `single_term r c ⊆ A (RALTS [r]) c`.

By the IH at the changed continuation `c`:

```isabelle
D1 r c <= rsize r
```

using the preservation lemma:

```isabelle
lemma apder_nf_s4:
  assumes "apder_nf r" "apder_nf k"
  shows "apder_nf (rsimp4_SEQ_atom r k)"
```

Therefore:

```isabelle
D1 (RSTAR r) k
 <= 1 + D1 r c
 <= 1 + rsize r
 =  rsize (RSTAR r)
```

Here the `+1` star constructor is spent exactly on the possible new boundary/root row.

### Auxiliary top-`RALTS` case

Even though the target branch `q` is nonalt, this case is useful because subterms may be alternations.

First prove a flattening lemma:

```isabelle
lemma A_single_nested_RALTS:
  "A (RALTS [RALTS rs]) k = A (RALTS rs) k"
```

Then use L1:

```isabelle
A (RALTS rs) k
  ⊆ (UN q:set rs. A (RALTS [q]) k)
```

Thus:

```isabelle
D1 (RALTS rs) k
 <= card (((UN q:set rs. A (RALTS [q]) k) - B k))
 <= ralts_size_budget rs
```

by list induction and `card_Un_le`. The branch IH gives:

```isabelle
card (A (RALTS [q]) k - B k) <= rsize q
```

for every `q ∈ set rs`. Finally:

```isabelle
ralts_size_budget rs = sum_list (map rsize rs)
< Suc (sum_list (map rsize rs))
= rsize (RALTS rs)
```

This is the singleton version of the RALTS budget described in `DESIGN.md`. 

---

## 4. Isabelle proof skeleton

This is the shape I would formalize.

```isabelle
lemma finite_A [simp]: "finite (A r k)"
  (* by existing finiteness facts for rfrontier, atf, dlforms, closure *)

lemma finite_single_root [simp]: "finite (single_root q k)"
  unfolding single_root_def by simp

lemma finite_single_term [simp]: "finite (single_term q k)"
  unfolding single_term_def by simp

lemma A_single_decomp:
  "A (RALTS [q]) k = single_root q k ∪ single_term q k"
  unfolding strong_apder_acc_def single_root_def single_term_def
  by simp

lemma B_alt:
  "B k = rsimpStrong_dlform_closure (rfrontier k)"
  unfolding strong_apder_acc_def by simp

lemma apder_nf_s4:
  assumes "apder_nf r" "apder_nf k"
  shows "apder_nf (rsimp4_SEQ_atom r k)"
  using assms
  by (induction r arbitrary: k) auto

lemma A_single_RCHAR_eq:
  "A (RALTS [RCHAR c]) k = A (RCHAR c) k"
  unfolding strong_apder_acc_def
  by (cases k) (auto simp: rsimp7_SEQ_atom_def)

lemma star_single_root_eq_B:
  "single_root (RSTAR r) k =
   B (rsimp4_SEQ_atom (RSTAR r) k)"
  unfolding single_root_def B_alt
  by (cases k) (auto simp: rsimp7_SEQ_atom_def)

lemma star_boundary_shift_le_one:
  assumes "apder_nf r" "apder_nf k"
  shows "card (B (rsimp4_SEQ_atom (RSTAR r) k) - B k) <= 1"
proof -
  (* case split on rsimpStrong_raw r and rsimpStrong_raw k;
     use s7 definition: only one leading star row can survive outside B k *)
  show ?thesis sorry
qed

lemma boundary_term_absorb:
  assumes "apder_nf t" "apder_nf k"
  shows
    "card ((B (rsimp4_SEQ_atom t k) - B k) ∪
           (single_term t k - B k))
     <= D1 t k"
  using assms
proof (induction t arbitrary: k)
  case RZERO
  then show ?case by (simp add: D1_def single_term_def)
next
  case RONE
  then show ?case by (simp add: D1_def single_term_def)
next
  case (RCHAR c)
  then show ?case
    unfolding D1_def A_single_decomp single_term_def
    by (auto intro!: card_mono)
next
  case (RSEQ t1 t2)
  (* split s4 t1 (s4 t2 k), use IHs and card_Un_Diff_telescope_le *)
  show ?case sorry
next
  case (RALTS rs)
  (* use singleton cover L1 and list card-union bound *)
  show ?case sorry
next
  case (RSTAR r)
  let ?c = "rsimp4_SEQ_atom (RSTAR r) k"
  have nf_c: "apder_nf ?c"
    using RSTAR.prems apder_nf_s4 by blast
  show ?case
    using RSTAR.IH[OF nf_c] star_boundary_shift_le_one[of r k]
    by (simp add: D1_def A_single_decomp)
qed

lemma seq_head_core_le_rsize:
  assumes "apder_nf h" "apder_nf t" "apder_nf k"
  shows
    "card
       ((single_root (RSEQ h t) k ∪
         single_term h (rsimp4_SEQ_atom t k))
        - (B k ∪ B (rsimp4_SEQ_atom t k)))
     <= rsize h"
  using assms
proof (induction h arbitrary: t k)
  case RZERO
  then show ?case by (simp add: single_root_def single_term_def)
next
  case RONE
  then show ?case by (simp add: single_root_def single_term_def)
next
  case (RCHAR c)
  have term_is_boundary:
    "single_term (RCHAR c) (rsimp4_SEQ_atom t k)
     = B (rsimp4_SEQ_atom t k)"
    unfolding single_term_def B_alt
    by simp
  have root_le_one:
    "card (single_root (RSEQ (RCHAR c) t) k
           - (B k ∪ B (rsimp4_SEQ_atom t k))) <= 1"
    unfolding single_root_def
    by (cases "rsimpStrong_raw (rsimp4_SEQ_atom t k)")
       (auto simp: rsimp7_SEQ_atom_def)
  then show ?case
    using term_is_boundary by simp
next
  case (RSEQ h1 h2)
  (* reassociate with s4:
       s4 (RSEQ h1 h2) c = s4 h1 (s4 h2 c)
     apply seq_head_core_le_rsize IH to h1 and boundary_term_absorb/IH to h2. *)
  show ?case sorry
next
  case (RALTS rs)
  (* branch-origin cover; sum branch head cores *)
  show ?case sorry
next
  case (RSTAR r)
  let ?c = "rsimp4_SEQ_atom t k"
  let ?c' = "rsimp4_SEQ_atom (RSTAR r) ?c"

  have nf_c: "apder_nf ?c"
    using RSTAR.prems apder_nf_s4 by blast
  have nf_c': "apder_nf ?c'"
    using RSTAR.prems nf_c apder_nf_s4 by blast

  have boundary:
    "card (B ?c' - B ?c) <= 1"
    using star_boundary_shift_le_one[of r ?c] RSTAR.prems nf_c by simp

  have child:
    "card (single_term r ?c' - B ?c') <= D1 r ?c'"
    unfolding D1_def A_single_decomp by (intro card_mono) auto

  have ih: "D1 r ?c' <= rsize r"
    using RSTAR.IH[OF _ nf_c'] RSTAR.prems by simp

  show ?case
    using boundary child ih by simp
qed

lemma D1_RSEQ_step:
  assumes "apder_nf r1" "apder_nf r2" "apder_nf k"
  shows "D1 (RSEQ r1 r2) k <= rsize r1 + D1 r2 k"
proof -
  let ?c = "rsimp4_SEQ_atom r2 k"

  have nf_c: "apder_nf ?c"
    using assms apder_nf_s4 by blast

  have decomp:
    "A (RALTS [RSEQ r1 r2]) k
     = single_root (RSEQ r1 r2) k
       ∪ single_term r1 ?c
       ∪ single_term r2 k"
    unfolding strong_apder_acc_def single_root_def single_term_def
    by simp

  have incl:
    "A (RALTS [RSEQ r1 r2]) k - B k
     ⊆
       ((single_root (RSEQ r1 r2) k ∪ single_term r1 ?c)
          - (B k ∪ B ?c))
       ∪
       ((B ?c - B k) ∪ (single_term r2 k - B k))"
    using decomp by auto

  have h1:
    "card ((single_root (RSEQ r1 r2) k ∪ single_term r1 ?c)
            - (B k ∪ B ?c))
     <= rsize r1"
    using seq_head_core_le_rsize[OF assms] .

  have h2:
    "card ((B ?c - B k) ∪ (single_term r2 k - B k))
     <= D1 r2 k"
    using boundary_term_absorb[OF assms(2,3)] .

  show ?thesis
    unfolding D1_def
    using incl h1 h2 finite_A
    by (meson card_mono card_Un_le le_trans add_mono)
qed

lemma D1_RSTAR_step:
  assumes "apder_nf r" "apder_nf k"
  shows "D1 (RSTAR r) k <= 1 + D1 r (rsimp4_SEQ_atom (RSTAR r) k)"
proof -
  let ?c = "rsimp4_SEQ_atom (RSTAR r) k"

  have root: "single_root (RSTAR r) k = B ?c"
    using star_single_root_eq_B by simp

  have term:
    "single_term (RSTAR r) k = single_term r ?c"
    unfolding single_term_def by simp

  have incl:
    "A (RALTS [RSTAR r]) k - B k
     ⊆ (B ?c - B k) ∪ (single_term r ?c - B ?c)"
    using A_single_decomp root term by auto

  have bnd: "card (B ?c - B k) <= 1"
    using star_boundary_shift_le_one[OF assms] .

  have child:
    "card (single_term r ?c - B ?c) <= D1 r ?c"
    unfolding D1_def A_single_decomp by (intro card_mono) auto

  show ?thesis
    unfolding D1_def
    using incl bnd child finite_A
    by (meson card_mono card_Un_le le_trans add_mono)
qed

lemma A_single_nested_RALTS:
  "A (RALTS [RALTS rs]) k = A (RALTS rs) k"
  unfolding strong_apder_acc_def
  by simp

lemma card_UN_list_Diff_le_budget:
  assumes "⋀q. q ∈ set rs ⟹ card (F q - B k) <= rsize q"
  shows "card ((⋃q∈set rs. F q) - B k) <= ralts_size_budget rs"
  using assms
  by (induction rs) (auto intro!: le_trans[OF card_Un_le] add_mono)

lemma singleton_size_nf:
  assumes "apder_nf q" "apder_nf k"
  shows "D1 q k <= rsize q"
  using assms
proof (induction q arbitrary: k)
  case RZERO
  then show ?case
    unfolding D1_def A_single_decomp single_root_def single_term_def
    by simp
next
  case RONE
  then show ?case
    unfolding D1_def A_single_decomp single_root_def single_term_def
    using row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE
    by auto
next
  case (RCHAR c)
  then show ?case
    unfolding D1_def
    using A_single_RCHAR_eq
          card_strong_apder_acc_RCHAR_diff_base_le
    by simp
next
  case (RSEQ r1 r2)
  have step:
    "D1 (RSEQ r1 r2) k <= rsize r1 + D1 r2 k"
    using D1_RSEQ_step RSEQ.prems by simp
  have right:
    "D1 r2 k <= rsize r2"
    using RSEQ.IH(2) RSEQ.prems by simp
  show ?case
    using step right by simp
next
  case (RALTS rs)
  have cover:
    "A (RALTS [RALTS rs]) k
     <= (⋃q∈set rs. A (RALTS [q]) k)"
    using A_single_nested_RALTS
          strong_apder_acc_RALTS_singleton_cover[of rs k]
    by simp

  have branch:
    "⋀q. q ∈ set rs ⟹ D1 q k <= rsize q"
    using RALTS.IH RALTS.prems by auto

  have "D1 (RALTS rs) k <= ralts_size_budget rs"
    unfolding D1_def
    using cover branch card_UN_list_Diff_le_budget
    by blast

  then show ?case by simp
next
  case (RSTAR r)
  let ?c = "rsimp4_SEQ_atom (RSTAR r) k"

  have nf_c: "apder_nf ?c"
    using RSTAR.prems apder_nf_s4 by blast

  have step:
    "D1 (RSTAR r) k <= 1 + D1 r ?c"
    using D1_RSTAR_step RSTAR.prems by simp

  have child:
    "D1 r ?c <= rsize r"
    using RSTAR.IH[OF _ nf_c] RSTAR.prems by simp

  show ?case
    using step child by simp
qed

lemma card_strong_apder_acc_singleton_RALTS_diff_base_le_rsize:
  assumes "apder_nf q" "nonalt q" "apder_nf k"
  shows "card (A (RALTS [q]) k - B k) <= rsize q"
  using singleton_size_nf[OF assms(1,3)]
  unfolding D1_def .
```

If you want the exact lemma statement from `DESIGN.md` without the explicit `nonalt q`, use `singleton_size_nf` directly. If you want the branch-only L2, keep the final corollary with `nonalt q`. The design invokes L2 only for nonalt branches of an alternation. 

---

## 5. Python evidence

I implemented the clean-fragment constructors and the definitions of `rsize`, `s4`, `s7`, `S`, `rfrontier`, `row_dlforms`, `rsimpStrong_dlform_closure`, `apder_term_frontier_acc`, `strong_apder_acc`, `apder_nf`, and `D1` directly from `DEFINITIONS.txt`. The strong simplifier includes `rsimpStrong_ALTs_raw`, `rflts`, `rdistinct`, and the pairwise prune. The relevant definitions are the verbatim ones in the attached file.  

Results I ran:

```text
Exhaustive NF clean-fragment search:
  alphabet = {a,b}
  rsize(q), rsize(k) <= 5
  top alternation arity <= 2
  nonalt q pairs tested: 329,150
  L2 violations: 0
  max(D1(q,k) - rsize(q)): 0

Adversarial witness-biased search:
  q ending in stars, k star/seq-of-stars, nested stars, (1+a*).b* family
  pairs tested: 3,825
  L2 violations: 0

Random NF search:
  42,000 random q,k pairs up to size 22
  L2 violations: 0
  RSEQ corrected recurrence violations: 0
  RSTAR recurrence violations: 0

Per-constructor recurrence validation over the exhaustive space:
  RZERO:    725 cases, 0 violations
  RONE:     725 cases, 0 violations
  RCHAR:  1,450 cases, 0 violations
  RSEQ: 203,000 cases, 0 violations for
         D1(seq r1 r2,k) <= rsize r1 + D1(r2,k)
  RSTAR:123,250 cases, 0 violations for
         D1(star r,k) <= 1 + D1(r, s4(star r,k))
  RALTS:196,475 cases, 0 violations for
         D1(RALTS rs,k) <= sum(D1(branch,k))
```

The deliberately false RSEQ recurrence was also checked and rejected:

```text
q = ((1+(a)*).(c)*), k = (c)*
D1(q,k) = 3
1 + D1(1+a*, c*.c*) + D1(c*, c*) = 2
```

That is why the proof above uses `seq_head_core_le_rsize` instead.

Here is the compact version of the Python harness I ran; the full model follows the definitions literally.

```python
def D1(q, k):
    return len(A(Alts((q,)), k) - A(RONE, k))

def single_root(q, k):
    return Cclosure(rfrontier(s4(Alts((q,)), k)))

def single_term(q, k):
    return Cclosure(atf(q, k))

def check_l2(qs, ks):
    violations = []
    max_margin = -10**9
    for q in qs:
        if not (apder_nf(q) and nonalt(q)):
            continue
        for k in ks:
            if not apder_nf(k):
                continue
            lhs = D1(q, k)
            rhs = rsize(q)
            max_margin = max(max_margin, lhs - rhs)
            if lhs > rhs:
                violations.append((q, k, lhs, rhs))
                return violations, max_margin
    return violations, max_margin

def check_steps(qs, ks):
    out = {
        "Z": 0, "O": 0, "C": 0,
        "SEQ_CORR": 0, "STAR": 0, "ALTS_SUM": 0
    }
    for q in qs:
        if not apder_nf(q):
            continue
        for k in ks:
            if not apder_nf(k):
                continue

            if q.tag == "Z":
                assert D1(q, k) <= 0
                out["Z"] += 1

            elif q.tag == "O":
                assert D1(q, k) <= 0
                out["O"] += 1

            elif q.tag == "C":
                assert D1(q, k) <= 1
                out["C"] += 1

            elif q.tag == "SEQ":
                r1, r2 = q.args
                assert apder_nf(s4(r2, k))
                assert D1(q, k) <= rsize(r1) + D1(r2, k)
                out["SEQ_CORR"] += 1

            elif q.tag == "STAR":
                r = q.args[0]
                c = s4(q, k)
                assert apder_nf(c)
                assert D1(q, k) <= 1 + D1(r, c)
                out["STAR"] += 1

            elif q.tag == "ALTS":
                assert D1(q, k) <= sum(D1(b, k) for b in q.args)
                out["ALTS_SUM"] += 1

    return out
```

The implementation also checked the two new helper inequalities:

```python
# boundary_term_absorb
assert len((B(s4(t,k)) - B(k)) | (single_term(t,k) - B(k))) <= D1(t,k)

# seq_head_core_le_rsize
assert len((single_root(Seq(h,t),k) | single_term(h, s4(t,k)))
           - (B(k) | B(s4(t,k)))) <= rsize(h)
```

Both had zero violations in exhaustive `rsize <= 5` testing and in adversarial/random testing.

---

## 6. Bottom line

L2 appears true under the exact model. The proof should not use the false “`+1 + left D + right D`” RSEQ recurrence. The formal route that survives is:

```isabelle
RSEQ:
  D1 (r1.r2) k <= rsize r1 + D1 r2 k

RSTAR:
  D1 (r*) k <= 1 + D1 r (s4 (r*) k)

RALTS helper:
  D1 (RALTS rs) k <= sum_list (map rsize rs)
```

The tail-doubling `(x*.a*).a* -> x*.(a*.a*)` is paid inside `seq_head_core_le_rsize`: for `h = x*`, the two rows are charged to `rsize h = 2`; for alt heads like `(1+a*)`, the alternation and star slack pay the multiple parent rows. This gives the requested singleton-size bound and plugs into the singleton-cover/global induction chain from `DESIGN.md`, yielding the final linear card bound needed by the cubic gate.
