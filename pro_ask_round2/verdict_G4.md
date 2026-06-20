I treated L1 and L2 as assumed, exactly as requested, and assembled the remaining chain. The key design is the singleton-origin cover plus singleton-size budget: `A(RALTS rs,k)` is covered by singleton alternation carriers, and each singleton carrier pays from its branch’s own `rsize`. The uploaded design defines the intended notation `A`, `B`, `U`, and `D`, and states the target lemma chain; the definitions file gives the carrier and green lemmas used below.   

## 0. Small local definitions

```isabelle
fun ralts_size_budget :: "rrexp list \<Rightarrow> nat" where
  "ralts_size_budget [] = 0"
| "ralts_size_budget (q # qs) = rsize q + ralts_size_budget qs"

definition D :: "rrexp \<Rightarrow> rrexp \<Rightarrow> nat" where
  "D r k = card (strong_apder_acc r k - strong_apder_acc RONE k)"

definition rho_RSTAR :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "rho_RSTAR r k =
     row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))"
```

Useful local simp lemma:

```isabelle
lemma ralts_size_budget_eq_sum_list:
  "ralts_size_budget rs = sum_list (map rsize rs)"
  by (induction rs) simp_all
```

This matches `rsize (RALTS rs) = Suc (sum_list (map rsize rs))` from `rsize`. 

---

## 1. Assumed L1 and L2

These are the two externally proved crux lemmas.

```isabelle
lemma strong_apder_acc_RALTS_singleton_cover:  (* L1, assumed *)
  "strong_apder_acc (RALTS rs) k \<subseteq>
     (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
  sorry

lemma card_strong_apder_acc_singleton_RALTS_diff_base_le_rsize:  (* L2, assumed *)
  assumes "apder_nf q" "apder_nf k"
  shows
    "card (strong_apder_acc (RALTS [q]) k - strong_apder_acc RONE k)
      \<le> rsize q"
  sorry
```

The definition of `apder_nf` gives the needed RALTS branch fact:
`apder_nf (RALTS rs)` implies `q ∈ set rs ⟹ apder_nf q`. 

---

## 2. RALTS budget step

### Statement

```isabelle
lemma card_strong_apder_acc_RALTS_diff_base_le_size_budget:
  assumes nfs: "list_all apder_nf rs"
      and nfk: "apder_nf k"
  shows
    "card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
      \<le> ralts_size_budget rs"
```

### Required set-algebra and finite side lemmas

The exact set identity requested:

```isabelle
lemma Diff_UNION_indexed:
  "((\<Union>i \<in> I. X i) - C) = (\<Union>i \<in> I. X i - C)"
  by auto
```

Finite side condition needed for `card_mono` and `card_UN_le`:

```isabelle
lemma finite_strong_apder_acc [simp]:
  "finite (strong_apder_acc r k)"
  sorry
```

This should be mechanical from `strong_apder_acc_def`, `rsimpStrong_dlform_closure_def`, `rfrontier`, `row_dlforms`, and `apder_term_frontier_acc`, all of which are finite syntax-recursive set constructors in the clean fragment. The definitions of `strong_apder_acc`, `rsimpStrong_dlform_closure`, and `row_dlforms` are exactly as used here.  

Budget comparison from set-indexed sum to list budget:

```isabelle
lemma sum_rsize_set_le_ralts_size_budget:
  "(\<Sum>q \<in> set rs. rsize q) \<le> ralts_size_budget rs"
  by (induction rs) (auto simp: ralts_size_budget_eq_sum_list)
```

This handles duplicate branches correctly: the set-sum counts each syntactic branch value once, while the list budget counts duplicates.

### Isar skeleton

```isabelle
lemma card_strong_apder_acc_RALTS_diff_base_le_size_budget:
  assumes nfs: "list_all apder_nf rs"
      and nfk: "apder_nf k"
  shows
    "card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
      \<le> ralts_size_budget rs"
proof -
  let ?B = "strong_apder_acc RONE k"
  let ?U = "(\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"

  have cover:
    "strong_apder_acc (RALTS rs) k \<subseteq> ?U"
    using strong_apder_acc_RALTS_singleton_cover .

  have cover_diff:
    "strong_apder_acc (RALTS rs) k - ?B \<subseteq> ?U - ?B"
    using cover by auto

  have finite_U_diff: "finite (?U - ?B)"
    by simp

  have mono:
    "card (strong_apder_acc (RALTS rs) k - ?B) \<le> card (?U - ?B)"
    by (rule card_mono[OF finite_U_diff cover_diff])

  have diff_UN:
    "?U - ?B =
      (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k - ?B)"
    by auto

  have card_UN:
    "card (?U - ?B)
      \<le> (\<Sum>q \<in> set rs.
            card (strong_apder_acc (RALTS [q]) k - ?B))"
    unfolding diff_UN
    by (rule card_UN_le) simp_all

  have per_branch:
    "\<And>q. q \<in> set rs \<Longrightarrow>
      card (strong_apder_acc (RALTS [q]) k - ?B) \<le> rsize q"
    using nfs nfk
    by (auto simp: list_all_iff
        intro: card_strong_apder_acc_singleton_RALTS_diff_base_le_rsize)

  have sum_bound:
    "(\<Sum>q \<in> set rs.
        card (strong_apder_acc (RALTS [q]) k - ?B))
      \<le> (\<Sum>q \<in> set rs. rsize q)"
    by (intro sum_mono per_branch)

  have set_to_list:
    "(\<Sum>q \<in> set rs. rsize q) \<le> ralts_size_budget rs"
    by (rule sum_rsize_set_le_ralts_size_budget)

  show ?thesis
    using mono card_UN sum_bound set_to_list by linarith
qed
```

Green/non-green facts used here: L1, L2, standard `card_UN_le`, standard `card_mono`, and the non-green but mechanical finite and sum/list helper lemmas. The RALTS step is exactly the design’s chain:
`D(RALTS rs,k) ≤ card((⋃q. A(RALTS[q],k)) - B(k)) ≤ Σq card(A(RALTS[q],k)-B(k)) ≤ Σq rsize q`.  

---

## 3. RSTAR root-row helper

This is the only substantive new helper outside L1/L2 in the induction.

### Precise statement

```isabelle
lemma card_rho_RSTAR_diff_base_le_1:
  assumes nfr: "apder_nf r"
      and nfk: "apder_nf k"
  shows
    "card (rho_RSTAR r k - strong_apder_acc RONE k) \<le> 1"
```

Expanded, this is exactly:

```isabelle
lemma card_RSTAR_root_row_diff_base_le_1:
  assumes "apder_nf r" "apder_nf k"
  shows
    "card
      (row_dlforms
        (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))
       - strong_apder_acc RONE k)
     \<le> 1"
```

### Supporting equality needed in the RSTAR telescope

```isabelle
lemma strong_apder_acc_RONE_s4_RSTAR_eq_rho:
  "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) = rho_RSTAR r k"
  unfolding rho_RSTAR_def strong_apder_acc_def rsimpStrong_dlform_closure_def
  by (cases k) auto
```

Reason: `rsimp4_SEQ_atom (RSTAR r) k` is either `RZERO`, `RSTAR r`, or `RSEQ (RSTAR r) k`, never a top-level `RALTS`; hence the RONE carrier at that continuation is the singleton strong-opened root row.

The helper proof itself should case-split on `rsimpStrong_raw r` and `k`. If `rsimpStrong_raw (RSTAR r)` collapses to `RONE`, the root row is already inside `strong_apder_acc RONE k`, using the green continuation-row inclusion:

```isabelle
row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE
```

If it remains a star, `rsimp7_SEQ_atom` can only produce one top root row after the possible `a*.a*` collapse, so the root-row difference has cardinality at most one. The relevant green definitions are `rsimp4_SEQ_atom`, `rsimp7_SEQ_atom`, `rsimpStrong_raw`, and `row_dlforms`.    

---

## 4. Global excess bound

### Statement

```isabelle
lemma card_strong_apder_acc_diff_base_le_rsize:
  assumes clean: "apder_clean r"
      and nfk: "apder_nf k"
  shows
    "card (strong_apder_acc r k - strong_apder_acc RONE k) \<le> rsize r"
```

### Additional mechanical side lemmas

These are not listed as green facts in `DEFINITIONS.txt`, but they are needed for smooth transcription.

```isabelle
lemma apder_nf_rsimp4_SEQ_atom:
  assumes "apder_nf r" "apder_nf k"
  shows "apder_nf (rsimp4_SEQ_atom r k)"
  sorry

lemma apder_cleanD_RSEQ:
  assumes "apder_clean (RSEQ r1 r2)"
  shows "apder_clean r1" "apder_clean r2" "apder_nf r1" "apder_nf r2"
  using assms by (auto simp: apder_clean_def)

lemma apder_cleanD_RSTAR:
  assumes "apder_clean (RSTAR r)"
  shows "apder_clean r" "apder_nf r"
  using assms by (auto simp: apder_clean_def)

lemma apder_cleanD_RALTS:
  assumes "apder_clean (RALTS rs)"
  shows "list_all apder_nf rs"
  using assms by (auto simp: apder_clean_def list_all_iff)
```

`apder_clean` is defined as `legacy_rrexp ∧ rntimes_free ∧ apder_nf ∧ apder_zero_budget_trivial`, so these destructors should mostly be `simp`/`auto`.  

### Isar skeleton

```isabelle
lemma card_strong_apder_acc_diff_base_le_rsize:
  assumes clean: "apder_clean r"
      and nfk: "apder_nf k"
  shows
    "card (strong_apder_acc r k - strong_apder_acc RONE k) \<le> rsize r"
  using clean nfk
proof (induction r arbitrary: k)
  case RZERO
  show ?case
    by (simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

next
  case RONE
  show ?case
    by (simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

next
  case (RCHAR c)
  show ?case
    using card_strong_apder_acc_RCHAR_diff_base_le[OF RCHAR.prems(2)]
    by simp

next
  case (RSEQ r1 r2)
  let ?k1 = "rsimp4_SEQ_atom r2 k"
  let ?A1 = "strong_apder_acc r1 ?k1"
  let ?A2 = "strong_apder_acc r2 k"
  let ?B  = "strong_apder_acc RONE k"
  let ?M  = "strong_apder_acc RONE ?k1"

  have clean1: "apder_clean r1"
    using RSEQ.prems by (auto simp: apder_clean_def)
  have clean2: "apder_clean r2"
    using RSEQ.prems by (auto simp: apder_clean_def)
  have nf2: "apder_nf r2"
    using RSEQ.prems by (auto simp: apder_clean_def)
  have nf_k1: "apder_nf ?k1"
    using nf2 RSEQ.prems
    by (intro apder_nf_rsimp4_SEQ_atom) auto

  have IH1: "card (?A1 - ?M) \<le> rsize r1"
    using RSEQ.IH(1)[OF clean1 nf_k1] .
  have IH2: "card (?A2 - ?B) \<le> rsize r2"
    using RSEQ.IH(2)[OF clean2 RSEQ.prems(2)] .

  have split:
    "strong_apder_acc (RSEQ r1 r2) k \<subseteq> ?A1 \<union> ?A2"
    using strong_apder_acc_RSEQ_subset .

  have diff_sub:
    "strong_apder_acc (RSEQ r1 r2) k - ?B \<subseteq> (?A1 \<union> ?A2) - ?B"
    using split by auto

  have mono:
    "card (strong_apder_acc (RSEQ r1 r2) k - ?B)
      \<le> card ((?A1 \<union> ?A2) - ?B)"
    by (rule card_mono) simp_all

  have M_subset_A2: "?M \<subseteq> ?A2"
    using strong_apder_acc_RONE_sigma_subset[of r2 k] by simp

  have telescope:
    "card ((?A1 \<union> ?A2) - ?B)
      \<le> card (?A1 - ?M) + card (?A2 - ?B)"
    by (rule card_Un_Diff_telescope_le[OF _ _ M_subset_A2]) simp_all

  show ?case
    using mono telescope IH1 IH2 by simp

next
  case (RSTAR r)
  let ?ks = "rsimp4_SEQ_atom (RSTAR r) k"
  let ?Root = "rho_RSTAR r k"
  let ?Ar = "strong_apder_acc r ?ks"
  let ?B = "strong_apder_acc RONE k"
  let ?Bs = "strong_apder_acc RONE ?ks"

  have clean_r: "apder_clean r"
    using RSTAR.prems by (auto simp: apder_clean_def)
  have nf_r: "apder_nf r"
    using RSTAR.prems by (auto simp: apder_clean_def)
  have nf_ks: "apder_nf ?ks"
    using nf_r RSTAR.prems
    by (intro apder_nf_rsimp4_SEQ_atom) auto

  have IH: "card (?Ar - ?Bs) \<le> rsize r"
    using RSTAR.IH[OF clean_r nf_ks] .

  have root_eq: "?Bs = ?Root"
    using strong_apder_acc_RONE_s4_RSTAR_eq_rho[of r k]
    by simp

  have root_bound: "card (?Root - ?B) \<le> 1"
    using card_rho_RSTAR_diff_base_le_1[OF nf_r RSTAR.prems(2)]
    by simp

  have split:
    "strong_apder_acc (RSTAR r) k \<subseteq> ?Root \<union> ?Ar"
    using strong_apder_acc_RSTAR_subset[of r k]
    unfolding rho_RSTAR_def by simp

  have diff_sub:
    "strong_apder_acc (RSTAR r) k - ?B \<subseteq> (?Ar \<union> ?Root) - ?B"
    using split by auto

  have mono:
    "card (strong_apder_acc (RSTAR r) k - ?B)
      \<le> card ((?Ar \<union> ?Root) - ?B)"
    by (rule card_mono) simp_all

  have telescope:
    "card ((?Ar \<union> ?Root) - ?B)
      \<le> card (?Ar - ?Root) + card (?Root - ?B)"
    by (rule card_Un_Diff_telescope_le[of ?Ar ?Root ?Root ?B]) simp_all

  have recur:
    "card (?Ar - ?Root) \<le> rsize r"
    using IH root_eq by simp

  show ?case
    using mono telescope recur root_bound by simp

next
  case (RALTS rs)
  have nfs: "list_all apder_nf rs"
    using RALTS.prems by (auto simp: apder_clean_def list_all_iff)

  have budget:
    "card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
      \<le> ralts_size_budget rs"
    using card_strong_apder_acc_RALTS_diff_base_le_size_budget[OF nfs RALTS.prems(2)] .

  show ?case
    using budget
    by (simp add: ralts_size_budget_eq_sum_list)

next
  case (RNTIMES r n)
  then show ?case
    by (simp add: apder_clean_def)

next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
    by (simp add: apder_clean_def)

next
  case (RHALF r cs rep)
  then show ?case
    by (simp add: apder_clean_def)

next
  case (RRESIDUE cs rep)
  then show ?case
    by (simp add: apder_clean_def)
qed
```

Green facts used by constructor: `card_strong_apder_acc_RCHAR_diff_base_le` for `RCHAR`; `strong_apder_acc_RSEQ_subset`, `strong_apder_acc_RONE_sigma_subset`, and `card_Un_Diff_telescope_le` for `RSEQ`; `strong_apder_acc_RSTAR_subset` and `card_Un_Diff_telescope_le` plus the new root helper for `RSTAR`; and the L1/L2-derived RALTS budget lemma for `RALTS`. These exact green lemma names appear in `DEFINITIONS.txt`. 

---

## 5. Final frontier cardinality bound

### Statement

```isabelle
lemma card_apder_strong_dlfrontier_le:
  assumes clean: "apder_clean r"
  shows "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
```

### Isar skeleton

```isabelle
lemma card_apder_strong_dlfrontier_le:
  assumes clean: "apder_clean r"
  shows "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
proof -
  let ?U = "apder_strong_dlfrontier r"
  let ?A = "strong_apder_acc r RONE"

  have nfr: "apder_nf r"
    using clean by (simp add: apder_clean_def)

  have bridge: "?U \<subseteq> ?A"
    using apder_strong_dlfrontier_subset_strong_apder_acc_RONE[OF nfr] .

  have finA: "finite ?A"
    by simp

  have card_U_A: "card ?U \<le> card ?A"
    by (rule card_mono[OF finA bridge])

  have lift:
    "card ?A \<le> Suc (card (?A - {RONE}))"
    using card_le_Suc_card_Diff_singleton[OF finA] .

  have diff_bound:
    "card (?A - {RONE}) \<le> rsize r"
  proof -
    have
      "card (?A - strong_apder_acc RONE RONE) \<le> rsize r"
      using card_strong_apder_acc_diff_base_le_rsize[OF clean, of RONE]
      by simp
    thus ?thesis
      by simp
  qed

  show ?thesis
    using card_U_A lift diff_bound by linarith
qed
```

This uses the green bridge `apder_strong_dlfrontier_subset_strong_apder_acc_RONE`, the simp lemma `strong_apder_acc_RONE_RONE`, and the green absolute-lift lemma `card_le_Suc_card_Diff_singleton`. 

---

## 6. Gate corollary

### Statement

```isabelle
corollary cubic_gate_unconditional:
  assumes clean: "apder_clean r"
  shows
    "rsize_set
       (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
      \<le> 2 * (rsize r + 3) ^ 3"
```

### Proof

```isabelle
corollary cubic_gate_unconditional:
  assumes clean: "apder_clean r"
  shows
    "rsize_set
       (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
      \<le> 2 * (rsize r + 3) ^ 3"
proof -
  have cardU:
    "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
    using card_apder_strong_dlfrontier_le[OF clean] .

  show ?thesis
    using actual_gate_from_direct_universe_rowlevel[OF clean cardU] .
qed
```

`actual_gate_from_direct_universe_rowlevel` is the green black-box gate lemma consuming exactly `apder_clean r` plus the frontier cardinality bound. 

---

## What remains to prove outside the green facts

Substantive:

1. `strong_apder_acc_RALTS_singleton_cover` — L1, assumed here.
2. `card_strong_apder_acc_singleton_RALTS_diff_base_le_rsize` — L2, assumed here.
3. `card_rho_RSTAR_diff_base_le_1` — the RSTAR root-row bound:

   ```isabelle
   assumes "apder_nf r" "apder_nf k"
   shows "card
     (row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))
      - strong_apder_acc RONE k) \<le> 1"
   ```

Mechanical but still needed if not already available:

```isabelle
lemma finite_strong_apder_acc [simp]:
  "finite (strong_apder_acc r k)"

lemma finite_row_dlforms [simp]:
  "finite (row_dlforms r)"

lemma apder_nf_rsimp4_SEQ_atom:
  assumes "apder_nf r" "apder_nf k"
  shows "apder_nf (rsimp4_SEQ_atom r k)"

lemma Diff_UNION_indexed:
  "((\<Union>i \<in> I. X i) - C) = (\<Union>i \<in> I. X i - C)"

lemma sum_rsize_set_le_ralts_size_budget:
  "(\<Sum>q \<in> set rs. rsize q) \<le> ralts_size_budget rs"

lemma strong_apder_acc_RONE_s4_RSTAR_eq_rho:
  "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) =
     rho_RSTAR r k"
```

The design file also identifies L1/L2 as the remaining formalization work, with L2 as the crux. 

---

## Python validation

I ran an independent Python model of the clean fragment definitions and the carrier/universe functions. The run checked the global target

```text
card(apder_strong_dlfrontier r) <= rsize r + 1
```

and also checked the stronger excess bound

```text
D(r, RONE) <= rsize r
```

### Exhaustive clean NF run

Alphabet: `{a,b}`
Exhaustive clean NF through `rsize <= 9`.

```text
size 1:       4 terms
size 2:       6 terms
size 3:      22 terms
size 4:     106 terms
size 5:     532 terms
size 6:   2,814 terms
size 7:  15,500 terms
size 8:  87,872 terms
size 9: 509,506 terms
total:  616,362 terms

violations of |U(r)| <= rsize(r)+1: 0
violations of D(r,RONE) <= rsize(r): 0

max observed |U(r)|: 6 at size 9
max observed D(r,RONE): 5 at size 9
```

### Named witness checks

For the known singleton-size witness:

```text
q = (1 + a*) . b*
k = b*

apder_clean q: true
rsize q: 7
D(q,k): 1
D(RALTS[q],k): 3
|U(q)|: 2
```

For the broken `+1` RALTS family with `n` branches `x_i*.a*` under `k = a*`:

```text
n=1:  parent D=2,   child-sum+1=2,   singleton-sum=2,   L1=true
n=2:  parent D=4,   child-sum+1=3,   singleton-sum=4,   L1=true
n=3:  parent D=6,   child-sum+1=4,   singleton-sum=6,   L1=true
n=5:  parent D=10,  child-sum+1=6,   singleton-sum=10,  L1=true
n=10: parent D=20,  child-sum+1=11,  singleton-sum=20,  L1=true
n=20: parent D=40,  child-sum+1=21,  singleton-sum=40,  L1=true
n=50: parent D=100, child-sum+1=51,  singleton-sum=100, L1=true
```

### Adversarial family sweep

```text
wide_alt n<=80:        0 violations; max |U|=81,  size=401, D=81
nested_seq n<=45:      0 violations; max |U|=92,  size=226, D=91
star_alt n<=120:       0 violations; max |U|=1
chain_alt_star n<=50:  0 violations; max |U|=101, size=351, D=101
```

Harness file: [cubic_bound_check_harness.py](sandbox:/mnt/data/cubic_bound_check_harness.py). It defaults to `--N 8` for a quick run; use `--N 9` to reproduce the exhaustive size-9 run.
