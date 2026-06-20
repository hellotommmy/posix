## Result

The L1 lemma should be formalized as stated, with **no clean/nf assumptions**:

```isabelle
lemma strong_apder_acc_RALTS_singleton_cover:
  "strong_apder_acc (RALTS rs) k
     \<subseteq> (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
```

The proof route below is the provenance-tagged one requested in the prompt: tag every row in the strong alternation pipeline by its top-level source branch, prove the tag projection is faithful to the untagged pipeline, and prove that every tagged row opens inside the singleton-alt carrier for its tag. This targets the `strong_apder_acc` definition and the `rsimpStrong_dlform_closure`/`row_dlforms` opening semantics directly.  The relevant definitions are: `strong_apder_acc` as the strong closure of `rfrontier (rsimp4_SEQ_atom r k) ∪ apder_term_frontier_acc r k`; `rsimpStrong_raw` on `RALTS` via `rsimpStrong_ALTs_raw`; the `rflts`/`rdistinct`/prune pipeline; and `row_dlforms`, which opens top alternations and alternation-headed sequences.   

---

## 1. Tagged helper definitions

Use a pair `(q,t)` where `q` is the **top-level source branch** from the original `rs`, and `t` is the current row after simplification/pruning.

```isabelle
type_synonym tagged_row = "rrexp \<times> rrexp"
```

### Tag-preserving flatten

```isabelle
fun tagged_rflts :: "tagged_row list \<Rightarrow> tagged_row list" where
  "tagged_rflts [] = []"
| "tagged_rflts ((q, RZERO) # xs) =
     tagged_rflts xs"
| "tagged_rflts ((q, RALTS ys) # xs) =
     map (\<lambda>y. (q,y)) ys @ tagged_rflts xs"
| "tagged_rflts ((q, t) # xs) =
     (q,t) # tagged_rflts xs"
```

Projection lemma:

```isabelle
lemma map_snd_tagged_rflts:
  "map snd (tagged_rflts xs) = rflts (map snd xs)"
  by (induction xs rule: tagged_rflts.induct) auto
```

Origin lemma:

```isabelle
lemma fst_tagged_rflts_subset:
  "set (map fst (tagged_rflts xs)) \<subseteq> set (map fst xs)"
  by (induction xs rule: tagged_rflts.induct) auto
```

### Tag-preserving prune

The pairwise rule keeps the **later** row’s origin. This exactly matches the untagged pairwise prune, which changes only the later row. The untagged pairwise rule fires only for two rows of shape `(RALTS lrs).k` and `(RALTS rrs).k`, and then deletes branches already covered by the earlier row; otherwise it leaves the later row unchanged. 

```isabelle
definition tagged_prune_pair_raw ::
  "tagged_row \<Rightarrow> tagged_row \<Rightarrow> tagged_row" where
  "tagged_prune_pair_raw earlier later =
     (fst later, rsimpStrong_prune_pair_raw (snd earlier) (snd later))"
```

```isabelle
fun tagged_prune_against_rows_raw ::
  "tagged_row list \<Rightarrow> tagged_row \<Rightarrow> tagged_row" where
  "tagged_prune_against_rows_raw [] r = r"
| "tagged_prune_against_rows_raw (x # xs) r =
     tagged_prune_against_rows_raw xs (tagged_prune_pair_raw x r)"
```

```isabelle
fun tagged_prune_rows_acc_raw ::
  "tagged_row list \<Rightarrow> tagged_row list \<Rightarrow> tagged_row list" where
  "tagged_prune_rows_acc_raw seen [] = []"
| "tagged_prune_rows_acc_raw seen (r # rs) =
     (let r' = tagged_prune_against_rows_raw seen r
      in r' # tagged_prune_rows_acc_raw (r' # seen) rs)"
```

```isabelle
definition tagged_prune_rows_raw ::
  "tagged_row list \<Rightarrow> tagged_row list" where
  "tagged_prune_rows_raw rs =
     tagged_prune_rows_acc_raw [] rs"
```

Projection lemmas:

```isabelle
lemma map_snd_tagged_prune_pair_raw:
  "snd (tagged_prune_pair_raw e r) =
     rsimpStrong_prune_pair_raw (snd e) (snd r)"
  by (simp add: tagged_prune_pair_raw_def)
```

```isabelle
lemma map_snd_tagged_prune_against_rows_raw:
  "snd (tagged_prune_against_rows_raw seen r) =
     rsimpStrong_prune_against_rows_raw (map snd seen) (snd r)"
  by (induction seen arbitrary: r) 
     (simp_all add: tagged_prune_pair_raw_def)
```

```isabelle
lemma map_snd_tagged_prune_rows_acc_raw:
  "map snd (tagged_prune_rows_acc_raw seen rs) =
     rsimpStrong_prune_rows_acc_raw (map snd seen) (map snd rs)"
  by (induction rs arbitrary: seen) 
     (simp_all add: Let_def map_snd_tagged_prune_against_rows_raw)
```

```isabelle
lemma map_snd_tagged_prune_rows_raw:
  "map snd (tagged_prune_rows_raw rs) =
     rsimpStrong_prune_rows_raw (map snd rs)"
  by (simp add: tagged_prune_rows_raw_def
                rsimpStrong_prune_rows_raw_def
                map_snd_tagged_prune_rows_acc_raw)
```

### Tag-preserving row-dedup

`rdistinct` deduplicates by row equality, not by `(origin,row)` pair equality, so the tagged version must use a row-set accumulator.

```isabelle
fun tagged_rdistinct ::
  "tagged_row list \<Rightarrow> rrexp set \<Rightarrow> tagged_row list" where
  "tagged_rdistinct [] acc = []"
| "tagged_rdistinct ((q,t)#xs) acc =
     (if t \<in> acc
      then tagged_rdistinct xs acc
      else (q,t) # tagged_rdistinct xs ({t} \<union> acc))"
```

Projection lemma:

```isabelle
lemma map_snd_tagged_rdistinct:
  "map snd (tagged_rdistinct xs acc) =
     rdistinct (map snd xs) acc"
  by (induction xs arbitrary: acc) auto
```

### Tagged strong-alternation row list

```isabelle
definition tagged_Strong_ALTs_rows ::
  "rrexp list \<Rightarrow> tagged_row list" where
  "tagged_Strong_ALTs_rows rs =
     tagged_rdistinct
       (tagged_rflts
         (tagged_prune_rows_raw
           (tagged_rflts (map (\<lambda>q. (q, rsimpStrong_raw q)) rs))))
       {}"
```

Projection to the real untagged rows:

```isabelle
lemma map_snd_tagged_Strong_ALTs_rows:
  "map snd (tagged_Strong_ALTs_rows rs) =
     rdistinct
       (rflts
         (rsimpStrong_prune_rows_raw
           (rflts (map rsimpStrong_raw rs))))
       {}"
  unfolding tagged_Strong_ALTs_rows_def
  by (simp add:
      map_snd_tagged_rdistinct
      map_snd_tagged_rflts
      map_snd_tagged_prune_rows_raw)
```

Thus:

```isabelle
lemma rsimpStrong_raw_RALTS_tagged_rows:
  "rsimpStrong_raw (RALTS rs) =
     rsimp_ALTs (map snd (tagged_Strong_ALTs_rows rs))"
  by (simp add:
      rsimpStrong_ALTs_raw_def
      map_snd_tagged_Strong_ALTs_rows)
```

Origin soundness:

```isabelle
lemma tagged_Strong_ALTs_rows_origin:
  assumes "(q,t) \<in> set (tagged_Strong_ALTs_rows rs)"
  shows "q \<in> set rs"
  using assms
  unfolding tagged_Strong_ALTs_rows_def
  by (auto dest!: fst_tagged_rflts_subset)
```

The exact final line may need a small supporting lemma for `tagged_prune_*` and `tagged_rdistinct` preserving the set of first components:

```isabelle
lemma fst_tagged_prune_pair_raw:
  "fst (tagged_prune_pair_raw e r) = fst r"
  by (simp add: tagged_prune_pair_raw_def)

lemma fst_tagged_prune_rows_raw_subset:
  "set (map fst (tagged_prune_rows_raw xs)) \<subseteq> set (map fst xs)"
  by (induction xs rule: rev_induct)
     (auto simp: tagged_prune_rows_raw_def tagged_prune_pair_raw_def)

lemma fst_tagged_rdistinct_subset:
  "set (map fst (tagged_rdistinct xs acc)) \<subseteq> set (map fst xs)"
  by (induction xs arbitrary: acc) auto
```

---

## 2. The key row-opening preorder

The clean way to avoid dozens of ad hoc cases is to define one “opened under optional tail” preorder.

```isabelle
definition dlplug :: "rrexp option \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "dlplug T r =
     (case T of
        None \<Rightarrow> row_dlforms r
      | Some k \<Rightarrow> row_dlforms (rsimp7_SEQ_atom r k))"
```

```isabelle
definition dl_le :: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool"  (infix "\<preceq>dl" 50) where
  "x \<preceq>dl y \<longleftrightarrow> (\<forall>T. dlplug T x \<subseteq> dlplug T y)"
```

Basic facts:

```isabelle
lemma dl_le_refl [simp]: "x \<preceq>dl x"
  by (simp add: dl_le_def)

lemma dl_le_trans:
  assumes "x \<preceq>dl y" and "y \<preceq>dl z"
  shows "x \<preceq>dl z"
  using assms by (auto simp: dl_le_def)
```

### Branch deletion is opening-monotone

First, the branch-list deletion lemma:

```isabelle
lemma set_rprune_eq_against_subset:
  "set (rprune_eq_against covered rs) \<subseteq> set rs"
  by (induction rs) auto
```

Then the important local monotonicity lemma:

```isabelle
lemma dl_le_pruned_altseq:
  assumes "set xs \<subseteq> set ys"
  shows "rsimp7_SEQ_atom (rsimp_ALTs xs) k
           \<preceq>dl
         RSEQ (RALTS ys) k"
```

Proof sketch:

```isabelle
  unfolding dl_le_def dlplug_def
  apply clarify
  apply (case_tac T)
   apply simp_all
  apply (cases xs rule: list.exhaust)
   apply simp
  apply (rename_tac x xs')
  apply (cases xs')
   apply simp
   apply (use assms in auto)
  apply simp
  apply (use assms in auto)
  done
```

In practice, the `Some K` side may need explicit expansion of `rsimp7_SEQ_atom_def`, `rsimp4_SEQ_atom.simps`, `row_dlforms.simps`, and `rsimp_ALTs.simps`. The proof is finite case analysis: `xs=[]`, `xs=[x]`, or `length xs ≥ 2`; `ys=[]/[y]/≥2`; and `T=None/Some K`. The only nontrivial observation is that `row_dlforms (RSEQ (RALTS ys) k)` is exactly the union over `y ∈ set ys` of `row_dlforms (rsimp7_SEQ_atom y k)`. 

Now prove pairwise prune monotonicity:

```isabelle
lemma rsimpStrong_prune_pair_raw_dl_le:
  "rsimpStrong_prune_pair_raw earlier later \<preceq>dl later"
proof -
  show ?thesis
    unfolding rsimpStrong_prune_pair_raw_def
    apply (cases earlier; cases later; simp)
    subgoal for l1 l2 r1 r2
      apply (cases l1; cases r1; simp)
      apply (split if_splits)
       apply (rule dl_le_pruned_altseq)
       apply (rule set_rprune_eq_against_subset)
      apply simp
      done
    done
qed
```

The real script may need constructor-specific names, but the proof shape is exactly this: all non-firing cases reduce to reflexivity; the firing case uses `set_rprune_eq_against_subset` and `dl_le_pruned_altseq`. The pairwise rule is the only place where pruning can change a row, and it only deletes branches already covered by the earlier row. 

Pruning against a whole seen list:

```isabelle
lemma rsimpStrong_prune_against_rows_raw_dl_le:
  "rsimpStrong_prune_against_rows_raw seen r \<preceq>dl r"
proof (induction seen arbitrary: r)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have step:
    "rsimpStrong_prune_pair_raw x r \<preceq>dl r"
    by (rule rsimpStrong_prune_pair_raw_dl_le)
  have rest:
    "rsimpStrong_prune_against_rows_raw xs
       (rsimpStrong_prune_pair_raw x r)
       \<preceq>dl
     rsimpStrong_prune_pair_raw x r"
    by (rule Cons.IH)
  show ?case
    by (simp add: dl_le_trans[OF rest step])
qed
```

---

## 3. Source-branch invariant

For the root proof, the exact invariant needed for each tagged final row `(q,t)` is:

```isabelle
definition singleton_source_ok :: "rrexp \<Rightarrow> rrexp \<Rightarrow> bool" where
  "singleton_source_ok q t \<longleftrightarrow>
     row_dlforms t
       \<subseteq> row_dlforms
             (rsimp7_SEQ_atom (rsimpStrong_raw (RALTS [q])) RONE)
     \<and>
     (\<forall>K. row_dlforms (rsimp7_SEQ_atom t K)
          \<subseteq> row_dlforms
                (rsimp7_SEQ_atom (rsimpStrong_raw (RALTS [q])) K))"
```

The first conjunct is deliberately targeted at `... RONE`, not just `row_dlforms (rsimpStrong_raw (RALTS [q]))`. This handles the case where the parent alternation has multiple final rows but the continuation normalizes to `RONE`: parent opening uses the rows directly, while the singleton root is `rsimp7_SEQ_atom (S (RALTS [q])) RONE`.

### Initial singleton rows are source-ok

```isabelle
lemma singleton_initial_rows_source_ok:
  assumes "(q,t) \<in> set (tagged_rflts [(q, rsimpStrong_raw q)])"
  shows "singleton_source_ok q t"
```

Proof sketch:

1. From the assumption and `tagged_rflts`, obtain `t ∈ set (rflts [rsimpStrong_raw q])`.
2. Unfold:

   ```isabelle
   rsimpStrong_raw (RALTS [q])
     = rsimpStrong_ALTs_raw (rflts [rsimpStrong_raw q])
   ```
3. Prove a local singleton coverage lemma:

   ```isabelle
   lemma rsimpStrong_ALTs_raw_singleton_covers_initial:
     assumes "t \<in> set (rflts [rsimpStrong_raw q])"
     shows
       "row_dlforms t
          \<subseteq> row_dlforms
              (rsimp7_SEQ_atom
                (rsimpStrong_ALTs_raw (rflts [rsimpStrong_raw q]))
                RONE)"
       "row_dlforms (rsimp7_SEQ_atom t K)
          \<subseteq> row_dlforms
              (rsimp7_SEQ_atom
                (rsimpStrong_ALTs_raw (rflts [rsimpStrong_raw q]))
                K)"
   ```
4. The proof of that local lemma is by the same prune-pipeline reasoning:
   `rflts` only exposes existing rows, `rsimpStrong_prune_pair_raw` is `dl_le`-monotone, `rdistinct` only drops duplicate rows, and `rsimp_ALTs` opens as the union of its branches.

### Preservation through tagged transformations

Flatten preservation:

```isabelle
lemma singleton_source_ok_flatten:
  assumes "singleton_source_ok q (RALTS xs)"
    and "x \<in> set xs"
  shows "singleton_source_ok q x"
```

Proof: unfold `singleton_source_ok`; use `row_dlforms (RALTS xs)` and `row_dlforms (RSEQ (RALTS xs) K)` equations.

Prune preservation:

```isabelle
lemma singleton_source_ok_prune_pair:
  assumes "singleton_source_ok q t"
  shows "singleton_source_ok q (rsimpStrong_prune_pair_raw e t)"
proof -
  have "rsimpStrong_prune_pair_raw e t \<preceq>dl t"
    by (rule rsimpStrong_prune_pair_raw_dl_le)
  then show ?thesis
    using assms
    unfolding singleton_source_ok_def dl_le_def dlplug_def
    by auto
qed
```

Prune-scan preservation:

```isabelle
lemma singleton_source_ok_prune_against_rows:
  assumes "singleton_source_ok q t"
  shows "singleton_source_ok q
           (snd (tagged_prune_against_rows_raw seen (q,t)))"
```

This follows by induction on `seen`, using `singleton_source_ok_prune_pair`.

Whole pipeline invariant:

```isabelle
lemma tagged_Strong_ALTs_rows_source_ok:
  assumes "(q,t) \<in> set (tagged_Strong_ALTs_rows rs)"
  shows "q \<in> set rs"
    and "singleton_source_ok q t"
```

Proof skeleton:

```isabelle
proof -
  have origin: "q \<in> set rs"
    using assms by (rule tagged_Strong_ALTs_rows_origin)

  have init:
    "\<forall>(q,t)\<in>set (tagged_rflts
        (map (\<lambda>q. (q, rsimpStrong_raw q)) rs)).
        singleton_source_ok q t"
    using singleton_initial_rows_source_ok by auto

  have after_prune:
    "\<forall>(q,t)\<in>set
       (tagged_prune_rows_raw
         (tagged_rflts (map (\<lambda>q. (q, rsimpStrong_raw q)) rs))).
       singleton_source_ok q t"
    using init
    by (induction
          "tagged_rflts (map (\<lambda>q. (q, rsimpStrong_raw q)) rs)"
          rule: tagged_prune_rows_acc_raw.induct)
       (auto simp: tagged_prune_rows_raw_def
             intro: singleton_source_ok_prune_pair)

  have after_final_rflts:
    "\<forall>(q,t)\<in>set
       (tagged_rflts
         (tagged_prune_rows_raw
           (tagged_rflts (map (\<lambda>q. (q, rsimpStrong_raw q)) rs)))).
       singleton_source_ok q t"
    using after_prune
    by (auto intro: singleton_source_ok_flatten)

  show "singleton_source_ok q t"
    using assms after_final_rflts
    unfolding tagged_Strong_ALTs_rows_def
    by (induction
          "tagged_rflts
            (tagged_prune_rows_raw
              (tagged_rflts (map (\<lambda>q. (q, rsimpStrong_raw q)) rs)))"
          arbitrary: "{}")
       auto

  show "q \<in> set rs" by fact
qed
```

The exact induction over `tagged_rdistinct` is usually easiest as a separate lemma:

```isabelle
lemma tagged_rdistinct_preserves_source_ok:
  assumes "\<forall>(q,t)\<in>set xs. singleton_source_ok q t"
  shows "\<forall>(q,t)\<in>set (tagged_rdistinct xs acc). singleton_source_ok q t"
  using assms by (induction xs arbitrary: acc) auto
```

---

## 4. Root-cover lemma

First isolate the root part of `strong_apder_acc`.

```isabelle
lemma strong_apder_acc_RALTS_root_singleton_cover:
  "rsimpStrong_dlform_closure
     (rfrontier (rsimp4_SEQ_atom (RALTS rs) k))
   \<subseteq>
   (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
```

Proof by cases on `k`.

### Case `k = RZERO`

```isabelle
case RZERO
then show ?thesis
  by (simp add: rsimpStrong_dlform_closure_def)
```

Because `rsimp4_SEQ_atom (RALTS rs) RZERO = RZERO`, and `rfrontier RZERO = {}`.

### Case `k = RONE`

```isabelle
case RONE
then show ?thesis
  unfolding strong_apder_acc_def rsimpStrong_dlform_closure_def
  by auto
```

Here:

```isabelle
rsimp4_SEQ_atom (RALTS rs) RONE = RALTS rs
rfrontier (RALTS rs) = rfrontiers rs
```

Every `p ∈ rfrontier q` is also in the singleton carrier for `RALTS [q]`, since:

```isabelle
apder_term_frontier_acc (RALTS [q]) RONE = apder_term_frontier_acc q RONE
rfrontier (rsimp4_SEQ_atom (RALTS [q]) RONE) = rfrontier q
```

### Case `k ≠ RZERO` and `k ≠ RONE`

Let:

```isabelle
let ?trs = tagged_Strong_ALTs_rows rs
let ?rows = map snd ?trs
let ?K = rsimpStrong_raw k
```

Then:

```isabelle
rsimpStrong_raw (RSEQ (RALTS rs) k)
  = rsimp7_SEQ_atom
      (rsimp_ALTs ?rows)
      ?K
```

by `rsimpStrong_raw_RALTS_tagged_rows`.

Now split on `?rows`.

#### Empty rows

`rsimp_ALTs [] = RZERO`, so the opened set is empty.

#### Singleton row

If `?trs = [(q,t)]`, then by `tagged_Strong_ALTs_rows_source_ok`:

```isabelle
singleton_source_ok q t
```

and `q ∈ set rs`. The parent root contribution is:

```isabelle
row_dlforms (rsimp7_SEQ_atom t ?K)
```

which is included in:

```isabelle
row_dlforms
  (rsimp7_SEQ_atom (rsimpStrong_raw (RALTS [q])) ?K)
```

by the second conjunct of `singleton_source_ok`. Since `k ≠ RZERO` and `k ≠ RONE`,

```isabelle
rsimp4_SEQ_atom (RALTS [q]) k = RSEQ (RALTS [q]) k
```

and therefore the right side is exactly the strong opening of the singleton root row, hence included in `strong_apder_acc (RALTS [q]) k`.

#### Multiple rows

If `?rows = t1 # t2 # rest`, then `rsimp_ALTs ?rows = RALTS ?rows`. Split on `?K`.

If `?K = RZERO`, the parent root opens to `{}`.

If `?K = RONE`, parent opening is:

```isabelle
row_dlforms (RALTS ?rows)
```

so each opened row comes from some tagged `(q,t) ∈ set ?trs` and some element of `row_dlforms t`. The first conjunct of `singleton_source_ok` gives:

```isabelle
row_dlforms t
  \<subseteq>
row_dlforms
  (rsimp7_SEQ_atom (rsimpStrong_raw (RALTS [q])) RONE)
```

which is again the singleton root opening because `?K = rsimpStrong_raw k = RONE`.

If `?K ≠ RZERO` and `?K ≠ RONE`, then:

```isabelle
row_dlforms (RSEQ (RALTS ?rows) ?K)
 =
(\<Union>t \<in> set ?rows. row_dlforms (rsimp7_SEQ_atom t ?K))
```

and each tagged `(q,t)` is handled by the second conjunct of `singleton_source_ok`.

This proves the root-cover lemma.

---

## 5. Term-frontier cover lemma

The accumulator part is direct from the `RALTS` equation for `apder_term_frontier_acc`: for `RALTS rs`, it is the union over branches. 

```isabelle
lemma strong_apder_acc_RALTS_terms_singleton_cover:
  "rsimpStrong_dlform_closure
     (apder_term_frontier_acc (RALTS rs) k)
   \<subseteq>
   (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
proof
  fix x
  assume "x \<in> rsimpStrong_dlform_closure
              (apder_term_frontier_acc (RALTS rs) k)"
  then obtain q p where
    q: "q \<in> set rs"
    and p: "p \<in> apder_term_frontier_acc q k"
    and x: "x \<in> row_dlforms (rsimpStrong_raw p)"
    unfolding rsimpStrong_dlform_closure_def
    by auto

  have "p \<in>
      rfrontier (rsimp4_SEQ_atom (RALTS [q]) k)
      \<union> apder_term_frontier_acc (RALTS [q]) k"
    using p by simp

  then have "x \<in> strong_apder_acc (RALTS [q]) k"
    using x
    unfolding strong_apder_acc_def rsimpStrong_dlform_closure_def
    by auto

  then show "x \<in> (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    using q by auto
qed
```

---

## 6. Final L1 proof skeleton

```isabelle
lemma strong_apder_acc_RALTS_singleton_cover:
  "strong_apder_acc (RALTS rs) k
     \<subseteq> (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
proof -
  have root:
    "rsimpStrong_dlform_closure
       (rfrontier (rsimp4_SEQ_atom (RALTS rs) k))
     \<subseteq>
     (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    by (rule strong_apder_acc_RALTS_root_singleton_cover)

  have terms:
    "rsimpStrong_dlform_closure
       (apder_term_frontier_acc (RALTS rs) k)
     \<subseteq>
     (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    by (rule strong_apder_acc_RALTS_terms_singleton_cover)

  show ?thesis
    unfolding strong_apder_acc_def rsimpStrong_dlform_closure_def
    using root terms
    by auto
qed
```

This is exactly the L1 singleton cover from the live design, which is intended to replace the false child-carrier cover and feed the `RALTS` cardinality step via singleton-size L2.  The surrounding lemma chain in `DESIGN.md` then uses L1+L2 to prove the `RALTS` step and ultimately `card_apder_strong_dlfrontier_le`. 

---

## Python evidence

I implemented the tuple model of the clean-fragment constructors and the functions `s4`, `s7`, `S`, `rsimpStrong_ALTs_raw`, `rflts`, `rdistinct`, the prune scan, `row_dlforms`, `apder_term_frontier_acc`, and `strong_A`.

The checked predicate was stronger than L1:

```python
def provenance_ok(rs, k):
    pairs = tagged_A_ALTS(rs, k)
    lhs = A(ALT(tuple(rs)), k)

    # 1. Tagged model exactly accounts for parent carrier rows.
    assert {y for q, y in pairs} == lhs

    # 2. Every parent row has a branch origin q whose singleton carrier contains it.
    for q, y in pairs:
        assert q != "NO_ORIGIN"
        assert y in A(ALT((q,)), k)

    # 3. Therefore the plain L1 subset holds.
    rhs = set()
    for q in set(rs):
        rhs |= A(ALT((q,)), k)
    assert lhs <= rhs
```

Results from the run:

| Sweep                                                                                                                                                    | Instances | Parent rows checked | Orphans |
| -------------------------------------------------------------------------------------------------------------------------------------------------------- | --------: | ------------------: | ------: |
| Exhaustive clean `apder_nf`, all `RALTS` terms size ≤ 5 over `{a,b}` × all continuations size ≤ 5                                                        |   289,923 |             828,812 |       0 |
| Broader clean `RALTS` terms size ≤ 6 × continuations size ≤ 4                                                                                            |   323,032 |             938,628 |       0 |
| Named witness/adversarial families: `x_i*.a*` under `a*`, shared star-tail branches, Pro singleton `(1+a*).b*`, collapsing-tail cases, `S k = 0/1` cases |        28 |                 337 |       0 |
| Arbitrary random branch lists, not restricted to clean/nf                                                                                                |    20,000 |              53,787 |       0 |
| Pairwise prune monotonicity helper, exhaustive size ≤ 4 triples                                                                                          | 3,307,949 |                   — |       0 |
| Pairwise prune monotonicity helper, random triples                                                                                                       | 9,000,000 |                   — |       0 |

Full runnable script: [l1_singleton_cover_model.py](sandbox:/mnt/data/l1_singleton_cover_model.py)

Uploaded source files used: DEFINITIONS , DESIGN , and the L1 prompt .
