
theory FBound
  imports "BlexerSimp" "ClosedFormsBounds"
begin

fun distinctBy :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a list"
  where
  "distinctBy [] f acc = []"
| "distinctBy (x#xs) f acc = 
     (if (f x) \<in> acc then distinctBy xs f acc 
      else x # (distinctBy xs f ({f x} \<union> acc)))"

(* BACKREF-MIGRATION-COMPLETED (bounds-only skeleton, ADMIN APPROVAL APPROVED):
   rerase is the bridge from arexp to the proof-only rrexp skeleton used by the
   original bounds and closed-form chain. *)
fun rerase :: "arexp \<Rightarrow> rrexp"
where
  "rerase AZERO = RZERO"
| "rerase (AONE _) = RONE"
| "rerase (ACHAR _ c) = RCHAR c"
| "rerase (AALTs bs rs) = RALTS (map rerase rs)"
| "rerase (ASEQ _ r1 r2) = RSEQ (rerase r1) (rerase r2)"
| "rerase (ASTAR _ r) = RSTAR (rerase r)"
| "rerase (ANTIMES _ r n) = RNTIMES (rerase r) n"
| "rerase (ABACKREF4 _ r1 r2 r3 r4 cs) =
    RBACKREF4 (rerase r1) (rerase r2) (rerase r3) (rerase r4) cs"
| "rerase (AHALF _ r cs rep) = RHALF (rerase r) cs rep"
| "rerase (ARESIDUE _ cs rep) = RRESIDUE cs rep"



lemma eq1s_rerase:
  assumes "\<forall>r \<in> set xs. \<forall>y. (r ~1 y) \<longleftrightarrow> rerase r = rerase y"
  shows "eq1s xs ys \<longleftrightarrow> map rerase xs = map rerase ys"
  using assms
  apply(induct xs arbitrary: ys)
   apply(case_tac ys)
    apply(auto)[2]
  apply(case_tac ys)
   apply(auto)
  done

lemma eq1_rerase:
  shows "x ~1 y \<longleftrightarrow> (rerase x) = (rerase y)"
proof (induction x arbitrary: y)
  case (AALTs bs rs)
  then show ?case
    by (cases y) (auto simp add: eq1s_rerase)
qed (case_tac y; auto)+


lemma distinctBy_distinctWith:
  shows "distinctBy xs f (f ` acc) = distinctWith xs (\<lambda>x y. f x = f y) acc"
  apply(induct xs arbitrary: acc)
  apply(auto)
  by (metis image_insert)

lemma distinctBy_distinctWith2:
  shows "distinctBy xs rerase {} = distinctWith xs eq1 {}"
  apply(subst distinctBy_distinctWith[of _ _ "{}", simplified])
  using eq1_rerase by presburger
  
lemma asize_rsize:
  shows "rsize (rerase r) = asize r"
  apply(induct r rule: rerase.induct)
  apply(auto)
  apply (metis (mono_tags, lifting) comp_apply map_eq_conv)
  done

lemma rerase_fuse:
  shows "rerase (fuse bs r) = rerase r"
  apply(induct r)
       apply simp+
  done

lemma rerase_bsimp_ASEQ:
  shows "rerase (bsimp_ASEQ x1 a1 a2) = rsimp_SEQ (rerase a1) (rerase a2)"
  by (cases a1; cases a2; simp add: bsimp_ASEQ_def rerase_fuse)

lemma rerase_bsimp_AALTs:
  shows "rerase (bsimp_AALTs bs rs) = rsimp_ALTs (map rerase rs)"
  apply(induct bs rs rule: bsimp_AALTs.induct)
  apply(auto simp add: rerase_fuse)
  done

fun anonalt :: "arexp \<Rightarrow> bool"
  where
  "anonalt (AALTs bs2 rs) = False"
| "anonalt r = True"


definition agood :: "arexp \<Rightarrow> bool" where
  "agood r \<equiv> good (rerase r)"


fun anonnested :: "arexp \<Rightarrow> bool"
  where
  "anonnested (AALTs bs2 []) = True"
| "anonnested (AALTs bs2 ((AALTs bs1 rs1) # rs2)) = False"
| "anonnested (AALTs bs2 (r # rs2)) = anonnested (AALTs bs2 rs2)"
| "anonnested r = True"


lemma asize0:
  shows "0 < asize r"
  apply(induct  r)
  apply(auto)
  done

lemma rnullable:
  shows "rnullable (rerase r) = bnullable r"
  apply(induct r rule: rerase.induct)
  apply(auto)
  done

lemma rerase_bder_ARESIDUE:
  shows "rerase (bder c (ARESIDUE bs cs rep)) = rder_residue c cs rep"
  by (cases cs) auto

lemma rder_bder_rerase:
  shows "rder c (rerase r ) = rerase (bder c r)"
  by (induct r) (auto simp add: Let_def rerase_fuse rnullable rerase_bder_ARESIDUE)

lemma rerase_map_bsimp:
  assumes "\<And> r. r \<in> set rs \<Longrightarrow> rerase (bsimp r) = (rsimp \<circ> rerase) r"
  shows "map rerase (map bsimp rs) =  map (rsimp \<circ> rerase) rs"
  using assms
  apply(induct rs)
  by simp_all


lemma rerase_flts:
  shows "map rerase (flts rs) = rflts (map rerase rs)"
  apply(induct rs rule: flts.induct)
  apply(auto simp add: rerase_fuse)
  done

lemma rerase_dB:
  shows "map rerase (distinctBy rs rerase acc) = rdistinct (map rerase rs) acc"
  apply(induct rs arbitrary: acc)
  apply simp+
  done

lemma map_rerase_distinctWith_eq1:
  shows "map rerase (distinctWith xs eq1 {}) = rdistinct (map rerase xs) {}"
  using distinctBy_distinctWith2 rerase_dB by metis

lemma rerase_bsimp3_ASEQ_atom:
  shows "rerase (bsimp3_ASEQ_atom bs a1 a2) =
    rsimp3_SEQ_atom (rerase a1) (rerase a2)"
  by (cases a1; cases a2)
     (simp_all add: bsimp3_ASEQ_atom_def rsimp3_SEQ_atom_def rerase_fuse)

lemma rerase_bsimp3_seq_row:
  shows "map rerase (bsimp3_seq_row bs a1 a2) =
    rsimp3_seq_row (rerase a1) (rerase a2)"
  by (simp add: rerase_bsimp3_ASEQ_atom)

lemma rerase_concat_bsimp3_seq_rows:
  shows "map rerase (concat (map (\<lambda>x. bsimp3_seq_row bs x a2) rs)) =
    concat (map (\<lambda>x. rsimp3_seq_row (rerase x) (rerase a2)) rs)"
  by (induct rs) (simp_all add: rerase_bsimp3_seq_row rerase_bsimp3_ASEQ_atom)

lemma rerase_bsimp3_ASEQ:
  shows "rerase (bsimp3_ASEQ bs a1 a2) =
    rsimp3_SEQ (rerase a1) (rerase a2)"
  by (cases a1)
     (simp_all add: bsimp3_ASEQ_def rsimp3_SEQ_def rerase_bsimp_AALTs
       map_rerase_distinctWith_eq1 rerase_flts rerase_bsimp3_seq_row
       rerase_concat_bsimp3_seq_rows rerase_bsimp3_ASEQ_atom map_map comp_def)
  
lemma rerase_earlier_later_same:
  assumes " \<And>r. r \<in> set rs \<Longrightarrow> rerase (bsimp r) = rsimp (rerase r)"
  shows " (map rerase (distinctBy (flts (map bsimp rs)) rerase {})) =
          (rdistinct (rflts (map (rsimp \<circ> rerase) rs)) {})"
  apply(subst rerase_dB)
  apply(subst rerase_flts)
  apply(subst rerase_map_bsimp)
  apply auto
  using assms
  apply simp
  done

lemma rerase_map_bsimp3:
  assumes "\<And> r. r \<in> set rs \<Longrightarrow> rerase (bsimp3 r) = (rsimp3 \<circ> rerase) r"
  shows "map rerase (map bsimp3 rs) =  map (rsimp3 \<circ> rerase) rs"
  using assms
  apply(induct rs)
  by simp_all

lemma rerase_earlier_later_same3:
  assumes " \<And>r. r \<in> set rs \<Longrightarrow> rerase (bsimp3 r) = rsimp3 (rerase r)"
  shows " (map rerase (distinctBy (flts (map bsimp3 rs)) rerase {})) =
          (rdistinct (rflts (map (rsimp3 \<circ> rerase) rs)) {})"
  apply(subst rerase_dB)
  apply(subst rerase_flts)
  apply(subst rerase_map_bsimp3)
  apply auto
  using assms
  apply simp
  done

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend bsimp_rerase for the new constructor cases if rrexp is retained. If
   rrexp is removed, replace this transfer lemma with a direct arexp/rexp
   simplifier bound proof. *)
lemma bsimp_rerase:
  shows "rerase (bsimp a) = rsimp (rerase a)"
  apply(induct a rule: bsimp.induct)
  apply(auto)
  using rerase_bsimp_ASEQ apply presburger
  using distinctBy_distinctWith2 rerase_bsimp_AALTs rerase_earlier_later_same by fastforce

lemma bsimp3_rerase:
  shows "rerase (bsimp3 a) = rsimp3 (rerase a)"
  apply(induct a rule: bsimp3.induct)
  apply(auto)
  using rerase_bsimp3_ASEQ apply presburger
  using distinctBy_distinctWith2 rerase_bsimp_AALTs rerase_earlier_later_same3 by fastforce

lemma rerase_bsimp4_ASEQ_atom:
  shows "rerase (bsimp4_ASEQ_atom bs a1 a2) =
    rsimp4_SEQ_atom (rerase a1) (rerase a2)"
proof (induct a1 arbitrary: bs a2)
  case AZERO
  then show ?case by simp
next
  case (AONE x)
  then show ?case
    by (cases a2) (simp_all add: rerase_fuse)
next
  case (ACHAR x1 x2)
  then show ?case
    by (cases a2) simp_all
next
  case (ASEQ x1 a1a a1b)
  then show ?case
    by simp
next
  case (AALTs x1 x2)
  then show ?case
    by (cases a2) simp_all
next
  case (ASTAR x1 x2)
  then show ?case
    by (cases a2) simp_all
next
  case (ANTIMES x1 x2 x3)
  then show ?case
    by (cases a2) simp_all
next
  case (ABACKREF4 x1 x2 x3 x4 x5 x6)
  then show ?case
    by (cases a2) simp_all
next
  case (AHALF x1 x2 x3 x4)
  then show ?case
    by (cases a2) simp_all
next
  case (ARESIDUE x1 x2 x3)
  then show ?case
    by (cases a2) simp_all
qed

lemma rerase_bsimp4_seq_row:
  shows "map rerase (bsimp4_seq_row bs a1 a2) =
    rsimp4_seq_row (rerase a1) (rerase a2)"
  by (simp add: rerase_bsimp4_ASEQ_atom)

lemma rerase_concat_bsimp4_seq_rows:
  shows "map rerase (concat (map (\<lambda>x. bsimp4_seq_row bs x a2) rs)) =
    concat (map (\<lambda>x. rsimp4_seq_row (rerase x) (rerase a2)) rs)"
  by (induct rs) (simp_all add: rerase_bsimp4_seq_row rerase_bsimp4_ASEQ_atom)

lemma rerase_bsimp4_ASEQ:
  shows "rerase (bsimp4_ASEQ bs a1 a2) =
    rsimp4_SEQ (rerase a1) (rerase a2)"
  by (cases a1)
     (simp_all add: bsimp4_ASEQ_def rsimp4_SEQ_def rerase_bsimp_AALTs
       map_rerase_distinctWith_eq1 rerase_flts rerase_bsimp4_seq_row
       rerase_concat_bsimp4_seq_rows rerase_bsimp4_ASEQ_atom rerase_fuse map_map comp_def)

lemma rerase_map_bsimp4:
  assumes "\<And> r. r \<in> set rs \<Longrightarrow> rerase (bsimp4 r) = (rsimp4 \<circ> rerase) r"
  shows "map rerase (map bsimp4 rs) =  map (rsimp4 \<circ> rerase) rs"
  using assms
  apply(induct rs)
  by simp_all

lemma rerase_earlier_later_same4:
  assumes " \<And>r. r \<in> set rs \<Longrightarrow> rerase (bsimp4 r) = rsimp4 (rerase r)"
  shows " (map rerase (distinctBy (flts (map bsimp4 rs)) rerase {})) =
          (rdistinct (rflts (map (rsimp4 \<circ> rerase) rs)) {})"
  apply(subst rerase_dB)
  apply(subst rerase_flts)
  apply(subst rerase_map_bsimp4)
  apply auto
  using assms
  apply simp
  done

lemma bsimp4_rerase:
  shows "rerase (bsimp4 a) = rsimp4 (rerase a)"
  apply(induct a rule: bsimp4.induct)
  apply(auto)
  using rerase_bsimp4_ASEQ apply presburger
  using distinctBy_distinctWith2 rerase_bsimp_AALTs rerase_earlier_later_same4 by fastforce

lemma rerase_bsimp5_alt_rows:
  "map rerase (bsimp5_alt_rows r) = rsimp5_alt_rows (rerase r)"
  by (cases r) simp_all

lemma rerase_bsimp5_seq_products:
  "map rerase (bsimp5_seq_products bs xs ys) =
    rsimp5_seq_products (map rerase xs) (map rerase ys)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have "map rerase (map (\<lambda>y. bsimp4_ASEQ_atom bs x y) ys) =
    map (\<lambda>y. rsimp4_SEQ_atom (rerase x) y) (map rerase ys)"
    by (induct ys) (simp_all add: rerase_bsimp4_ASEQ_atom)
  then show ?case
    using Cons by simp
qed

lemma rerase_bsimp5_ASEQ:
  shows "rerase (bsimp5_ASEQ bs a1 a2) =
    rsimp5_SEQ (rerase a1) (rerase a2)"
  by (simp add: bsimp5_ASEQ_def rsimp5_SEQ_def rerase_bsimp_AALTs
      map_rerase_distinctWith_eq1 rerase_flts rerase_bsimp5_seq_products
      rerase_bsimp5_alt_rows)

lemma rerase_map_bsimp5:
  assumes "\<And> r. r \<in> set rs \<Longrightarrow> rerase (bsimp5 r) = (rsimp5 \<circ> rerase) r"
  shows "map rerase (map bsimp5 rs) =  map (rsimp5 \<circ> rerase) rs"
  using assms
  by (induct rs) simp_all

lemma rerase_earlier_later_same5:
  assumes " \<And>r. r \<in> set rs \<Longrightarrow> rerase (bsimp5 r) = rsimp5 (rerase r)"
  shows " (map rerase (distinctBy (flts (map bsimp5 rs)) rerase {})) =
          (rdistinct (rflts (map (rsimp5 \<circ> rerase) rs)) {})"
  apply(subst rerase_dB)
  apply(subst rerase_flts)
  apply(subst rerase_map_bsimp5)
  apply auto
  using assms
  apply simp
  done

lemma bsimp5_rerase:
  shows "rerase (bsimp5 a) = rsimp5 (rerase a)"
  apply(induct a rule: bsimp5.induct)
  apply(auto)
  using rerase_bsimp5_ASEQ apply presburger
  using distinctBy_distinctWith2 rerase_bsimp_AALTs rerase_earlier_later_same5 by fastforce

lemma rerase_bsimp6_ASEQ_atom:
  shows "rerase (bsimp6_ASEQ_atom bs a1 a2) =
    rsimp6_SEQ_atom (rerase a1) (rerase a2)"
  by (cases a1; cases a2)
    (simp_all add: bsimp6_ASEQ_atom_def rsimp6_SEQ_atom_def
      rerase_bsimp4_ASEQ_atom eq1_rerase)

lemma rerase_bsimp6_seq_products:
  "map rerase (bsimp6_seq_products bs xs ys) =
    rsimp6_seq_products (map rerase xs) (map rerase ys)"
proof (induct xs)
  case Nil
  then show ?case
    by (simp add: bsimp6_seq_products_def rsimp6_seq_products_def)
next
  case (Cons x xs)
  have "map rerase (map (bsimp6_ASEQ_atom bs x) ys) =
    map (rsimp6_SEQ_atom (rerase x)) (map rerase ys)"
    by (induct ys) (simp_all add: rerase_bsimp6_ASEQ_atom)
  then show ?case
    using Cons by (simp add: bsimp6_seq_products_def rsimp6_seq_products_def)
qed

lemma rerase_bsimp6_ASEQ:
  shows "rerase (bsimp6_ASEQ bs a1 a2) =
    rsimp6_SEQ (rerase a1) (rerase a2)"
  by (simp add: bsimp6_ASEQ_def rsimp6_SEQ_def rerase_bsimp_AALTs
      map_rerase_distinctWith_eq1 rerase_flts rerase_bsimp6_seq_products
      rerase_bsimp5_alt_rows)

lemma rerase_map_bsimp6:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> rerase (bsimp6 r) = (rsimp6 \<circ> rerase) r"
  shows "map rerase (map bsimp6 rs) = map (rsimp6 \<circ> rerase) rs"
  using assms
  by (induct rs) simp_all

lemma rerase_earlier_later_same6:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> rerase (bsimp6 r) = rsimp6 (rerase r)"
  shows "map rerase (distinctBy (flts (map bsimp6 rs)) rerase {}) =
    rdistinct (rflts (map (rsimp6 \<circ> rerase) rs)) {}"
  apply(subst rerase_dB)
  apply(subst rerase_flts)
  apply(subst rerase_map_bsimp6)
  apply auto
  using assms
  apply simp
  done

lemma bsimp6_rerase:
  shows "rerase (bsimp6 a) = rsimp6 (rerase a)"
proof (induct a rule: bsimp6.induct)
  case (1 bs r1 r2)
  then show ?case
    by (simp add: rerase_bsimp6_ASEQ)
next
  case (2 bs rs)
  then show ?case
    using distinctBy_distinctWith2 rerase_bsimp_AALTs rerase_earlier_later_same6
    by fastforce
next
  case (3 bs r)
  have ih_sym: "rsimp6 (rerase r) = rerase (bsimp6 r)"
    using 3 by simp
  then show ?case
    by (cases "bsimp6 r") (simp_all add: ih_sym)
qed simp_all

lemma rerase_bsimp7_ASEQ_atom:
  shows "rerase (bsimp7_ASEQ_atom bs a1 a2) =
    rsimp7_SEQ_atom (rerase a1) (rerase a2)"
  by (cases a1; cases a2)
    (simp_all add: bsimp7_ASEQ_atom_def rsimp7_SEQ_atom_def
      rerase_bsimp4_ASEQ_atom eq1_rerase split: arexp.splits)

lemma rerase_bsimp7_seq_products:
  "map rerase (bsimp7_seq_products bs xs ys) =
    rsimp7_seq_products (map rerase xs) (map rerase ys)"
proof (induct xs)
  case Nil
  then show ?case
    by (simp add: bsimp7_seq_products_def rsimp7_seq_products_def)
next
  case (Cons x xs)
  have "map rerase (map (bsimp7_ASEQ_atom bs x) ys) =
    map (rsimp7_SEQ_atom (rerase x)) (map rerase ys)"
    by (induct ys) (simp_all add: rerase_bsimp7_ASEQ_atom)
  then show ?case
    using Cons by (simp add: bsimp7_seq_products_def rsimp7_seq_products_def)
qed

lemma rerase_bsimp7_ASEQ:
  shows "rerase (bsimp7_ASEQ bs a1 a2) =
    rsimp7_SEQ (rerase a1) (rerase a2)"
  by (simp add: bsimp7_ASEQ_def rsimp7_SEQ_def rerase_bsimp_AALTs
      map_rerase_distinctWith_eq1 rerase_flts rerase_bsimp7_seq_products
      rerase_bsimp5_alt_rows)

lemma rerase_map_bsimp7:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> rerase (bsimp7 r) = (rsimp7 \<circ> rerase) r"
  shows "map rerase (map bsimp7 rs) = map (rsimp7 \<circ> rerase) rs"
  using assms
  by (induct rs) simp_all

lemma rerase_earlier_later_same7:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> rerase (bsimp7 r) = rsimp7 (rerase r)"
  shows "map rerase (distinctBy (flts (map bsimp7 rs)) rerase {}) =
    rdistinct (rflts (map (rsimp7 \<circ> rerase) rs)) {}"
  apply(subst rerase_dB)
  apply(subst rerase_flts)
  apply(subst rerase_map_bsimp7)
  apply auto
  using assms
  apply simp
  done

lemma bsimp7_rerase:
  shows "rerase (bsimp7 a) = rsimp7 (rerase a)"
proof (induct a rule: bsimp7.induct)
  case (1 bs r1 r2)
  then show ?case
    by (simp add: rerase_bsimp7_ASEQ)
next
  case (2 bs rs)
  then show ?case
    using distinctBy_distinctWith2 rerase_bsimp_AALTs rerase_earlier_later_same7
    by fastforce
next
  case (3 bs r)
  have ih_sym: "rsimp7 (rerase r) = rerase (bsimp7 r)"
    using 3 by simp
  then show ?case
    by (cases "bsimp7 r") (simp_all add: ih_sym)
qed simp_all

lemma rerase_map_bsimp8:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> rerase (bsimp8 r) = (rsimp8 \<circ> rerase) r"
  shows "map rerase (map bsimp8 rs) = map (rsimp8 \<circ> rerase) rs"
  using assms
  by (induct rs) simp_all

lemma rerase_earlier_later_same8:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> rerase (bsimp8 r) = rsimp8 (rerase r)"
  shows "map rerase (distinctBy (flts (map bsimp8 rs)) rerase {}) =
    rdistinct (rflts (map (rsimp8 \<circ> rerase) rs)) {}"
  apply(subst rerase_dB)
  apply(subst rerase_flts)
  apply(subst rerase_map_bsimp8)
  apply auto
  using assms
  apply simp
  done

lemma bsimp8_rerase:
  shows "rerase (bsimp8 a) = rsimp8 (rerase a)"
proof (induct a rule: bsimp8.induct)
  case (1 bs r1 r2)
  then show ?case
    by (simp add: rerase_bsimp7_ASEQ_atom)
next
  case (2 bs rs)
  then show ?case
    using distinctBy_distinctWith2 rerase_bsimp_AALTs rerase_earlier_later_same8
    by fastforce
next
  case (3 bs r)
  have ih_sym: "rsimp8 (rerase r) = rerase (bsimp8 r)"
    using 3 by simp
  then show ?case
    by (cases "bsimp8 r") (simp_all add: ih_sym)
qed simp_all

lemma L_bsimp_AALTs:
  "L (erase (bsimp_AALTs bs rs)) = L (erase (AALTs bs rs))"
  by (cases rs; cases "tl rs") (simp_all add: erase_fuse)

lemma L_bsimp4_ASEQ_atom:
  "L (erase (bsimp4_ASEQ_atom bs r1 r2)) =
    L (erase (ASEQ bs r1 r2))"
  by (induct bs r1 r2 rule: bsimp4_ASEQ_atom.induct)
    (simp_all add: erase_fuse conc_assoc)

lemma L_bsimp7_ASEQ_atom:
  "L (erase (bsimp7_ASEQ_atom bs r1 r2)) =
    L (erase (ASEQ bs r1 r2))"
proof (cases r1)
  case (ASTAR bs1 r)
  note r1_ASTAR = ASTAR
  show ?thesis
  proof (cases r2)
    case (ASTAR bs2 s)
    note r2_ASTAR = ASTAR
    show ?thesis
    proof (cases "r ~1 s")
      case True
      have same: "L (erase s) = L (erase r)"
        using True eq1_L by blast
      show ?thesis
        using r1_ASTAR r2_ASTAR same
        by (simp add: bsimp7_ASEQ_atom_def Star_Sequ_idem)
    next
      case False
      then show ?thesis
        using r1_ASTAR r2_ASTAR
        by (simp add: bsimp7_ASEQ_atom_def L_bsimp4_ASEQ_atom)
    qed
  next
    case (ASEQ bs2 q k)
    note r2_ASEQ = ASEQ
    show ?thesis
    proof (cases q)
      case (ASTAR bs3 s)
      note q_ASTAR = ASTAR
      show ?thesis
      proof (cases "r ~1 s")
        case True
        have same: "L (erase s) = L (erase r)"
          using True eq1_L by blast
        show ?thesis
          using r1_ASTAR r2_ASEQ q_ASTAR same
          by (simp add: bsimp7_ASEQ_atom_def Star_Sequ_prefix_idem)
      next
        case False
        then show ?thesis
          using r1_ASTAR r2_ASEQ q_ASTAR
          by (simp add: bsimp7_ASEQ_atom_def L_bsimp4_ASEQ_atom)
      qed
    qed (insert r1_ASTAR r2_ASEQ, simp_all add: bsimp7_ASEQ_atom_def
      L_bsimp4_ASEQ_atom erase_fuse conc_assoc)
  qed (insert r1_ASTAR, simp_all add: bsimp7_ASEQ_atom_def
    L_bsimp4_ASEQ_atom erase_fuse conc_assoc)
qed (simp_all add: bsimp7_ASEQ_atom_def L_bsimp4_ASEQ_atom erase_fuse
    conc_assoc)

lemma flts_L_UN:
  "(\<Union>r \<in> set (flts rs). L (erase r)) =
    (\<Union>r \<in> set rs. L (erase r))"
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  show ?case
  proof (cases a)
    case AZERO
    then show ?thesis
      using Cons.hyps by simp
  next
    case (AALTs bs rs1)
    have mapped: "(\<Union>r \<in> set (map (fuse bs) rs1). L (erase r)) =
        (\<Union>r \<in> set rs1. L (erase r))"
      by (auto simp add: erase_fuse)
    have alt: "L (erase (AALTs bs rs1)) =
        (\<Union>r \<in> set rs1. L (erase r))"
      by (simp add: L_erase_AALTs_set)
    show ?thesis
      using Cons.hyps AALTs mapped alt by auto
  qed (use Cons.hyps in simp_all)
qed

lemma L_flts_AALTs:
  "L (erase (AALTs bs (flts rs))) = L (erase (AALTs bs rs))"
  by (simp add: L_erase_AALTs_set flts_L_UN)

lemma distinctWith_eq1_L_UN_acc:
  "(\<Union>r \<in> set (distinctWith rs eq1 acc). L (erase r)) \<union>
    (\<Union>r \<in> acc. L (erase r)) =
    (\<Union>r \<in> set rs. L (erase r)) \<union>
    (\<Union>r \<in> acc. L (erase r))"
proof (induct rs arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  show ?case
  proof (cases "\<exists>y \<in> acc. r ~1 y")
    case True
    then obtain y where y: "y \<in> acc" "r ~1 y"
      by blast
    have "L (erase r) \<subseteq> (\<Union>q \<in> acc. L (erase q))"
      using y eq1_L by blast
    then show ?thesis
      using Cons.hyps[of acc] True by auto
  next
    case False
    have ih: "(\<Union>x \<in> set (distinctWith rs eq1 ({r} \<union> acc)). L (erase x)) \<union>
        (\<Union>x \<in> {r} \<union> acc. L (erase x)) =
        (\<Union>x \<in> set rs. L (erase x)) \<union>
        (\<Union>x \<in> {r} \<union> acc. L (erase x))"
      by (rule Cons.hyps)
    show ?thesis
      using False ih by auto
  qed
qed

lemma L_distinctWith_eq1_AALTs:
  "L (erase (AALTs bs (distinctWith rs eq1 {}))) =
    L (erase (AALTs bs rs))"
  using distinctWith_eq1_L_UN_acc[of rs "{}"]
  by (simp add: L_erase_AALTs_set)

lemma L_prune_eq1_against_AALTs_union:
  "L (erase (AALTs lbs covered)) \<union>
    L (erase (AALTs rbs (prune_eq1_against covered rs))) =
    L (erase (AALTs lbs covered)) \<union>
    L (erase (AALTs rbs rs))"
  using prune_eq1_against_cover_UN[of covered rs]
  by (simp add: L_erase_AALTs_set)

lemma Sequ_union_right_cong:
  assumes "A \<union> B = A \<union> C"
  shows "A ;; K \<union> B ;; K = A ;; K \<union> C ;; K"
proof -
  have "A ;; K \<union> B ;; K = (A \<union> B) ;; K"
    by (auto simp add: Sequ_def)
  also have "... = (A \<union> C) ;; K"
    using assms by simp
  also have "... = A ;; K \<union> C ;; K"
    by (auto simp add: Sequ_def)
  finally show ?thesis .
qed

lemma L_bsimpStrong_prune_pair_cover:
  "L (erase earlier) \<union>
    L (erase (bsimpStrong_prune_pair earlier later)) =
    L (erase earlier) \<union> L (erase later)"
proof (cases earlier)
  case (ASEQ x41 x42 x43)
  note earlier_ASEQ = ASEQ
  show ?thesis
  proof (cases later)
    case (ASEQ x41a x42a x43a)
    note later_ASEQ = ASEQ
    show ?thesis
    proof (cases x42)
      case (AALTs x51 x52)
      note earlier_left_AALTs = AALTs
      show ?thesis
      proof (cases x42a)
        case (AALTs x51a x52a)
        note later_left_AALTs = AALTs
        show ?thesis
        proof (cases "x43 ~1 x43a")
          case True
          have suffix: "L (erase x43) = L (erase x43a)"
            using True eq1_L by blast
          have left_union:
            "L (erase (AALTs x51 x52)) \<union>
              L (erase (bsimp_AALTs x51a (prune_eq1_against x52 x52a))) =
              L (erase (AALTs x51 x52)) \<union>
              L (erase (AALTs x51a x52a))"
            using L_prune_eq1_against_AALTs_union[of x51 x52 x51a x52a]
              L_bsimp_AALTs[of x51a "prune_eq1_against x52 x52a"]
            by simp
          let ?A = "L (erase (AALTs x51 x52))"
          let ?B = "L (erase (bsimp_AALTs x51a
            (prune_eq1_against x52 x52a)))"
          let ?C = "L (erase (AALTs x51a x52a))"
          let ?K = "L (erase x43a)"
          have earlier_eq: "earlier = ASEQ x41 (AALTs x51 x52) x43"
            using earlier_ASEQ earlier_left_AALTs by simp
          have earlier_lang: "L (erase earlier) = ?A ;; ?K"
            using earlier_eq suffix by simp
          have pair_eval:
            "bsimpStrong_prune_pair earlier later =
              bsimp7_ASEQ_atom x41a
                (bsimp_AALTs x51a (prune_eq1_against x52 x52a)) x43a"
            using earlier_ASEQ later_ASEQ
              earlier_left_AALTs later_left_AALTs True
            by (simp add: bsimpStrong_prune_pair_def)
          have pair_lang:
            "L (erase (bsimpStrong_prune_pair earlier later)) = ?B ;; ?K"
            using pair_eval L_bsimp7_ASEQ_atom[
              of x41a "bsimp_AALTs x51a (prune_eq1_against x52 x52a)" x43a]
            by simp
          have later_lang: "L (erase later) = ?C ;; ?K"
            using later_ASEQ later_left_AALTs
            by simp
          have seq_union: "?A ;; ?K \<union> ?B ;; ?K = ?A ;; ?K \<union> ?C ;; ?K"
            by (rule Sequ_union_right_cong[OF left_union])
          show ?thesis
            using earlier_lang pair_lang later_lang seq_union by simp
        next
          case False
          then show ?thesis
            using earlier_ASEQ later_ASEQ
              earlier_left_AALTs later_left_AALTs
            by (simp add: bsimpStrong_prune_pair_def)
        qed
      qed (insert earlier_ASEQ later_ASEQ earlier_left_AALTs,
        simp_all add: bsimpStrong_prune_pair_def)
    qed (insert earlier_ASEQ later_ASEQ,
      simp_all add: bsimpStrong_prune_pair_def)
  qed (insert earlier_ASEQ,
    simp_all add: bsimpStrong_prune_pair_def split: arexp.splits)
qed (simp_all add: bsimpStrong_prune_pair_def)

lemma L_bsimpStrong_prune_against_rows_cover:
  "(\<Union>x \<in> set seen. L (erase x)) \<union>
    L (erase (bsimpStrong_prune_against_rows seen r)) =
    (\<Union>x \<in> set seen. L (erase x)) \<union> L (erase r)"
proof (induct seen arbitrary: r)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have tail:
    "(\<Union>y \<in> set xs. L (erase y)) \<union>
      L (erase (bsimpStrong_prune_against_rows xs
        (bsimpStrong_prune_pair x r))) =
      (\<Union>y \<in> set xs. L (erase y)) \<union>
      L (erase (bsimpStrong_prune_pair x r))"
    by (rule Cons.hyps)
  have pair:
    "L (erase x) \<union> L (erase (bsimpStrong_prune_pair x r)) =
      L (erase x) \<union> L (erase r)"
    by (rule L_bsimpStrong_prune_pair_cover)
  show ?case
    using tail pair by auto
qed

lemma L_bsimpStrong_prune_rows_acc_cover:
  "(\<Union>x \<in> set seen. L (erase x)) \<union>
    (\<Union>x \<in> set (bsimpStrong_prune_rows_acc seen rs). L (erase x)) =
    (\<Union>x \<in> set seen. L (erase x)) \<union>
    (\<Union>x \<in> set rs. L (erase x))"
proof (induct rs arbitrary: seen)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  let ?r' = "bsimpStrong_prune_against_rows seen r"
  have head:
    "(\<Union>x \<in> set seen. L (erase x)) \<union> L (erase ?r') =
      (\<Union>x \<in> set seen. L (erase x)) \<union> L (erase r)"
    by (rule L_bsimpStrong_prune_against_rows_cover)
  have tail:
    "(\<Union>x \<in> set (?r' # seen). L (erase x)) \<union>
      (\<Union>x \<in> set (bsimpStrong_prune_rows_acc (?r' # seen) rs).
        L (erase x)) =
      (\<Union>x \<in> set (?r' # seen). L (erase x)) \<union>
      (\<Union>x \<in> set rs. L (erase x))"
    by (rule Cons.hyps)
  let ?S = "(\<Union>x \<in> set seen. L (erase x))"
  let ?R = "L (erase r)"
  let ?R' = "L (erase ?r')"
  let ?T = "(\<Union>x \<in> set (bsimpStrong_prune_rows_acc (?r' # seen) rs).
    L (erase x))"
  let ?U = "(\<Union>x \<in> set rs. L (erase x))"
  have tail': "(?S \<union> ?R') \<union> ?T = (?S \<union> ?R') \<union> ?U"
    using tail by (simp add: Un_assoc Un_commute Un_left_commute)
  have head': "?S \<union> ?R' = ?S \<union> ?R"
    by (rule head)
  have "?S \<union> (?R' \<union> ?T) = (?S \<union> ?R') \<union> ?T"
    by (simp add: Un_assoc)
  also have "... = (?S \<union> ?R') \<union> ?U"
    by (rule tail')
  also have "... = (?S \<union> ?R) \<union> ?U"
    using head' by simp
  also have "... = ?S \<union> (?R \<union> ?U)"
    by (simp add: Un_assoc)
  finally have union_step: "?S \<union> (?R' \<union> ?T) = ?S \<union> (?R \<union> ?U)" .
  show ?case
    using union_step by (simp add: Let_def Un_assoc)
qed

lemma L_bsimpStrong_prune_rows:
  "L (erase (AALTs bs (bsimpStrong_prune_rows rs))) =
    L (erase (AALTs bs rs))"
  using L_bsimpStrong_prune_rows_acc_cover[of "[]" rs]
  by (simp add: bsimpStrong_prune_rows_def L_erase_AALTs_set)

lemma L_bsimpStrong_AALTs:
  "L (erase (bsimpStrong_AALTs bs rs)) =
    L (erase (AALTs bs rs))"
  by (simp add: bsimpStrong_AALTs_def L_bsimp_AALTs
      L_distinctWith_eq1_AALTs L_flts_AALTs L_bsimpStrong_prune_rows)

lemma Star_epsilon [simp]:
  "({[]} :: string set)\<star> = {[]}"
proof
  show "({[]} :: string set)\<star> \<subseteq> {[]}"
  proof
    fix s
    assume "s \<in> ({[]} :: string set)\<star>"
    then show "s \<in> {[]}"
      by (induct rule: Star.induct) auto
  qed
next
  show "{[]} \<subseteq> ({[]} :: string set)\<star>"
    by auto
qed

lemma L_bsimpStrong:
  "L (erase (bsimpStrong r)) = L (erase r)"
proof (induct r rule: bsimpStrong.induct)
  case (1 bs r1 r2)
  then show ?case
    by (simp add: L_bsimp7_ASEQ_atom)
next
  case (2 bs rs)
  have rows:
    "L (erase (AALTs bs (map bsimpStrong rs))) =
      L (erase (AALTs bs rs))"
    using 2 by (auto simp add: L_erase_AALTs_set)
  show ?case
    by (simp add: L_bsimpStrong_AALTs L_flts_AALTs rows)
next
  case (3 bs r)
  note ih = 3
  show ?case
  proof (cases "bsimpStrong r")
    case AZERO
    have body: "L (erase r) = {}"
      using ih AZERO by simp
    then show ?thesis
      using AZERO body by simp
  next
    case (AONE x2)
    have body: "L (erase r) = {[]}"
      using ih AONE by simp
    then show ?thesis
      using AONE body by simp
  next
    case (ASTAR x61 x62)
    have body: "L (erase r) = (L (erase x62))\<star>"
      using ih ASTAR by simp
    then show ?thesis
      using ASTAR body by (simp add: Star_idem)
  qed (use ih in simp_all)
qed simp_all

lemma L_bsimpCubic_ASEQ_atom:
  "L (erase (bsimpCubic_ASEQ_atom bs r1 r2)) =
    L (erase (ASEQ bs r1 r2))"
  by (induct bs r1 r2 rule: bsimpCubic_ASEQ_atom.induct)
    (simp_all add: erase_fuse erase_AALTs_ignore_bits L_erase_AALTs_set
      conc_assoc)

lemma L_bsimpCubic_seq_cover:
  assumes "bsimpCubic_seq_cover earlier = Some (covered, k)"
  shows "L (erase earlier) =
    L (erase (AALTs [] covered)) ;; L (erase k)"
  using assms
proof (cases earlier)
  case (ASEQ bs left right)
  then show ?thesis
  proof (cases left)
    case (AALTs lbs lrs)
    then show ?thesis
      using assms ASEQ by (simp add: L_erase_AALTs_set erase_AALTs_ignore_bits)
  qed (use assms ASEQ in \<open>auto simp add: L_erase_AALTs_set\<close>)
qed simp_all

lemma L_bsimpCubic_prune_pair_non_AALTs:
  assumes cover: "bsimpCubic_seq_cover earlier = Some (covered, k1)"
      and later: "later = ASEQ bs2 row k2"
      and non_alts: "\<And>rbs rrs. row \<noteq> AALTs rbs rrs"
  shows "L (erase earlier) \<union>
    L (erase (bsimpCubic_prune_pair earlier later)) =
    L (erase earlier) \<union> L (erase later)"
proof (cases "k1 ~1 k2 \<and> eq1_member row covered")
  case True
  have suffix: "L (erase k1) = L (erase k2)"
    using True eq1_L by blast
  obtain q where q: "q \<in> set covered" "row ~1 q"
    using True eq1_member_set by blast
  have earlier_lang:
    "L (erase earlier) =
      L (erase (AALTs [] covered)) ;; L (erase k2)"
    using L_bsimpCubic_seq_cover[OF cover] suffix by simp
  have left_subset:
    "L (erase row) \<subseteq> L (erase (AALTs [] covered))"
    using q eq1_L[OF q(2)] by (auto simp add: L_erase_AALTs_set)
  have seq_subset:
    "L (erase row) ;; L (erase k2) \<subseteq>
      L (erase (AALTs [] covered)) ;; L (erase k2)"
    using left_subset by (auto simp add: Sequ_def)
  have pair_zero:
    "bsimpCubic_prune_pair earlier later = AZERO"
    using cover later non_alts True
    by (cases row; cases "k1 ~1 k2")
      (simp_all add: bsimpCubic_prune_pair_def)
  show ?thesis
    using earlier_lang later pair_zero seq_subset by auto
next
  case False
  have pair_same:
    "bsimpCubic_prune_pair earlier later = later"
    using cover later non_alts False
    by (cases row; cases "k1 ~1 k2")
      (simp_all add: bsimpCubic_prune_pair_def)
  show ?thesis
    using pair_same by simp
qed

lemma L_bsimpCubic_prune_pair_cover:
  "L (erase earlier) \<union>
    L (erase (bsimpCubic_prune_pair earlier later)) =
    L (erase earlier) \<union> L (erase later)"
proof (cases "bsimpCubic_seq_cover earlier")
  case None
  then show ?thesis
    by (simp add: bsimpCubic_prune_pair_def)
next
  case (Some ck)
  then obtain covered k1 where cover:
    "bsimpCubic_seq_cover earlier = Some (covered, k1)"
    by (cases ck) simp
  have earlier_lang:
    "L (erase earlier) =
      L (erase (AALTs [] covered)) ;; L (erase k1)"
    by (rule L_bsimpCubic_seq_cover[OF cover])
  show ?thesis
  proof (cases later)
    case (ASEQ bs2 left k2)
    show ?thesis
    proof (cases left)
      case (AALTs rbs rrs)
      show ?thesis
      proof (cases "k1 ~1 k2")
        case True
        have suffix: "L (erase k1) = L (erase k2)"
          using True eq1_L by blast
        have left_union:
          "L (erase (AALTs [] covered)) \<union>
            L (erase (bsimp_AALTs rbs
              (prune_eq1_against covered rrs))) =
            L (erase (AALTs [] covered)) \<union>
            L (erase (AALTs rbs rrs))"
          using L_prune_eq1_against_AALTs_union[of "[]" covered rbs rrs]
            L_bsimp_AALTs[of rbs "prune_eq1_against covered rrs"]
          by simp
        let ?A = "L (erase (AALTs [] covered))"
        let ?B = "L (erase (bsimp_AALTs rbs
          (prune_eq1_against covered rrs)))"
        let ?C = "L (erase (AALTs rbs rrs))"
        let ?K = "L (erase k2)"
        have pair_eval:
          "bsimpCubic_prune_pair earlier later =
            bsimpCubic_ASEQ_atom bs2
              (bsimp_AALTs rbs (prune_eq1_against covered rrs)) k2"
          using cover ASEQ AALTs True
          by (simp add: bsimpCubic_prune_pair_def)
        have pair_lang:
          "L (erase (bsimpCubic_prune_pair earlier later)) = ?B ;; ?K"
          using pair_eval L_bsimpCubic_ASEQ_atom[
            of bs2 "bsimp_AALTs rbs (prune_eq1_against covered rrs)" k2]
          by simp
        have later_lang: "L (erase later) = ?C ;; ?K"
          using ASEQ AALTs by simp
        have earlier_lang': "L (erase earlier) = ?A ;; ?K"
          using earlier_lang suffix by simp
        have seq_union: "?A ;; ?K \<union> ?B ;; ?K = ?A ;; ?K \<union> ?C ;; ?K"
          by (rule Sequ_union_right_cong[OF left_union])
        show ?thesis
          using earlier_lang' pair_lang later_lang seq_union by simp
      next
        case False
        then show ?thesis
          using cover ASEQ AALTs by (simp add: bsimpCubic_prune_pair_def)
      qed
    next
      case non_alts: AZERO
      show ?thesis
        by (rule L_bsimpCubic_prune_pair_non_AALTs[OF cover ASEQ])
          (use non_alts in simp)
    next
      case non_alts: (AONE x2)
      show ?thesis
        by (rule L_bsimpCubic_prune_pair_non_AALTs[OF cover ASEQ])
          (use non_alts in simp)
    next
      case non_alts: (ACHAR x31 x32)
      show ?thesis
        by (rule L_bsimpCubic_prune_pair_non_AALTs[OF cover ASEQ])
          (use non_alts in simp)
    next
      case non_alts: (ASEQ x41 x42 x43)
      show ?thesis
        by (rule L_bsimpCubic_prune_pair_non_AALTs[OF cover ASEQ])
          (use non_alts in simp)
    next
      case non_alts: (ASTAR x61 x62)
      show ?thesis
        by (rule L_bsimpCubic_prune_pair_non_AALTs[OF cover ASEQ])
          (use non_alts in simp)
    next
      case non_alts: (ANTIMES x71 x72 x73)
      show ?thesis
        by (rule L_bsimpCubic_prune_pair_non_AALTs[OF cover ASEQ])
          (use non_alts in simp)
    next
      case non_alts: (ABACKREF4 x81 x82 x83 x84 x85 x86)
      show ?thesis
        by (rule L_bsimpCubic_prune_pair_non_AALTs[OF cover ASEQ])
          (use non_alts in simp)
    next
      case non_alts: (AHALF x91 x92 x93 x94)
      show ?thesis
        by (rule L_bsimpCubic_prune_pair_non_AALTs[OF cover ASEQ])
          (use non_alts in simp)
    next
      case non_alts: (ARESIDUE x101 x102 x103)
      show ?thesis
        by (rule L_bsimpCubic_prune_pair_non_AALTs[OF cover ASEQ])
          (use non_alts in simp)
    qed
  qed (insert cover, simp_all add: bsimpCubic_prune_pair_def)
qed

lemma L_bsimpCubic_prune_against_rows_cover:
  "(\<Union>x \<in> set seen. L (erase x)) \<union>
    L (erase (bsimpCubic_prune_against_rows seen r)) =
    (\<Union>x \<in> set seen. L (erase x)) \<union> L (erase r)"
proof (induct seen arbitrary: r)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have tail:
    "(\<Union>y \<in> set xs. L (erase y)) \<union>
      L (erase (bsimpCubic_prune_against_rows xs
        (bsimpCubic_prune_pair x r))) =
      (\<Union>y \<in> set xs. L (erase y)) \<union>
      L (erase (bsimpCubic_prune_pair x r))"
    by (rule Cons.hyps)
  have pair:
    "L (erase x) \<union> L (erase (bsimpCubic_prune_pair x r)) =
      L (erase x) \<union> L (erase r)"
    by (rule L_bsimpCubic_prune_pair_cover)
  show ?case
    using tail pair by auto
qed

lemma L_bsimpCubic_prune_rows_acc_cover:
  "(\<Union>x \<in> set seen. L (erase x)) \<union>
    (\<Union>x \<in> set (bsimpCubic_prune_rows_acc seen rs). L (erase x)) =
    (\<Union>x \<in> set seen. L (erase x)) \<union>
    (\<Union>x \<in> set rs. L (erase x))"
proof (induct rs arbitrary: seen)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  let ?r' = "bsimpCubic_prune_against_rows seen r"
  have head:
    "(\<Union>x \<in> set seen. L (erase x)) \<union> L (erase ?r') =
      (\<Union>x \<in> set seen. L (erase x)) \<union> L (erase r)"
    by (rule L_bsimpCubic_prune_against_rows_cover)
  have tail:
    "(\<Union>x \<in> set (?r' # seen). L (erase x)) \<union>
      (\<Union>x \<in> set (bsimpCubic_prune_rows_acc (?r' # seen) rs).
        L (erase x)) =
      (\<Union>x \<in> set (?r' # seen). L (erase x)) \<union>
      (\<Union>x \<in> set rs. L (erase x))"
    by (rule Cons.hyps)
  let ?S = "(\<Union>x \<in> set seen. L (erase x))"
  let ?R = "L (erase r)"
  let ?R' = "L (erase ?r')"
  let ?T = "(\<Union>x \<in> set (bsimpCubic_prune_rows_acc (?r' # seen) rs).
    L (erase x))"
  let ?U = "(\<Union>x \<in> set rs. L (erase x))"
  have tail': "(?S \<union> ?R') \<union> ?T = (?S \<union> ?R') \<union> ?U"
    using tail by (simp add: Un_assoc Un_commute Un_left_commute)
  have head': "?S \<union> ?R' = ?S \<union> ?R"
    by (rule head)
  have "?S \<union> (?R' \<union> ?T) = (?S \<union> ?R') \<union> ?T"
    by (simp add: Un_assoc)
  also have "... = (?S \<union> ?R') \<union> ?U"
    by (rule tail')
  also have "... = (?S \<union> ?R) \<union> ?U"
    using head' by simp
  also have "... = ?S \<union> (?R \<union> ?U)"
    by (simp add: Un_assoc)
  finally have union_step: "?S \<union> (?R' \<union> ?T) = ?S \<union> (?R \<union> ?U)" .
  show ?case
    using union_step by (simp add: Let_def Un_assoc)
qed

lemma L_bsimpCubic_prune_rows:
  "L (erase (AALTs bs (bsimpCubic_prune_rows rs))) =
    L (erase (AALTs bs rs))"
  using L_bsimpCubic_prune_rows_acc_cover[of "[]" rs]
  by (simp add: bsimpCubic_prune_rows_def L_erase_AALTs_set)

lemma L_bsimpCubic_AALTs:
  "L (erase (bsimpCubic_AALTs bs rs)) =
    L (erase (AALTs bs rs))"
  by (simp add: bsimpCubic_AALTs_def L_bsimp_AALTs
      L_distinctWith_eq1_AALTs L_flts_AALTs L_bsimpCubic_prune_rows)

lemma L_bsimpCubic:
  "L (erase (bsimpCubic r)) = L (erase r)"
proof (induct r rule: bsimpCubic.induct)
  case (1 bs r1 r2)
  then show ?case
    by (simp add: L_bsimpCubic_ASEQ_atom)
next
  case (2 bs rs)
  have rows:
    "L (erase (AALTs bs (map bsimpCubic rs))) =
      L (erase (AALTs bs rs))"
    using 2 by (auto simp add: L_erase_AALTs_set)
  show ?case
    by (simp add: L_bsimpCubic_AALTs L_flts_AALTs rows)
next
  case (3 bs r)
  note ih = 3
  show ?case
  proof (cases "bsimpCubic r")
    case AZERO
    have body: "L (erase r) = {}"
      using ih AZERO by simp
    then show ?thesis
      using AZERO body by simp
  next
    case (AONE x2)
    have body: "L (erase r) = {[]}"
      using ih AONE by simp
    then show ?thesis
      using AONE body by simp
  next
    case (ASTAR x61 x62)
    have body: "L (erase r) = (L (erase x62))\<star>"
      using ih ASTAR by simp
    then show ?thesis
      using ASTAR body by (simp add: Star_idem)
  qed (use ih in simp_all)
next
  case (4 bs r n)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      by simp
  next
    case (Suc m)
    have ih_body: "L (erase (bsimpCubic r)) = L (erase r)"
      using 4 Suc by simp
    show ?thesis
    proof (cases "bsimpCubic r")
      case AZERO
      have body: "{} = L (erase r)"
        using ih_body AZERO by simp
      then show ?thesis
        using Suc AZERO body[symmetric] by (simp add: lang_pow_empty)
    next
      case (AONE bs')
      have body: "{[]} = L (erase r)"
        using ih_body AONE by simp
      then show ?thesis
        using Suc AONE body[symmetric] by (simp add: lang_pow_epsilon)
    qed (use 4 Suc in simp_all)
  qed
qed simp_all

lemma RL_rerase_AALTs:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow> RL (rerase r) = L (erase r)"
  shows "RL (RALTS (map rerase rs)) = L (erase (AALTs bs rs))"
using assms
proof (induct rs arbitrary: bs)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
      using Cons.prems by simp
  next
    case (Cons q qs)
    have "RL (RALTS (map rerase (r # rs))) =
        RL (rerase r) \<union> RL (RALTS (map rerase rs))"
      by simp
    also have "... = L (erase r) \<union> L (erase (AALTs bs rs))"
      using Cons.hyps Cons.prems by simp
    also have "... = L (erase (AALTs bs (r # rs)))"
      using Cons by simp
    finally show ?thesis .
  qed
qed

lemma RL_rerase:
  "RL (rerase r) = L (erase r)"
proof (induct r)
  case (AALTs bs rs)
  have elems: "\<And>r. r \<in> set rs \<Longrightarrow> RL (rerase r) = L (erase r)"
    using AALTs by auto
  have alts: "RL (RALTS (map rerase rs)) = L (erase (AALTs bs rs))"
    by (rule RL_rerase_AALTs) (rule elems)
  show ?case
    using alts by simp
qed simp_all

lemma RLS_set_map_rerase_AALTs:
  "RLS (set (map rerase rs)) = L (erase (AALTs bs rs))"
proof -
  have "RL (RALTS (map rerase rs)) = L (erase (AALTs bs rs))"
    by (rule RL_rerase_AALTs) (rule RL_rerase)
  then show ?thesis
    by (simp add: RLS_def)
qed

lemma RL_rerase_bsimpStrong:
  "RL (rerase (bsimpStrong r)) = RL (rerase r)"
  by (simp add: RL_rerase L_bsimpStrong)

lemma RL_rerase_bsimpCubic:
  "RL (rerase (bsimpCubic r)) = RL (rerase r)"
  by (simp add: RL_rerase L_bsimpCubic)

lemma RL_rerase_bsimpStrong_rsimpStrong:
  "RL (rerase (bsimpStrong r)) = RL (rsimpStrong (rerase r))"
  by (simp add: RL_rerase_bsimpStrong RL_rsimpStrong)

lemma RL_rerase_bders_simpStrong:
  "RL (rerase (bders_simpStrong r s)) = Ders s (RL (rerase r))"
proof (induct s arbitrary: r)
  case Nil
  then show ?case
    by (simp add: Ders_def)
next
  case (Cons c s)
  have "RL (rerase (bders_simpStrong r (c # s))) =
      RL (rerase (bders_simpStrong (bsimpStrong (bder c r)) s))"
    by simp
  also have "... = Ders s (RL (rerase (bsimpStrong (bder c r))))"
    by (rule Cons.hyps)
  also have "... = Ders s (RL (rerase (bder c r)))"
    by (simp add: RL_rerase_bsimpStrong)
  also have "... = Ders s (Der c (RL (rerase r)))"
    by (simp add: rder_bder_rerase[symmetric] RL_rder)
  also have "... = Ders (c # s) (RL (rerase r))"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma bnullable_bders_simpStrong_iff_Ders:
  "bnullable (bders_simpStrong r s) \<longleftrightarrow> [] \<in> Ders s (RL (rerase r))"
proof -
  have "bnullable (bders_simpStrong r s) \<longleftrightarrow>
      [] \<in> L (erase (bders_simpStrong r s))"
    by (simp add: bnullable_correctness[symmetric] nullable_correctness)
  also have "... \<longleftrightarrow>
      [] \<in> RL (rerase (bders_simpStrong r s))"
    by (simp add: RL_rerase)
  also have "... \<longleftrightarrow> [] \<in> Ders s (RL (rerase r))"
    by (simp add: RL_rerase_bders_simpStrong)
  finally show ?thesis .
qed

lemma bnullable_bders_simpStrong_iff_member:
  "bnullable (bders_simpStrong r s) \<longleftrightarrow> s \<in> RL (rerase r)"
  by (simp add: bnullable_bders_simpStrong_iff_Ders Ders_def)

lemma bnullable_bders_simpStrong_intern_iff_Posix:
  "bnullable (bders_simpStrong (intern r) s) \<longleftrightarrow> (\<exists>v. s \<in> r \<rightarrow> v)"
proof -
  have "bnullable (bders_simpStrong (intern r) s) \<longleftrightarrow> s \<in> L r"
    by (simp add: bnullable_bders_simpStrong_iff_member RL_rerase)
  also have "... \<longleftrightarrow> (\<exists>v. s \<in> r \<rightarrow> v)"
  proof
    assume "s \<in> L r"
    then have "\<exists>v. lexer r s = Some v \<and> s \<in> r \<rightarrow> v"
      using lexer_correct_Some[of s r] by simp
    then show "\<exists>v. s \<in> r \<rightarrow> v"
      by (elim exE conjE) (intro exI)
  next
    assume "\<exists>v. s \<in> r \<rightarrow> v"
    then obtain v where "s \<in> r \<rightarrow> v" ..
    then show "s \<in> L r"
      by (rule Posix1(1))
  qed
  finally show ?thesis .
qed

lemma bnullable_bders_simpStrong_intern_iff_lexer_defined:
  "bnullable (bders_simpStrong (intern r) s) \<longleftrightarrow> lexer r s \<noteq> None"
proof -
  have strong: "bnullable (bders_simpStrong (intern r) s) \<longleftrightarrow> s \<in> L r"
    by (simp add: bnullable_bders_simpStrong_iff_member RL_rerase)
  show ?thesis
  proof
    assume "bnullable (bders_simpStrong (intern r) s)"
    then have "s \<in> L r"
      using strong by simp
    then show "lexer r s \<noteq> None"
      using lexer_correct_None[of s r] by simp
  next
    assume "lexer r s \<noteq> None"
    then have "s \<in> L r"
      using lexer_correct_None[of s r] by auto
    then show "bnullable (bders_simpStrong (intern r) s)"
      using strong by simp
  qed
qed

lemma bnullable_bders_simpStrong_intern_obtain_lexer:
  assumes "bnullable (bders_simpStrong (intern r) s)"
  obtains v where "lexer r s = Some v" "s \<in> r \<rightarrow> v"
proof -
  have "s \<in> L r"
    using assms
    by (simp add: bnullable_bders_simpStrong_iff_member RL_rerase)
  then have "\<exists>v. lexer r s = Some v \<and> s \<in> r \<rightarrow> v"
    using lexer_correct_Some[of s r] by simp
  then show ?thesis
  proof (elim exE conjE)
    fix v
    assume "lexer r s = Some v" "s \<in> r \<rightarrow> v"
    then show ?thesis
      by (rule that)
  qed
qed

lemma bnullable_bders_simpStrong_intern_unique_Posix:
  assumes "bnullable (bders_simpStrong (intern r) s)"
  shows "\<exists>!v. s \<in> r \<rightarrow> v"
proof -
  obtain v where v: "s \<in> r \<rightarrow> v"
    using assms bnullable_bders_simpStrong_intern_iff_Posix by auto
  show ?thesis
  proof (rule ex1I)
    show "s \<in> r \<rightarrow> v"
      by (rule v)
  next
    fix w
    assume "s \<in> r \<rightarrow> w"
    then show "w = v"
      by (rule Posix_determ[OF _ v])
  qed
qed

fun rxsize :: "rexp \<Rightarrow> nat" where
  "rxsize ZERO = 1"
| "rxsize ONE = 1"
| "rxsize (CH c) = 1"
| "rxsize (SEQ r1 r2) = Suc (rxsize r1 + rxsize r2)"
| "rxsize (ALT r1 r2) = Suc (rxsize r1 + rxsize r2)"
| "rxsize (STAR r) = Suc (rxsize r)"
| "rxsize (NTIMES r n) = Suc n + rxsize r"
| "rxsize (BACKREF4 r1 r2 r3 r4 cs) =
    Suc (rxsize r1 + rxsize r2 + rxsize r3 + rxsize r4)"
| "rxsize (HALF r cs rep) = Suc (rxsize r)"
| "rxsize (RESIDUE cs rep) = 1"

fun rexp_subterms :: "rexp \<Rightarrow> rexp set" where
  "rexp_subterms ZERO = {ZERO}"
| "rexp_subterms ONE = {ONE}"
| "rexp_subterms (CH c) = {CH c}"
| "rexp_subterms (SEQ r1 r2) =
    insert (SEQ r1 r2) (rexp_subterms r1 \<union> rexp_subterms r2)"
| "rexp_subterms (ALT r1 r2) =
    insert (ALT r1 r2) (rexp_subterms r1 \<union> rexp_subterms r2)"
| "rexp_subterms (STAR r) = insert (STAR r) (rexp_subterms r)"
| "rexp_subterms (NTIMES r n) = ((\<lambda>k. NTIMES r k) ` {..n}) \<union> rexp_subterms r"
| "rexp_subterms (BACKREF4 r1 r2 r3 r4 cs) =
    insert (BACKREF4 r1 r2 r3 r4 cs)
      (rexp_subterms r1 \<union> rexp_subterms r2 \<union>
       rexp_subterms r3 \<union> rexp_subterms r4)"
| "rexp_subterms (HALF r cs rep) = insert (HALF r cs rep) (rexp_subterms r)"
| "rexp_subterms (RESIDUE cs rep) = {RESIDUE cs rep}"

lemma finite_rexp_subterms [simp]:
  "finite (rexp_subterms r)"
  by (induct r) simp_all

lemma card_rexp_subterms_le_rxsize:
  "card (rexp_subterms r) \<le> rxsize r"
proof (induct r)
  case ZERO
  then show ?case by simp
next
  case ONE
  then show ?case by simp
next
  case (CH x)
  then show ?case by simp
next
  case (SEQ r1 r2)
  have "card (rexp_subterms (SEQ r1 r2)) \<le>
      Suc (card (rexp_subterms r1 \<union> rexp_subterms r2))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> Suc (card (rexp_subterms r1) + card (rexp_subterms r2))"
    using card_Un_le by simp
  also have "... \<le> rxsize (SEQ r1 r2)"
    using SEQ by simp
  finally show ?case .
next
  case (ALT r1 r2)
  have "card (rexp_subterms (ALT r1 r2)) \<le>
      Suc (card (rexp_subterms r1 \<union> rexp_subterms r2))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> Suc (card (rexp_subterms r1) + card (rexp_subterms r2))"
    using card_Un_le by simp
  also have "... \<le> rxsize (ALT r1 r2)"
    using ALT by simp
  finally show ?case .
next
  case (STAR r)
  have "card (rexp_subterms (STAR r)) \<le> Suc (card (rexp_subterms r))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> rxsize (STAR r)"
    using STAR by simp
  finally show ?case .
next
  case (NTIMES r n)
  have "card (rexp_subterms (NTIMES r n)) \<le>
      card (((\<lambda>k. NTIMES r k) ` {..n}) \<union> rexp_subterms r)"
    by simp
  also have "... \<le> card ((\<lambda>k. NTIMES r k) ` {..n}) + card (rexp_subterms r)"
    by (rule card_Un_le)
  also have "... \<le> Suc n + card (rexp_subterms r)"
  proof -
    have "card ((\<lambda>k. NTIMES r k) ` {..n}) \<le> card ({..n})"
      by (rule card_image_le) simp
    then show ?thesis
      by simp
  qed
  also have "... \<le> Suc n + rxsize r"
    using NTIMES by simp
  also have "... = rxsize (NTIMES r n)"
    by simp
  finally show ?case .
next
  case (BACKREF4 r1 r2 r3 r4 cs)
  have "card (rexp_subterms (BACKREF4 r1 r2 r3 r4 cs)) \<le>
      Suc (card (rexp_subterms r1 \<union> rexp_subterms r2 \<union>
        rexp_subterms r3 \<union> rexp_subterms r4))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le>
      Suc (card (rexp_subterms r1) + card (rexp_subterms r2) +
        card (rexp_subterms r3) + card (rexp_subterms r4))"
    using card_Un4_le[of "rexp_subterms r1" "rexp_subterms r2"
        "rexp_subterms r3" "rexp_subterms r4"] by simp
  also have "... \<le> rxsize (BACKREF4 r1 r2 r3 r4 cs)"
    using BACKREF4 by simp
  finally show ?case .
next
  case (HALF r cs rep)
  have "card (rexp_subterms (HALF r cs rep)) \<le> Suc (card (rexp_subterms r))"
    by (simp add: card_insert_le_Suc)
  also have "... \<le> rxsize (HALF r cs rep)"
    using HALF by simp
  finally show ?case .
next
  case (RESIDUE cs rep)
  then show ?case by simp
qed

lemma rexp_subterms_root [simp]:
  "r \<in> rexp_subterms r"
  by (induct r) simp_all

lemma rexp_subterms_ALT_children:
  assumes "ALT r1 r2 \<in> rexp_subterms root"
  shows "r1 \<in> rexp_subterms root" "r2 \<in> rexp_subterms root"
  using assms by (induct root) auto

lemma rexp_subterms_SEQ_children:
  assumes "SEQ r1 r2 \<in> rexp_subterms root"
  shows "r1 \<in> rexp_subterms root" "r2 \<in> rexp_subterms root"
  using assms by (induct root) auto

lemma rexp_subterms_STAR_child:
  assumes "STAR q \<in> rexp_subterms root"
  shows "q \<in> rexp_subterms root"
  using assms by (induct root) auto

lemma rexp_subterms_NTIMES_child:
  assumes "NTIMES q n \<in> rexp_subterms root"
  shows "q \<in> rexp_subterms root"
  using assms by (induct root) auto

lemma rexp_subterms_NTIMES_countdown:
  assumes "NTIMES q n \<in> rexp_subterms root" "m \<le> n"
  shows "NTIMES q m \<in> rexp_subterms root"
  using assms by (induct root) auto

definition rexp_span_states :: "rexp \<Rightarrow> string \<Rightarrow> (rexp * nat * nat) set" where
  "rexp_span_states r s =
    (\<lambda>(q, (i, j)). (q, i, j)) ` (rexp_subterms r \<times> ({..length s} \<times> {..length s}))"

lemma finite_rexp_span_states [simp]:
  "finite (rexp_span_states r s)"
  by (simp add: rexp_span_states_def)

lemma rexp_span_statesI:
  assumes "q \<in> rexp_subterms r" "i \<le> length s" "j \<le> length s"
  shows "(q, i, j) \<in> rexp_span_states r s"
  using assms by (auto simp: rexp_span_states_def)

lemma rexp_span_statesE:
  assumes "(q, i, j) \<in> rexp_span_states r s"
  obtains "q \<in> rexp_subterms r" "i \<le> length s" "j \<le> length s"
  using assms by (auto simp: rexp_span_states_def)

lemma card_rexp_span_states_bound:
  "card (rexp_span_states r s) \<le> rxsize r * Suc (length s) * Suc (length s)"
proof -
  have "card (rexp_span_states r s) \<le>
      card (rexp_subterms r \<times> ({..length s} \<times> {..length s}))"
    by (simp add: rexp_span_states_def card_image_le)
  also have "... = card (rexp_subterms r) * Suc (length s) * Suc (length s)"
    by (simp add: algebra_simps)
  also have "... \<le> rxsize r * Suc (length s) * Suc (length s)"
    using card_rexp_subterms_le_rxsize[of r]
    by (intro mult_mono; simp)
  finally show ?thesis .
qed

definition rexp_span_split_probes :: "rexp \<Rightarrow> string \<Rightarrow> (rexp * nat * nat * nat) set" where
  "rexp_span_split_probes r s =
    (\<lambda>(q, (i, (k, j))). (q, i, k, j)) `
      (rexp_subterms r \<times> ({..length s} \<times> ({..length s} \<times> {..length s})))"

lemma finite_rexp_span_split_probes [simp]:
  "finite (rexp_span_split_probes r s)"
  by (simp add: rexp_span_split_probes_def)

lemma rexp_span_split_probesI:
  assumes "q \<in> rexp_subterms r"
    and "i \<le> length s"
    and "k \<le> length s"
    and "j \<le> length s"
  shows "(q, i, k, j) \<in> rexp_span_split_probes r s"
  using assms by (auto simp: rexp_span_split_probes_def)

lemma rexp_span_split_probesE:
  assumes "(q, i, k, j) \<in> rexp_span_split_probes r s"
  obtains "q \<in> rexp_subterms r" "i \<le> length s" "k \<le> length s" "j \<le> length s"
  using assms by (auto simp: rexp_span_split_probes_def)

lemma card_rexp_span_split_probes_bound:
  "card (rexp_span_split_probes r s) \<le>
    rxsize r * Suc (length s) * Suc (length s) * Suc (length s)"
proof -
  have "card (rexp_span_split_probes r s) \<le>
      card (rexp_subterms r \<times> ({..length s} \<times> ({..length s} \<times> {..length s})))"
    by (simp add: rexp_span_split_probes_def card_image_le)
  also have "... =
      card (rexp_subterms r) * Suc (length s) * Suc (length s) * Suc (length s)"
    by (simp add: algebra_simps)
  also have "... \<le>
      rxsize r * Suc (length s) * Suc (length s) * Suc (length s)"
    using card_rexp_subterms_le_rxsize[of r]
    by (intro mult_mono; simp)
  finally show ?thesis .
qed

definition rexp_span_all_split_probes :: "rexp \<Rightarrow> string \<Rightarrow> (rexp * nat * nat * nat) set" where
  "rexp_span_all_split_probes r s =
    {(q, i, k, j). q \<in> rexp_subterms r \<and> i \<le> k \<and> k \<le> j \<and> j \<le> length s}"

lemma finite_rexp_span_all_split_probes [simp]:
  "finite (rexp_span_all_split_probes r s)"
proof -
  have "rexp_span_all_split_probes r s \<subseteq> rexp_span_split_probes r s"
    by (auto simp: rexp_span_all_split_probes_def intro: rexp_span_split_probesI)
  then show ?thesis
    using finite_rexp_span_split_probes finite_subset by blast
qed

lemma rexp_span_all_split_probes_subset:
  "rexp_span_all_split_probes r s \<subseteq> rexp_span_split_probes r s"
  by (auto simp: rexp_span_all_split_probes_def intro: rexp_span_split_probesI)

lemma rexp_span_all_split_probesI:
  assumes "q \<in> rexp_subterms r"
    and "i \<le> k"
    and "k \<le> j"
    and "j \<le> length s"
  shows "(q, i, k, j) \<in> rexp_span_all_split_probes r s"
  using assms by (auto simp: rexp_span_all_split_probes_def)

lemma rexp_span_all_split_probesE:
  assumes "(q, i, k, j) \<in> rexp_span_all_split_probes r s"
  obtains "q \<in> rexp_subterms r" "i \<le> k" "k \<le> j" "j \<le> length s"
  using assms by (auto simp: rexp_span_all_split_probes_def)

lemma card_rexp_span_all_split_probes_bound:
  "card (rexp_span_all_split_probes r s) \<le>
    rxsize r * Suc (length s) * Suc (length s) * Suc (length s)"
proof -
  have "card (rexp_span_all_split_probes r s) \<le>
      card (rexp_span_split_probes r s)"
    using rexp_span_all_split_probes_subset
    by (meson card_mono finite_rexp_span_split_probes)
  also have "... \<le>
      rxsize r * Suc (length s) * Suc (length s) * Suc (length s)"
    by (rule card_rexp_span_split_probes_bound)
  finally show ?thesis .
qed

definition rexp_span_posix :: "rexp \<Rightarrow> string \<Rightarrow> (rexp * nat * nat * val) set" where
  "rexp_span_posix r s =
    {(q, i, j, v).
      q \<in> rexp_subterms r \<and> i \<le> j \<and> j \<le> length s \<and>
      rslice s i j \<in> q \<rightarrow> v}"

definition rexp_span_posix_states :: "rexp \<Rightarrow> string \<Rightarrow> (rexp * nat * nat) set" where
  "rexp_span_posix_states r s =
    {(q, i, j). \<exists>v. (q, i, j, v) \<in> rexp_span_posix r s}"

lemma rexp_span_posixI:
  assumes "q \<in> rexp_subterms r"
    and "i \<le> j"
    and "j \<le> length s"
    and "rslice s i j \<in> q \<rightarrow> v"
  shows "(q, i, j, v) \<in> rexp_span_posix r s"
  using assms by (auto simp: rexp_span_posix_def)

lemma rexp_span_posixE:
  assumes "(q, i, j, v) \<in> rexp_span_posix r s"
  obtains "q \<in> rexp_subterms r" "i \<le> j" "j \<le> length s"
    "rslice s i j \<in> q \<rightarrow> v"
  using assms by (auto simp: rexp_span_posix_def)

lemma rexp_span_posix_root_iff:
  "(r, 0, length s, v) \<in> rexp_span_posix r s \<longleftrightarrow> s \<in> r \<rightarrow> v"
  by (auto simp: rexp_span_posix_def)

lemma rexp_span_posix_ONE_emptyI:
  assumes "ONE \<in> rexp_subterms r" "i \<le> length s"
  shows "(ONE, i, i, Void) \<in> rexp_span_posix r s"
proof -
  have "rslice s i i \<in> ONE \<rightarrow> Void"
    using assms by (simp add: Posix_ONE)
  then show ?thesis
    by (rule rexp_span_posixI[OF assms(1) order_refl assms(2)])
qed

lemma rexp_span_posix_CHI:
  assumes "CH c \<in> rexp_subterms r"
    and "i \<le> j"
    and "j \<le> length s"
    and "rslice s i j = [c]"
  shows "(CH c, i, j, Char c) \<in> rexp_span_posix r s"
proof -
  have "rslice s i j \<in> CH c \<rightarrow> Char c"
    using assms by (simp add: Posix_CH)
  then show ?thesis
    by (rule rexp_span_posixI[OF assms(1-3)])
qed

lemma rexp_span_posix_ALT1I:
  assumes sub: "ALT r1 r2 \<in> rexp_subterms root"
    and left: "(r1, i, j, v) \<in> rexp_span_posix root s"
  shows "(ALT r1 r2, i, j, Left v) \<in> rexp_span_posix root s"
proof -
  have ij: "i \<le> j"
    and jl: "j \<le> length s"
    and pos: "rslice s i j \<in> r1 \<rightarrow> v"
    using left by (auto simp: rexp_span_posix_def)
  have "rslice s i j \<in> ALT r1 r2 \<rightarrow> Left v"
    using pos by (rule Posix_ALT1)
  then show ?thesis
    by (rule rexp_span_posixI[OF sub ij jl])
qed

lemma rexp_span_posix_ALT2I:
  assumes sub: "ALT r1 r2 \<in> rexp_subterms root"
    and right: "(r2, i, j, v) \<in> rexp_span_posix root s"
    and no_left: "rslice s i j \<notin> L r1"
  shows "(ALT r1 r2, i, j, Right v) \<in> rexp_span_posix root s"
proof -
  have ij: "i \<le> j"
    and jl: "j \<le> length s"
    and pos: "rslice s i j \<in> r2 \<rightarrow> v"
    using right by (auto simp: rexp_span_posix_def)
  have "rslice s i j \<in> ALT r1 r2 \<rightarrow> Right v"
    using pos no_left by (rule Posix_ALT2)
  then show ?thesis
    by (rule rexp_span_posixI[OF sub ij jl])
qed

lemma rexp_span_posix_SEQI:
  assumes split: "(SEQ r1 r2, i, k, j) \<in> rexp_span_all_split_probes root s"
    and left: "(r1, i, k, v1) \<in> rexp_span_posix root s"
    and right: "(r2, k, j, v2) \<in> rexp_span_posix root s"
    and longest:
      "\<not>(\<exists>s3 s4. s3 \<noteq> [] \<and> s3 @ s4 = rslice s k j \<and>
        (rslice s i k @ s3) \<in> L r1 \<and> s4 \<in> L r2)"
  shows "(SEQ r1 r2, i, j, Seq v1 v2) \<in> rexp_span_posix root s"
proof -
  obtain sub ik kj jl where
    sub: "SEQ r1 r2 \<in> rexp_subterms root" and
    ik: "i \<le> k" and kj: "k \<le> j" and jl: "j \<le> length s"
    using split by (rule rexp_span_all_split_probesE)
  have left_pos: "rslice s i k \<in> r1 \<rightarrow> v1"
    using left by (auto simp: rexp_span_posix_def)
  have right_pos: "rslice s k j \<in> r2 \<rightarrow> v2"
    using right by (auto simp: rexp_span_posix_def)
  have ij: "i \<le> j"
    using ik kj by simp
  have slice: "rslice s i j = rslice s i k @ rslice s k j"
    by (rule rslice_append[OF ik kj jl])
  have "(rslice s i k @ rslice s k j) \<in> SEQ r1 r2 \<rightarrow> Seq v1 v2"
    by (rule Posix_SEQ[OF left_pos right_pos longest])
  then have "rslice s i j \<in> SEQ r1 r2 \<rightarrow> Seq v1 v2"
    by (simp add: slice)
  then show ?thesis
    by (rule rexp_span_posixI[OF sub ij jl])
qed

lemma rexp_span_posix_STAR_emptyI:
  assumes "STAR q \<in> rexp_subterms r" "i \<le> length s"
  shows "(STAR q, i, i, Stars []) \<in> rexp_span_posix r s"
proof -
  have "rslice s i i \<in> STAR q \<rightarrow> Stars []"
    using assms by (simp add: Posix_STAR2)
  then show ?thesis
    by (rule rexp_span_posixI[OF assms(1) order_refl assms(2)])
qed

lemma rexp_span_posix_STAR_stepI:
  assumes split: "(STAR q, i, k, j) \<in> rexp_span_all_split_probes root s"
    and head: "(q, i, k, v) \<in> rexp_span_posix root s"
    and tail: "(STAR q, k, j, Stars vs) \<in> rexp_span_posix root s"
    and nonempty: "flat v \<noteq> []"
    and longest:
      "\<not>(\<exists>s3 s4. s3 \<noteq> [] \<and> s3 @ s4 = rslice s k j \<and>
        (rslice s i k @ s3) \<in> L q \<and> s4 \<in> L (STAR q))"
  shows "(STAR q, i, j, Stars (v # vs)) \<in> rexp_span_posix root s"
proof -
  obtain sub ik kj jl where
    sub: "STAR q \<in> rexp_subterms root" and
    ik: "i \<le> k" and kj: "k \<le> j" and jl: "j \<le> length s"
    using split by (rule rexp_span_all_split_probesE)
  have head_pos: "rslice s i k \<in> q \<rightarrow> v"
    using head by (auto simp: rexp_span_posix_def)
  have tail_pos: "rslice s k j \<in> STAR q \<rightarrow> Stars vs"
    using tail by (auto simp: rexp_span_posix_def)
  have ij: "i \<le> j"
    using ik kj by simp
  have slice: "rslice s i j = rslice s i k @ rslice s k j"
    by (rule rslice_append[OF ik kj jl])
  have "(rslice s i k @ rslice s k j) \<in> STAR q \<rightarrow> Stars (v # vs)"
    by (rule Posix_STAR1[OF head_pos tail_pos nonempty longest])
  then have "rslice s i j \<in> STAR q \<rightarrow> Stars (v # vs)"
    by (simp add: slice)
  then show ?thesis
    by (rule rexp_span_posixI[OF sub ij jl])
qed

lemma rexp_span_posix_NTIMES_zero_emptyI:
  assumes "NTIMES q 0 \<in> rexp_subterms r" "i \<le> length s"
  shows "(NTIMES q 0, i, i, Stars []) \<in> rexp_span_posix r s"
proof -
  have "rslice s i i \<in> NTIMES q 0 \<rightarrow> Stars []"
    using assms by (simp add: Posix_NTIMES2)
  then show ?thesis
    by (rule rexp_span_posixI[OF assms(1) order_refl assms(2)])
qed

lemma rexp_span_posix_NTIMES_SucI:
  assumes split: "(NTIMES q (Suc n), i, k, j) \<in> rexp_span_all_split_probes root s"
    and head: "(q, i, k, v) \<in> rexp_span_posix root s"
    and tail: "(NTIMES q n, k, j, Stars vs) \<in> rexp_span_posix root s"
    and nonempty: "flat v \<noteq> []"
    and longest:
      "\<not>(\<exists>s3 s4. s3 \<noteq> [] \<and> s3 @ s4 = rslice s k j \<and>
        (rslice s i k @ s3) \<in> L q \<and> s4 \<in> L (NTIMES q n))"
  shows "(NTIMES q (Suc n), i, j, Stars (v # vs)) \<in> rexp_span_posix root s"
proof -
  obtain sub ik kj jl where
    sub: "NTIMES q (Suc n) \<in> rexp_subterms root" and
    ik: "i \<le> k" and kj: "k \<le> j" and jl: "j \<le> length s"
    using split by (rule rexp_span_all_split_probesE)
  have head_pos: "rslice s i k \<in> q \<rightarrow> v"
    using head by (auto simp: rexp_span_posix_def)
  have tail_pos: "rslice s k j \<in> NTIMES q n \<rightarrow> Stars vs"
    using tail by (auto simp: rexp_span_posix_def)
  have tail_pos': "rslice s k j \<in> NTIMES q (Suc n - 1) \<rightarrow> Stars vs"
    using tail_pos by simp
  have longest':
      "\<not>(\<exists>s3 s4. s3 \<noteq> [] \<and> s3 @ s4 = rslice s k j \<and>
        (rslice s i k @ s3) \<in> L q \<and> s4 \<in> L (NTIMES q (Suc n - 1)))"
    using longest by simp
  have positive: "0 < Suc n"
    by simp
  have ij: "i \<le> j"
    using ik kj by simp
  have slice: "rslice s i j = rslice s i k @ rslice s k j"
    by (rule rslice_append[OF ik kj jl])
  have "(rslice s i k @ rslice s k j) \<in> NTIMES q (Suc n) \<rightarrow> Stars (v # vs)"
    by (rule Posix_NTIMES1[OF head_pos tail_pos' nonempty positive longest'])
  then have "rslice s i j \<in> NTIMES q (Suc n) \<rightarrow> Stars (v # vs)"
    by (simp add: slice)
  then show ?thesis
    by (rule rexp_span_posixI[OF sub ij jl])
qed

lemma rexp_span_posix_ALT1E:
  assumes entry: "(ALT r1 r2, i, j, Left v) \<in> rexp_span_posix root s"
  obtains "(r1, i, j, v) \<in> rexp_span_posix root s"
proof -
  have sub: "ALT r1 r2 \<in> rexp_subterms root"
    and ij: "i \<le> j"
    and jl: "j \<le> length s"
    and pos: "rslice s i j \<in> ALT r1 r2 \<rightarrow> Left v"
    using entry by (auto simp: rexp_span_posix_def)
  have child: "r1 \<in> rexp_subterms root"
    using sub by (rule rexp_subterms_ALT_children(1))
  have left_pos: "rslice s i j \<in> r1 \<rightarrow> v"
    using pos by (auto elim!: Posix_elims(4))
  have "(r1, i, j, v) \<in> rexp_span_posix root s"
    by (rule rexp_span_posixI[OF child ij jl left_pos])
  then show ?thesis
    by (rule that)
qed

lemma rexp_span_posix_ALT2E:
  assumes entry: "(ALT r1 r2, i, j, Right v) \<in> rexp_span_posix root s"
  obtains "(r2, i, j, v) \<in> rexp_span_posix root s" "rslice s i j \<notin> L r1"
proof -
  have sub: "ALT r1 r2 \<in> rexp_subterms root"
    and ij: "i \<le> j"
    and jl: "j \<le> length s"
    and pos: "rslice s i j \<in> ALT r1 r2 \<rightarrow> Right v"
    using entry by (auto simp: rexp_span_posix_def)
  have child: "r2 \<in> rexp_subterms root"
    using sub by (rule rexp_subterms_ALT_children(2))
  have right_pos: "rslice s i j \<in> r2 \<rightarrow> v"
    and no_left: "rslice s i j \<notin> L r1"
    using pos by (auto elim!: Posix_elims(4))
  have "(r2, i, j, v) \<in> rexp_span_posix root s"
    by (rule rexp_span_posixI[OF child ij jl right_pos])
  then show ?thesis
    using no_left by (rule that)
qed

lemma rexp_span_posix_SEQE:
  assumes entry: "(SEQ r1 r2, i, j, Seq v1 v2) \<in> rexp_span_posix root s"
  obtains k where
    "(SEQ r1 r2, i, k, j) \<in> rexp_span_all_split_probes root s"
    "(r1, i, k, v1) \<in> rexp_span_posix root s"
    "(r2, k, j, v2) \<in> rexp_span_posix root s"
    "\<not>(\<exists>s3 s4. s3 \<noteq> [] \<and> s3 @ s4 = rslice s k j \<and>
      (rslice s i k @ s3) \<in> L r1 \<and> s4 \<in> L r2)"
proof -
  have sub: "SEQ r1 r2 \<in> rexp_subterms root"
    and ij: "i \<le> j"
    and jl: "j \<le> length s"
    and pos: "rslice s i j \<in> SEQ r1 r2 \<rightarrow> Seq v1 v2"
    using entry by (auto simp: rexp_span_posix_def)
  obtain s1 s2 where
    eq: "rslice s i j = s1 @ s2"
    and left_pos: "s1 \<in> r1 \<rightarrow> v1"
    and right_pos: "s2 \<in> r2 \<rightarrow> v2"
    and longest_raw:
      "\<not>(\<exists>s3 s4. s3 \<noteq> [] \<and> s3 @ s4 = s2 \<and>
        (s1 @ s3) \<in> L r1 \<and> s4 \<in> L r2)"
    using pos by (auto elim!: Posix_elims(5))
  define k where "k = i + length s1"
  have ik: "i \<le> k"
    and kj: "k \<le> j"
    and left_slice: "rslice s i k = s1"
    and right_slice: "rslice s k j = s2"
    using rslice_prefix_split[OF ij jl eq k_def] by blast+
  have left_child: "r1 \<in> rexp_subterms root"
    using sub by (rule rexp_subterms_SEQ_children(1))
  have right_child: "r2 \<in> rexp_subterms root"
    using sub by (rule rexp_subterms_SEQ_children(2))
  have k_len: "k \<le> length s"
    using kj jl by simp
  have split: "(SEQ r1 r2, i, k, j) \<in> rexp_span_all_split_probes root s"
    by (rule rexp_span_all_split_probesI[OF sub ik kj jl])
  have left: "(r1, i, k, v1) \<in> rexp_span_posix root s"
    using left_pos left_slice by (intro rexp_span_posixI[OF left_child ik k_len]) simp
  have right: "(r2, k, j, v2) \<in> rexp_span_posix root s"
    using right_pos right_slice by (intro rexp_span_posixI[OF right_child kj jl]) simp
  have longest:
    "\<not>(\<exists>s3 s4. s3 \<noteq> [] \<and> s3 @ s4 = rslice s k j \<and>
      (rslice s i k @ s3) \<in> L r1 \<and> s4 \<in> L r2)"
    using longest_raw left_slice right_slice by simp
  show ?thesis
    by (rule that[OF split left right longest])
qed

lemma rexp_span_posix_states_subset:
  "rexp_span_posix_states r s \<subseteq> rexp_span_states r s"
proof
  fix x
  assume "x \<in> rexp_span_posix_states r s"
  then obtain q i j v where
    x: "x = (q, i, j)" and
    entry: "(q, i, j, v) \<in> rexp_span_posix r s"
    by (auto simp: rexp_span_posix_states_def)
  have sub: "q \<in> rexp_subterms r"
    and ij: "i \<le> j"
    and jl: "j \<le> length s"
    using entry by (auto simp: rexp_span_posix_def)
  have il: "i \<le> length s"
    using ij jl by simp
  show "x \<in> rexp_span_states r s"
    using x rexp_span_statesI[OF sub il jl] by simp
qed

lemma finite_rexp_span_posix_states [simp]:
  "finite (rexp_span_posix_states r s)"
  using rexp_span_posix_states_subset finite_rexp_span_states finite_subset by blast

lemma card_rexp_span_posix_states_bound:
  "card (rexp_span_posix_states r s) \<le>
    rxsize r * Suc (length s) * Suc (length s)"
proof -
  have "card (rexp_span_posix_states r s) \<le> card (rexp_span_states r s)"
    using rexp_span_posix_states_subset
    by (meson card_mono finite_rexp_span_states)
  also have "... \<le> rxsize r * Suc (length s) * Suc (length s)"
    by (rule card_rexp_span_states_bound)
  finally show ?thesis .
qed

lemma bnullable_bders_simpStrong_intern_iff_rexp_span_posix_root:
  "bnullable (bders_simpStrong (intern r) s) \<longleftrightarrow>
    (\<exists>v. (r, 0, length s, v) \<in> rexp_span_posix r s)"
  by (simp add: bnullable_bders_simpStrong_intern_iff_Posix
      rexp_span_posix_root_iff)

lemma rexp_span_posix_root_unique:
  assumes "(r, 0, length s, v) \<in> rexp_span_posix r s"
    and "(r, 0, length s, w) \<in> rexp_span_posix r s"
  shows "v = w"
proof -
  have v: "s \<in> r \<rightarrow> v"
    using assms(1) by (simp add: rexp_span_posix_root_iff)
  have w: "s \<in> r \<rightarrow> w"
    using assms(2) by (simp add: rexp_span_posix_root_iff)
  show ?thesis
    by (rule Posix_determ[OF v w])
qed

lemma bnullable_bders_simpStrong_intern_unique_rexp_span_posix_root:
  assumes "bnullable (bders_simpStrong (intern r) s)"
  shows "\<exists>!v. (r, 0, length s, v) \<in> rexp_span_posix r s"
proof -
  obtain v where v: "(r, 0, length s, v) \<in> rexp_span_posix r s"
    using assms bnullable_bders_simpStrong_intern_iff_rexp_span_posix_root by auto
  show ?thesis
  proof (rule ex1I)
    show "(r, 0, length s, v) \<in> rexp_span_posix r s"
      by (rule v)
  next
    fix w
    assume "(r, 0, length s, w) \<in> rexp_span_posix r s"
    then show "w = v"
      by (rule rexp_span_posix_root_unique[OF _ v])
  qed
qed

lemma RL_rerase_bders_simpCubic:
  "RL (rerase (bders_simpCubic r s)) = Ders s (RL (rerase r))"
proof (induct s arbitrary: r)
  case Nil
  then show ?case
    by (simp add: Ders_def)
next
  case (Cons c s)
  have "RL (rerase (bders_simpCubic r (c # s))) =
      RL (rerase (bders_simpCubic (bsimpCubic (bder c r)) s))"
    by simp
  also have "... = Ders s (RL (rerase (bsimpCubic (bder c r))))"
    by (rule Cons.hyps)
  also have "... = Ders s (RL (rerase (bder c r)))"
    by (simp add: RL_rerase_bsimpCubic)
  also have "... = Ders s (Der c (RL (rerase r)))"
    by (simp add: rder_bder_rerase[symmetric] RL_rder)
  also have "... = Ders (c # s) (RL (rerase r))"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma RL_rerase_bders_simpStrong_rders_simpStrong:
  "RL (rerase (bders_simpStrong r s)) =
    RL (rders_simpStrong (rerase r) s)"
  by (simp add: RL_rerase_bders_simpStrong RL_rders_simpStrong)

lemma eq1_member_rerase:
  "eq1_member r rs \<longleftrightarrow> rerase r \<in> set (map rerase rs)"
proof (induct rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
    using Cons.hyps by (simp add: eq1_rerase)
qed

lemma map_rerase_prune_eq1_against:
  "map rerase (prune_eq1_against covered rs) =
    rprune_eq_against (map rerase covered) (map rerase rs)"
proof (induct rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  show ?case
    by (simp add: Cons.hyps eq1_member_rerase)
qed

lemma RL_rerase_bsimpStrong_prune_pair_with_earlier:
  "RL (rerase earlier) \<union>
    RL (rerase (bsimpStrong_prune_pair earlier later)) =
    RL (rerase earlier) \<union>
    RL (rsimpStrong_prune_pair (rerase earlier) (rerase later))"
proof -
  have left:
    "RL (rerase earlier) \<union>
      RL (rerase (bsimpStrong_prune_pair earlier later)) =
      RL (rerase earlier) \<union> RL (rerase later)"
    using L_bsimpStrong_prune_pair_cover[of earlier later]
    by (simp add: RL_rerase)
  have right:
    "RL (rerase earlier) \<union>
      RL (rsimpStrong_prune_pair (rerase earlier) (rerase later)) =
      RL (rerase earlier) \<union> RL (rerase later)"
    by (rule RL_rsimpStrong_prune_pair_with_earlier)
  show ?thesis
    using left right by simp
qed

lemma bsimpStrong_prune_pair_exact_rerase_counterexample:
  assumes "a \<noteq> b"
  shows
    "rerase
      (bsimpStrong_prune_pair
        (ASEQ [] (AALTs [] [ACHAR [] b]) (ACHAR [] c))
        (ASEQ [] (AALTs [] [ACHAR [] a, ACHAR [] a]) (ACHAR [] c))) \<noteq>
     rsimpStrong_prune_pair
      (rerase (ASEQ [] (AALTs [] [ACHAR [] b]) (ACHAR [] c)))
      (rerase (ASEQ [] (AALTs [] [ACHAR [] a, ACHAR [] a]) (ACHAR [] c)))"
  using assms
  by (simp add: bsimpStrong_prune_pair_def rsimpStrong_prune_pair_def
      bsimp7_ASEQ_atom_def rsimp7_SEQ_atom_def)

lemma legacy_rerase_flts:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
  shows "\<forall>r \<in> set (flts rs). legacy_rrexp (rerase r)"
  using assms
  by (induct rs rule: flts.induct) (auto simp add: rerase_fuse)

lemma legacy_rerase_distinctWith:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
  shows "\<forall>r \<in> set (distinctWith rs eq acc). legacy_rrexp (rerase r)"
  using assms
  by (induct rs arbitrary: acc) auto

lemma legacy_rerase_prune_eq1_against:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
  shows "\<forall>r \<in> set (prune_eq1_against covered rs). legacy_rrexp (rerase r)"
  using assms
  by (induct rs) auto

lemma legacy_rerase_bsimp_AALTs:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
  shows "legacy_rrexp (rerase (bsimp_AALTs bs rs))"
proof (cases rs)
  case Nil
  then show ?thesis
    by simp
next
  case (Cons r rest)
  have rs_def: "rs = r # rest"
    using Cons by simp
  show ?thesis
  proof (cases rest)
    case Nil
    then show ?thesis
      using rs_def assms by (simp add: rerase_fuse)
  next
    case (Cons q qs)
    then show ?thesis
      using rs_def assms by simp
  qed
qed

lemma legacy_rerase_bsimpStrong_prune_pair:
  assumes "legacy_rrexp (rerase later)"
  shows "legacy_rrexp (rerase (bsimpStrong_prune_pair earlier later))"
proof -
  consider
    (shared) bs1 lbs lrs k1 bs2 rbs rrs k2 where
      "earlier = ASEQ bs1 (AALTs lbs lrs) k1"
      "later = ASEQ bs2 (AALTs rbs rrs) k2"
      "k1 ~1 k2"
  | (other) "\<not> (\<exists>bs1 lbs lrs k1 bs2 rbs rrs k2.
      earlier = ASEQ bs1 (AALTs lbs lrs) k1 \<and>
      later = ASEQ bs2 (AALTs rbs rrs) k2 \<and> k1 ~1 k2)"
    by blast
  then show ?thesis
  proof cases
    case (shared bs1 lbs lrs k1 bs2 rbs rrs k2)
    have rows: "\<forall>r \<in> set rrs. legacy_rrexp (rerase r)"
      using assms shared by simp
    have tail: "legacy_rrexp (rerase k2)"
      using assms shared by simp
    have pruned:
      "\<forall>r \<in> set (prune_eq1_against lrs rrs). legacy_rrexp (rerase r)"
      by (rule legacy_rerase_prune_eq1_against[OF rows])
    have left:
      "legacy_rrexp (rerase (bsimp_AALTs rbs (prune_eq1_against lrs rrs)))"
      by (rule legacy_rerase_bsimp_AALTs[OF pruned])
    show ?thesis
      using shared left tail
      by (simp add: bsimpStrong_prune_pair_def
          rerase_bsimp7_ASEQ_atom legacy_rsimp7_SEQ_atom)
  next
    case other
    have "bsimpStrong_prune_pair earlier later = later"
      using other
      unfolding bsimpStrong_prune_pair_def
      by (cases earlier; cases later) (auto split: arexp.splits)
    then show ?thesis
      using assms by simp
  qed
qed

lemma legacy_rerase_bsimpStrong_prune_against_rows:
  assumes "legacy_rrexp (rerase r)"
  shows "legacy_rrexp (rerase (bsimpStrong_prune_against_rows seen r))"
  using assms
proof (induct seen arbitrary: r)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  have nxt: "legacy_rrexp (rerase (bsimpStrong_prune_pair x r))"
    by (rule legacy_rerase_bsimpStrong_prune_pair[OF Cons.prems])
  show ?case
    by (simp add: Cons.hyps[OF nxt])
qed

lemma legacy_rerase_bsimpStrong_prune_rows_acc:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
  shows "\<forall>r \<in> set (bsimpStrong_prune_rows_acc seen rs).
    legacy_rrexp (rerase r)"
  using assms
proof (induct rs arbitrary: seen)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  let ?r' = "bsimpStrong_prune_against_rows seen r"
  have head: "legacy_rrexp (rerase ?r')"
    by (rule legacy_rerase_bsimpStrong_prune_against_rows) (use Cons.prems in simp)
  have tail:
    "\<forall>q \<in> set (bsimpStrong_prune_rows_acc (?r' # seen) rs).
      legacy_rrexp (rerase q)"
    by (rule Cons.hyps) (use Cons.prems in simp)
  show ?case
    using head tail by (simp add: Let_def)
qed

lemma legacy_rerase_bsimpStrong_prune_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
  shows "\<forall>r \<in> set (bsimpStrong_prune_rows rs). legacy_rrexp (rerase r)"
  using legacy_rerase_bsimpStrong_prune_rows_acc[OF assms, of "[]"]
  by (simp add: bsimpStrong_prune_rows_def)

lemma legacy_rerase_bsimpStrong_AALTs:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
  shows "legacy_rrexp (rerase (bsimpStrong_AALTs bs rs))"
proof -
  have rows: "\<forall>r \<in> set (bsimpStrong_prune_rows rs). legacy_rrexp (rerase r)"
    by (rule legacy_rerase_bsimpStrong_prune_rows[OF assms])
  have flat:
    "\<forall>r \<in> set (flts (bsimpStrong_prune_rows rs)).
      legacy_rrexp (rerase r)"
    by (rule legacy_rerase_flts[OF rows])
  have distinct:
    "\<forall>r \<in> set (distinctWith (flts (bsimpStrong_prune_rows rs)) eq1 {}).
      legacy_rrexp (rerase r)"
    by (rule legacy_rerase_distinctWith[OF flat])
  show ?thesis
    unfolding bsimpStrong_AALTs_def
    by (rule legacy_rerase_bsimp_AALTs[OF distinct])
qed

lemma legacy_rerase_bsimpStrong:
  assumes "legacy_rrexp (rerase r)"
  shows "legacy_rrexp (rerase (bsimpStrong r))"
  using assms
proof (induct r)
  case AZERO
  then show ?case by simp
next
  case (AONE x)
  then show ?case by simp
next
  case (ACHAR x1 x2)
  then show ?case by simp
next
  case (ASEQ bs r1 r2)
  have left: "legacy_rrexp (rerase (bsimpStrong r1))"
    by (rule ASEQ.hyps(1)) (use ASEQ.prems in simp)
  have right: "legacy_rrexp (rerase (bsimpStrong r2))"
    by (rule ASEQ.hyps(2)) (use ASEQ.prems in simp)
  show ?case
    using left right
    by (simp add: rerase_bsimp7_ASEQ_atom legacy_rsimp7_SEQ_atom)
next
  case (AALTs bs rs)
  have mapped:
    "\<forall>r \<in> set (map bsimpStrong rs). legacy_rrexp (rerase r)"
    using AALTs by auto
  have flat: "\<forall>r \<in> set (flts (map bsimpStrong rs)).
      legacy_rrexp (rerase r)"
    by (rule legacy_rerase_flts[OF mapped])
  have alts:
    "legacy_rrexp (rerase (bsimpStrong_AALTs bs (flts (map bsimpStrong rs))))"
    by (rule legacy_rerase_bsimpStrong_AALTs[OF flat])
  show ?case
    using alts by simp
next
  case (ASTAR bs r)
  have body: "legacy_rrexp (rerase (bsimpStrong r))"
    by (rule ASTAR.hyps) (use ASTAR.prems in simp)
  show ?case
    using body by (cases "bsimpStrong r") simp_all
qed simp_all

lemma legacy_rerase_bders_simpStrong:
  assumes "legacy_rrexp (rerase r)"
  shows "legacy_rrexp (rerase (bders_simpStrong r s))"
  using assms
proof (induct s arbitrary: r)
  case Nil
  then show ?case
    by simp
next
  case (Cons c s)
  have der: "legacy_rrexp (rerase (bder c r))"
    using legacy_rder[OF Cons.prems, of c] rder_bder_rerase[of c r]
    by simp
  have step: "legacy_rrexp (rerase (bsimpStrong (bder c r)))"
    by (rule legacy_rerase_bsimpStrong[OF der])
  show ?case
    by (simp add: Cons.hyps[OF step])
qed

lemma rerase_map_fuse:
  "map rerase (map (fuse bs) rs) = map rerase rs"
  by (induct rs) (simp_all add: rerase_fuse)

lemma rerase_map_fuse_fuse:
  "map rerase (map (\<lambda>r. fuse bs (fuse bs' r)) rs) = map rerase rs"
  by (induct rs) (simp_all add: rerase_fuse)

lemma rerase_map_bsimp4_ASEQ_atom_if:
  assumes "map rerase xs = ys"
  shows "map rerase (map (\<lambda>x. bsimp4_ASEQ_atom bs x r) xs) =
    map (\<lambda>x. rsimp4_SEQ_atom x (rerase r)) ys"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (cases ys) (simp_all add: rerase_bsimp4_ASEQ_atom)
qed

lemma map_rsimp4_SEQ_atom_rerase_cong:
  assumes "map rerase xs = ys"
  shows "map (\<lambda>x. rsimp4_SEQ_atom (rerase x) k) xs =
    map (\<lambda>x. rsimp4_SEQ_atom x k) ys"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (cases ys) simp_all
qed

lemma rerase_concat_map_bpder_list:
  assumes "\<And>r. r \<in> set rs \<Longrightarrow>
    map rerase (bpder_list c r) = rpder_list c (rerase r)"
  shows "map rerase (concat (map (bpder_list c) rs)) =
    concat (map (\<lambda>r. rpder_list c (rerase r)) rs)"
  using assms
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons r rs)
  have head: "map rerase (bpder_list c r) = rpder_list c (rerase r)"
    by (rule Cons.prems) simp
  have tail: "map rerase (concat (map (bpder_list c) rs)) =
    concat (map (\<lambda>r. rpder_list c (rerase r)) rs)"
    by (rule Cons.hyps) (use Cons.prems in auto)
  show ?case
    using head tail by simp
qed

lemma rerase_bpder_list:
  "map rerase (bpder_list c r) = rpder_list c (rerase r)"
  by (induct r)
    (simp_all add: rerase_bsimp4_ASEQ_atom rerase_fuse rnullable map_map comp_def
      rerase_map_bsimp4_ASEQ_atom_if rerase_map_fuse_fuse
      rerase_concat_map_bpder_list map_rsimp4_SEQ_atom_rerase_cong)

lemma bp_der_rerase:
  shows "rerase (bp_der c r) = rpd_der c (rerase r)"
  by (simp add: bp_der_def rpd_der_def rerase_bsimp_AALTs
      map_rerase_distinctWith_eq1 rerase_flts rerase_bpder_list)

lemma rerase_bpder_norm_list:
  "map rerase (bpder_norm_list c r) = rpder_norm_list c (rerase r)"
proof -
  have rows: "map rerase (bpder_list c r) = rpder_list c (rerase r)"
    by (rule rerase_bpder_list)
  have "map rerase (bpder_norm_list c r) =
    map (\<lambda>x. rsimp4_SEQ_atom (rerase x) RONE) (bpder_list c r)"
    by (simp add: bpder_norm_list_def rerase_bsimp4_ASEQ_atom)
  also have "... =
    map (\<lambda>x. rsimp4_SEQ_atom x RONE) (rpder_list c (rerase r))"
    by (rule map_rsimp4_SEQ_atom_rerase_cong[OF rows])
  also have "... = rpder_norm_list c (rerase r)"
    by (simp add: rpder_norm_list_def)
  finally show ?thesis .
qed

lemma rerase_concat_map_bpder_norm_list:
  "map rerase (concat (map (bpder_norm_list c) rs)) =
    concat (map (\<lambda>r. rpder_norm_list c (rerase r)) rs)"
  by (induct rs) (simp_all add: rerase_bpder_norm_list)

lemma rerase_bpder_norm_rows:
  "map rerase (bpder_norm_rows c rs) = rpder_norm_rows c (map rerase rs)"
  by (simp add: bpder_norm_rows_def rpder_norm_rows_def
      map_rerase_distinctWith_eq1 rerase_flts
      rerase_concat_map_bpder_norm_list map_map comp_def)

lemma bp_der_norm_rerase:
  shows "rerase (bp_der_norm c r) = rpd_der_norm c (rerase r)"
  by (simp add: bp_der_norm_def rpd_der_norm_def rerase_bsimp_AALTs
      map_rerase_distinctWith_eq1 rerase_flts rerase_bpder_norm_list)

lemma map_rerase_bsimp6_list:
  "map rerase (map bsimp6 xs) = map rsimp6 (map rerase xs)"
  by (induct xs) (simp_all add: bsimp6_rerase)

lemma rerase_bpder_norm6_list:
  "map rerase (bpder_norm6_list c r) = rpder_norm6_list c (rerase r)"
proof -
  have rows: "map rerase (bpder_norm_list c r) = rpder_norm_list c (rerase r)"
    by (rule rerase_bpder_norm_list)
  have "map rerase (bpder_norm6_list c r) =
    map (\<lambda>x. rerase (bsimp6 x)) (bpder_norm_list c r)"
    by (simp add: bpder_norm6_list_def)
  also have "... =
    map (\<lambda>x. rsimp6 (rerase x)) (bpder_norm_list c r)"
    by (simp add: bsimp6_rerase)
  also have "... =
    map rsimp6 (map rerase (bpder_norm_list c r))"
    by (simp add: map_map comp_def)
  also have "... = rpder_norm6_list c (rerase r)"
    by (simp add: rows rpder_norm6_list_def)
  finally show ?thesis .
qed

lemma rerase_concat_map_bpder_norm6_list:
  "map rerase (concat (map (bpder_norm6_list c) rs)) =
    concat (map (\<lambda>r. rpder_norm6_list c (rerase r)) rs)"
  by (induct rs) (simp_all add: rerase_bpder_norm6_list)

lemma rerase_bpder_norm6_rows:
  "map rerase (bpder_norm6_rows c rs) = rpder_norm6_rows c (map rerase rs)"
  by (simp add: bpder_norm6_rows_def rpder_norm6_rows_def
      map_rerase_distinctWith_eq1 rerase_flts
      rerase_concat_map_bpder_norm6_list map_map comp_def)

lemma bp_der_norm6_rerase:
  shows "rerase (bp_der_norm6 c r) = rpd_der_norm6 c (rerase r)"
  by (simp add: bp_der_norm6_def rpd_der_norm6_def rerase_bsimp_AALTs
      map_rerase_distinctWith_eq1 rerase_flts rerase_bpder_norm6_list)

lemma map_rerase_bsimp7_list:
  "map rerase (map bsimp7 xs) = map rsimp7 (map rerase xs)"
  by (induct xs) (simp_all add: bsimp7_rerase)

lemma rerase_bpder_norm7_list:
  "map rerase (bpder_norm7_list c r) = rpder_norm7_list c (rerase r)"
proof -
  have rows: "map rerase (bpder_norm_list c r) = rpder_norm_list c (rerase r)"
    by (rule rerase_bpder_norm_list)
  have "map rerase (bpder_norm7_list c r) =
    map (\<lambda>x. rerase (bsimp7 x)) (bpder_norm_list c r)"
    by (simp add: bpder_norm7_list_def)
  also have "... =
    map (\<lambda>x. rsimp7 (rerase x)) (bpder_norm_list c r)"
    by (simp add: bsimp7_rerase)
  also have "... =
    map rsimp7 (map rerase (bpder_norm_list c r))"
    by (simp add: map_map comp_def)
  also have "... = rpder_norm7_list c (rerase r)"
    by (simp add: rows rpder_norm7_list_def)
  finally show ?thesis .
qed

lemma rerase_concat_map_bpder_norm7_list:
  "map rerase (concat (map (bpder_norm7_list c) rs)) =
    concat (map (\<lambda>r. rpder_norm7_list c (rerase r)) rs)"
  by (induct rs) (simp_all add: rerase_bpder_norm7_list)

lemma rerase_bpder_norm7_rows:
  "map rerase (bpder_norm7_rows c rs) = rpder_norm7_rows c (map rerase rs)"
  by (simp add: bpder_norm7_rows_def rpder_norm7_rows_def
      map_rerase_distinctWith_eq1 rerase_flts
      rerase_concat_map_bpder_norm7_list map_map comp_def)

lemma bp_der_norm7_rerase:
  shows "rerase (bp_der_norm7 c r) = rpd_der_norm7 c (rerase r)"
  by (simp add: bp_der_norm7_def rpd_der_norm7_def rerase_bsimp_AALTs
      map_rerase_distinctWith_eq1 rerase_flts rerase_bpder_norm7_list)

lemma RLS_set_map_rerase_strong_rows_cleanup:
  "RLS (set (map rerase
      (distinctWith (flts (bsimpStrong_prune_rows (flts xs))) eq1 {}))) =
    RLS (set (map rerase xs))"
proof -
  have "RLS (set (map rerase
      (distinctWith (flts (bsimpStrong_prune_rows (flts xs))) eq1 {}))) =
      L (erase (AALTs []
        (distinctWith (flts (bsimpStrong_prune_rows (flts xs))) eq1 {})))"
    by (rule RLS_set_map_rerase_AALTs)
  also have "... =
      L (erase (AALTs [] (flts (bsimpStrong_prune_rows (flts xs)))))"
    by (rule L_distinctWith_eq1_AALTs)
  also have "... = L (erase (AALTs [] (bsimpStrong_prune_rows (flts xs))))"
    by (rule L_flts_AALTs)
  also have "... = L (erase (AALTs [] (flts xs)))"
    by (rule L_bsimpStrong_prune_rows)
  also have "... = L (erase (AALTs [] xs))"
    by (rule L_flts_AALTs)
  also have "... = RLS (set (map rerase xs))"
    using RLS_set_map_rerase_AALTs[of xs "[]"] by simp
  finally show ?thesis .
qed

lemma RLS_set_map_rerase_bpder_strong_list:
  "RLS (set (map rerase (bpder_strong_list c r))) =
    RLS (set (map rerase (bpder_norm_list c r)))"
  by (auto simp add: RLS_def bpder_strong_list_def RL_rerase_bsimpStrong)

lemma RLS_set_map_rerase_concat_bpder_strong_list:
  "RLS (set (map rerase (concat (map (bpder_strong_list c) rs)))) =
    RLS (set (map rerase (concat (map (bpder_norm_list c) rs))))"
proof (induct rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  have head:
    "RLS (set (map rerase (bpder_strong_list c r))) =
      RLS (set (map rerase (bpder_norm_list c r)))"
    by (rule RLS_set_map_rerase_bpder_strong_list)
  have tail:
    "RLS (set (map rerase (concat (map (bpder_strong_list c) rs)))) =
      RLS (set (map rerase (concat (map (bpder_norm_list c) rs))))"
    by (rule Cons.hyps)
  show ?case
    using head tail by (auto simp add: RLS_def)
qed

lemma RLS_set_map_rerase_bpder_strong_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
  shows "RLS (set (map rerase (bpder_strong_rows c rs))) =
    Der c (RLS (set (map rerase rs)))"
proof -
  have "RLS (set (map rerase (bpder_strong_rows c rs))) =
      RLS (set (map rerase (concat (map (bpder_strong_list c) rs))))"
    unfolding bpder_strong_rows_def
    by (rule RLS_set_map_rerase_strong_rows_cleanup)
  also have "... =
      RLS (set (map rerase (concat (map (bpder_norm_list c) rs))))"
    by (rule RLS_set_map_rerase_concat_bpder_strong_list)
  also have "... =
      RLS (set (concat (map (rpder_norm_list c) (map rerase rs))))"
    by (simp add: rerase_concat_map_bpder_norm_list map_map comp_def)
  also have "... = RLS (rpder_norm_set c (set (map rerase rs)))"
    by (rule RLS_set_concat_rpder_norm_list)
  also have "... = Der c (RLS (set (map rerase rs)))"
    by (rule RLS_rpder_norm_set) (use assms in auto)
  finally show ?thesis .
qed

lemma RLS_rerase_bp_der_strong:
  assumes "legacy_rrexp (rerase r)"
  shows "RL (rerase (bp_der_strong c r)) = Der c (RL (rerase r))"
proof -
  have "RL (rerase (bp_der_strong c r)) =
      RLS (set (map rerase (bpder_strong_rows c [r])))"
    by (simp add: bp_der_strong_def rerase_bsimp_AALTs RLS_def RL_rsimp_RALTS)
  also have "... = Der c (RLS (set (map rerase [r])))"
    by (rule RLS_set_map_rerase_bpder_strong_rows) (use assms in simp)
  also have "... = Der c (RL (rerase r))"
    by (simp add: RLS_def)
  finally show ?thesis .
qed

lemma legacy_rerase_bpder_norm_list:
  assumes "legacy_rrexp (rerase r)"
  shows "\<forall>p \<in> set (bpder_norm_list c r). legacy_rrexp (rerase p)"
proof -
  have rows: "\<forall>p \<in> set (rpder_norm_list c (rerase r)). legacy_rrexp p"
    by (rule legacy_rpder_norm_list[OF assms])
  show ?thesis
  proof
    fix p
    assume p: "p \<in> set (bpder_norm_list c r)"
    have "rerase p \<in> set (map rerase (bpder_norm_list c r))"
      using p by simp
    also have "... = set (rpder_norm_list c (rerase r))"
      using rerase_bpder_norm_list[of c r] by simp
    finally show "legacy_rrexp (rerase p)"
      using rows by simp
  qed
qed

lemma legacy_rerase_bpder_strong_list:
  assumes "legacy_rrexp (rerase r)"
  shows "\<forall>p \<in> set (bpder_strong_list c r). legacy_rrexp (rerase p)"
proof -
  have norm: "\<forall>p \<in> set (bpder_norm_list c r). legacy_rrexp (rerase p)"
    by (rule legacy_rerase_bpder_norm_list[OF assms])
  show ?thesis
    unfolding bpder_strong_list_def
    using norm legacy_rerase_bsimpStrong by auto
qed

lemma legacy_rerase_bpder_strong_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
  shows "\<forall>p \<in> set (bpder_strong_rows c rs). legacy_rrexp (rerase p)"
proof -
  have strong:
    "\<forall>p \<in> set (concat (map (bpder_strong_list c) rs)).
      legacy_rrexp (rerase p)"
    using assms legacy_rerase_bpder_strong_list by auto
  have flat1:
    "\<forall>p \<in> set (flts (concat (map (bpder_strong_list c) rs))).
      legacy_rrexp (rerase p)"
    by (rule legacy_rerase_flts[OF strong])
  have pruned:
    "\<forall>p \<in> set (bsimpStrong_prune_rows
        (flts (concat (map (bpder_strong_list c) rs)))).
      legacy_rrexp (rerase p)"
    by (rule legacy_rerase_bsimpStrong_prune_rows[OF flat1])
  have flat2:
    "\<forall>p \<in> set (flts (bsimpStrong_prune_rows
        (flts (concat (map (bpder_strong_list c) rs))))).
      legacy_rrexp (rerase p)"
    by (rule legacy_rerase_flts[OF pruned])
  show ?thesis
    unfolding bpder_strong_rows_def
    by (rule legacy_rerase_distinctWith[OF flat2])
qed

lemma legacy_rerase_bpders_strong_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
    and "p \<in> set (bpders_strong_rows rs s)"
  shows "legacy_rrexp (rerase p)"
  using assms
proof (induct s arbitrary: rs p)
  case Nil
  then show ?case
    by simp
next
  case (Cons c s)
  have next_legacy:
    "\<forall>r \<in> set (bpder_strong_rows c rs). legacy_rrexp (rerase r)"
    by (rule legacy_rerase_bpder_strong_rows[OF Cons.prems(1)])
  have p_next: "p \<in> set (bpders_strong_rows (bpder_strong_rows c rs) s)"
    using Cons.prems by simp
  show ?case
    by (rule Cons.hyps[OF next_legacy p_next])
qed

lemma RLS_set_map_rerase_bpders_strong_rows:
  assumes "\<forall>r \<in> set rs. legacy_rrexp (rerase r)"
  shows "RLS (set (map rerase (bpders_strong_rows rs s))) =
    Ders s (RLS (set (map rerase rs)))"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case
    by (simp add: Ders_def)
next
  case (Cons c s)
  have next_legacy:
    "\<forall>r \<in> set (bpder_strong_rows c rs). legacy_rrexp (rerase r)"
    by (rule legacy_rerase_bpder_strong_rows[OF Cons.prems])
  have ih:
    "RLS (set (map rerase
        (bpders_strong_rows (bpder_strong_rows c rs) s))) =
      Ders s (RLS (set (map rerase (bpder_strong_rows c rs))))"
    by (rule Cons.hyps[OF next_legacy])
  have step:
    "RLS (set (map rerase (bpder_strong_rows c rs))) =
      Der c (RLS (set (map rerase rs)))"
    by (rule RLS_set_map_rerase_bpder_strong_rows[OF Cons.prems])
  have "RLS (set (map rerase (bpders_strong_rows rs (c # s)))) =
      Ders s (RLS (set (map rerase (bpder_strong_rows c rs))))"
    using ih by simp
  also have "... = Ders s (Der c (RLS (set (map rerase rs))))"
    using step by simp
  also have "... = Ders (c # s) (RLS (set (map rerase rs)))"
    by (simp add: Ders_Cons)
  finally show ?case .
qed

lemma RLS_set_map_rerase_bpders_strong1_rows:
  assumes "legacy_rrexp (rerase r)"
  shows "RLS (set (map rerase (bpders_strong1_rows r s))) =
    Ders s (RL (rerase r))"
  using RLS_set_map_rerase_bpders_strong_rows[of "[r]" s] assms
  by (simp add: bpders_strong1_rows_def RLS_def)

lemma rders_simp4_size:
  shows "rders_simp4 (rerase r) s = rerase (bders_simp4 r s)"
  by (induct s arbitrary: r) (simp_all add: rder_bder_rerase bsimp4_rerase[symmetric])

lemma rders_simp5_size:
  shows "rders_simp5 (rerase r) s = rerase (bders_simp5 r s)"
  by (induct s arbitrary: r) (simp_all add: rder_bder_rerase bsimp5_rerase[symmetric])

lemma rders_simp6_size:
  shows "rders_simp6 (rerase r) s = rerase (bders_simp6 r s)"
  by (induct s arbitrary: r) (simp_all add: rder_bder_rerase bsimp6_rerase[symmetric])

lemma rders_simp7_size:
  shows "rders_simp7 (rerase r) s = rerase (bders_simp7 r s)"
  by (induct s arbitrary: r) (simp_all add: rder_bder_rerase bsimp7_rerase[symmetric])

lemma rders_simp8_size:
  shows "rders_simp8 (rerase r) s = rerase (bders_simp8 r s)"
  by (induct s arbitrary: r) (simp_all add: rder_bder_rerase bsimp8_rerase[symmetric])

lemma asize_bders_simp5_rders_simp5:
  shows "asize (bders_simp5 r s) = rsize (rders_simp5 (rerase r) s)"
  by (simp add: asize_rsize rders_simp5_size)

lemma asize_bders_simp6_rders_simp6:
  shows "asize (bders_simp6 r s) = rsize (rders_simp6 (rerase r) s)"
  by (simp add: asize_rsize rders_simp6_size)

lemma asize_bders_simp7_rders_simp7:
  shows "asize (bders_simp7 r s) = rsize (rders_simp7 (rerase r) s)"
  by (simp add: asize_rsize rders_simp7_size)

lemma asize_bders_simp8_rders_simp8:
  shows "asize (bders_simp8 r s) = rsize (rders_simp8 (rerase r) s)"
  by (simp add: asize_rsize rders_simp8_size)

lemma RL_rerase_bders_simp5:
  shows "RL (rerase (bders_simp5 r s)) = Ders s (RL (rerase r))"
  using RL_rders_simp5[of "rerase r" s] rders_simp5_size[of r s]
  by simp

lemma RL_rerase_bders_simp6:
  shows "RL (rerase (bders_simp6 r s)) = Ders s (RL (rerase r))"
  using RL_rders_simp6[of "rerase r" s] rders_simp6_size[of r s]
  by simp

lemma RL_rerase_bders_simp7:
  shows "RL (rerase (bders_simp7 r s)) = Ders s (RL (rerase r))"
  using RL_rders_simp7[of "rerase r" s] rders_simp7_size[of r s]
  by simp

lemma RL_rerase_bders_simp8:
  shows "RL (rerase (bders_simp8 r s)) = Ders s (RL (rerase r))"
  using RL_rders_simp8[of "rerase r" s] rders_simp8_size[of r s]
  by simp

corollary aders_simp5_finiteness:
  assumes "\<exists>N. \<forall>s. rsize (rders_simp5 (rerase r) s) \<le> N"
  shows "\<exists>N. \<forall>s. asize (bders_simp5 r s) \<le> N"
proof -
  from assms obtain N where "\<forall>s. rsize (rders_simp5 (rerase r) s) \<le> N"
    by blast
  then have "\<forall>s. asize (bders_simp5 r s) \<le> N"
    by (simp add: asize_bders_simp5_rders_simp5)
  then show ?thesis by blast
qed

corollary aders_simp6_finiteness:
  assumes "\<exists>N. \<forall>s. rsize (rders_simp6 (rerase r) s) \<le> N"
  shows "\<exists>N. \<forall>s. asize (bders_simp6 r s) \<le> N"
proof -
  from assms obtain N where "\<forall>s. rsize (rders_simp6 (rerase r) s) \<le> N"
    by blast
  then have "\<forall>s. asize (bders_simp6 r s) \<le> N"
    by (simp add: asize_bders_simp6_rders_simp6)
  then show ?thesis by blast
qed

corollary aders_simp7_finiteness:
  assumes "\<exists>N. \<forall>s. rsize (rders_simp7 (rerase r) s) \<le> N"
  shows "\<exists>N. \<forall>s. asize (bders_simp7 r s) \<le> N"
proof -
  from assms obtain N where "\<forall>s. rsize (rders_simp7 (rerase r) s) \<le> N"
    by blast
  then have "\<forall>s. asize (bders_simp7 r s) \<le> N"
    by (simp add: asize_bders_simp7_rders_simp7)
  then show ?thesis by blast
qed

corollary aders_simp8_finiteness:
  assumes "\<exists>N. \<forall>s. rsize (rders_simp8 (rerase r) s) \<le> N"
  shows "\<exists>N. \<forall>s. asize (bders_simp8 r s) \<le> N"
proof -
  from assms obtain N where "\<forall>s. rsize (rders_simp8 (rerase r) s) \<le> N"
    by blast
  then have "\<forall>s. asize (bders_simp8 r s) \<le> N"
    by (simp add: asize_bders_simp8_rders_simp8)
  then show ?thesis by blast
qed

section \<open>Chapter 7 Strong-Pruning Regression Tests\<close>

definition thesis_ch7_a :: char where
  "thesis_ch7_a = CHR ''a''"

definition thesis_ch7_b :: char where
  "thesis_ch7_b = CHR ''b''"

definition thesis_ch7_c :: char where
  "thesis_ch7_c = CHR ''c''"

definition thesis_ch7_d :: char where
  "thesis_ch7_d = CHR ''d''"

definition thesis_ch7_e :: char where
  "thesis_ch7_e = CHR ''e''"

fun thesis_ch7_rexp_char_power :: "char \<Rightarrow> nat \<Rightarrow> rexp" where
  "thesis_ch7_rexp_char_power c 0 = ONE"
| "thesis_ch7_rexp_char_power c (Suc n) =
    SEQ (CH c) (thesis_ch7_rexp_char_power c n)"

fun thesis_ch7_rexp_alt_list :: "rexp list \<Rightarrow> rexp" where
  "thesis_ch7_rexp_alt_list [] = ZERO"
| "thesis_ch7_rexp_alt_list [r] = r"
| "thesis_ch7_rexp_alt_list (r # rs) =
    ALT r (thesis_ch7_rexp_alt_list rs)"

definition thesis_ch7_evil_body :: "nat \<Rightarrow> rexp" where
  "thesis_ch7_evil_body k =
    thesis_ch7_rexp_alt_list
      (map (\<lambda>n. STAR (thesis_ch7_rexp_char_power thesis_ch7_a n))
        [1..<Suc k])"

definition thesis_ch7_evil :: "nat \<Rightarrow> rexp" where
  "thesis_ch7_evil k = STAR (STAR (thesis_ch7_evil_body k))"

definition asizes :: "arexp list \<Rightarrow> nat" where
  "asizes rs = sum_list (map asize rs)"

lemma asizes_append [simp]:
  "asizes (xs @ ys) = asizes xs + asizes ys"
  by (simp add: asizes_def)

lemma asizes_cons [simp]:
  "asizes (x # xs) = asize x + asizes xs"
  by (simp add: asizes_def)

lemma asize_fuse [simp]:
  "asize (fuse bs r) = asize r"
  by (cases r) simp_all

lemma asizes_map_fuse [simp]:
  "asizes (map (fuse bs) rs) = asizes rs"
  by (induct rs) (simp_all add: asizes_def)

lemma sum_list_map_asize_fuse [simp]:
  "sum_list (map (asize \<circ> fuse bs) rs) = sum_list (map asize rs)"
  by (induct rs) simp_all

lemma asizes_flts_le:
  "asizes (flts rs) \<le> asizes rs"
proof (induct rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  then show ?case
    by (cases r) (simp_all add: asizes_def)
qed

lemma asizes_distinctWith_le:
  "asizes (distinctWith rs eq acc) \<le> asizes rs"
proof (induct rs arbitrary: acc)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  show ?case
  proof (cases "\<exists>y \<in> acc. eq r y")
    case True
    have "asizes (distinctWith rs eq acc) \<le> asizes rs"
      by (rule Cons.hyps)
    then show ?thesis
      using True by (simp add: asizes_def)
  next
    case False
    have "asizes (distinctWith rs eq ({r} \<union> acc)) \<le> asizes rs"
      by (rule Cons.hyps)
    then show ?thesis
      using False by (simp add: asizes_def)
  qed
qed

lemma asizes_prune_eq1_against_le:
  "asizes (prune_eq1_against covered rs) \<le> asizes rs"
proof (induct rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  show ?case
  proof (cases "eq1_member r covered")
    case True
    then show ?thesis
      using Cons.hyps by (simp add: asizes_def)
  next
    case False
    then show ?thesis
      using Cons.hyps by (simp add: asizes_def)
  qed
qed

lemma length_prune_eq1_against_le:
  "length (prune_eq1_against covered rs) \<le> length rs"
proof (induct rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  show ?case
  proof (cases "eq1_member r covered")
    case True
    then show ?thesis
      using Cons.hyps by simp
  next
    case False
    then show ?thesis
      using Cons.hyps by simp
  qed
qed

lemma length_prune_eq1_against_lt:
  assumes "\<exists>r \<in> set rs. eq1_member r covered"
  shows "length (prune_eq1_against covered rs) < length rs"
  using assms
proof (induct rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "eq1_member x covered")
    case True
    have tail_le: "length (prune_eq1_against covered xs) \<le> length xs"
      by (rule length_prune_eq1_against_le)
    show ?thesis
      using True tail_le by simp
  next
    case False
    obtain r where r_in: "r \<in> set (x # xs)"
        and r_hit: "eq1_member r covered"
      using Cons.prems by blast
    have r_tail: "r \<in> set xs"
    proof (cases "r = x")
      case True
      then have "eq1_member x covered"
        using r_hit by simp
      then show ?thesis
        using False by contradiction
    next
      case False
      then show ?thesis
        using r_in by simp
    qed
    have hit_tail: "\<exists>r \<in> set xs. eq1_member r covered"
      using r_tail r_hit by blast
    have tail_lt: "length (prune_eq1_against covered xs) < length xs"
      by (rule Cons.hyps[OF hit_tail])
    show ?thesis
      using False tail_lt by simp
  qed
qed

lemma asizes_prune_eq1_against_lt:
  assumes "\<exists>r \<in> set rs. eq1_member r covered"
  shows "asizes (prune_eq1_against covered rs) < asizes rs"
  using assms
proof (induct rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "eq1_member x covered")
    case True
    have tail_le: "asizes (prune_eq1_against covered xs) \<le> asizes xs"
      by (rule asizes_prune_eq1_against_le)
    have x_pos: "0 < asize x"
      by (rule asize0)
    show ?thesis
      using True tail_le x_pos by (simp add: asizes_def)
  next
    case False
    obtain r where r_in: "r \<in> set (x # xs)"
        and r_hit: "eq1_member r covered"
      using Cons.prems by blast
    have r_tail: "r \<in> set xs"
    proof (cases "r = x")
      case True
      then have "eq1_member x covered"
        using r_hit by simp
      then show ?thesis
        using False by contradiction
    next
      case False
      then show ?thesis
        using r_in by simp
    qed
    have hit_tail: "\<exists>r \<in> set xs. eq1_member r covered"
      using r_tail r_hit by blast
    have tail_lt: "asizes (prune_eq1_against covered xs) < asizes xs"
      by (rule Cons.hyps[OF hit_tail])
    show ?thesis
      using False tail_lt by simp
  qed
qed

lemma asize_bsimp_AALTs_le:
  "asize (bsimp_AALTs bs rs) \<le> Suc (asizes rs)"
proof (cases rs)
  case Nil
  then show ?thesis
    by simp
next
  case (Cons r rest)
  have rs_def: "rs = r # rest"
    using Cons by simp
  show ?thesis
  proof (cases rest)
    case Nil
    then show ?thesis
      using rs_def by (simp add: asizes_def)
  next
    case (Cons s ss)
    then show ?thesis
      using rs_def by (simp add: asizes_def)
  qed
qed

lemma asize_bsimp7_ASEQ_atom_le:
  "asize (bsimp7_ASEQ_atom bs r1 r2) \<le> Suc (asize r1 + asize r2)"
proof -
  have "asize (bsimp7_ASEQ_atom bs r1 r2) =
      rsize (rerase (bsimp7_ASEQ_atom bs r1 r2))"
    by (simp add: asize_rsize)
  also have "... =
      rsize (rsimp7_SEQ_atom (rerase r1) (rerase r2))"
    by (simp add: rerase_bsimp7_ASEQ_atom)
  also have "... \<le> Suc (rsize (rerase r1) + rsize (rerase r2))"
    by (rule rsize_rsimp7_SEQ_atom_le)
  also have "... = Suc (asize r1 + asize r2)"
    by (simp add: asize_rsize)
  finally show ?thesis .
qed

lemma asize_bsimpStrong_pruned_AALTs_le:
  "asize (bsimp_AALTs bs (prune_eq1_against covered rs)) \<le>
    asize (AALTs bs rs)"
proof -
  have "asize (bsimp_AALTs bs (prune_eq1_against covered rs)) \<le>
      Suc (asizes (prune_eq1_against covered rs))"
    by (rule asize_bsimp_AALTs_le)
  also have "... \<le> Suc (asizes rs)"
    using asizes_prune_eq1_against_le[of covered rs] by simp
  finally show ?thesis
    by (simp add: asizes_def)
qed

lemma asize_bsimpStrong_shared_prune_result_le:
  "asize
    (bsimp7_ASEQ_atom bs
      (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k) \<le>
    asize (ASEQ bs (AALTs rbs (prune_eq1_against lrs rrs)) k)"
proof -
  let ?pruned = "prune_eq1_against lrs rrs"
  have "asize
      (bsimp7_ASEQ_atom bs (bsimp_AALTs rbs ?pruned) k) \<le>
      Suc (asize (bsimp_AALTs rbs ?pruned) + asize k)"
    by (rule asize_bsimp7_ASEQ_atom_le)
  also have "... \<le> Suc (asize (AALTs rbs ?pruned) + asize k)"
    using asize_bsimp_AALTs_le[of rbs ?pruned] by (simp add: asizes_def)
  finally show ?thesis
    by simp
qed

lemma asize_bsimpStrong_prune_pair_le:
  "asize (bsimpStrong_prune_pair earlier later) \<le> asize later"
proof -
  consider
    (shared) bs1 lbs lrs k1 bs2 rbs rrs k2 where
      "earlier = ASEQ bs1 (AALTs lbs lrs) k1"
      "later = ASEQ bs2 (AALTs rbs rrs) k2"
      "k1 ~1 k2"
  | (other) "\<not> (\<exists>bs1 lbs lrs k1 bs2 rbs rrs k2.
      earlier = ASEQ bs1 (AALTs lbs lrs) k1 \<and>
      later = ASEQ bs2 (AALTs rbs rrs) k2 \<and> k1 ~1 k2)"
    by blast
  then show ?thesis
  proof cases
    case (shared bs1 lbs lrs k1 bs2 rbs rrs k2)
    have "asize (bsimpStrong_prune_pair earlier later) =
        asize (bsimp7_ASEQ_atom bs2
          (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k2)"
      using shared by (simp add: bsimpStrong_prune_pair_def)
    also have "... \<le> Suc
        (asize (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) + asize k2)"
      by (rule asize_bsimp7_ASEQ_atom_le)
    also have "... \<le> Suc (asize (AALTs rbs rrs) + asize k2)"
      using asize_bsimpStrong_pruned_AALTs_le[of rbs lrs rrs] by simp
    also have "... = asize later"
      using shared by simp
    finally show ?thesis .
  next
    case other
    have "bsimpStrong_prune_pair earlier later = later"
      using other
      unfolding bsimpStrong_prune_pair_def
      by (cases earlier; cases later) (auto split: arexp.splits)
    then show ?thesis
      by simp
  qed
qed

lemma asize_bsimpStrong_prune_pair_shared_suffix_lt:
  assumes hit: "\<exists>r \<in> set rrs. eq1_member r lrs"
      and suffix: "k1 ~1 k2"
  shows "asize (bsimpStrong_prune_pair
      (ASEQ bs1 (AALTs lbs lrs) k1)
      (ASEQ bs2 (AALTs rbs rrs) k2)) <
    asize (ASEQ bs2 (AALTs rbs rrs) k2)"
proof -
  have pruned_lt: "asizes (prune_eq1_against lrs rrs) < asizes rrs"
    by (rule asizes_prune_eq1_against_lt[OF hit])
  have pair_le:
    "asize (bsimpStrong_prune_pair
        (ASEQ bs1 (AALTs lbs lrs) k1)
        (ASEQ bs2 (AALTs rbs rrs) k2)) \<le>
      asize (ASEQ bs2 (AALTs rbs (prune_eq1_against lrs rrs)) k2)"
  proof -
    have pair_eq:
      "bsimpStrong_prune_pair
        (ASEQ bs1 (AALTs lbs lrs) k1)
        (ASEQ bs2 (AALTs rbs rrs) k2) =
       bsimp7_ASEQ_atom bs2
        (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k2"
      using suffix by (simp add: bsimpStrong_prune_pair_def)
    show ?thesis
      using asize_bsimpStrong_shared_prune_result_le[of bs2 rbs lrs rrs k2]
      by (simp add: pair_eq)
  qed
  have tail_lt:
    "asize (ASEQ bs2 (AALTs rbs (prune_eq1_against lrs rrs)) k2) <
      asize (ASEQ bs2 (AALTs rbs rrs) k2)"
    using pruned_lt by (simp add: asizes_def)
  show ?thesis
    using pair_le tail_lt by linarith
qed

lemma asize_bsimpStrong_prune_against_rows_le:
  "asize (bsimpStrong_prune_against_rows seen r) \<le> asize r"
proof (induct seen arbitrary: r)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  let ?p = "bsimpStrong_prune_pair x r"
  have "asize (bsimpStrong_prune_against_rows (x # xs) r) =
      asize (bsimpStrong_prune_against_rows xs ?p)"
    by simp
  also have "... \<le> asize ?p"
    by (rule Cons.hyps)
  also have "... \<le> asize r"
    by (rule asize_bsimpStrong_prune_pair_le)
  finally show ?case .
qed

lemma asize_bsimpStrong_prune_against_rows_head_shared_suffix_lt:
  assumes hit: "\<exists>r \<in> set rrs. eq1_member r lrs"
      and suffix: "k1 ~1 k2"
  shows "asize
      (bsimpStrong_prune_against_rows
        (ASEQ bs1 (AALTs lbs lrs) k1 # seen)
        (ASEQ bs2 (AALTs rbs rrs) k2)) <
    asize (ASEQ bs2 (AALTs rbs rrs) k2)"
proof -
  let ?p = "bsimpStrong_prune_pair
    (ASEQ bs1 (AALTs lbs lrs) k1)
    (ASEQ bs2 (AALTs rbs rrs) k2)"
  have tail_le: "asize (bsimpStrong_prune_against_rows seen ?p) \<le> asize ?p"
    by (rule asize_bsimpStrong_prune_against_rows_le)
  have pair_lt: "asize ?p < asize (ASEQ bs2 (AALTs rbs rrs) k2)"
    by (rule asize_bsimpStrong_prune_pair_shared_suffix_lt[OF hit suffix])
  show ?thesis
    using tail_le pair_lt by simp
qed

lemma asizes_bsimpStrong_prune_rows_two_shared_suffix_lt:
  assumes hit: "\<exists>r \<in> set rrs. eq1_member r lrs"
      and suffix: "k1 ~1 k2"
  shows "asizes (bsimpStrong_prune_rows
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2]) <
    asizes
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2]"
proof -
  have tail_lt:
    "asize (bsimpStrong_prune_against_rows
        [ASEQ bs1 (AALTs lbs lrs) k1]
        (ASEQ bs2 (AALTs rbs rrs) k2)) <
      asize (ASEQ bs2 (AALTs rbs rrs) k2)"
    by (rule asize_bsimpStrong_prune_against_rows_head_shared_suffix_lt
        [OF hit suffix, where seen = "[]"])
  show ?thesis
    using tail_lt by (simp add: bsimpStrong_prune_rows_def Let_def asizes_def)
qed

lemma asizes_bsimpStrong_prune_rows_acc_le:
  "asizes (bsimpStrong_prune_rows_acc seen rs) \<le> asizes rs"
proof (induct rs arbitrary: seen)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  let ?r' = "bsimpStrong_prune_against_rows seen r"
  have head: "asize ?r' \<le> asize r"
    by (rule asize_bsimpStrong_prune_against_rows_le)
  have tail:
    "asizes (bsimpStrong_prune_rows_acc (?r' # seen) rs) \<le> asizes rs"
    by (rule Cons.hyps)
  show ?case
    using head tail by (simp add: Let_def asizes_def)
qed

lemma asizes_bsimpStrong_prune_rows_le:
  "asizes (bsimpStrong_prune_rows rs) \<le> asizes rs"
  using asizes_bsimpStrong_prune_rows_acc_le[of "[]" rs]
  by (simp add: bsimpStrong_prune_rows_def)

lemma asize_bsimpStrong_AALTs_le_pruned:
  "asize (bsimpStrong_AALTs bs rs) \<le>
    Suc (asizes (bsimpStrong_prune_rows rs))"
proof -
  have "asize (bsimpStrong_AALTs bs rs) \<le>
      Suc (asizes (distinctWith (flts (bsimpStrong_prune_rows rs)) eq1 {}))"
    by (simp add: bsimpStrong_AALTs_def asize_bsimp_AALTs_le)
  also have "... \<le> Suc (asizes (flts (bsimpStrong_prune_rows rs)))"
    using asizes_distinctWith_le[of "flts (bsimpStrong_prune_rows rs)" eq1 "{}"]
    by simp
  also have "... \<le> Suc (asizes (bsimpStrong_prune_rows rs))"
    using asizes_flts_le[of "bsimpStrong_prune_rows rs"] by simp
  finally show ?thesis .
qed

lemma asize_bsimpStrong_AALTs_le:
  "asize (bsimpStrong_AALTs bs rs) \<le> asize (AALTs bs rs)"
proof -
  have "asize (bsimpStrong_AALTs bs rs) \<le>
      Suc (asizes (bsimpStrong_prune_rows rs))"
    by (rule asize_bsimpStrong_AALTs_le_pruned)
  also have "... \<le> Suc (asizes rs)"
    using asizes_bsimpStrong_prune_rows_le[of rs] by simp
  finally show ?thesis
    by (simp add: asizes_def)
qed

lemma asize_bsimpStrong_AALTs_two_shared_suffix_lt:
  assumes hit: "\<exists>r \<in> set rrs. eq1_member r lrs"
      and suffix: "k1 ~1 k2"
  shows "asize (bsimpStrong_AALTs bs
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2]) <
    asize (AALTs bs
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2])"
proof -
  have "asize (bsimpStrong_AALTs bs
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2]) \<le>
    Suc (asizes (bsimpStrong_prune_rows
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2]))"
    by (rule asize_bsimpStrong_AALTs_le_pruned)
  also have "... < Suc (asizes
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2])"
    using asizes_bsimpStrong_prune_rows_two_shared_suffix_lt[OF hit suffix]
    by simp
  finally show ?thesis
    by (simp add: asizes_def)
qed

lemma asize_bsimpStrong_le:
  "asize (bsimpStrong r) \<le> asize r"
proof (induct r rule: bsimpStrong.induct)
  case (1 bs r1 r2)
  have "asize (bsimpStrong (ASEQ bs r1 r2)) \<le>
      Suc (asize (bsimpStrong r1) + asize (bsimpStrong r2))"
    by (simp add: asize_bsimp7_ASEQ_atom_le)
  also have "... \<le> asize (ASEQ bs r1 r2)"
    using 1 by simp
  finally show ?case .
next
  case (2 bs rs)
  have elems: "\<And>x. x \<in> set rs \<Longrightarrow> asize (bsimpStrong x) \<le> asize x"
    using 2 by auto
  have mapped: "asizes (map bsimpStrong rs) \<le> asizes rs"
    using elems by (simp add: asizes_def sum_list_mono)
  have "asize (bsimpStrong (AALTs bs rs)) =
      asize (bsimpStrong_AALTs bs (flts (map bsimpStrong rs)))"
    by simp
  also have "... \<le> asize (AALTs bs (flts (map bsimpStrong rs)))"
    by (rule asize_bsimpStrong_AALTs_le)
  also have "... \<le> Suc (asizes (map bsimpStrong rs))"
    using asizes_flts_le[of "map bsimpStrong rs"] by (simp add: asizes_def)
  also have "... \<le> Suc (asizes rs)"
    using mapped by simp
  finally show ?case
    by (simp add: asizes_def)
next
  case (3 bs r)
  note ih = 3
  show ?case
  proof (cases "bsimpStrong r")
    case AZERO
    then show ?thesis by simp
  next
    case (AONE x2)
    then show ?thesis by simp
  next
    case (ASTAR x61 x62)
    have "asize (ASTAR x61 x62) \<le> asize r"
      using ih ASTAR by simp
    then show ?thesis
      using ASTAR by simp
  qed (use ih in simp_all)
qed simp_all

lemma asizes_map_bsimpStrong_le:
  "asizes (map bsimpStrong rs) \<le> asizes rs"
  using asize_bsimpStrong_le
  by (simp add: asizes_def sum_list_mono)

lemma asizes_bpder_strong_list_le:
  "asizes (bpder_strong_list c r) \<le> asizes (bpder_norm_list c r)"
  unfolding bpder_strong_list_def
  by (rule asizes_map_bsimpStrong_le)

lemma asizes_concat_map_bpder_strong_list_le:
  "asizes (concat (map (bpder_strong_list c) rs)) \<le>
    asizes (concat (map (bpder_norm_list c) rs))"
proof (induct rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  have head: "asizes (bpder_strong_list c r) \<le> asizes (bpder_norm_list c r)"
    by (rule asizes_bpder_strong_list_le)
  have tail:
    "asizes (concat (map (bpder_strong_list c) rs)) \<le>
      asizes (concat (map (bpder_norm_list c) rs))"
    by (rule Cons.hyps)
  show ?case
    using head tail by simp
qed

lemma asizes_bpder_strong_rows_le:
  "asizes (bpder_strong_rows c rs) \<le>
    asizes (concat (map (bpder_norm_list c) rs))"
proof -
  let ?strong = "concat (map (bpder_strong_list c) rs)"
  have "asizes (bpder_strong_rows c rs) \<le>
      asizes (flts (bsimpStrong_prune_rows (flts ?strong)))"
    unfolding bpder_strong_rows_def
    by (rule asizes_distinctWith_le)
  also have "... \<le> asizes (bsimpStrong_prune_rows (flts ?strong))"
    by (rule asizes_flts_le)
  also have "... \<le> asizes (flts ?strong)"
    by (rule asizes_bsimpStrong_prune_rows_le)
  also have "... \<le> asizes ?strong"
    by (rule asizes_flts_le)
  also have "... \<le> asizes (concat (map (bpder_norm_list c) rs))"
    by (rule asizes_concat_map_bpder_strong_list_le)
  finally show ?thesis .
qed

lemma length_bpder_strong_rows_le_pruned:
  "length (bpder_strong_rows c rs) \<le>
    length
      (flts
        (bsimpStrong_prune_rows
          (flts (concat (map (bpder_strong_list c) rs)))))"
  by (simp add: bpder_strong_rows_def length_distinctWith_le)

lemma asizes_bpder_strong_rows_full_cover_shared_suffix:
  assumes raw: "flts (concat (map (bpder_strong_list c) rs)) =
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2]"
    and cover: "\<forall>r \<in> set rrs. eq1_member r lrs"
    and suffix: "k1 ~1 k2"
  shows "asizes (bpder_strong_rows c rs) =
    asize (ASEQ bs1 (AALTs lbs lrs) k1)"
proof -
  have rows:
    "bpder_strong_rows c rs = [ASEQ bs1 (AALTs lbs lrs) k1]"
    by (rule bpder_strong_rows_full_cover_shared_suffix
        [OF raw cover suffix])
  show ?thesis
    by (simp add: rows asizes_def)
qed

lemma length_bpder_strong_rows_full_cover_shared_suffix:
  assumes raw: "flts (concat (map (bpder_strong_list c) rs)) =
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2]"
    and cover: "\<forall>r \<in> set rrs. eq1_member r lrs"
    and suffix: "k1 ~1 k2"
  shows "length (bpder_strong_rows c rs) = 1"
  by (simp add: bpder_strong_rows_full_cover_shared_suffix
      [OF raw cover suffix])

lemma asizes_bpder_strong_rows_shared_suffix_le:
  assumes raw: "flts (concat (map (bpder_strong_list c) rs)) =
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2]"
    and suffix: "k1 ~1 k2"
  shows "asizes (bpder_strong_rows c rs) \<le>
    asize (ASEQ bs1 (AALTs lbs lrs) k1) +
    asize (ASEQ bs2 (AALTs rbs (prune_eq1_against lrs rrs)) k2)"
proof -
  let ?earlier = "ASEQ bs1 (AALTs lbs lrs) k1"
  let ?tail =
    "bsimp7_ASEQ_atom bs2
      (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k2"
  have "asizes (bpder_strong_rows c rs) =
      asizes (distinctWith (flts [?earlier, ?tail]) eq1 {})"
    by (simp add: bpder_strong_rows_shared_suffix[OF raw suffix])
  also have "... \<le> asizes (flts [?earlier, ?tail])"
    by (rule asizes_distinctWith_le)
  also have "... \<le> asizes [?earlier, ?tail]"
    by (rule asizes_flts_le)
  also have "... \<le>
      asize ?earlier +
      asize (ASEQ bs2 (AALTs rbs (prune_eq1_against lrs rrs)) k2)"
    using asize_bsimpStrong_shared_prune_result_le[of bs2 rbs lrs rrs k2]
    by (simp add: asizes_def)
  finally show ?thesis .
qed

lemma length_bpder_strong_rows_shared_suffix_le:
  assumes raw: "flts (concat (map (bpder_strong_list c) rs)) =
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2]"
    and suffix: "k1 ~1 k2"
  shows "length (bpder_strong_rows c rs) \<le>
    length
      (flts
        [ASEQ bs1 (AALTs lbs lrs) k1,
         bsimp7_ASEQ_atom bs2
          (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k2])"
  by (simp add: bpder_strong_rows_shared_suffix[OF raw suffix]
      length_distinctWith_le)

lemma asizes_bpder_strong_rows_shared_suffix_lt:
  assumes raw: "flts (concat (map (bpder_strong_list c) rs)) =
      [ASEQ bs1 (AALTs lbs lrs) k1,
       ASEQ bs2 (AALTs rbs rrs) k2]"
    and suffix: "k1 ~1 k2"
    and hit: "\<exists>r \<in> set rrs. eq1_member r lrs"
  shows "asizes (bpder_strong_rows c rs) <
    asize (ASEQ bs1 (AALTs lbs lrs) k1) +
    asize (ASEQ bs2 (AALTs rbs rrs) k2)"
proof -
  have pruned_lt: "asizes (prune_eq1_against lrs rrs) < asizes rrs"
    by (rule asizes_prune_eq1_against_lt[OF hit])
  have rows_le: "asizes (bpder_strong_rows c rs) \<le>
      asize (ASEQ bs1 (AALTs lbs lrs) k1) +
      asize (ASEQ bs2 (AALTs rbs (prune_eq1_against lrs rrs)) k2)"
    by (rule asizes_bpder_strong_rows_shared_suffix_le[OF raw suffix])
  have tail_lt:
      "asize (ASEQ bs2 (AALTs rbs (prune_eq1_against lrs rrs)) k2) <
       asize (ASEQ bs2 (AALTs rbs rrs) k2)"
    using pruned_lt by (simp add: asizes_def)
  show ?thesis
    using rows_le tail_lt by linarith
qed

lemma asize_bp_der_strong_le_asizes:
  "asize (bp_der_strong c r) \<le> Suc (asizes (bpder_norm_list c r))"
proof -
  have "asize (bp_der_strong c r) \<le>
      Suc (asizes (bpder_strong_rows c [r]))"
    unfolding bp_der_strong_def by (rule asize_bsimp_AALTs_le)
  also have "... \<le> Suc (asizes (concat (map (bpder_norm_list c) [r])))"
    using asizes_bpder_strong_rows_le[of c "[r]"] by simp
  also have "... = Suc (asizes (bpder_norm_list c r))"
    by simp
  finally show ?thesis .
qed

lemma asize_bp_der_strong_le_rows:
  "asize (bp_der_strong c r) \<le> Suc (asizes (bpder_strong_rows c [r]))"
  unfolding bp_der_strong_def by (rule asize_bsimp_AALTs_le)

lemma distinct_map_rerase_distinctWith_eq1:
  "distinct (map rerase (distinctWith rs eq1 {}))"
  by (simp add: map_rerase_distinctWith_eq1 rdistinct_does_the_job)

lemma distinct_map_rerase_bpder_strong_rows [simp]:
  "distinct (map rerase (bpder_strong_rows c rs))"
  unfolding bpder_strong_rows_def
  by (rule distinct_map_rerase_distinctWith_eq1)

lemma distinct_map_rerase_bpders_strong_rows:
  assumes "distinct (map rerase rs)"
  shows "distinct (map rerase (bpders_strong_rows rs s))"
  using assms
proof (induct s arbitrary: rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons c s)
  show ?case
    by (simp add: Cons.hyps)
qed

lemma map_rerase_flts_bpder_strong_list_subsetI:
  assumes "\<And>p. p \<in> set (bpder_norm_list c q) \<Longrightarrow>
    set (map rerase (flts [bsimpStrong p])) \<subseteq> U"
  shows "set (map rerase (flts (bpder_strong_list c q))) \<subseteq> U"
proof -
  have "map rerase (flts (bpder_strong_list c q)) =
      rflts (map rerase (map bsimpStrong (bpder_norm_list c q)))"
    by (simp add: bpder_strong_list_def rerase_flts)
  have rows: "set (map rerase (flts (map bsimpStrong
        (bpder_norm_list c q)))) \<subseteq> U"
  proof
    fix x
    assume x: "x \<in> set (map rerase
        (flts (map bsimpStrong (bpder_norm_list c q))))"
    have xr: "x \<in> set (rflts (map rerase
        (map bsimpStrong (bpder_norm_list c q))))"
      using x by (simp add: rerase_flts)
    obtain p' where p': "p' \<in> set (map bsimpStrong (bpder_norm_list c q))"
      and x_p': "x \<in> set (rflts [rerase p'])"
      by (rule set_rflts_map_memberE[OF xr])
    obtain p where p: "p \<in> set (bpder_norm_list c q)"
      and p'_eq: "p' = bsimpStrong p"
      using p' by auto
    have "set (map rerase (flts [bsimpStrong p])) \<subseteq> U"
      by (rule assms[OF p])
    moreover have "x \<in> set (map rerase (flts [bsimpStrong p]))"
      using x_p' p'_eq by (simp add: rerase_flts)
    then show "x \<in> U"
      using calculation by blast
  qed
  show ?thesis
    using rows by (simp add: bpder_strong_list_def)
qed

lemma map_rerase_flts_concat_map_bpder_strong_list_subsetI:
  assumes "\<And>q. q \<in> set rs \<Longrightarrow>
    set (map rerase (flts (bpder_strong_list c q))) \<subseteq> U"
  shows "set (map rerase
    (flts (concat (map (bpder_strong_list c) rs)))) \<subseteq> U"
proof -
  have flat: "set (rflts
      (concat (map (\<lambda>q. map rerase (bpder_strong_list c q)) rs)))
      \<subseteq> U"
  proof
    fix x
    assume x: "x \<in> set (rflts
        (concat (map (\<lambda>q. map rerase (bpder_strong_list c q)) rs)))"
    have sub: "set (rflts
        (concat (map (\<lambda>q. map rerase (bpder_strong_list c q)) rs)))
        \<subseteq>
        (\<Union>q \<in> set rs. set (rflts (map rerase (bpder_strong_list c q))))"
      by (induct rs) (auto simp add: flts_append)
    obtain q where q: "q \<in> set rs"
      and xq: "x \<in> set (rflts (map rerase (bpder_strong_list c q)))"
      using x sub by blast
    have "set (map rerase (flts (bpder_strong_list c q))) \<subseteq> U"
      by (rule assms[OF q])
    moreover have "x \<in> set (map rerase (flts (bpder_strong_list c q)))"
      using xq by (simp add: rerase_flts)
    then show "x \<in> U"
      using calculation by blast
  qed
  have "map rerase
      (flts (concat (map (bpder_strong_list c) rs))) =
      rflts
        (concat (map (\<lambda>q. map rerase (bpder_strong_list c q)) rs))"
    by (induct rs) (simp_all add: rerase_flts flts_append)
  then show ?thesis
    using flat by simp
qed

lemma map_rerase_bpder_strong_rows_local_subsetI:
  assumes lists: "\<And>q. q \<in> set rs \<Longrightarrow>
      set (map rerase (flts (bpder_strong_list c q))) \<subseteq> U"
    and prune: "\<And>xs. set (map rerase xs) \<subseteq> U \<Longrightarrow>
      set (map rerase (flts (bsimpStrong_prune_rows xs))) \<subseteq> U"
  shows "set (map rerase (bpder_strong_rows c rs)) \<subseteq> U"
proof -
  let ?rows = "flts (concat (map (bpder_strong_list c) rs))"
  have flat: "set (map rerase ?rows) \<subseteq> U"
    by (rule map_rerase_flts_concat_map_bpder_strong_list_subsetI[OF lists])
  have pruned: "set (map rerase (flts (bsimpStrong_prune_rows ?rows))) \<subseteq> U"
    by (rule prune[OF flat])
  have "set (map rerase
      (distinctWith (flts (bsimpStrong_prune_rows ?rows)) eq1 {})) \<subseteq> U"
  proof -
    have "set (rdistinct
        (map rerase (flts (bsimpStrong_prune_rows ?rows))) {}) \<subseteq> U"
      using pruned by (auto simp add: rdistinct_set_equality1)
    then show ?thesis
      by (simp add: map_rerase_distinctWith_eq1)
  qed
  then show ?thesis
    by (simp add: bpder_strong_rows_def)
qed

lemma map_rerase_bpder_strong_rows_norm_prune_subsetI:
  assumes norm: "\<And>q p. q \<in> set rs \<Longrightarrow>
      p \<in> set (bpder_norm_list c q) \<Longrightarrow>
      set (map rerase (flts [bsimpStrong p])) \<subseteq> U"
    and prune: "\<And>xs. set (map rerase xs) \<subseteq> U \<Longrightarrow>
      set (map rerase (flts (bsimpStrong_prune_rows xs))) \<subseteq> U"
  shows "set (map rerase (bpder_strong_rows c rs)) \<subseteq> U"
proof (rule map_rerase_bpder_strong_rows_local_subsetI[OF _ prune])
  fix q
  assume q: "q \<in> set rs"
  show "set (map rerase (flts (bpder_strong_list c q))) \<subseteq> U"
    by (rule map_rerase_flts_bpder_strong_list_subsetI)
      (use norm[OF q] in blast)
qed

lemma map_rerase_flts_singleton_flat_closed:
  assumes row: "rerase r \<in> U"
    and flat_closed: "\<And>q. q \<in> U \<Longrightarrow> set (rflts [q]) \<subseteq> U"
  shows "set (map rerase (flts [r])) \<subseteq> U"
proof -
  have "set (rflts [rerase r]) \<subseteq> U"
    by (rule flat_closed[OF row])
  then show ?thesis
    by (simp add: rerase_flts)
qed

lemma map_rerase_bsimpStrong_prune_pair_later_shared_subsetI:
  assumes later: "set (map rerase (flts [later])) \<subseteq> U"
    and shared: "\<And>bs2 rbs lrs rrs k.
      rerase (ASEQ bs2 (AALTs rbs rrs) k) \<in> U \<Longrightarrow>
      set (map rerase (flts [bsimp7_ASEQ_atom bs2
        (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k])) \<subseteq> U"
  shows "set (map rerase
    (flts [bsimpStrong_prune_pair earlier later])) \<subseteq> U"
proof (cases earlier)
  case (ASEQ bs1 left k1)
  note earlier_ASEQ = ASEQ
  then show ?thesis
  proof (cases left)
    case (AALTs lbs lrs)
    note left_AALTs = AALTs
    then show ?thesis
    proof (cases later)
      case (ASEQ bs2 right k2)
      note later_ASEQ = ASEQ
      then show ?thesis
      proof (cases right)
        case (AALTs rbs rrs)
        note right_AALTs = AALTs
        show ?thesis
        proof (cases "k1 ~1 k2")
          case True
          have later_member:
            "rerase (ASEQ bs2 (AALTs rbs rrs) k2) \<in> U"
            using later later_ASEQ right_AALTs by simp
          have "set (map rerase (flts [bsimp7_ASEQ_atom bs2
              (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k2])) \<subseteq> U"
            by (rule shared[OF later_member])
          then show ?thesis
            using later_ASEQ right_AALTs True earlier_ASEQ left_AALTs
            by (simp add: bsimpStrong_prune_pair_def)
        next
          case False
          then show ?thesis
            using later later_ASEQ right_AALTs earlier_ASEQ left_AALTs
            by (simp add: bsimpStrong_prune_pair_def)
        qed
      qed (insert later later_ASEQ earlier_ASEQ left_AALTs,
          auto simp add: bsimpStrong_prune_pair_def)
    qed (insert later earlier_ASEQ left_AALTs,
        auto simp add: bsimpStrong_prune_pair_def)
  next
    case AZERO
    then show ?thesis
      using later earlier_ASEQ by (simp add: bsimpStrong_prune_pair_def)
  next
    case (AONE x2)
    then show ?thesis
      using later earlier_ASEQ by (simp add: bsimpStrong_prune_pair_def)
  next
    case (ACHAR x31 x32)
    then show ?thesis
      using later earlier_ASEQ by (simp add: bsimpStrong_prune_pair_def)
  next
    case (ASEQ x41 x42 x43)
    then show ?thesis
      using later earlier_ASEQ by (simp add: bsimpStrong_prune_pair_def)
  next
    case (ASTAR x61 x62)
    then show ?thesis
      using later earlier_ASEQ by (simp add: bsimpStrong_prune_pair_def)
  next
    case (ANTIMES x71 x72 x73)
    then show ?thesis
      using later earlier_ASEQ by (simp add: bsimpStrong_prune_pair_def)
  next
    case (ABACKREF4 x81 x82 x83 x84 x85 x86)
    then show ?thesis
      using later earlier_ASEQ by (simp add: bsimpStrong_prune_pair_def)
  next
    case (AHALF x91 x92 x93 x94)
    then show ?thesis
      using later earlier_ASEQ by (simp add: bsimpStrong_prune_pair_def)
  next
    case (ARESIDUE x101 x102 x103)
    then show ?thesis
      using later earlier_ASEQ by (simp add: bsimpStrong_prune_pair_def)
  qed
qed (insert later, auto simp add: bsimpStrong_prune_pair_def)

lemma map_rerase_bsimpStrong_prune_against_rows_pair_subsetI:
  assumes row: "set (map rerase (flts [r])) \<subseteq> U"
    and pair: "\<And>earlier later.
      set (map rerase (flts [later])) \<subseteq> U \<Longrightarrow>
      set (map rerase
        (flts [bsimpStrong_prune_pair earlier later])) \<subseteq> U"
  shows "set (map rerase
    (flts [bsimpStrong_prune_against_rows seen r])) \<subseteq> U"
  using row
proof (induct seen arbitrary: r)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  let ?p = "bsimpStrong_prune_pair x r"
  have first: "set (map rerase (flts [?p])) \<subseteq> U"
    by (rule pair[OF Cons.prems])
  show ?case
    using Cons.hyps[OF first] by simp
qed

lemma map_rerase_bsimpStrong_prune_rows_acc_pair_subsetI:
  assumes rows: "\<And>r. r \<in> set rs \<Longrightarrow>
      set (map rerase (flts [r])) \<subseteq> U"
    and pair: "\<And>earlier later.
      set (map rerase (flts [later])) \<subseteq> U \<Longrightarrow>
      set (map rerase
        (flts [bsimpStrong_prune_pair earlier later])) \<subseteq> U"
  shows "set (map rerase
    (flts (bsimpStrong_prune_rows_acc seen rs))) \<subseteq> U"
  using rows
proof (induct rs arbitrary: seen)
  case Nil
  then show ?case
    by simp
next
  case (Cons r rs)
  let ?r' = "bsimpStrong_prune_against_rows seen r"
  have head: "set (map rerase (flts [?r'])) \<subseteq> U"
  proof (rule map_rerase_bsimpStrong_prune_against_rows_pair_subsetI)
    show "set (map rerase (flts [r])) \<subseteq> U"
      by (rule Cons.prems) simp
    show "\<And>earlier later.
      set (map rerase (flts [later])) \<subseteq> U \<Longrightarrow>
      set (map rerase
        (flts [bsimpStrong_prune_pair earlier later])) \<subseteq> U"
      by (rule pair)
  qed
  have tail: "set (map rerase
      (flts (bsimpStrong_prune_rows_acc (?r' # seen) rs))) \<subseteq> U"
    by (rule Cons.hyps) (use Cons.prems in simp)
  have split:
    "flts (?r' # bsimpStrong_prune_rows_acc (?r' # seen) rs) =
      flts [?r'] @ flts (bsimpStrong_prune_rows_acc (?r' # seen) rs)"
    by (cases ?r') simp_all
  have "set (map rerase
      (flts (?r' # bsimpStrong_prune_rows_acc (?r' # seen) rs))) \<subseteq> U"
    using head tail split by auto
  then show ?case
    by (simp add: Let_def)
qed

lemma map_rerase_bsimpStrong_prune_rows_pair_subsetI:
  assumes rows: "\<And>r. r \<in> set rs \<Longrightarrow>
      set (map rerase (flts [r])) \<subseteq> U"
    and pair: "\<And>earlier later.
      set (map rerase (flts [later])) \<subseteq> U \<Longrightarrow>
      set (map rerase
        (flts [bsimpStrong_prune_pair earlier later])) \<subseteq> U"
  shows "set (map rerase (flts (bsimpStrong_prune_rows rs))) \<subseteq> U"
  unfolding bsimpStrong_prune_rows_def
  by (rule map_rerase_bsimpStrong_prune_rows_acc_pair_subsetI[OF rows pair])

lemma map_rerase_bsimpStrong_prune_rows_later_shared_subsetI:
  assumes rows: "set (map rerase rs) \<subseteq> U"
    and flat_closed: "\<And>q. q \<in> U \<Longrightarrow> set (rflts [q]) \<subseteq> U"
    and shared: "\<And>bs2 rbs lrs rrs k.
      rerase (ASEQ bs2 (AALTs rbs rrs) k) \<in> U \<Longrightarrow>
      set (map rerase (flts [bsimp7_ASEQ_atom bs2
        (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k])) \<subseteq> U"
  shows "set (map rerase (flts (bsimpStrong_prune_rows rs))) \<subseteq> U"
proof (rule map_rerase_bsimpStrong_prune_rows_pair_subsetI)
  fix r
  assume r: "r \<in> set rs"
  have "rerase r \<in> U"
    using rows r by auto
  then show "set (map rerase (flts [r])) \<subseteq> U"
    by (rule map_rerase_flts_singleton_flat_closed[OF _ flat_closed])
next
  fix earlier later
  assume later: "set (map rerase (flts [later])) \<subseteq> U"
  show "set (map rerase
      (flts [bsimpStrong_prune_pair earlier later])) \<subseteq> U"
    by (rule map_rerase_bsimpStrong_prune_pair_later_shared_subsetI
        [OF later shared])
qed

lemma map_rerase_bpder_strong_rows_norm_later_shared_subsetI:
  assumes norm: "\<And>q p. q \<in> set rs \<Longrightarrow>
      p \<in> set (bpder_norm_list c q) \<Longrightarrow>
      set (map rerase (flts [bsimpStrong p])) \<subseteq> U"
    and flat_closed: "\<And>q. q \<in> U \<Longrightarrow> set (rflts [q]) \<subseteq> U"
    and shared: "\<And>bs2 rbs lrs rrs k.
      rerase (ASEQ bs2 (AALTs rbs rrs) k) \<in> U \<Longrightarrow>
      set (map rerase (flts [bsimp7_ASEQ_atom bs2
        (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k])) \<subseteq> U"
  shows "set (map rerase (bpder_strong_rows c rs)) \<subseteq> U"
proof (rule map_rerase_bpder_strong_rows_local_subsetI)
  fix q
  assume q: "q \<in> set rs"
  show "set (map rerase (flts (bpder_strong_list c q))) \<subseteq> U"
    by (rule map_rerase_flts_bpder_strong_list_subsetI)
      (use norm[OF q] in blast)
next
  fix xs
  assume xs: "set (map rerase xs) \<subseteq> U"
  show "set (map rerase (flts (bsimpStrong_prune_rows xs))) \<subseteq> U"
    by (rule map_rerase_bsimpStrong_prune_rows_later_shared_subsetI
        [OF xs flat_closed shared])
qed

lemma map_rerase_bpders_strong_rows_subsetI:
  assumes init: "set (map rerase rs) \<subseteq> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
  shows "set (map rerase (bpders_strong_rows rs s)) \<subseteq> U"
  using init
proof (induct s arbitrary: rs)
  case Nil
  then show ?case
    by simp
next
  case (Cons c s)
  have rows: "set (map rerase (bpder_strong_rows c rs)) \<subseteq> U"
    by (rule step[OF Cons.prems])
  have tail:
    "set (map rerase (bpders_strong_rows (bpder_strong_rows c rs) s))
      \<subseteq> U"
    by (rule Cons.hyps[OF rows])
  show ?case
    using tail by simp
qed

lemma map_rerase_bpders_strong_rows_norm_later_shared_subsetI:
  assumes init: "set (map rerase rs) \<subseteq> U"
    and flat_closed: "\<And>q. q \<in> U \<Longrightarrow> set (rflts [q]) \<subseteq> U"
    and norm: "\<And>ars c q p. set (map rerase ars) \<subseteq> U \<Longrightarrow>
      q \<in> set ars \<Longrightarrow> p \<in> set (bpder_norm_list c q) \<Longrightarrow>
      set (map rerase (flts [bsimpStrong p])) \<subseteq> U"
    and shared: "\<And>bs2 rbs lrs rrs k.
      rerase (ASEQ bs2 (AALTs rbs rrs) k) \<in> U \<Longrightarrow>
      set (map rerase (flts [bsimp7_ASEQ_atom bs2
        (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k])) \<subseteq> U"
  shows "set (map rerase (bpders_strong_rows rs s)) \<subseteq> U"
proof (rule map_rerase_bpders_strong_rows_subsetI[OF init])
  fix ars c
  assume ars: "set (map rerase ars) \<subseteq> U"
  show "set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
    by (rule map_rerase_bpder_strong_rows_norm_later_shared_subsetI)
      (use ars flat_closed norm shared in blast)+
qed

lemma asizes_rsizes_rerase:
  "rsizes (map rerase rs) = asizes rs"
  by (induct rs) (simp_all add: asizes_def asize_rsize)

lemma asizes_distinct_rerase_finite_universe_bound:
  assumes finite: "finite U"
      and rows: "set (map rerase rs) \<subseteq> U"
      and distinct: "distinct (map rerase rs)"
      and member_size: "\<And>q. q \<in> U \<Longrightarrow> rsize q \<le> M"
  shows "asizes rs \<le> card U * M"
proof -
  have "rsizes (map rerase rs) \<le> card U * M"
    by (rule rsizes_distinct_finite_universe_bound
        [OF finite rows distinct member_size])
  then show ?thesis
    by (simp add: asizes_def asize_rsize comp_def)
qed

lemma length_bpders_strong_rows_finite_universe_boundI:
  assumes init: "set (map rerase rs) \<subseteq> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
      and finite: "finite U"
      and distinct: "distinct (map rerase rs)"
  shows "length (bpders_strong_rows rs s) \<le> card U"
proof -
  have rows:
    "set (map rerase (bpders_strong_rows rs s)) \<subseteq> U"
    by (rule map_rerase_bpders_strong_rows_subsetI[OF init step])
  have dist:
    "distinct (map rerase (bpders_strong_rows rs s))"
    by (rule distinct_map_rerase_bpders_strong_rows[OF distinct])
  have "length (map rerase (bpders_strong_rows rs s)) \<le> card U"
    by (rule length_distinct_subset_card[OF finite rows dist])
  then show ?thesis
    by simp
qed

lemma length_bpders_strong1_rows_finite_universe_boundI:
  assumes init: "rerase r \<in> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
      and finite: "finite U"
  shows "length (bpders_strong1_rows r s) \<le> card U"
proof -
  have rows: "set (map rerase [r]) \<subseteq> U"
    using init by simp
  have distinct_rows: "distinct (map rerase [r])"
    by simp
  have "length (bpders_strong_rows [r] s) \<le> card U"
    by (rule length_bpders_strong_rows_finite_universe_boundI
        [OF rows step finite distinct_rows])
  then show ?thesis
    by (simp add: bpders_strong1_rows_def)
qed

lemma length_bpders_strong_rows_card_boundI:
  assumes init: "set (map rerase rs) \<subseteq> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
      and finite: "finite U"
      and distinct: "distinct (map rerase rs)"
      and card_bound: "card U \<le> C"
  shows "length (bpders_strong_rows rs s) \<le> C"
proof -
  have "length (bpders_strong_rows rs s) \<le> card U"
    by (rule length_bpders_strong_rows_finite_universe_boundI
        [OF init step finite distinct])
  also have "... \<le> C"
    by (rule card_bound)
  finally show ?thesis .
qed

lemma length_bpders_strong1_rows_card_boundI:
  assumes init: "rerase r \<in> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
      and finite: "finite U"
      and card_bound: "card U \<le> C"
  shows "length (bpders_strong1_rows r s) \<le> C"
proof -
  have "length (bpders_strong1_rows r s) \<le> card U"
    by (rule length_bpders_strong1_rows_finite_universe_boundI
        [OF init step finite])
  also have "... \<le> C"
    by (rule card_bound)
  finally show ?thesis .
qed

lemma asizes_bpders_strong_rows_finite_universe_boundI:
  assumes init: "set (map rerase rs) \<subseteq> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
      and finite: "finite U"
      and member_size: "\<And>q. q \<in> U \<Longrightarrow> rsize q \<le> M"
      and distinct: "distinct (map rerase rs)"
  shows "asizes (bpders_strong_rows rs s) \<le> card U * M"
proof -
  have rows:
    "set (map rerase (bpders_strong_rows rs s)) \<subseteq> U"
    by (rule map_rerase_bpders_strong_rows_subsetI[OF init step])
  have dist:
    "distinct (map rerase (bpders_strong_rows rs s))"
    by (rule distinct_map_rerase_bpders_strong_rows[OF distinct])
  show ?thesis
    by (rule asizes_distinct_rerase_finite_universe_bound
        [OF finite rows dist member_size])
qed

lemma asizes_bpders_strong1_rows_finite_universe_boundI:
  assumes init: "rerase r \<in> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
      and finite: "finite U"
      and member_size: "\<And>q. q \<in> U \<Longrightarrow> rsize q \<le> M"
  shows "asizes (bpders_strong1_rows r s) \<le> card U * M"
proof -
  have rows: "set (map rerase [r]) \<subseteq> U"
    using init by simp
  have distinct_rows: "distinct (map rerase [r])"
    by simp
  have "asizes (bpders_strong_rows [r] s) \<le> card U * M"
    by (rule asizes_bpders_strong_rows_finite_universe_boundI
        [OF rows step finite member_size distinct_rows])
  then show ?thesis
    by (simp add: bpders_strong1_rows_def)
qed

lemma asizes_bpders_strong_rows_cubic_universe_boundI:
  assumes init: "set (map rerase rs) \<subseteq> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
      and finite: "finite U"
      and card_bound: "card U \<le> C"
      and member_size: "\<And>q. q \<in> U \<Longrightarrow> rsize q \<le> M"
      and distinct: "distinct (map rerase rs)"
      and cubic: "C * M \<le> B"
  shows "asizes (bpders_strong_rows rs s) \<le> B"
proof -
  have "asizes (bpders_strong_rows rs s) \<le> card U * M"
    by (rule asizes_bpders_strong_rows_finite_universe_boundI
        [OF init step finite member_size distinct])
  also have "... \<le> C * M"
    by (rule mult_right_mono[OF card_bound]) simp
  also have "... \<le> B"
    by (rule cubic)
  finally show ?thesis .
qed

lemma asizes_bpders_strong_rows_norm_later_shared_finite_universe_boundI:
  assumes init: "set (map rerase rs) \<subseteq> U"
    and flat_closed: "\<And>q. q \<in> U \<Longrightarrow> set (rflts [q]) \<subseteq> U"
    and norm: "\<And>ars c q p. set (map rerase ars) \<subseteq> U \<Longrightarrow>
      q \<in> set ars \<Longrightarrow> p \<in> set (bpder_norm_list c q) \<Longrightarrow>
      set (map rerase (flts [bsimpStrong p])) \<subseteq> U"
    and shared: "\<And>bs2 rbs lrs rrs k.
      rerase (ASEQ bs2 (AALTs rbs rrs) k) \<in> U \<Longrightarrow>
      set (map rerase (flts [bsimp7_ASEQ_atom bs2
        (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k])) \<subseteq> U"
    and finite: "finite U"
    and member_size: "\<And>q. q \<in> U \<Longrightarrow> rsize q \<le> M"
    and distinct: "distinct (map rerase rs)"
  shows "asizes (bpders_strong_rows rs s) \<le> card U * M"
proof (rule asizes_bpders_strong_rows_finite_universe_boundI
    [OF init _ finite member_size distinct])
  fix ars c
  assume ars: "set (map rerase ars) \<subseteq> U"
  show "set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
    by (rule map_rerase_bpder_strong_rows_norm_later_shared_subsetI)
      (use ars flat_closed norm shared in blast)+
qed

lemma asizes_bpders_strong_rows_norm_later_shared_cubic_universe_boundI:
  assumes init: "set (map rerase rs) \<subseteq> U"
    and flat_closed: "\<And>q. q \<in> U \<Longrightarrow> set (rflts [q]) \<subseteq> U"
    and norm: "\<And>ars c q p. set (map rerase ars) \<subseteq> U \<Longrightarrow>
      q \<in> set ars \<Longrightarrow> p \<in> set (bpder_norm_list c q) \<Longrightarrow>
      set (map rerase (flts [bsimpStrong p])) \<subseteq> U"
    and shared: "\<And>bs2 rbs lrs rrs k.
      rerase (ASEQ bs2 (AALTs rbs rrs) k) \<in> U \<Longrightarrow>
      set (map rerase (flts [bsimp7_ASEQ_atom bs2
        (bsimp_AALTs rbs (prune_eq1_against lrs rrs)) k])) \<subseteq> U"
    and finite: "finite U"
    and card_bound: "card U \<le> C"
    and member_size: "\<And>q. q \<in> U \<Longrightarrow> rsize q \<le> M"
    and distinct: "distinct (map rerase rs)"
    and cubic: "C * M \<le> B"
  shows "asizes (bpders_strong_rows rs s) \<le> B"
proof -
  have "asizes (bpders_strong_rows rs s) \<le> card U * M"
    by (rule asizes_bpders_strong_rows_norm_later_shared_finite_universe_boundI
        [OF init flat_closed norm shared finite member_size distinct])
  also have "... \<le> C * M"
    by (rule mult_right_mono[OF card_bound]) simp
  also have "... \<le> B"
    by (rule cubic)
  finally show ?thesis .
qed

lemma asizes_bpders_strong1_rows_cubic_universe_boundI:
  assumes init: "rerase r \<in> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
      and finite: "finite U"
      and card_bound: "card U \<le> C"
      and member_size: "\<And>q. q \<in> U \<Longrightarrow> rsize q \<le> M"
      and cubic: "C * M \<le> B"
  shows "asizes (bpders_strong1_rows r s) \<le> B"
proof -
  have "asizes (bpders_strong1_rows r s) \<le> card U * M"
    by (rule asizes_bpders_strong1_rows_finite_universe_boundI
        [OF init step finite member_size])
  also have "... \<le> C * M"
    by (rule mult_right_mono[OF card_bound]) simp
  also have "... \<le> B"
    by (rule cubic)
  finally show ?thesis .
qed

lemma asize_bp_der_strong_finite_universe_boundI:
  assumes init: "rerase r \<in> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
      and finite: "finite U"
      and member_size: "\<And>q. q \<in> U \<Longrightarrow> rsize q \<le> M"
  shows "asize (bp_der_strong c r) \<le> Suc (card U * M)"
proof -
  have rows:
    "asizes (bpders_strong1_rows r [c]) \<le> card U * M"
    by (rule asizes_bpders_strong1_rows_finite_universe_boundI
        [OF init step finite member_size])
  have "asize (bp_der_strong c r) \<le>
      Suc (asizes (bpder_strong_rows c [r]))"
    by (rule asize_bp_der_strong_le_rows)
  also have "... \<le> Suc (card U * M)"
    using rows by (simp add: bpders_strong1_rows_def)
  finally show ?thesis .
qed

lemma asize_bp_der_strong_cubic_universe_boundI:
  assumes init: "rerase r \<in> U"
      and step: "\<And>ars c. set (map rerase ars) \<subseteq> U \<Longrightarrow>
        set (map rerase (bpder_strong_rows c ars)) \<subseteq> U"
      and finite: "finite U"
      and card_bound: "card U \<le> C"
      and member_size: "\<And>q. q \<in> U \<Longrightarrow> rsize q \<le> M"
      and cubic: "Suc (C * M) \<le> B"
  shows "asize (bp_der_strong c r) \<le> B"
proof -
  have "asize (bp_der_strong c r) \<le> Suc (card U * M)"
    by (rule asize_bp_der_strong_finite_universe_boundI
        [OF init step finite member_size])
  also have "... \<le> Suc (C * M)"
    by (simp add: card_bound mult_right_mono)
  also have "... \<le> B"
    by (rule cubic)
  finally show ?thesis .
qed

lemma thesis_ch7_evil5_bders_simp_size_16:
  "asize (bders_simp (intern (thesis_ch7_evil 5))
      (replicate 16 thesis_ch7_a)) = 14876"
  by eval

lemma thesis_ch7_evil5_bders_simp8_size_16:
  "asize (bders_simp8 (intern (thesis_ch7_evil 5))
      (replicate 16 thesis_ch7_a)) = 1308"
  by eval

lemma thesis_ch7_evil5_bders_simpStrong_lt_simp8_size_16:
  "asize (bders_simpStrong (intern (thesis_ch7_evil 5))
      (replicate 16 thesis_ch7_a)) < 1308"
  by eval

lemma thesis_ch7_evil5_bders_simpStrong_size_16_under_825:
  "asize (bders_simpStrong (intern (thesis_ch7_evil 5))
      (replicate 16 thesis_ch7_a)) < 825"
  by eval

lemma thesis_ch7_evil5_bders_simpStrong_size_16_not_under_812:
  "\<not> asize (bders_simpStrong (intern (thesis_ch7_evil 5))
      (replicate 16 thesis_ch7_a)) < 812"
  by eval

lemma thesis_ch7_evil5_bpders_norm17_row_size_16:
  "asizes (bpders_norm17_rows (bsimp7 (intern (thesis_ch7_evil 5)))
      (replicate 16 thesis_ch7_a)) = 645"
  by eval

definition thesis_ch7_overlap :: arexp where
  "thesis_ch7_overlap =
    AALTs []
      [ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b,
          ACHAR [] thesis_ch7_d]) (ACHAR [] thesis_ch7_c),
       ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_c,
          ACHAR [] thesis_ch7_e]) (ACHAR [] thesis_ch7_c)]"

definition thesis_ch7_overlap_pruned :: arexp where
  "thesis_ch7_overlap_pruned =
    AALTs []
      [ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b,
          ACHAR [] thesis_ch7_d]) (ACHAR [] thesis_ch7_c),
       ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_c, ACHAR [] thesis_ch7_e])
          (ACHAR [] thesis_ch7_c)]"

lemma thesis_ch7_bsimp_misses_overlap_prune:
  "bsimp thesis_ch7_overlap = thesis_ch7_overlap"
  by (simp add: thesis_ch7_overlap_def thesis_ch7_a_def thesis_ch7_b_def
      thesis_ch7_c_def thesis_ch7_d_def thesis_ch7_e_def bsimp_ASEQ_def)

lemma thesis_ch7_overlap_pruned_smaller:
  "asize thesis_ch7_overlap_pruned < asize thesis_ch7_overlap"
  by (simp add: thesis_ch7_overlap_def thesis_ch7_overlap_pruned_def)

lemma thesis_ch7_overlap_pruned_same_language:
  "L (erase thesis_ch7_overlap) = L (erase thesis_ch7_overlap_pruned)"
  by (auto simp add: thesis_ch7_overlap_def thesis_ch7_overlap_pruned_def
      thesis_ch7_a_def thesis_ch7_b_def thesis_ch7_c_def thesis_ch7_d_def
      thesis_ch7_e_def Sequ_def)

lemma thesis_ch7_bsimpStrong_prunes_overlap:
  "bsimpStrong thesis_ch7_overlap = thesis_ch7_overlap_pruned"
  by (simp add: thesis_ch7_overlap_def thesis_ch7_overlap_pruned_def
      thesis_ch7_a_def thesis_ch7_b_def thesis_ch7_c_def thesis_ch7_d_def
      thesis_ch7_e_def bsimpStrong_AALTs_def bsimpStrong_prune_rows_def
      bsimpStrong_prune_pair_def bsimp7_ASEQ_atom_def)

lemma thesis_ch7_bsimpStrong_overlap_smaller:
  "asize (bsimpStrong thesis_ch7_overlap) < asize thesis_ch7_overlap"
  by (simp add: thesis_ch7_bsimpStrong_prunes_overlap
      thesis_ch7_overlap_pruned_smaller)

lemma thesis_ch7_bsimpStrong_overlap_same_language:
  "L (erase (bsimpStrong thesis_ch7_overlap)) = L (erase thesis_ch7_overlap)"
  by (simp add: thesis_ch7_bsimpStrong_prunes_overlap
      thesis_ch7_overlap_pruned_same_language)

lemma thesis_cubic_smoke_A_shared_suffix:
  "bsimp thesis_ch7_overlap = thesis_ch7_overlap"
  "bsimpCubic thesis_ch7_overlap = thesis_ch7_overlap_pruned"
  "asize (bsimpCubic thesis_ch7_overlap) < asize thesis_ch7_overlap"
  by eval+

lemma thesis_cubic_smoke_B_ch7_three_star:
  "asize (bders_simp (intern (thesis_ch7_evil 5))
      (replicate 16 thesis_ch7_a)) = 14876"
  "asize (bders_simp8 (intern (thesis_ch7_evil 5))
      (replicate 16 thesis_ch7_a)) = 1308"
  "asize (bders_simpCubic (intern (thesis_ch7_evil 5))
      (replicate 16 thesis_ch7_a)) < 825"
  by eval+

definition thesis_cubic_counterexample_C :: arexp where
  "thesis_cubic_counterexample_C =
    AALTs []
      [ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b,
          ACHAR [] thesis_ch7_d])
          (ACHAR [] thesis_ch7_c),
       ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b])
          (ACHAR [] thesis_ch7_c)]"

definition thesis_cubic_counterexample_C_pruned :: arexp where
  "thesis_cubic_counterexample_C_pruned =
    ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b,
        ACHAR [] thesis_ch7_d])
      (ACHAR [] thesis_ch7_c)"

lemma thesis_cubic_counterexample_C_checks:
  "bsimp thesis_cubic_counterexample_C = thesis_cubic_counterexample_C"
  "bsimpCubic thesis_cubic_counterexample_C =
    thesis_cubic_counterexample_C_pruned"
  "asize (bsimpCubic thesis_cubic_counterexample_C) <
    asize thesis_cubic_counterexample_C"
  by eval+

definition thesis_cubic_counterexample_D :: arexp where
  "thesis_cubic_counterexample_D =
    AALTs []
      [ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b])
          (ACHAR [] thesis_ch7_c),
       ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_d])
          (ACHAR [] thesis_ch7_c),
       ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_e])
          (ACHAR [] thesis_ch7_c)]"

definition thesis_cubic_counterexample_D_pruned :: arexp where
  "thesis_cubic_counterexample_D_pruned =
    AALTs []
      [ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b])
          (ACHAR [] thesis_ch7_c),
       ASEQ [] (ACHAR [] thesis_ch7_d) (ACHAR [] thesis_ch7_c),
       ASEQ [] (ACHAR [] thesis_ch7_e) (ACHAR [] thesis_ch7_c)]"

lemma thesis_cubic_counterexample_D_checks:
  "bsimp thesis_cubic_counterexample_D = thesis_cubic_counterexample_D"
  "bsimpCubic thesis_cubic_counterexample_D =
    thesis_cubic_counterexample_D_pruned"
  "asize (bsimpCubic thesis_cubic_counterexample_D) <
    asize thesis_cubic_counterexample_D"
  by eval+

definition thesis_cubic_counterexample_E :: arexp where
  "thesis_cubic_counterexample_E =
    AALTs []
      [ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b])
          (ASEQ [] (ACHAR [] thesis_ch7_c) (ACHAR [] thesis_ch7_d)),
       ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_e])
          (ASEQ [] (ACHAR [] thesis_ch7_c) (ACHAR [] thesis_ch7_d))]"

definition thesis_cubic_counterexample_E_pruned :: arexp where
  "thesis_cubic_counterexample_E_pruned =
    AALTs []
      [ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b])
          (ASEQ [] (ACHAR [] thesis_ch7_c) (ACHAR [] thesis_ch7_d)),
       ASEQ [] (ACHAR [] thesis_ch7_e)
          (ASEQ [] (ACHAR [] thesis_ch7_c) (ACHAR [] thesis_ch7_d))]"

lemma thesis_cubic_counterexample_E_checks:
  "bsimp thesis_cubic_counterexample_E = thesis_cubic_counterexample_E"
  "bsimpCubic thesis_cubic_counterexample_E =
    thesis_cubic_counterexample_E_pruned"
  "asize (bsimpCubic thesis_cubic_counterexample_E) <
    asize thesis_cubic_counterexample_E"
  by eval+

definition thesis_cubic_counterexample_F :: arexp where
  "thesis_cubic_counterexample_F =
    AALTs []
      [ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b,
          ACHAR [] thesis_ch7_d]) (ACHAR [] thesis_ch7_c),
       ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b])
          (ACHAR [] thesis_ch7_c),
       ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_e])
          (ACHAR [] thesis_ch7_c)]"

definition thesis_cubic_counterexample_F_pruned :: arexp where
  "thesis_cubic_counterexample_F_pruned =
    AALTs []
      [ASEQ [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b,
          ACHAR [] thesis_ch7_d]) (ACHAR [] thesis_ch7_c),
       ASEQ [] (ACHAR [] thesis_ch7_e) (ACHAR [] thesis_ch7_c)]"

lemma thesis_cubic_counterexample_F_checks:
  "bsimp thesis_cubic_counterexample_F = thesis_cubic_counterexample_F"
  "bsimpCubic thesis_cubic_counterexample_F =
    thesis_cubic_counterexample_F_pruned"
  "asize (bsimpCubic thesis_cubic_counterexample_F) <
    asize thesis_cubic_counterexample_F"
  by eval+

definition thesis_cubic_counterexample_G :: arexp where
  "thesis_cubic_counterexample_G =
    ANTIMES [] (AALTs [] [AZERO, AONE []]) 3"

definition thesis_cubic_counterexample_G_pruned :: arexp where
  "thesis_cubic_counterexample_G_pruned = AONE [Z, Z, Z, S]"

lemma thesis_cubic_counterexample_G_checks:
  "bsimpStrong thesis_cubic_counterexample_G =
    thesis_cubic_counterexample_G"
  "bsimpCubic thesis_cubic_counterexample_G =
    thesis_cubic_counterexample_G_pruned"
  "asize (bsimpCubic thesis_cubic_counterexample_G) <
    asize thesis_cubic_counterexample_G"
  by eval+

definition thesis_cubic_counterexample_H :: arexp where
  "thesis_cubic_counterexample_H =
    ANTIMES [] (AALTs [] [ACHAR [] thesis_ch7_a, ACHAR [] thesis_ch7_b]) 0"

definition thesis_cubic_counterexample_H_pruned :: arexp where
  "thesis_cubic_counterexample_H_pruned = AONE [S]"

lemma thesis_cubic_counterexample_H_checks:
  "bsimpStrong thesis_cubic_counterexample_H =
    thesis_cubic_counterexample_H"
  "bsimpCubic thesis_cubic_counterexample_H =
    thesis_cubic_counterexample_H_pruned"
  "asize (bsimpCubic thesis_cubic_counterexample_H) <
    asize thesis_cubic_counterexample_H"
  by eval+

lemma thesis_cubic_smoke_suite_bsimpCubic:
  "bsimpCubic thesis_ch7_overlap = thesis_ch7_overlap_pruned"
  "asize (bders_simpCubic (intern (thesis_ch7_evil 5))
      (replicate 16 thesis_ch7_a)) < 825"
  "bsimpCubic thesis_cubic_counterexample_C =
    thesis_cubic_counterexample_C_pruned"
  "bsimpCubic thesis_cubic_counterexample_D =
    thesis_cubic_counterexample_D_pruned"
  "bsimpCubic thesis_cubic_counterexample_E =
    thesis_cubic_counterexample_E_pruned"
  "bsimpCubic thesis_cubic_counterexample_F =
    thesis_cubic_counterexample_F_pruned"
  "bsimpCubic thesis_cubic_counterexample_G =
    thesis_cubic_counterexample_G_pruned"
  "bsimpCubic thesis_cubic_counterexample_H =
    thesis_cubic_counterexample_H_pruned"
  by eval+

lemma rders_simp3_size:
  shows "rders_simp3 (rerase r) s = rerase (bders_simp3 r s)"
  by (induct s arbitrary: r) (simp_all add: rder_bder_rerase bsimp3_rerase[symmetric])

lemma rders_pder_size:
  shows "rders_pder (rerase r) s = rerase (bders_pder r s)"
  by (induct s arbitrary: r) (simp_all add: bp_der_rerase[symmetric])

lemma rders_pder_norm_size:
  shows "rders_pder_norm (rerase r) s = rerase (bders_pder_norm r s)"
  by (induct s arbitrary: r) (simp_all add: bp_der_norm_rerase[symmetric])

lemma rders_pder_norm6_size:
  shows "rders_pder_norm6 (rerase r) s = rerase (bders_pder_norm6 r s)"
  by (induct s arbitrary: r) (simp_all add: bp_der_norm6_rerase[symmetric])

lemma rders_pder_norm7_size:
  shows "rders_pder_norm7 (rerase r) s = rerase (bders_pder_norm7 r s)"
  by (induct s arbitrary: r) (simp_all add: bp_der_norm7_rerase[symmetric])

lemma rpders_norm_rows_rerase:
  "rpders_norm_rows (map rerase rs) s =
    map rerase (bpders_norm_rows rs s)"
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have "rpders_norm_rows (map rerase rs) (c # s) =
    rpders_norm_rows (rpder_norm_rows c (map rerase rs)) s"
    by simp
  also have "... =
    rpders_norm_rows (map rerase (bpder_norm_rows c rs)) s"
    by (simp add: rerase_bpder_norm_rows)
  also have "... =
    map rerase (bpders_norm_rows (bpder_norm_rows c rs) s)"
    by (rule Cons.hyps)
  finally show ?case by simp
qed

lemma rpders_norm1_rows_rerase:
  "rpders_norm1_rows (rerase r) s =
    map rerase (bpders_norm1_rows r s)"
  using rpders_norm_rows_rerase[of "[r]" s]
  by (simp add: rpders_norm1_rows_def bpders_norm1_rows_def)

lemma rpders_norm6_rows_rerase:
  "rpders_norm6_rows (map rerase rs) s =
    map rerase (bpders_norm6_rows rs s)"
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have "rpders_norm6_rows (map rerase rs) (c # s) =
    rpders_norm6_rows (rpder_norm6_rows c (map rerase rs)) s"
    by simp
  also have "... =
    rpders_norm6_rows (map rerase (bpder_norm6_rows c rs)) s"
    by (simp add: rerase_bpder_norm6_rows)
  also have "... =
    map rerase (bpders_norm6_rows (bpder_norm6_rows c rs) s)"
    by (rule Cons.hyps)
  finally show ?case by simp
qed

lemma rpders_norm16_rows_rerase:
  "rpders_norm16_rows (rerase r) s =
    map rerase (bpders_norm16_rows r s)"
  using rpders_norm6_rows_rerase[of "[r]" s]
  by (simp add: rpders_norm16_rows_def bpders_norm16_rows_def)

lemma rpders_norm7_rows_rerase:
  "rpders_norm7_rows (map rerase rs) s =
    map rerase (bpders_norm7_rows rs s)"
proof (induct s arbitrary: rs)
  case Nil
  then show ?case by simp
next
  case (Cons c s)
  have "rpders_norm7_rows (map rerase rs) (c # s) =
    rpders_norm7_rows (rpder_norm7_rows c (map rerase rs)) s"
    by simp
  also have "... =
    rpders_norm7_rows (map rerase (bpder_norm7_rows c rs)) s"
    by (simp add: rerase_bpder_norm7_rows)
  also have "... =
    map rerase (bpders_norm7_rows (bpder_norm7_rows c rs) s)"
    by (rule Cons.hyps)
  finally show ?case by simp
qed

lemma rpders_norm17_rows_rerase:
  "rpders_norm17_rows (rerase r) s =
    map rerase (bpders_norm17_rows r s)"
  using rpders_norm7_rows_rerase[of "[r]" s]
  by (simp add: rpders_norm17_rows_def bpders_norm17_rows_def)

lemma asize_bp_der_rpd_der:
  shows "asize (bp_der c r) = rsize (rpd_der c (rerase r))"
  by (simp add: asize_rsize bp_der_rerase[symmetric])

lemma asize_bp_der_norm_rpd_der_norm:
  shows "asize (bp_der_norm c r) = rsize (rpd_der_norm c (rerase r))"
  by (simp add: asize_rsize bp_der_norm_rerase[symmetric])

lemma asize_bp_der_norm6_rpd_der_norm6:
  shows "asize (bp_der_norm6 c r) = rsize (rpd_der_norm6 c (rerase r))"
  by (simp add: asize_rsize bp_der_norm6_rerase[symmetric])

lemma asize_bp_der_norm7_rpd_der_norm7:
  shows "asize (bp_der_norm7 c r) = rsize (rpd_der_norm7 c (rerase r))"
  by (simp add: asize_rsize bp_der_norm7_rerase[symmetric])

lemma asize_bders_pder_rders_pder:
  shows "asize (bders_pder r s) = rsize (rders_pder (rerase r) s)"
  by (simp add: asize_rsize rders_pder_size)

lemma asize_bders_pder_norm_rders_pder_norm:
  shows "asize (bders_pder_norm r s) = rsize (rders_pder_norm (rerase r) s)"
  by (simp add: asize_rsize rders_pder_norm_size)

lemma asize_bders_pder_norm6_rders_pder_norm6:
  shows "asize (bders_pder_norm6 r s) = rsize (rders_pder_norm6 (rerase r) s)"
  by (simp add: asize_rsize rders_pder_norm6_size)

lemma asize_bders_pder_norm7_rders_pder_norm7:
  shows "asize (bders_pder_norm7 r s) = rsize (rders_pder_norm7 (rerase r) s)"
  by (simp add: asize_rsize rders_pder_norm7_size)

lemma asize_bp_der_norm_cubic:
  assumes "legacy_rrexp (rerase r)"
  shows "asize (bp_der_norm c r) \<le> Suc (2 * (rsize (rerase r) + 3) ^ 3)"
  using rsize_rpd_der_norm_cubic[OF assms, of c]
  by (simp add: asize_bp_der_norm_rpd_der_norm)

lemma asizes_bpder_norm_list_cubic:
  assumes "legacy_rrexp (rerase r)"
  shows "asizes (bpder_norm_list c r) \<le>
    2 * (rsize (rerase r) + 3) ^ 3"
proof -
  have "asizes (bpder_norm_list c r) =
      rsizes (rpder_norm_list c (rerase r))"
    by (simp add: asizes_rsizes_rerase[symmetric]
        rerase_bpder_norm_list)
  also have "... \<le> 2 * (rsize (rerase r) + 3) ^ 3"
    by (rule rsizes_rpder_norm_list_cubic[OF assms])
  finally show ?thesis .
qed

lemma asize_bp_der_strong_cubic:
  assumes "legacy_rrexp (rerase r)"
  shows "asize (bp_der_strong c r) \<le>
    Suc (2 * (rsize (rerase r) + 3) ^ 3)"
proof -
  have "asize (bp_der_strong c r) \<le>
      Suc (asizes (bpder_norm_list c r))"
    by (rule asize_bp_der_strong_le_asizes)
  also have "... \<le> Suc (2 * (rsize (rerase r) + 3) ^ 3)"
    using asizes_bpder_norm_list_cubic[OF assms, of c] by simp
  finally show ?thesis .
qed

corollary aders_pder_finiteness:
  assumes "\<exists>N. \<forall>s. rsize (rders_pder (rerase r) s) \<le> N"
  shows "\<exists>N. \<forall>s. asize (bders_pder r s) \<le> N"
proof -
  from assms obtain N where "\<forall>s. rsize (rders_pder (rerase r) s) \<le> N"
    by blast
  then have "\<forall>s. asize (bders_pder r s) \<le> N"
    by (simp add: asize_bders_pder_rders_pder)
  then show ?thesis by blast
qed

corollary aders_pder_norm_finiteness:
  assumes "\<exists>N. \<forall>s. rsize (rders_pder_norm (rerase r) s) \<le> N"
  shows "\<exists>N. \<forall>s. asize (bders_pder_norm r s) \<le> N"
proof -
  from assms obtain N where "\<forall>s. rsize (rders_pder_norm (rerase r) s) \<le> N"
    by blast
  then have "\<forall>s. asize (bders_pder_norm r s) \<le> N"
    by (simp add: asize_bders_pder_norm_rders_pder_norm)
  then show ?thesis by blast
qed

lemma legacy_rerase_bders_pder:
  assumes "legacy_rrexp (rerase r)"
  shows "legacy_rrexp (rerase (bders_pder r s))"
  using legacy_rders_pder[OF assms, of s] rders_pder_size[of r s]
  by simp

lemma legacy_rerase_bders_pder_norm:
  assumes "legacy_rrexp (rerase r)"
  shows "legacy_rrexp (rerase (bders_pder_norm r s))"
  using legacy_rders_pder_norm[OF assms, of s] rders_pder_norm_size[of r s]
  by simp

lemma legacy_rerase_bders_pder_norm6:
  assumes "legacy_rrexp (rerase r)"
  shows "legacy_rrexp (rerase (bders_pder_norm6 r s))"
  using legacy_rders_pder_norm6[OF assms, of s] rders_pder_norm6_size[of r s]
  by simp

lemma legacy_rerase_bders_pder_norm7:
  assumes "legacy_rrexp (rerase r)"
  shows "legacy_rrexp (rerase (bders_pder_norm7 r s))"
  using legacy_rders_pder_norm7[OF assms, of s] rders_pder_norm7_size[of r s]
  by simp

lemma RL_rerase_bders_pder:
  assumes "legacy_rrexp (rerase r)"
  shows "RL (rerase (bders_pder r s)) = Ders s (RL (rerase r))"
  using RL_rders_pder[OF assms, of s] rders_pder_size[of r s]
  by simp

lemma RL_rerase_bders_pder_norm:
  assumes "legacy_rrexp (rerase r)"
  shows "RL (rerase (bders_pder_norm r s)) = Ders s (RL (rerase r))"
  using RL_rders_pder_norm[OF assms, of s] rders_pder_norm_size[of r s]
  by simp

lemma RL_rerase_bders_pder_norm6:
  assumes "legacy_rrexp (rerase r)"
  shows "RL (rerase (bders_pder_norm6 r s)) = Ders s (RL (rerase r))"
  using RL_rders_pder_norm6[OF assms, of s] rders_pder_norm6_size[of r s]
  by simp

lemma RL_rerase_bders_pder_norm7:
  assumes "legacy_rrexp (rerase r)"
  shows "RL (rerase (bders_pder_norm7 r s)) = Ders s (RL (rerase r))"
  using RL_rders_pder_norm7[OF assms, of s] rders_pder_norm7_size[of r s]
  by simp

(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this original bound-transfer proof for the new constructor cases.
   Bounty counts only if annotated_size_bound itself is preserved or directly
   strengthened; separate wrapper bounds do not count. *)
lemma rders_simp_size:
  shows "rders_simp (rerase r) s  = rerase (bders_simp r s)"
  apply(induct s rule: rev_induct)
  apply simp
  by (simp add: bders_simp_append rder_bder_rerase rders_simp_append bsimp_rerase)


corollary aders_simp_finiteness:
  assumes "\<exists>N. \<forall>s. rsize (rders_simp (rerase r) s) \<le> N"
  shows " \<exists>N. \<forall>s. asize (bders_simp r s) \<le> N"
proof - 
  from assms obtain N where "\<forall>s. rsize (rders_simp (rerase r) s) \<le> N"
    by blast
  then have "\<forall>s. rsize (rerase (bders_simp r s)) \<le> N"
    by (simp add: rders_simp_size) 
  then have "\<forall>s. asize (bders_simp r s) \<le> N"
    by (simp add: asize_rsize) 
  then show "\<exists>N. \<forall>s. asize (bders_simp r s) \<le> N" by blast
qed
  
(* BACKREF-MIGRATION-TODO (proof constructor-case extension):
   Extend this original final bound theorem for the approved representation.
   Do not claim a separate BackRefBoundedBlueprint wrapper as the final bounty. *)
theorem annotated_size_bound:
  assumes "legacy_rrexp (rerase r)"
  shows "\<exists>N. \<forall>s. asize (bders_simp r s) \<le> N"
  apply(rule aders_simp_finiteness)
  using assms rders_simp_bounded by blast




end
