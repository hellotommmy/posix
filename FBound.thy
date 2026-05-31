
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
