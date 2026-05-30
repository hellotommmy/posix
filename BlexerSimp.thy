theory BlexerSimp
  imports Blexer 
begin

(* BACKREF-MIGRATION-COMPLETED (aggressive simplifier/rewrite-system preservation):
   Backreference support must preserve the original thesis-style bsimp route:
   aggressive flattening of alternatives, zero elimination, singleton-alt fuse,
   duplicate/subsumed alternative removal, and the rrewrite/srewrite simulation.
   A conservative structural simplifier is not an acceptable replacement. If a
   proof command runs for more than about 10 seconds, replace it with explicit
   local lemmas or narrower tactics. *)

fun distinctWith :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a list"
  where
  "distinctWith [] eq acc = []"
| "distinctWith (x # xs) eq acc = 
     (if (\<exists> y \<in> acc. eq x y) then distinctWith xs eq acc 
      else x # (distinctWith xs eq ({x} \<union> acc)))"


(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add cases for the new arexp constructors while preserving the existing
   aggressive equivalence test behaviour. Any rule that changes backreference
   structure or capture order needs admin approval before implementation. *)
primrec eq1 ("_ ~1 _" [80, 80] 80) and eq1s where
  "AZERO ~1 y = (case y of AZERO \<Rightarrow> True | _ \<Rightarrow> False)"
| "(AONE bs1) ~1 y = (case y of AONE bs2 \<Rightarrow> True | _ \<Rightarrow> False)"
| "(ACHAR bs1 c) ~1 y = (case y of ACHAR bs2 d \<Rightarrow> c = d | _ \<Rightarrow> False)"
| "(ASEQ bs1 ra1 ra2) ~1 y =
    (case y of ASEQ bs2 rb1 rb2 \<Rightarrow> ra1 ~1 rb1 \<and> ra2 ~1 rb2 | _ \<Rightarrow> False)"
| "(AALTs bs1 rs1) ~1 y =
    (case y of AALTs bs2 rs2 \<Rightarrow> eq1s rs1 rs2 | _ \<Rightarrow> False)"
| "(ASTAR bs1 r1) ~1 y =
    (case y of ASTAR bs2 r2 \<Rightarrow> r1 ~1 r2 | _ \<Rightarrow> False)"
| "(ANTIMES bs1 r1 n1) ~1 y =
    (case y of ANTIMES bs2 r2 n2 \<Rightarrow> r1 ~1 r2 \<and> n1 = n2 | _ \<Rightarrow> False)"
| "(ABACKREF4 bs1 ra1 ra2 ra3 ra4 cs1) ~1 y =
    (case y of ABACKREF4 bs2 rb1 rb2 rb3 rb4 cs2 \<Rightarrow>
       cs1 = cs2 \<and> ra1 ~1 rb1 \<and> ra2 ~1 rb2 \<and> ra3 ~1 rb3 \<and> ra4 ~1 rb4
     | _ \<Rightarrow> False)"
| "(AHALF bs1 r1 cs1 rep1) ~1 y =
    (case y of AHALF bs2 r2 cs2 rep2 \<Rightarrow> cs1 = cs2 \<and> rep1 = rep2 \<and> r1 ~1 r2
     | _ \<Rightarrow> False)"
| "(ARESIDUE bs1 cs1 rep1) ~1 y =
    (case y of ARESIDUE bs2 cs2 rep2 \<Rightarrow> cs1 = cs2 \<and> rep1 = rep2 | _ \<Rightarrow> False)"
| "eq1s [] ys = (case ys of [] \<Rightarrow> True | _ \<Rightarrow> False)"
| "eq1s (r # rs) ys =
    (case ys of s # ss \<Rightarrow> r ~1 s \<and> eq1s rs ss | _ \<Rightarrow> False)"

lemma ABACKREF4_cs_affects_language:
  fixes c :: char
  shows
    "L (erase (ABACKREF4 [] (AONE []) (AONE []) (AONE []) (AONE []) [])) \<noteq>
     L (erase (ABACKREF4 [] (AONE []) (AONE []) (AONE []) (AONE []) [c]))"
proof
  assume same:
    "L (erase (ABACKREF4 [] (AONE []) (AONE []) (AONE []) (AONE []) [])) =
     L (erase (ABACKREF4 [] (AONE []) (AONE []) (AONE []) (AONE []) [c]))"
  have empty_left:
    "[] \<in> L (erase (ABACKREF4 [] (AONE []) (AONE []) (AONE []) (AONE []) []))"
    by (simp add: backref_lang4_def)
  have empty_not_right:
    "[] \<notin> L (erase (ABACKREF4 [] (AONE []) (AONE []) (AONE []) (AONE []) [c]))"
    by (auto simp add: backref_lang4_def)
  show False
    using same empty_left empty_not_right by blast
qed

(* The ABACKREF4 branch of eq1 must compare cs. Otherwise distinctWith could
   drop a later alternative with the same four subexpressions but a different
   language, as witnessed by ABACKREF4_cs_affects_language. *)

lemma size_list_member_less:
  assumes "r \<in> set rs"
  shows "size r < Suc (size_list size rs)"
  using assms
  by (induct rs) auto

lemma eq1_L:
  assumes "x ~1 y"
  shows "L (erase x) = L (erase y)"
  using assms
proof (induct "size x" arbitrary: x y rule: less_induct)
  case less
  show ?case
  proof (cases x)
  case AZERO
  then show ?thesis using less.prems by (cases y) auto
next
  case (AONE bs)
  then show ?thesis using less.prems by (cases y) auto
next
  case (ACHAR bs c)
  then show ?thesis using less.prems by (cases y) auto
next
  case (ASEQ bs r1 r2)
  note x_ASEQ = ASEQ
  show ?thesis
  proof (cases y)
    case (ASEQ bs' s1 s2)
    have small1: "size r1 < size x"
      using x_ASEQ by simp
    have small2: "size r2 < size x"
      using x_ASEQ by simp
    have eq_left: "r1 ~1 s1"
      using less.prems x_ASEQ ASEQ by simp
    have eq_right: "r2 ~1 s2"
      using less.prems x_ASEQ ASEQ by simp
    have left: "L (erase r1) = L (erase s1)"
      using less.hyps[OF small1 eq_left] .
    have right: "L (erase r2) = L (erase s2)"
      using less.hyps[OF small2 eq_right] .
    then show ?thesis
      using x_ASEQ ASEQ left by (simp add: Sequ_def)
  qed (use less.prems x_ASEQ in auto)
next
  case (AALTs bs rs)
  note x_AALTs = AALTs
  have list_eq:
    "\<And>xs ys bs bs'.
      \<lbrakk>eq1s xs ys;
       \<forall>r \<in> set xs. size r < size x\<rbrakk>
      \<Longrightarrow> L (erase (AALTs bs xs)) = L (erase (AALTs bs' ys))"
  proof -
    fix xs ys bs bs'
    assume eqs: "eq1s xs ys"
      and smalls: "\<forall>r \<in> set xs. size r < size x"
    show "L (erase (AALTs bs xs)) = L (erase (AALTs bs' ys))"
      using eqs smalls
    proof (induct xs arbitrary: ys bs bs')
    case Nil
    then show ?case by (cases ys) simp_all
  next
    case (Cons r xs)
    note IH = Cons.hyps
    note prems = Cons.prems
    show ?case
    proof (cases ys)
      case Nil
      then show ?thesis using prems by simp
    next
      case (Cons s ss)
      have small_r: "size r < size x"
        using prems by simp
      have eq_head: "r ~1 s"
        using prems Cons by simp
      have head: "L (erase r) = L (erase s)"
        using less.hyps[OF small_r eq_head] .
      have eq_tail: "eq1s xs ss"
        using prems Cons by simp
      have small_tail: "\<forall>r \<in> set xs. size r < size x"
        using prems by simp
      have tail: "L (erase (AALTs bs xs)) = L (erase (AALTs bs' ss))"
        using IH[OF eq_tail small_tail] .
      show ?thesis
      proof -
        have "L (erase (AALTs bs (r # xs))) =
              L (erase r) \<union> L (erase (AALTs bs xs))"
          by (cases xs) auto
        also have "... = L (erase s) \<union> L (erase (AALTs bs' ss))"
          using head tail by simp
        also have "... = L (erase (AALTs bs' (s # ss)))"
          by (cases ss) auto
        finally show ?thesis
          using Cons by simp
      qed
    qed
    qed
  qed
  have small: "\<forall>r \<in> set rs. size r < size x"
    using x_AALTs size_list_member_less by auto
  show ?thesis
  proof (cases y)
    case (AALTs bs' ys)
    have eqs: "eq1s rs ys"
      using less.prems x_AALTs AALTs by simp
    have "L (erase (AALTs bs rs)) = L (erase (AALTs bs' ys))"
      using list_eq[OF eqs small] .
    then show ?thesis
      using x_AALTs AALTs by simp
  qed (use less.prems x_AALTs in auto)
next
  case (ASTAR bs r)
  note x_ASTAR = ASTAR
  show ?thesis
  proof (cases y)
    case (ASTAR bs' s)
    have small: "size r < size x"
      using x_ASTAR by simp
    have eq: "r ~1 s"
      using less.prems x_ASTAR ASTAR by simp
    have "L (erase r) = L (erase s)"
      using less.hyps[OF small eq] .
    then show ?thesis
      using x_ASTAR ASTAR by simp
  qed (use less.prems x_ASTAR in auto)
next
  case (ANTIMES bs r n)
  note x_ANTIMES = ANTIMES
  show ?thesis
  proof (cases y)
    case (ANTIMES bs' s m)
    have small: "size r < size x"
      using x_ANTIMES by simp
    have eq: "r ~1 s"
      using less.prems x_ANTIMES ANTIMES by simp
    have n_eq: "n = m"
      using less.prems x_ANTIMES ANTIMES by simp
    have "L (erase r) = L (erase s)"
      using less.hyps[OF small eq] .
    then show ?thesis
      using x_ANTIMES ANTIMES n_eq by simp
  qed (use less.prems x_ANTIMES in auto)
next
  case (ABACKREF4 bs r1 r2 r3 r4 cs)
  note x_ABACKREF4 = ABACKREF4
  show ?thesis
  proof (cases y)
    case (ABACKREF4 bs' s1 s2 s3 s4 ds)
    have small1: "size r1 < size x" and small2: "size r2 < size x"
      and small3: "size r3 < size x" and small4: "size r4 < size x"
      using x_ABACKREF4 by simp_all
    have eq1: "r1 ~1 s1" and eq2: "r2 ~1 s2"
      and eq3: "r3 ~1 s3" and eq4: "r4 ~1 s4" and cs_eq: "cs = ds"
      using less.prems x_ABACKREF4 ABACKREF4 by simp_all
    have l1: "L (erase r1) = L (erase s1)"
      using less.hyps[OF small1 eq1] .
    have l2: "L (erase r2) = L (erase s2)"
      using less.hyps[OF small2 eq2] .
    have l3: "L (erase r3) = L (erase s3)"
      using less.hyps[OF small3 eq3] .
    have l4: "L (erase r4) = L (erase s4)"
      using less.hyps[OF small4 eq4] .
    show ?thesis
      using x_ABACKREF4 ABACKREF4 cs_eq l1 l2 l3 l4 by simp
  qed (use less.prems x_ABACKREF4 in auto)
next
  case (AHALF bs r cs rep)
  note x_AHALF = AHALF
  show ?thesis
  proof (cases y)
    case (AHALF bs' s ds rep')
    have small: "size r < size x"
      using x_AHALF by simp
    have eq: "r ~1 s" and cs_eq: "cs = ds" and rep_eq: "rep = rep'"
      using less.prems x_AHALF AHALF by simp_all
    have "L (erase r) = L (erase s)"
      using less.hyps[OF small eq] .
    then show ?thesis
      using x_AHALF AHALF cs_eq rep_eq by simp
  qed (use less.prems x_AHALF in auto)
next
  case (ARESIDUE bs cs rep)
  then show ?thesis using less.prems by (cases y) auto
  qed
qed

(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add cases for the new arexp constructors while preserving aggressive
   alternative flattening. *)
fun flts :: "arexp list \<Rightarrow> arexp list"
  where 
  "flts [] = []"
| "flts (AZERO # rs) = flts rs"
| "flts ((AALTs bs  rs1) # rs) = (map (fuse bs) rs1) @ flts rs"
| "flts (r1 # rs) = r1 # flts rs"



(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Add cases for new constructor interactions with sequence simplification only
   after the capture-order implications are approved. *)
definition bsimp_ASEQ :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp \<Rightarrow> arexp"
  where
  "bsimp_ASEQ bs1 r1 r2 =
    (if r1 = AZERO \<or> r2 = AZERO then AZERO
     else case r1 of
       AONE bs2 \<Rightarrow> fuse (bs1 @ bs2) r2
     | _ \<Rightarrow> ASEQ bs1 r1 r2)"

lemma bsimp_ASEQ0[simp]:
  shows "bsimp_ASEQ bs r1 AZERO = AZERO"
  by (simp add: bsimp_ASEQ_def)

lemma bsimp_ASEQ_left0[simp]:
  shows "bsimp_ASEQ bs AZERO r2 = AZERO"
  by (simp add: bsimp_ASEQ_def)

lemma bsimp_ASEQ1:
  assumes "r1 \<noteq> AZERO" "r2 \<noteq> AZERO" "\<nexists>bs. r1 = AONE bs"
  shows "bsimp_ASEQ bs r1 r2 = ASEQ bs r1 r2"
  using assms
  by (cases r1) (auto simp add: bsimp_ASEQ_def)

lemma bsimp_ASEQ2[simp]:
  shows "bsimp_ASEQ bs1 (AONE bs2) r2 = fuse (bs1 @ bs2) r2"
  by (cases r2) (simp_all add: bsimp_ASEQ_def)


(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation):
   Preserve singleton-alt fuse and zero-alt elimination for the extended arexp
   datatype. *)
fun bsimp_AALTs :: "bit list \<Rightarrow> arexp list \<Rightarrow> arexp"
  where
  "bsimp_AALTs _ [] = AZERO"
| "bsimp_AALTs bs1 [r] = fuse bs1 r"
| "bsimp_AALTs bs1 rs = AALTs bs1 rs"




(* BACKREF-MIGRATION-COMPLETED (datatype/function augmentation, ADMIN APPROVAL REQUIRED):
   Extend bsimp with the new arexp constructors while keeping the original
   aggressive, structure-changing simplifier. Do not replace this with a weak
   structural recursion or a wrapper equality theorem. *)
fun bsimp :: "arexp \<Rightarrow> arexp" 
  where
  "bsimp (ASEQ bs1 r1 r2) = bsimp_ASEQ bs1 (bsimp r1) (bsimp r2)"
| "bsimp (AALTs bs1 rs) = bsimp_AALTs bs1 (distinctWith (flts (map bsimp rs)) eq1 {}) "
| "bsimp r = r"

definition bsimp3_ASEQ_atom :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp \<Rightarrow> arexp" where
  "bsimp3_ASEQ_atom bs r1 r2 =
    (if r1 = AZERO \<or> r2 = AZERO then AZERO
     else case r1 of
       AONE bs2 \<Rightarrow> fuse (bs @ bs2) r2
     | _ \<Rightarrow> ASEQ bs r1 r2)"

fun bsimp3_seq_row :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp \<Rightarrow> arexp list" where
  "bsimp3_seq_row bs r1 r2 = [bsimp3_ASEQ_atom bs r1 r2]"

definition bsimp3_ASEQ :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp \<Rightarrow> arexp" where
  "bsimp3_ASEQ bs r1 r2 =
    (case r1 of
      AALTs bs1 rs1 \<Rightarrow>
        bsimp_AALTs (bs @ bs1)
          (distinctWith (flts (concat (map (\<lambda>x. bsimp3_seq_row [] x r2) rs1))) eq1 {})
    | _ \<Rightarrow>
        bsimp_AALTs [] (distinctWith (flts (bsimp3_seq_row bs r1 r2)) eq1 {}))"

(* Cubic-bound prototype for the annotated layer. This mirrors rsimp3 and only
   distributes a sequence over a left alternative frontier, preserving the
   order of right-hand alternative choice bits for later bitcoded proofs. *)
fun bsimp3 :: "arexp \<Rightarrow> arexp" 
  where
  "bsimp3 (ASEQ bs1 r1 r2) = bsimp3_ASEQ bs1 (bsimp3 r1) (bsimp3 r2)"
| "bsimp3 (AALTs bs1 rs) = bsimp_AALTs bs1 (distinctWith (flts (map bsimp3 rs)) eq1 {})"
| "bsimp3 r = r"

fun 
  bders_simp3 :: "arexp \<Rightarrow> string \<Rightarrow> arexp"
where
  "bders_simp3 r [] = r"
| "bders_simp3 r (c # s) = bders_simp3 (bsimp3 (bder c r)) s"

fun bsimp4_ASEQ_atom :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp \<Rightarrow> arexp" where
  "bsimp4_ASEQ_atom bs AZERO r2 = AZERO"
| "bsimp4_ASEQ_atom bs (AONE bs2) r2 = fuse (bs @ bs2) r2"
| "bsimp4_ASEQ_atom bs (ASEQ bs2 r1 r2) r3 =
    bsimp4_ASEQ_atom bs2 r1 (bsimp4_ASEQ_atom bs r2 r3)"
| "bsimp4_ASEQ_atom bs (ACHAR bs2 c) AZERO = AZERO"
| "bsimp4_ASEQ_atom bs (ACHAR bs2 c) r2 = ASEQ bs (ACHAR bs2 c) r2"
| "bsimp4_ASEQ_atom bs (AALTs bs2 rs) AZERO = AZERO"
| "bsimp4_ASEQ_atom bs (AALTs bs2 rs) r2 = ASEQ bs (AALTs bs2 rs) r2"
| "bsimp4_ASEQ_atom bs (ASTAR bs2 r) AZERO = AZERO"
| "bsimp4_ASEQ_atom bs (ASTAR bs2 r) r2 = ASEQ bs (ASTAR bs2 r) r2"
| "bsimp4_ASEQ_atom bs (ANTIMES bs2 r n) AZERO = AZERO"
| "bsimp4_ASEQ_atom bs (ANTIMES bs2 r n) r2 = ASEQ bs (ANTIMES bs2 r n) r2"
| "bsimp4_ASEQ_atom bs (ABACKREF4 bs2 r1 r2 r3 r4 s) AZERO = AZERO"
| "bsimp4_ASEQ_atom bs (ABACKREF4 bs2 r1 r2 r3 r4 s) r5 =
    ASEQ bs (ABACKREF4 bs2 r1 r2 r3 r4 s) r5"
| "bsimp4_ASEQ_atom bs (AHALF bs2 r s rep) AZERO = AZERO"
| "bsimp4_ASEQ_atom bs (AHALF bs2 r s rep) r2 = ASEQ bs (AHALF bs2 r s rep) r2"
| "bsimp4_ASEQ_atom bs (ARESIDUE bs2 s rep) AZERO = AZERO"
| "bsimp4_ASEQ_atom bs (ARESIDUE bs2 s rep) r2 = ASEQ bs (ARESIDUE bs2 s rep) r2"

fun bsimp4_seq_row :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp \<Rightarrow> arexp list" where
  "bsimp4_seq_row bs r1 r2 = [bsimp4_ASEQ_atom bs r1 r2]"

definition bsimp4_ASEQ :: "bit list \<Rightarrow> arexp \<Rightarrow> arexp \<Rightarrow> arexp" where
  "bsimp4_ASEQ bs r1 r2 =
    (case r1 of
      AALTs bs1 rs1 \<Rightarrow>
        bsimp_AALTs (bs @ bs1)
          (distinctWith (flts (concat (map (\<lambda>x. bsimp4_seq_row [] x r2) rs1))) eq1 {})
    | _ \<Rightarrow>
        bsimp_AALTs [] (distinctWith (flts (bsimp4_seq_row bs r1 r2)) eq1 {}))"

(* Annotated counterpart of rsimp4. It reassociates left-nested ASEQ nodes while
   preserving the erasure-level head-plus-continuation normal form. *)
fun bsimp4 :: "arexp \<Rightarrow> arexp" 
where
  "bsimp4 (ASEQ bs1 r1 r2) = bsimp4_ASEQ bs1 (bsimp4 r1) (bsimp4 r2)"
| "bsimp4 (AALTs bs1 rs) = bsimp_AALTs bs1 (distinctWith (flts (map bsimp4 rs)) eq1 {})"
| "bsimp4 r = r"

fun 
  bders_simp4 :: "arexp \<Rightarrow> string \<Rightarrow> arexp"
where
  "bders_simp4 r [] = r"
| "bders_simp4 r (c # s) = bders_simp4 (bsimp4 (bder c r)) s"


fun 
  bders_simp :: "arexp \<Rightarrow> string \<Rightarrow> arexp"
where
  "bders_simp r [] = r"
| "bders_simp r (c # s) = bders_simp (bsimp (bder c r)) s"

definition blexer_simp where
 "blexer_simp r s \<equiv> if bnullable (bders_simp (intern r) s) then 
                    decode (bmkeps (bders_simp (intern r) s)) r else None"



lemma bders_simp_append:
  shows "bders_simp r (s1 @ s2) = bders_simp (bders_simp r s1) s2"
  apply(induct s1 arbitrary: r s2)
  apply(simp_all)
  done

lemma bmkeps_fuse:
  assumes "bnullable r"
  shows "bmkeps (fuse bs r) = bs @ bmkeps r"
  using assms
  apply(induct r rule: bnullable.induct) 
        apply(auto)
  apply (metis append.assoc bmkeps_retrieve bmkeps_retrieve_AALTs bnullable.simps(4))  
  done

lemma bmkepss_fuse: 
  assumes "bnullables rs"
  shows "bmkepss (map (fuse bs) rs) = bs @ bmkepss rs"
  using assms
  apply(induct rs arbitrary: bs)
  apply(auto simp add: bmkeps_fuse bnullable_fuse)
  done

lemma bder_fuse:
  shows "bder c (fuse bs a) = fuse bs  (bder c a)"
  apply(induct a arbitrary: bs c)
  apply(simp_all add: Let_def append_assoc fuse_append)
  apply(case_tac x2a; simp add: append_assoc)
  done




(* BACKREF-MIGRATION-COMPLETED (aggressive simplifier/rewrite-system preservation):
   Extend rrewrite/srewrite with context rules for the new constructors and any
   approved backreference simplification rules. The proof obligation remains
   r \<leadsto>* bsimp r and derivative-commutation through rewrites; wrapper
   equivalence theorems do not count as bounty. *)
inductive 
  rrewrite:: "arexp \<Rightarrow> arexp \<Rightarrow> bool" ("_ \<leadsto> _" [99, 99] 99)
and 
  srewrite:: "arexp list \<Rightarrow> arexp list \<Rightarrow> bool" (" _ s\<leadsto> _" [100, 100] 100)
where
  bs1: "ASEQ bs AZERO r2 \<leadsto> AZERO"
| bs2: "ASEQ bs r1 AZERO \<leadsto> AZERO"
| bs3: "ASEQ bs1 (AONE bs2) r \<leadsto> fuse (bs1@bs2) r"
| bs4: "r1 \<leadsto> r2 \<Longrightarrow> ASEQ bs r1 r3 \<leadsto> ASEQ bs r2 r3"
| bs5: "r3 \<leadsto> r4 \<Longrightarrow> ASEQ bs r1 r3 \<leadsto> ASEQ bs r1 r4"
| bs6: "AALTs bs [] \<leadsto> AZERO"
| bs7: "AALTs bs [r] \<leadsto> fuse bs r"
| bs10: "rs1 s\<leadsto> rs2 \<Longrightarrow> AALTs bs rs1 \<leadsto> AALTs bs rs2"
| ss1:  "[] s\<leadsto> []"
| ss2:  "rs1 s\<leadsto> rs2 \<Longrightarrow> (r # rs1) s\<leadsto> (r # rs2)"
| ss3:  "r1 \<leadsto> r2 \<Longrightarrow> (r1 # rs) s\<leadsto> (r2 # rs)"
| ss4:  "(AZERO # rs) s\<leadsto> rs"
| ss5:  "(AALTs bs1 rs1 # rsb) s\<leadsto> ((map (fuse bs1) rs1) @ rsb)"
| ss6:  "L (erase a2) \<subseteq> L (erase a1) \<Longrightarrow> (rsa@[a1]@rsb@[a2]@rsc) s\<leadsto> (rsa@[a1]@rsb@rsc)"


inductive 
  rrewrites:: "arexp \<Rightarrow> arexp \<Rightarrow> bool" ("_ \<leadsto>* _" [100, 100] 100)
where 
  rs1[intro, simp]:"r \<leadsto>* r"
| rs2[intro]: "\<lbrakk>r1 \<leadsto>* r2; r2 \<leadsto> r3\<rbrakk> \<Longrightarrow> r1 \<leadsto>* r3"

inductive 
  srewrites:: "arexp list \<Rightarrow> arexp list \<Rightarrow> bool" ("_ s\<leadsto>* _" [100, 100] 100)
where 
  sss1[intro, simp]:"rs s\<leadsto>* rs"
| sss2[intro]: "\<lbrakk>rs1 s\<leadsto> rs2; rs2 s\<leadsto>* rs3\<rbrakk> \<Longrightarrow> rs1 s\<leadsto>* rs3"


lemma r_in_rstar : "r1 \<leadsto> r2 \<Longrightarrow> r1 \<leadsto>* r2"
  using rrewrites.intros(1) rrewrites.intros(2) by blast

lemma rs_in_rstar: 
  shows "r1 s\<leadsto> r2 \<Longrightarrow> r1 s\<leadsto>* r2"
  using rrewrites.intros(1) rrewrites.intros(2) by blast


lemma rrewrites_trans[trans]: 
  assumes a1: "r1 \<leadsto>* r2"  and a2: "r2 \<leadsto>* r3"
  shows "r1 \<leadsto>* r3"
  using a2 a1
  apply(induct r2 r3 arbitrary: r1 rule: rrewrites.induct) 
  apply(auto)
  done

lemma srewrites_trans[trans]: 
  assumes a1: "r1 s\<leadsto>* r2"  and a2: "r2 s\<leadsto>* r3"
  shows "r1 s\<leadsto>* r3"
  using a1 a2
  apply(induct r1 r2 arbitrary: r3 rule: srewrites.induct) 
   apply(auto)
  done



lemma contextrewrites0: 
  "rs1 s\<leadsto>* rs2 \<Longrightarrow> AALTs bs rs1 \<leadsto>* AALTs bs rs2"
  apply(induct rs1 rs2 rule: srewrites.inducts)
   apply simp
  using bs10 r_in_rstar rrewrites_trans by blast

lemma contextrewrites1: 
  "r \<leadsto>* r' \<Longrightarrow> AALTs bs (r # rs) \<leadsto>* AALTs bs (r' # rs)"
  apply(induct r r' rule: rrewrites.induct)
   apply simp
  using bs10 ss3 by blast

lemma srewrite1: 
  shows "rs1 s\<leadsto> rs2 \<Longrightarrow> (rs @ rs1) s\<leadsto> (rs @ rs2)"
  apply(induct rs)
   apply(auto)
  using ss2 by auto

lemma srewrites1: 
  shows "rs1 s\<leadsto>* rs2 \<Longrightarrow> (rs @ rs1) s\<leadsto>* (rs @ rs2)"
  apply(induct rs1 rs2 rule: srewrites.induct)
   apply(auto)
  using srewrite1 by blast

lemma srewrite2: 
  shows  "r1 \<leadsto> r2 \<Longrightarrow> True"
  and "rs1 s\<leadsto> rs2 \<Longrightarrow> (rs1 @ rs) s\<leadsto>* (rs2 @ rs)"
  apply(induct rule: rrewrite_srewrite.inducts)
  apply(auto)
  apply (metis append_Cons append_Nil srewrites1)
  apply(meson srewrites.simps ss3)
  apply (meson srewrites.simps ss4)
  apply (meson srewrites.simps ss5)
  by (metis append_Cons append_Nil srewrites.simps ss6)
  

lemma srewrites3: 
  shows "rs1 s\<leadsto>* rs2 \<Longrightarrow> (rs1 @ rs) s\<leadsto>* (rs2 @ rs)"
  apply(induct rs1 rs2 arbitrary: rs rule: srewrites.induct)
   apply(auto)
  by (meson srewrite2(2) srewrites_trans)

(*
lemma srewrites4:
  assumes "rs3 s\<leadsto>* rs4" "rs1 s\<leadsto>* rs2" 
  shows "(rs1 @ rs3) s\<leadsto>* (rs2 @ rs4)"
  using assms
  apply(induct rs3 rs4 arbitrary: rs1 rs2 rule: srewrites.induct)
  apply (simp add: srewrites3)
  using srewrite1 by blast
*)

lemma srewrites6:
  assumes "r1 \<leadsto>* r2" 
  shows "[r1] s\<leadsto>* [r2]"
  using assms
  apply(induct r1 r2 rule: rrewrites.induct)
   apply(auto)
  by (meson srewrites.simps srewrites_trans ss3)

lemma srewrites7:
  assumes "rs3 s\<leadsto>* rs4" "r1 \<leadsto>* r2" 
  shows "(r1 # rs3) s\<leadsto>* (r2 # rs4)"
  using assms
  by (smt (verit, best) append_Cons append_Nil srewrites1 srewrites3 srewrites6 srewrites_trans)

lemma ss6_stronger_aux:
  shows "(rs1 @ rs2) s\<leadsto>* (rs1 @ distinctWith rs2 eq1 (set rs1))"
  apply(induct rs2 arbitrary: rs1)
  apply(auto)
  prefer 2
  apply(drule_tac x="rs1 @ [a]" in meta_spec)
  apply(simp)
  apply(drule_tac x="rs1" in meta_spec)
  apply(subgoal_tac "(rs1 @ a # rs2) s\<leadsto>* (rs1 @ rs2)")
  using srewrites_trans apply blast
  apply(subgoal_tac "\<exists>rs1a rs1b. rs1 = rs1a @ [x] @ rs1b")
  prefer 2
  apply (simp add: split_list)
  apply(erule exE)+
  apply(simp)
  using eq1_L rs_in_rstar ss6 by force

lemma ss6_stronger:
  shows "rs1 s\<leadsto>* distinctWith rs1 eq1 {}"
  by (metis append_Nil list.set(1) ss6_stronger_aux)


lemma rewrite_preserves_fuse: 
  shows "r2 \<leadsto> r3 \<Longrightarrow> fuse bs r2 \<leadsto> fuse bs r3"
  and   "rs2 s\<leadsto> rs3 \<Longrightarrow> map (fuse bs) rs2 s\<leadsto>* map (fuse bs) rs3"
proof(induct rule: rrewrite_srewrite.inducts)
  case (bs3 bs1 bs2 r)
  then show ?case
    by (metis fuse.simps(5) fuse_append rrewrite_srewrite.bs3) 
next
  case (bs7 bs r)
  then show ?case
    by (metis fuse.simps(4) fuse_append rrewrite_srewrite.bs7) 
next
  case (ss2 rs1 rs2 r)
  then show ?case
    using srewrites7 by force 
next
  case (ss3 r1 r2 rs)
  then show ?case by (simp add: r_in_rstar srewrites7)
next
  case (ss5 bs1 rs1 rsb)
  then show ?case 
    apply(simp)
    by (metis (mono_tags, lifting) comp_def fuse_append map_eq_conv rrewrite_srewrite.ss5 srewrites.simps)
next
  case (ss6 a1 a2 rsa rsb rsc)
  then show ?case 
    apply(simp only: map_append)
    by (smt (verit, best) erase_fuse list.simps(8) list.simps(9) rrewrite_srewrite.ss6 srewrites.simps)
qed (auto intro: rrewrite_srewrite.intros)


lemma rewrites_fuse:  
  assumes "r1 \<leadsto>* r2"
  shows "fuse bs r1 \<leadsto>* fuse bs r2"
using assms
apply(induction r1 r2 arbitrary: bs rule: rrewrites.induct)
apply(auto intro: rewrite_preserves_fuse rrewrites_trans)
done


lemma star_seq:  
  assumes "r1 \<leadsto>* r2"
  shows "ASEQ bs r1 r3 \<leadsto>* ASEQ bs r2 r3"
using assms
apply(induct r1 r2 arbitrary: r3 rule: rrewrites.induct)
apply(auto intro: rrewrite_srewrite.intros)
done

lemma star_seq2:  
  assumes "r3 \<leadsto>* r4"
  shows "ASEQ bs r1 r3 \<leadsto>* ASEQ bs r1 r4"
  using assms
apply(induct r3 r4 arbitrary: r1 rule: rrewrites.induct)
apply(auto intro: rrewrite_srewrite.intros)
done

lemma continuous_rewrite: 
  assumes "r1 \<leadsto>* AZERO"
  shows "ASEQ bs1 r1 r2 \<leadsto>* AZERO"
using assms bs1 star_seq by blast

(*
lemma continuous_rewrite2: 
  assumes "r1 \<leadsto>* AONE bs"
  shows "ASEQ bs1 r1 r2 \<leadsto>* (fuse (bs1 @ bs) r2)"
  using assms  by (meson bs3 rrewrites.simps star_seq)
*)

lemma bsimp_aalts_simpcases: 
  shows "AONE bs \<leadsto>* bsimp (AONE bs)"  
  and   "AZERO \<leadsto>* bsimp AZERO" 
  and   "ACHAR bs c \<leadsto>* bsimp (ACHAR bs c)"
  by (simp_all)

lemma bsimp_AALTs_rewrites: 
  shows "AALTs bs1 rs \<leadsto>* bsimp_AALTs bs1 rs"
  by (smt (verit) bs6 bs7 bsimp_AALTs.elims rrewrites.simps)

lemma trivialbsimp_srewrites: 
  "\<lbrakk>\<And>x. x \<in> set rs \<Longrightarrow> x \<leadsto>* f x \<rbrakk> \<Longrightarrow> rs s\<leadsto>* (map f rs)"
  apply(induction rs)
   apply simp
  apply(simp)
  using srewrites7 by auto



lemma fltsfrewrites: "rs s\<leadsto>* flts rs"
  apply(induction rs rule: flts.induct)
  apply(auto intro: rrewrite_srewrite.intros)
  apply (meson srewrites.simps srewrites1 ss5)
  using rs1 srewrites7 apply presburger
  using srewrites7 apply force
  apply (simp add: srewrites7)
   apply(simp add: srewrites7)
  apply(erule srewrites7, simp)
  apply(erule srewrites7, simp)
  apply(erule srewrites7, simp)
  apply(erule srewrites7, simp)
  done



(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend this proof over the new constructor cases using the original rewrite
   relation. Keep proof commands lightweight; split resource-heavy automation. *)
lemma bnullable0:
shows "r1 \<leadsto> r2 \<Longrightarrow> bnullable r1 = bnullable r2" 
  and "rs1 s\<leadsto> rs2 \<Longrightarrow> bnullables rs1 = bnullables rs2" 
  apply(induct rule: rrewrite_srewrite.inducts)
  apply(auto simp add:  bnullable_fuse)
   apply (meson UnCI bnullable_fuse imageI)
  using bnullable_correctness nullable_correctness by blast 


lemma rewritesnullable: 
  assumes "r1 \<leadsto>* r2" 
  shows "bnullable r1 = bnullable r2"
using assms 
  apply(induction r1 r2 rule: rrewrites.induct)
  apply simp
  using bnullable0(1) by auto

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend this proof over the new constructor cases using the original rewrite
   relation. Keep proof commands lightweight; split resource-heavy automation. *)
lemma rewrite_bmkeps_aux: 
  shows "r1 \<leadsto> r2 \<Longrightarrow> (bnullable r1 \<and> bnullable r2 \<Longrightarrow> bmkeps r1 = bmkeps r2)"
  and   "rs1 s\<leadsto> rs2 \<Longrightarrow> (bnullables rs1 \<and> bnullables rs2 \<Longrightarrow> bmkepss rs1 = bmkepss rs2)" 
proof (induct rule: rrewrite_srewrite.inducts)
  case (bs3 bs1 bs2 r)
  then show ?case by (simp add: bmkeps_fuse) 
next
  case (bs7 bs r)
  then show ?case by (simp add: bmkeps_fuse) 
next
  case (ss3 r1 r2 rs)
  then show ?case
    using bmkepss.simps bnullable0(1) by presburger
next
  case (ss5 bs1 rs1 rsb)
  then show ?case
    apply (simp add: bmkepss1 bmkepss2 bmkepss_fuse bnullable_fuse)
    apply(case_tac rs1)
     apply(auto simp add: bnullable_fuse)
    apply (metis bmkeps_retrieve bmkeps_retrieve_AALTs bnullable.simps(4))
    apply (metis bmkeps_retrieve bmkeps_retrieve_AALTs bnullable.simps(4))
    apply (metis bmkeps_retrieve bmkeps_retrieve_AALTs bnullable.simps(4))
    by (metis bmkeps_retrieve bmkeps_retrieve_AALTs bnullable.simps(4))    
next
  case (ss6 a1 a2 rsa rsb rsc)
  then show ?case
    by (smt (verit, best) Nil_is_append_conv bmkepss1 bmkepss2 bnullable_correctness in_set_conv_decomp list.distinct(1) list.set_intros(1) nullable_correctness set_ConsD subsetD)
next
  case (bs10 rs1 rs2 bs)
  then show ?case
    by (metis bmkeps_retrieve bmkeps_retrieve_AALTs bnullable.simps(4)) 
qed (auto)

lemma rewrites_bmkeps: 
  assumes "r1 \<leadsto>* r2" "bnullable r1" 
  shows "bmkeps r1 = bmkeps r2"
  using assms
proof(induction r1 r2 rule: rrewrites.induct)
  case (rs1 r)
  then show "bmkeps r = bmkeps r" by simp
next
  case (rs2 r1 r2 r3)
  then have IH: "bmkeps r1 = bmkeps r2" by simp
  have a1: "bnullable r1" by fact
  have a2: "r1 \<leadsto>* r2" by fact
  have a3: "r2 \<leadsto> r3" by fact
  have a4: "bnullable r2" using a1 a2 by (simp add: rewritesnullable) 
  then have "bmkeps r2 = bmkeps r3"
    using a3 bnullable0(1) rewrite_bmkeps_aux(1) by blast 
  then show "bmkeps r1 = bmkeps r3" using IH by simp
qed


(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend rewrites_to_bsimp for the new constructors. This is the central
   thesis-style simplifier theorem; wrapper equalities do not count. *)
lemma rewrites_to_bsimp: 
  shows "r \<leadsto>* bsimp r"
proof (induction r rule: bsimp.induct)
  case (1 bs1 r1 r2)
  have IH1: "r1 \<leadsto>* bsimp r1" by fact
  have IH2: "r2 \<leadsto>* bsimp r2" by fact
  { assume as: "bsimp r1 = AZERO \<or> bsimp r2 = AZERO"
    with IH1 IH2 have "r1 \<leadsto>* AZERO \<or> r2 \<leadsto>* AZERO" by auto
    then have "ASEQ bs1 r1 r2 \<leadsto>* AZERO"
      by (metis bs2 continuous_rewrite rrewrites.simps star_seq2)  
    then have "ASEQ bs1 r1 r2 \<leadsto>* bsimp (ASEQ bs1 r1 r2)" using as by auto
  }
  moreover
  { assume "\<exists>bs. bsimp r1 = AONE bs"
    then obtain bs where as: "bsimp r1 = AONE bs" by blast
    with IH1 have "r1 \<leadsto>* AONE bs" by simp
    then have "ASEQ bs1 r1 r2 \<leadsto>* fuse (bs1 @ bs) r2" using bs3 star_seq by blast
    with IH2 have "ASEQ bs1 r1 r2 \<leadsto>* fuse (bs1 @ bs) (bsimp r2)"
      using rewrites_fuse by (meson rrewrites_trans) 
    then have "ASEQ bs1 r1 r2 \<leadsto>* bsimp (ASEQ bs1 (AONE bs) r2)" by simp
    then have "ASEQ bs1 r1 r2 \<leadsto>* bsimp (ASEQ bs1 r1 r2)" by (simp add: as) 
  } 
  moreover
  { assume as1: "bsimp r1 \<noteq> AZERO" "bsimp r2 \<noteq> AZERO" and as2: "(\<nexists>bs. bsimp r1 = AONE bs)" 
    then have "bsimp_ASEQ bs1 (bsimp r1) (bsimp r2) = ASEQ bs1 (bsimp r1) (bsimp r2)" 
      by (simp add: bsimp_ASEQ1) 
    then have "ASEQ bs1 r1 r2 \<leadsto>* bsimp_ASEQ bs1 (bsimp r1) (bsimp r2)" using as1 as2 IH1 IH2
      by (metis rrewrites_trans star_seq star_seq2) 
    then have "ASEQ bs1 r1 r2 \<leadsto>* bsimp (ASEQ bs1 r1 r2)" by simp
  } 
  ultimately show "ASEQ bs1 r1 r2 \<leadsto>* bsimp (ASEQ bs1 r1 r2)" by blast
next
  case (2 bs1 rs)
  have IH: "\<And>x. x \<in> set rs \<Longrightarrow> x \<leadsto>* bsimp x" by fact
  then have "rs s\<leadsto>* (map bsimp rs)" by (simp add: trivialbsimp_srewrites)
  also have "... s\<leadsto>* flts (map bsimp rs)" by (simp add: fltsfrewrites) 
  also have "... s\<leadsto>* distinctWith (flts (map bsimp rs)) eq1 {}" by (simp add: ss6_stronger)
  finally have "AALTs bs1 rs \<leadsto>* AALTs bs1 (distinctWith (flts (map bsimp rs)) eq1 {})"
    using contextrewrites0 by auto
  also have "... \<leadsto>* bsimp_AALTs  bs1 (distinctWith (flts (map bsimp rs)) eq1 {})"
    by (simp add: bsimp_AALTs_rewrites)     
  finally show "AALTs bs1 rs \<leadsto>* bsimp (AALTs bs1 rs)" by simp
qed (simp_all)


lemma to_zero_in_alt: 
  shows "AALT bs (ASEQ [] AZERO r) r2 \<leadsto> AALT bs AZERO r2"
  by (simp add: bs1 bs10 ss3)



lemma  bder_fuse_list: 
  shows "map (bder c \<circ> fuse bs1) rs1 = map (fuse bs1 \<circ> bder c) rs1"
  apply(induction rs1)
  apply(simp_all add: bder_fuse)
  done

lemma map1:
  shows "(map f [a]) = [f a]"
  by (simp)

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend derivative preservation through rewrites for BACKREF4/HALF/RESIDUE.
   This is where long-running automation must be replaced by explicit cases. *)
lemma rewrite_preserves_bder: 
  shows "r1 \<leadsto> r2 \<Longrightarrow> (bder c r1) \<leadsto>* (bder c r2)"
  and   "rs1 s\<leadsto> rs2 \<Longrightarrow> map (bder c) rs1 s\<leadsto>* map (bder c) rs2"
proof(induction rule: rrewrite_srewrite.inducts)
  case (bs1 bs r2)
  then show ?case
    by (simp add: continuous_rewrite) 
next
  case (bs2 bs r1)
  then show ?case 
    apply(auto)
    apply (meson bs6 contextrewrites0 rrewrite_srewrite.bs2 rs2 ss3 ss4 sss1 sss2)
    by (simp add: r_in_rstar rrewrite_srewrite.bs2)
next
  case (bs3 bs1 bs2 r)
  then show ?case 
    apply(simp)
    
    by (metis (no_types, lifting) bder_fuse bs10 bs7 fuse_append rrewrites.simps ss4 to_zero_in_alt)
next
  case (bs4 r1 r2 bs r3)
  have as: "r1 \<leadsto> r2" by fact
  have IH: "bder c r1 \<leadsto>* bder c r2" by fact
  from as IH show "bder c (ASEQ bs r1 r3) \<leadsto>* bder c (ASEQ bs r2 r3)"
    by (metis bder.simps(5) bnullable0(1) contextrewrites1 rewrite_bmkeps_aux(1) star_seq)
next
  case (bs5 r3 r4 bs r1)
  have as: "r3 \<leadsto> r4" by fact 
  have IH: "bder c r3 \<leadsto>* bder c r4" by fact 
  from as IH show "bder c (ASEQ bs r1 r3) \<leadsto>* bder c (ASEQ bs r1 r4)"
    apply(simp)
    apply(auto)
    using contextrewrites0 r_in_rstar rewrites_fuse srewrites6 srewrites7 star_seq2 apply presburger
    using star_seq2 by blast
next
  case (bs6 bs)
  then show ?case
    using rrewrite_srewrite.bs6 by force 
next
  case (bs7 bs r)
  then show ?case
    by (simp add: bder_fuse r_in_rstar rrewrite_srewrite.bs7) 
next
  case (bs10 rs1 rs2 bs)
  then show ?case
    using contextrewrites0 by force    
next
  case ss1
  then show ?case by simp
next
  case (ss2 rs1 rs2 r)
  then show ?case
    by (simp add: srewrites7) 
next
  case (ss3 r1 r2 rs)
  then show ?case
    by (simp add: srewrites7) 
next
  case (ss4 rs)
  then show ?case
    using rrewrite_srewrite.ss4 by fastforce 
next
  case (ss5 bs1 rs1 rsb)
  then show ?case 
    apply(simp)
    using bder_fuse_list map_map rrewrite_srewrite.ss5 srewrites.simps by blast
next
  case (ss6 a1 a2 bs rsa rsb)
  then show ?case
    apply(simp only: map_append map1)
    apply(rule srewrites_trans)
    apply(rule rs_in_rstar)
    apply(rule_tac rrewrite_srewrite.ss6)
    using Der_def der_correctness apply auto[1]
    by blast
qed

lemma rewrites_preserves_bder: 
  assumes "r1 \<leadsto>* r2"
  shows "bder c r1 \<leadsto>* bder c r2"
using assms  
apply(induction r1 r2 rule: rrewrites.induct)
apply(simp_all add: rewrite_preserves_bder rrewrites_trans)
done


(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend central after rewrites_to_bsimp and rewrite_preserves_bder are repaired
   for the new constructors. *)
lemma central:  
  shows "bders r s \<leadsto>* bders_simp r s"
proof(induct s arbitrary: r rule: rev_induct)
  case Nil
  then show "bders r [] \<leadsto>* bders_simp r []" by simp
next
  case (snoc x xs)
  have IH: "\<And>r. bders r xs \<leadsto>* bders_simp r xs" by fact
  have "bders r (xs @ [x]) = bders (bders r xs) [x]" by (simp add: bders_append)
  also have "... \<leadsto>* bders (bders_simp r xs) [x]" using IH
    by (simp add: rewrites_preserves_bder)
  also have "... \<leadsto>* bders_simp (bders_simp r xs) [x]" using IH
    by (simp add: rewrites_to_bsimp)
  finally show "bders r (xs @ [x]) \<leadsto>* bders_simp r (xs @ [x])" 
    by (simp add: bders_simp_append)
qed

lemma main_aux: 
  assumes "bnullable (bders r s)"
  shows "bmkeps (bders r s) = bmkeps (bders_simp r s)"
proof -
  have "bders r s \<leadsto>* bders_simp r s" by (rule central)
  then 
  show "bmkeps (bders r s) = bmkeps (bders_simp r s)" using assms
    by (rule rewrites_bmkeps)
qed  




(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend the original main_blexer_simp theorem; no wrapper simplifier theorem
   can substitute for this result. *)
theorem main_blexer_simp: 
  shows "blexer r s = blexer_simp r s"
  unfolding blexer_def blexer_simp_def
  by (metis central main_aux rewritesnullable)

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend the original blexersimp_correctness theorem after main_blexer_simp is
   repaired. *)
theorem blexersimp_correctness: 
  shows "lexer r s = blexer_simp r s"
  using blexer_correctness main_blexer_simp by simp

end
