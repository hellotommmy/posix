theory BasicIdentities 
  imports "Lexer" 
begin

(* BACKREF-MIGRATION-COMPLETED (bounds-only skeleton, ADMIN APPROVAL APPROVED):
   This file introduces rrexp, a third regex datatype used for bounds and closed
   forms. Admin approved retaining rrexp as a proof-only skeleton while the
   production syntax remains rexp/arexp. *)
datatype rrexp = 
  RZERO
| RONE 
| RCHAR char
| RSEQ rrexp rrexp
| RALTS "rrexp list"
| RSTAR rrexp
| RNTIMES rrexp nat
| RBACKREF4 rrexp rrexp rrexp rrexp string
| RHALF rrexp string string
| RRESIDUE string string

abbreviation
  "RALT r1 r2 \<equiv> RALTS [r1, r2]"


fun
 rnullable :: "rrexp \<Rightarrow> bool"
where
  "rnullable (RZERO) = False"
| "rnullable (RONE) = True"
| "rnullable (RCHAR c) = False"
| "rnullable (RALTS rs) = (\<exists>r \<in> set rs. rnullable r)"
| "rnullable (RSEQ r1 r2) = (rnullable r1 \<and> rnullable r2)"
| "rnullable (RSTAR r) = True"
| "rnullable (RNTIMES r n) = (if n = 0 then True else rnullable r)"
| "rnullable (RBACKREF4 r1 r2 r3 r4 cs) =
    (rnullable r1 \<and> rnullable r2 \<and> rnullable r3 \<and> rnullable r4 \<and> cs = [])"
| "rnullable (RHALF r cs rep) = (rnullable r \<and> cs = [])"
| "rnullable (RRESIDUE cs rep) = (cs = [])"

fun rder_residue :: "char \<Rightarrow> string \<Rightarrow> string \<Rightarrow> rrexp"
where
  "rder_residue c [] rep = RZERO"
| "rder_residue c (d # ds) rep = (if c = d then RRESIDUE ds rep else RZERO)"

fun
 rder :: "char \<Rightarrow> rrexp \<Rightarrow> rrexp"
where
  "rder c (RZERO) = RZERO"
| "rder c (RONE) = RZERO"
| "rder c (RCHAR d) = (if c = d then RONE else RZERO)"
| "rder c (RALTS rs) = RALTS (map (rder c) rs)"
| "rder c (RSEQ r1 r2) = 
     (if rnullable r1
      then RALT   (RSEQ (rder c r1) r2) (rder c r2)
      else RSEQ   (rder c r1) r2)"
| "rder c (RSTAR r) = RSEQ  (rder c r) (RSTAR r)"   
| "rder c (RNTIMES r n) = (if n = 0 then RZERO else RSEQ (rder c r) (RNTIMES r (n - 1)))"
| "rder c (RBACKREF4 r1 r2 r3 r4 cs) =
     (let prefix = RBACKREF4 (rder c r1) r2 r3 r4 cs;
          capture = RBACKREF4 RONE (rder c r2) r3 r4 (c # cs);
          res = rev cs;
          res_tail = (if res = []
            then RALT (RSEQ (rder_residue c res res) r4) (rder c r4)
            else RSEQ (rder_residue c res res) r4);
          tail = (if rnullable r3
            then RALT (RSEQ (rder c r3) (RSEQ (RRESIDUE res res) r4)) res_tail
            else RSEQ (rder c r3) (RSEQ (RRESIDUE res res) r4))
      in if rnullable r1
         then RALT prefix (if rnullable r2 then RALT capture tail else capture)
         else prefix)"
| "rder c (RHALF r cs rep) =
     (if rnullable r
      then RALT (RHALF (rder c r) cs rep) (rder_residue c cs rep)
      else RHALF (rder c r) cs rep)"
| "rder c (RRESIDUE cs rep) = rder_residue c cs rep"

fun 
  rders :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp"
where
  "rders r [] = r"
| "rders r (c#s) = rders (rder c r) s"

fun rdistinct :: "'a list \<Rightarrow>'a set \<Rightarrow> 'a list"
  where
  "rdistinct [] acc = []"
| "rdistinct (x#xs)  acc = 
     (if x \<in> acc then rdistinct xs  acc 
      else x # (rdistinct xs  ({x} \<union> acc)))"

lemma rdistinct1:
  assumes "a \<in> acc"
  shows "a \<notin> set (rdistinct rs acc)"
  using assms
  apply(induct rs arbitrary: acc a)
   apply(auto)
  done


lemma rdistinct_does_the_job:
  shows "distinct (rdistinct rs s)"
  apply(induct rs s rule: rdistinct.induct)
  apply(auto simp add: rdistinct1)
  done



lemma rdistinct_concat:
  assumes "set rs \<subseteq> rset"
  shows "rdistinct (rs @ rsa) rset = rdistinct rsa rset"
  using assms
  apply(induct rs)
  apply simp+
  done

lemma distinct_not_exist:
  assumes "a \<notin> set rs"
  shows "rdistinct rs rset = rdistinct rs (insert a rset)"
  using assms
  apply(induct rs arbitrary: rset)
  apply(auto)
  done

lemma rdistinct_on_distinct:
  shows "distinct rs \<Longrightarrow> rdistinct rs {} = rs"
  apply(induct rs)
  apply simp
  using distinct_not_exist by fastforce

lemma distinct_rdistinct_append:
  assumes "distinct rs1" "\<forall>r \<in> set rs1. r \<notin> acc"
  shows "rdistinct (rs1 @ rsa) acc = rs1 @ (rdistinct rsa (acc \<union> set rs1))"
  using assms
  apply(induct rs1 arbitrary: rsa acc)
   apply(auto)[1]
  apply(auto)[1]
  apply(drule_tac x="rsa" in meta_spec)
  apply(drule_tac x="{a} \<union> acc" in meta_spec)
  apply(simp)
  apply(drule meta_mp)
   apply(auto)[1]
  apply(simp)
  done
  

lemma rdistinct_set_equality1:
  shows "set (rdistinct rs acc) = set rs - acc"
  apply(induct rs acc rule: rdistinct.induct)
  apply(auto)
  done


lemma rdistinct_set_equality:
  shows "set (rdistinct rs {}) = set rs"
  by (simp add: rdistinct_set_equality1)


fun rflts :: "rrexp list \<Rightarrow> rrexp list"
  where 
  "rflts [] = []"
| "rflts (RZERO # rs) = rflts rs"
| "rflts ((RALTS rs1) # rs) = rs1 @ rflts rs"
| "rflts (r1 # rs) = r1 # rflts rs"


lemma rflts_def_idiot:
  shows "\<lbrakk> a \<noteq> RZERO; \<nexists>rs1. a = RALTS rs1\<rbrakk> \<Longrightarrow> rflts (a # rs) = a # rflts rs"
  apply(case_tac a)
  apply simp_all
  done

lemma rflts_def_idiot2:
  shows "\<lbrakk>a \<noteq> RZERO; \<nexists>rs1. a = RALTS rs1; a \<in> set rs\<rbrakk> \<Longrightarrow> a \<in> set (rflts rs)"
  apply(induct rs rule: rflts.induct)
  apply(auto)
  done

lemma flts_append:
  shows "rflts (rs1 @ rs2) = rflts rs1 @ rflts rs2"
  apply(induct rs1)
   apply simp
  apply(case_tac a)
       apply simp+
  done


fun rsimp_ALTs :: " rrexp list \<Rightarrow> rrexp"
  where
  "rsimp_ALTs  [] = RZERO"
| "rsimp_ALTs [r] =  r"
| "rsimp_ALTs rs = RALTS rs"

lemma rsimpalts_conscons:
  shows "rsimp_ALTs (r1 # rsa @ r2 # rsb) = RALTS (r1 # rsa @ r2 # rsb)"
  by (metis Nil_is_append_conv list.exhaust rsimp_ALTs.simps(3))

lemma rsimp_alts_equal:
  shows "rsimp_ALTs (rsa @ a # rsb @ a # rsc) = RALTS (rsa @ a # rsb @ a # rsc) "
  by (metis append_Cons append_Nil neq_Nil_conv rsimpalts_conscons)


fun rsimp_SEQ :: " rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp"
  where
  "rsimp_SEQ  RZERO _ = RZERO"
| "rsimp_SEQ  _ RZERO = RZERO"
| "rsimp_SEQ RONE r2 = r2"
| "rsimp_SEQ r1 r2 = RSEQ r1 r2"


fun rsimp :: "rrexp \<Rightarrow> rrexp" 
  where
  "rsimp (RSEQ r1 r2) = rsimp_SEQ  (rsimp r1) (rsimp r2)"
| "rsimp (RALTS rs) = rsimp_ALTs  (rdistinct (rflts (map rsimp rs))  {}) "
| "rsimp r = r"


fun 
  rders_simp :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp"
where
  "rders_simp r [] = r"
| "rders_simp r (c#s) = rders_simp (rsimp (rder c r)) s"

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Constructor-case maintenance below covers the proof-only RBACKREF4, RHALF,
   and RRESIDUE skeleton. *)
fun rsize :: "rrexp \<Rightarrow> nat" where
  "rsize RZERO = 1"
| "rsize (RONE) = 1" 
| "rsize (RCHAR  c) = 1"
| "rsize (RALTS  rs) = Suc (sum_list (map rsize rs))"
| "rsize (RSEQ  r1 r2) = Suc (rsize r1 + rsize r2)"
| "rsize (RSTAR  r) = Suc (rsize r)"
| "rsize (RNTIMES r n) = Suc (rsize r) + n"
| "rsize (RBACKREF4 r1 r2 r3 r4 cs) =
    Suc (rsize r1 + rsize r2 + rsize r3 + rsize r4)"
| "rsize (RHALF r cs rep) = Suc (rsize r)"
| "rsize (RRESIDUE cs rep) = 1"

abbreviation rsizes where
  "rsizes rs \<equiv> sum_list (map rsize rs)"


lemma rder_rsimp_ALTs_commute:
  shows "  (rder x (rsimp_ALTs rs)) = rsimp_ALTs (map (rder x) rs)"
  apply(induct rs)
   apply simp
  apply(case_tac rs)
   apply simp
  apply auto
  done


lemma rsimp_aalts_smaller:
  shows "rsize (rsimp_ALTs  rs) \<le> rsize (RALTS rs)"
  apply(induct rs)
   apply simp
  apply simp
  apply(case_tac "rs = []")
   apply simp
  apply(subgoal_tac "\<exists>rsp ap. rs = ap # rsp")
   apply(erule exE)+
   apply simp
  apply simp
  by(meson neq_Nil_conv)
  




lemma rSEQ_mono:
  shows "rsize (rsimp_SEQ r1 r2) \<le> rsize (RSEQ r1 r2)"
  apply auto
  apply(induct r1 r2 rule: rsimp_SEQ.induct)
       apply auto
  done

lemma ralts_cap_mono:
  shows "rsize (RALTS rs) \<le> Suc (rsizes rs)"
  by simp




lemma rflts_mono:
  shows "rsizes (rflts rs) \<le> rsizes rs"
  apply(induct rs)
  apply simp
  apply(case_tac "a = RZERO")
   apply simp
  apply(case_tac "\<exists>rs1. a = RALTS rs1")
  apply(erule exE)
   apply simp
  apply(subgoal_tac "rflts (a # rs) = a # (rflts rs)")
   prefer 2
  
  using rflts_def_idiot apply blast
  apply simp
  done

lemma rdistinct_smaller: 
  shows "rsizes (rdistinct rs ss) \<le> rsizes rs"
  apply (induct rs arbitrary: ss)
   apply simp
  by (simp add: trans_le_add2)


lemma rsimp_alts_mono :
  shows "\<And>x. (\<And>xa. xa \<in> set x \<Longrightarrow> rsize (rsimp xa) \<le> rsize xa)  \<Longrightarrow>
      rsize (rsimp_ALTs (rdistinct (rflts (map rsimp x)) {})) \<le> Suc (rsizes x)"
  apply(subgoal_tac "rsize (rsimp_ALTs (rdistinct (rflts (map rsimp x)) {} )) 
                    \<le> rsize (RALTS (rdistinct (rflts (map rsimp x)) {} ))")
  prefer 2
  using rsimp_aalts_smaller apply auto[1]
  apply(subgoal_tac "rsize (RALTS (rdistinct (rflts (map rsimp x)) {})) \<le>Suc (rsizes (rdistinct (rflts (map rsimp x)) {}))")
  prefer 2
  using ralts_cap_mono apply blast
  apply(subgoal_tac "rsizes (rdistinct (rflts (map rsimp x)) {}) \<le> rsizes (rflts (map rsimp x))")
  prefer 2
  using rdistinct_smaller apply presburger
  apply(subgoal_tac "rsizes (rflts (map rsimp x)) \<le> rsizes (map rsimp x)")
  prefer 2
  using rflts_mono apply blast
  apply(subgoal_tac "rsizes (map rsimp x) \<le> rsizes x")
  prefer 2
  
  apply (simp add: sum_list_mono)
  by linarith





lemma rsimp_mono:
  shows "rsize (rsimp r) \<le> rsize r"
  apply(induct r)
  apply simp_all
  apply(subgoal_tac "rsize (rsimp_SEQ (rsimp r1) (rsimp r2)) \<le> rsize (RSEQ (rsimp r1) (rsimp r2))")
    apply force
  using rSEQ_mono
   apply presburger
  using rsimp_alts_mono by auto

lemma idiot:
  shows "rsimp_SEQ RONE r = r"
  apply(case_tac r)
       apply simp_all
  done





lemma idiot2:
  assumes "r1 \<noteq> RZERO" "r1 \<noteq> RONE" "r2 \<noteq> RZERO"
  shows "rsimp_SEQ r1 r2 = RSEQ r1 r2"
  using assms
  apply(induct r1 r2 rule: rsimp_SEQ.induct)
  apply(auto)
  done

lemma rders__onechar:
  shows " (rders_simp r [c]) =  (rsimp (rders r [c]))"
  by simp

lemma rders_append:
  "rders c (s1 @ s2) = rders (rders c s1) s2"
  apply(induct s1 arbitrary: c s2)
  apply(simp_all)
  done

lemma rders_simp_append:
  "rders_simp c (s1 @ s2) = rders_simp (rders_simp c s1) s2"
  apply(induct s1 arbitrary: c s2)
   apply(simp_all)
  done


lemma rders_simp_one_char:
  shows "rders_simp r [c] = rsimp (rder c r)"
  apply auto
  done



fun nonalt :: "rrexp \<Rightarrow> bool"
  where
  "nonalt (RALTS  rs) = False"
| "nonalt r = True"


fun good :: "rrexp \<Rightarrow> bool" where
  "good RZERO = False"
| "good (RONE) = True" 
| "good (RCHAR c) = True"
| "good (RALTS []) = False"
| "good (RALTS [r]) = False"
| "good (RALTS (r1 # r2 # rs)) = ((distinct ( (r1 # r2 # rs))) \<and>(\<forall>r' \<in> set (r1 # r2 # rs). good r' \<and> nonalt r'))"
| "good (RSEQ RZERO _) = False"
| "good (RSEQ RONE _) = False"
| "good (RSEQ  _ RZERO) = False"
| "good (RSEQ r1 r2) = (good r1 \<and> good r2)"
| "good (RSTAR r) = True"
| "good (RNTIMES r n) = True"
| "good (RBACKREF4 r1 r2 r3 r4 cs) = True"
| "good (RHALF r cs rep) = True"
| "good (RRESIDUE cs rep) = True"

lemma  k0a:
  shows "rflts [RALTS rs] =   rs"
  apply(simp)
  done

lemma bbbbs:
  assumes "good r" "r = RALTS rs"
  shows "rsimp_ALTs  (rflts [r]) = RALTS rs"
  using  assms
  by (metis good.simps(4) good.simps(5) k0a rsimp_ALTs.elims)

lemma bbbbs1:
  shows "nonalt r \<or> (\<exists> rs. r  = RALTS  rs)"
  by (meson nonalt.elims(3))



lemma good0:
  assumes "rs \<noteq> Nil" "\<forall>r \<in> set rs. nonalt r" "distinct rs"
  shows "good (rsimp_ALTs rs) \<longleftrightarrow> (\<forall>r \<in> set rs. good r)"
  using  assms
  apply(induct  rs rule: rsimp_ALTs.induct)
  apply(auto)
  done

lemma flts1:
  assumes "good r" 
  shows "rflts [r] \<noteq> []"
  using  assms
  apply(induct r)
       apply(simp_all)
  using good.simps(4) by blast

lemma good_RALTS_elem:
  assumes "good (RALTS rs)" "r \<in> set rs"
  shows "good r \<and> nonalt r"
proof (cases rs)
  case Nil
  then show ?thesis
    using assms by simp
next
  case (Cons a xs)
  note rs_cons = Cons
  then show ?thesis
  proof (cases xs)
    case Nil
    then show ?thesis
      using assms rs_cons by simp
  next
    case (Cons b ys)
    then have rs: "rs = a # b # ys"
      using rs_cons by simp
    then have all: "\<forall>r \<in> set rs. good r \<and> nonalt r"
      using assms(1) by simp
    then show ?thesis
      using assms(2) by blast
  qed
qed

lemma flts2:
  assumes "good r" 
  shows "\<forall>r' \<in> set (rflts [r]). good r' \<and> nonalt r'"
proof (cases r)
  case (RALTS rs)
  then show ?thesis
    using assms good_RALTS_elem by auto
qed (use assms in simp_all)

lemma flts3:
  assumes "\<forall>r \<in> set rs. good r \<or> r = RZERO" 
  shows "\<forall>r \<in> set (rflts rs). good r"
  using  assms
  apply(induct rs arbitrary: rule: rflts.induct)
        apply(simp_all)
  by (metis UnE flts2 k0a)

lemma flts3_good_nonalt:
  assumes "\<forall>r \<in> set rs. good r \<or> r = RZERO"
  shows "\<forall>r \<in> set (rflts rs). good r \<and> nonalt r"
  using assms
proof (induct rs)
  case Nil
  then show ?case by simp
next
  case (Cons a rs)
  have tail_prems: "\<forall>r \<in> set rs. good r \<or> r = RZERO"
    using Cons.prems by simp
  have tail: "\<forall>r \<in> set (rflts rs). good r \<and> nonalt r"
    using Cons.hyps[OF tail_prems] .
  show ?case
  proof (cases a)
    case RZERO
    then show ?thesis
      using tail by simp
  next
    case (RALTS xs)
    then have "good (RALTS xs)"
      using Cons.prems by simp
    then have head: "\<forall>r \<in> set (rflts [RALTS xs]). good r \<and> nonalt r"
      using flts2 by blast
    show ?thesis
      using RALTS head tail by auto
  qed (use Cons.prems tail in simp_all)
qed

lemma good_not_RZERO:
  assumes "good r"
  shows "r \<noteq> RZERO"
  using assms by (cases r) auto


lemma  k0:
  shows "rflts (r # rs1) = rflts [r] @ rflts rs1"
  apply(induct r arbitrary: rs1)
   apply(auto)
  done


lemma good_SEQ:
  assumes "r1 \<noteq> RZERO" "r2 \<noteq> RZERO" " r1 \<noteq> RONE"
  shows "good (RSEQ r1 r2) = (good r1 \<and> good r2)"
  using assms
  by (cases r1; cases r2; simp)


lemma rsize0:
  shows "0 < rsize r"
  apply(induct  r)
       apply(auto)
  done


fun nonnested :: "rrexp \<Rightarrow> bool"
  where
  "nonnested (RALTS []) = True"
| "nonnested (RALTS ((RALTS rs1) # rs2)) = False"
| "nonnested (RALTS (r # rs2)) = nonnested (RALTS rs2)"
| "nonnested r = True"



lemma  k00:
  shows "rflts (rs1 @ rs2) = rflts rs1 @ rflts rs2"
  apply(induct rs1 arbitrary: rs2)
   apply(auto)
  by (metis append.assoc k0)




lemma k0b:
  assumes "nonalt r" "r \<noteq> RZERO"
  shows "rflts [r] = [r]"
  using assms
  apply(case_tac  r)
  apply(simp_all)
  done

lemma nn1qq:
  assumes "nonnested (RALTS rs)"
  shows "\<nexists> rs1. RALTS rs1 \<in> set rs"
  using assms
  apply(induct rs rule: rflts.induct)
  apply(auto)
  done

 

lemma n0:
  shows "nonnested (RALTS rs) \<longleftrightarrow> (\<forall>r \<in> set rs. nonalt r)"
  apply(induct rs )
   apply(auto)
     apply (metis list.set_intros(1) nn1qq nonalt.elims(3))
  using nonnested.elims(3) apply fastforce
  using bbbbs1 nonnested.simps(2) apply blast
  by (metis list.set_intros(2) nn1qq nonalt.elims(3))
  

lemma nn1c:
  assumes "\<forall>r \<in> set rs. nonnested r"
  shows "\<forall>r \<in> set (rflts rs). nonalt r"
  using assms
  apply(induct rs rule: rflts.induct)
        apply(auto)
  using n0 by blast

lemma nn1bb:
  assumes "\<forall>r \<in> set rs. nonalt r"
  shows "nonnested (rsimp_ALTs  rs)"
  using assms
  apply(induct  rs rule: rsimp_ALTs.induct)
    apply(auto)
  using nonalt.simps(1) nonnested.elims(3) apply blast
  using n0 by auto

lemma bsimp_ASEQ0:
  shows "rsimp_SEQ  r1 RZERO = RZERO"
  apply(induct r1)
  apply(auto)
  done

lemma nn1b:
  shows "nonnested (rsimp r)"
  apply(induct r)
       apply(simp_all)
  apply(case_tac "rsimp r1 = RZERO")
    apply(simp)
 apply(case_tac "rsimp r2 = RZERO")
   apply(simp)
    apply(subst bsimp_ASEQ0)
  apply(simp)
  apply(case_tac "\<exists>bs. rsimp r1 = RONE")
    apply(auto)[1]
  using idiot apply fastforce
  apply (simp add: idiot2)
  by (metis (mono_tags, lifting) image_iff list.set_map nn1bb nn1c rdistinct_set_equality)

lemma nonalt_flts_rd:
  shows "\<lbrakk>xa \<in> set (rdistinct (rflts (map rsimp rs)) {})\<rbrakk>
       \<Longrightarrow> nonalt xa"
  by (metis Diff_empty ex_map_conv nn1b nn1c rdistinct_set_equality1)


lemma rsimpalts_implies1:
  shows " rsimp_ALTs (a # rdistinct rs {a}) = RZERO \<Longrightarrow> a = RZERO"
  using rsimp_ALTs.elims by auto


lemma rsimpalts_implies2:
  shows "rsimp_ALTs (a # rdistinct rs rset) = RZERO \<Longrightarrow> rdistinct rs rset = []"
  by (metis append_butlast_last_id rrexp.distinct(7) rsimpalts_conscons)

lemma rsimpalts_implies21:
  shows "rsimp_ALTs (a # rdistinct rs {a}) = RZERO \<Longrightarrow> rdistinct rs {a} = []"
  using rsimpalts_implies2 by blast


lemma bsimp_ASEQ2:
  shows "rsimp_SEQ RONE r2 =  r2"
  apply(induct r2)
  apply(auto)
  done

lemma elem_smaller_than_set:
  shows "xa \<in> set  list \<Longrightarrow> rsize xa < Suc (rsizes list)"
  by (induct list) auto

lemma rsimp_list_mono:
  shows "rsizes (map rsimp rs) \<le> rsizes rs"
  apply(induct rs)
   apply simp+
  by (simp add: add_mono_thms_linordered_semiring(1) rsimp_mono)


(*says anything coming out of simp+flts+db will be good*)
lemma good2_obv_simplified:
  shows " \<lbrakk>\<forall>y. rsize y < Suc (rsizes rs) \<longrightarrow> good (rsimp y) \<or> rsimp y = RZERO;
           xa \<in> set (rdistinct (rflts (map rsimp rs)) {}); good (rsimp xa) \<or> rsimp xa = RZERO\<rbrakk> \<Longrightarrow> good xa"
  apply(subgoal_tac " \<forall>xa' \<in> set (map rsimp rs). good xa' \<or> xa' = RZERO")
  prefer 2
   apply (simp add: elem_smaller_than_set)
  by (metis Diff_empty flts3 rdistinct_set_equality1)

thm Diff_empty flts3 rdistinct_set_equality1
  
lemma good1:
  shows "good (rsimp a) \<or> rsimp a = RZERO"
  apply(induct a taking: rsize rule: measure_induct)
  apply(case_tac x)
  apply(simp)
  apply(simp)
  apply(simp)
  prefer 3
    apply(simp)
   prefer 2
   apply(simp only:)
   apply simp
  apply (smt (verit, ccfv_threshold) add_mono_thms_linordered_semiring(1) elem_smaller_than_set good0 good2_obv_simplified le_eq_less_or_eq nonalt_flts_rd order_less_trans plus_1_eq_Suc rdistinct_does_the_job rdistinct_smaller rflts_mono rsimp_ALTs.simps(1) rsimp_list_mono)
  apply simp
  apply(subgoal_tac "good (rsimp x41) \<or> rsimp x41 = RZERO")
   apply(subgoal_tac "good (rsimp x42) \<or> rsimp x42 = RZERO")
    apply(case_tac "rsimp x41 = RZERO")
     apply simp
    apply(case_tac "rsimp x42 = RZERO")
     apply simp
  using bsimp_ASEQ0 apply blast
    apply(subgoal_tac "good (rsimp x41)")
     apply(subgoal_tac "good (rsimp x42)")
      apply simp
  apply (metis bsimp_ASEQ2 good_SEQ idiot2)
  apply blast
  apply fastforce
  using less_add_Suc2 apply blast  
  using less_iff_Suc_add apply blast
  apply simp
  apply simp
  apply simp
  apply simp
  done


(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   RL/rnullable/rder/rsimp correctness covers the proof-only RBACKREF4, RHALF,
   and RRESIDUE skeleton. *)
fun
  RL :: "rrexp \<Rightarrow> string set"
where
  "RL (RZERO) = {}"
| "RL (RONE) = {[]}"
| "RL (RCHAR c) = {[c]}"
| "RL (RSEQ r1 r2) = (RL r1) ;; (RL r2)"
| "RL (RALTS rs) = (\<Union> (set (map RL rs)))"
| "RL (RSTAR r) = (RL r)\<star>"
| "RL (RNTIMES r n) = (RL r) ^^ n"
| "RL (RBACKREF4 r1 r2 r3 r4 cs) =
    backref_lang4 (RL r1) (RL r2) (RL r3) (RL r4) cs"
| "RL (RHALF r cs rep) = (RL r) ;; {cs}"
| "RL (RRESIDUE cs rep) = {cs}"

lemma pow_rempty_iff:
  shows "[] \<in> (RL r) ^^ n \<longleftrightarrow> (if n = 0 then True else [] \<in> (RL r))"
  by (induct n) (auto simp add: Sequ_def)

lemma RL_rnullable:
  shows "rnullable r = ([] \<in> RL r)"
  apply(induct r)
         apply(auto simp add: Sequ_def pow_rempty_iff backref_lang4_def)
  
  done

lemma concI_if_Nil1: "[] \<in> A \<Longrightarrow> xs : B \<Longrightarrow> xs \<in> A ;; B"
by (metis append_Nil concI)


lemma empty_pow_add:
  fixes A::"string set"
  assumes "[] \<in> A" "s \<in> A ^^ n"
  shows "s \<in> A ^^ (n + m)"
  using assms
  apply(induct m arbitrary: n)
   apply(auto simp add: Sequ_def)
  done

(*
lemma der_pow:
  shows "Der c (A ^^ n) = (if n = 0 then {} else (Der c A) ;; (A ^^ (n - 1)))"
  apply(induct n arbitrary: A)
   apply(auto)
  by (smt (verit, best) Suc_pred concE concI concI_if_Nil2 conc_pow_comm lang_pow.simps(2))
*)

lemma RL_rder_residue:
  shows "RL (rder_residue c cs rep) = Der c {cs}"
  by (cases cs) auto

lemma RL_rder:
  shows "RL (rder c r) = Der c (RL r)"
proof (induct r)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR x)
  then show ?case by simp
next
  case (RSEQ r1 r2)
  then show ?case
    by (simp add: Der_Sequ RL_rnullable)
next
  case (RALTS rs)
  then show ?case by simp
next
  case (RSTAR r)
  then show ?case by simp
next
  case (RNTIMES r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    have lhs: "RL (rder c (RNTIMES r (Suc m))) = Der c (RL r) ;; (RL r ^^ m)"
      using RNTIMES by simp
    have rhs: "Der c (RL (RNTIMES r (Suc m))) = Der c (RL r) ;; (RL r ^^ m)"
    proof -
      have "Der c (RL (RNTIMES r (Suc m))) = Der c ((RL r) ^^ Suc m)"
        by simp
      also have "... = Der c (RL r) ;; (RL r ^^ (Suc m - 1))"
        by (subst Der_pow) simp
      also have "... = Der c (RL r) ;; (RL r ^^ m)"
        by simp
      finally show ?thesis .
    qed
    show ?thesis
      using Suc lhs rhs by simp
  qed
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  let ?res = "rev cs"
  let ?mid = "RSEQ (RRESIDUE ?res ?res) r4"
  let ?res_tail =
    "if ?res = []
     then RALT (RSEQ (rder_residue c ?res ?res) r4) (rder c r4)
     else RSEQ (rder_residue c ?res ?res) r4"
  let ?tail =
    "if rnullable r3
     then RALT (RSEQ (rder c r3) ?mid) ?res_tail
     else RSEQ (rder c r3) ?mid"
  have res_tail: "RL ?res_tail = Der c ({?res} ;; RL r4)"
  proof (cases ?res)
    case Nil
    then show ?thesis
      using RBACKREF4(4)
      by (simp add: RL_rder_residue Der_Sequ)
  next
    case (Cons d ds)
    then show ?thesis
      by (simp add: RL_rder_residue Der_Sequ)
  qed
  have tail: "RL ?tail = Der c (RL r3 ;; ({?res} ;; RL r4))"
    using RBACKREF4(3) res_tail
    by (simp add: RL_rnullable Der_Sequ)
  show ?case
    using RBACKREF4(1,2) tail
    by (simp add: Let_def RL_rnullable Der_backref_lang4 Un_assoc)
next
  case (RHALF r cs rep)
  then show ?case
    by (simp add: RL_rnullable RL_rder_residue Der_Sequ)
next
  case (RRESIDUE cs rep)
  then show ?case
    by (simp add: RL_rder_residue)
qed


lemma RL_rsimp_RSEQ:
  shows "RL (rsimp_SEQ r1 r2) = (RL r1 ;; RL r2)"
  apply(induct r1 r2 rule: rsimp_SEQ.induct)
  apply(simp_all)
  done

lemma RL_rsimp_RALTS:
  shows "RL (rsimp_ALTs rs) = (\<Union> (set (map RL rs)))"
  apply(induct rs rule: rsimp_ALTs.induct)
  apply(simp_all)
  done

lemma RL_rsimp_rdistinct:
  shows "(\<Union> (set (map RL (rdistinct rs {})))) = (\<Union> (set (map RL rs)))"
  apply(auto)
  apply (metis Diff_iff rdistinct_set_equality1)
  by (metis Diff_empty rdistinct_set_equality1)

lemma RL_rsimp_rflts:
  shows "(\<Union> (set (map RL (rflts rs)))) = (\<Union> (set (map RL rs)))"
  apply(induct rs rule: rflts.induct)
  apply(simp_all)
  done

lemma RL_rsimp:
  shows "RL r = RL (rsimp r)"
  apply(induct r rule: rsimp.induct)
       apply(auto simp add: Sequ_def RL_rsimp_RSEQ)
  using RL_rsimp_RALTS RL_rsimp_rdistinct RL_rsimp_rflts apply auto[1]
  by (smt (verit, del_insts) RL_rsimp_RALTS RL_rsimp_rdistinct RL_rsimp_rflts UN_E image_iff list.set_map)

  
lemma qqq1:
  shows "RZERO \<notin> set (rflts (map rsimp rs))"
  by (metis ex_map_conv flts3 good.simps(1) good1)


fun nonazero :: "rrexp \<Rightarrow> bool"
  where
  "nonazero RZERO = False"
| "nonazero r = True"


lemma flts_single1:
  assumes "nonalt r" "nonazero r"
  shows "rflts [r] = [r]"
  using assms
  apply(induct r)
  apply(auto)
  done

lemma nonalt0_flts_keeps:
  shows "(a \<noteq> RZERO) \<and> (\<forall>rs. a \<noteq> RALTS rs) \<Longrightarrow> rflts (a # xs) = a # rflts xs"
  apply(case_tac a)
       apply simp+
  done


lemma nonalt0_fltseq:
  shows "\<forall>r \<in> set rs. r \<noteq> RZERO \<and> nonalt r \<Longrightarrow> rflts rs = rs"
  apply(induct rs)
   apply simp
  apply(case_tac "a = RZERO")
   apply fastforce
  apply(case_tac "\<exists>rs1. a = RALTS rs1")
   apply(erule exE)
   apply simp+
  using nonalt0_flts_keeps by presburger

  


lemma goodalts_nonalt:
  shows "good (RALTS rs) \<Longrightarrow> rflts rs = rs"
  apply(induct x == "RALTS rs" arbitrary: rs rule: good.induct)
    apply simp
  
  using good.simps(5) apply blast
  apply simp
  apply(case_tac "r1 = RZERO")
  using good.simps(1) apply force
  apply(case_tac "r2 = RZERO")
  using good.simps(1) apply force
  apply(subgoal_tac "rflts (r1 # r2 # rs) = r1 # r2 # rflts rs")
  prefer 2
   apply (metis nonalt.simps(1) rflts_def_idiot)
  apply(subgoal_tac "\<forall>r \<in> set rs. r \<noteq> RZERO \<and> nonalt r")
   apply(subgoal_tac "rflts rs = rs")
    apply presburger
  using nonalt0_fltseq apply presburger
  using good.simps(1) by blast
  

  


lemma test:
  assumes "good r"
  shows "rsimp r = r"

  using assms
  apply(induct rule: good.induct)
                      apply simp
                      apply simp
                      apply simp
                      apply simp
                      apply simp
                      apply(subgoal_tac "distinct (r1 # r2 # rs)")
  prefer 2
  using good.simps(6) apply blast
  apply(subgoal_tac "rflts (r1 # r2 # rs ) = r1 # r2 # rs")
  prefer 2
  using goodalts_nonalt apply blast

                      apply(subgoal_tac "r1 \<noteq> r2")
  prefer 2
                      apply (meson distinct_length_2_or_more)
                      apply(subgoal_tac "r1 \<notin> set rs")
                      apply(subgoal_tac "r2 \<notin> set rs")
                      apply(subgoal_tac "\<forall>r \<in> set rs. rsimp r = r")
                      apply(subgoal_tac "map rsimp rs = rs")
  apply simp             
                      apply(subgoal_tac "\<forall>r \<in>  {r1, r2}. r \<notin> set rs")
  apply (metis distinct_not_exist rdistinct_on_distinct)
  
                      apply blast
                      apply (meson map_idI)
                      apply (metis good.simps(6) insert_iff list.simps(15))

  apply (meson distinct.simps(2))
                      apply (simp add: distinct_length_2_or_more)
                      apply simp+
  done



lemma rsimp_idem:
  shows "rsimp (rsimp r) = rsimp r"
  using test good1
  by force

corollary rsimp_inner_idem4:
  shows "rsimp r = RALTS rs \<Longrightarrow> rflts rs = rs"
  by (metis good1 goodalts_nonalt rrexp.distinct(7))


lemma head_one_more_simp:
  shows "map rsimp (r # rs) = map rsimp (( rsimp r) # rs)"
  by (simp add: rsimp_idem)


lemma der_simp_nullability:
  shows "rnullable r = rnullable (rsimp r)"
  using RL_rnullable RL_rsimp by auto
  

lemma no_alt_short_list_after_simp:
  shows "RALTS rs = rsimp r \<Longrightarrow> rsimp_ALTs rs = RALTS rs"
  by (metis bbbbs good1 k0a rrexp.distinct(7))


lemma no_further_dB_after_simp:
  shows "RALTS rs = rsimp r \<Longrightarrow> rdistinct rs {} = rs"
  apply(subgoal_tac "good (RALTS rs)")
  apply(subgoal_tac "distinct rs")
  using rdistinct_on_distinct apply blast
  apply (metis distinct.simps(1) distinct.simps(2) empty_iff good.simps(6) list.exhaust set_empty2)
  using good1 by fastforce


lemma idem_after_simp1:
  shows "rsimp_ALTs (rdistinct (rflts [rsimp aa]) {}) = rsimp aa"
  apply(case_tac "rsimp aa")
  apply simp+
  apply (metis no_alt_short_list_after_simp no_further_dB_after_simp)
   apply(simp)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp)
  done



lemma identity_wwo0:
  shows "rsimp (rsimp_ALTs (RZERO # rs)) = rsimp (rsimp_ALTs rs)"
  apply (metis idem_after_simp1 list.exhaust list.simps(8) list.simps(9) rflts.simps(2) rsimp.simps(2) rsimp.simps(3) rsimp_ALTs.simps(1) rsimp_ALTs.simps(2) rsimp_ALTs.simps(3))
  done

lemma distinct_removes_last:
  shows "\<lbrakk>a \<in> set as\<rbrakk>
    \<Longrightarrow> rdistinct as rset = rdistinct (as @ [a]) rset"
and "rdistinct (ab # as @ [ab]) rset1 = rdistinct (ab # as) rset1"
  apply(induct as arbitrary: rset ab rset1 a)
     apply simp
    apply simp
  apply(case_tac "aa \<in> rset")
   apply(case_tac "a = aa")
  apply (metis append_Cons)
    apply simp
   apply(case_tac "a \<in> set as")
  apply (metis append_Cons rdistinct.simps(2) set_ConsD)
   apply(case_tac "a = aa")
    prefer 2
    apply simp
   apply (metis append_Cons)
  apply(case_tac "ab \<in> rset1")
  prefer 2
   apply(subgoal_tac "rdistinct (ab # (a # as) @ [ab]) rset1 = 
               ab # (rdistinct ((a # as) @ [ab]) (insert ab rset1))")
  prefer 2
  apply force
  apply(simp only:)
     apply(subgoal_tac "rdistinct (ab # a # as) rset1 = ab # (rdistinct (a # as) (insert ab rset1))")
    apply(simp only:)
    apply(subgoal_tac "rdistinct ((a # as) @ [ab]) (insert ab rset1) = rdistinct (a # as) (insert ab rset1)")
     apply blast
    apply(case_tac "a \<in> insert ab rset1")
     apply simp
     apply (metis insertI1)
    apply simp
    apply (meson insertI1)
   apply simp
  apply(subgoal_tac "rdistinct ((a # as) @ [ab]) rset1 = rdistinct (a # as) rset1")
   apply simp
  by (metis append_Cons insert_iff insert_is_Un rdistinct.simps(2))


lemma distinct_removes_middle:
  shows  "\<lbrakk>a \<in> set as\<rbrakk>
    \<Longrightarrow> rdistinct (as @ as2) rset = rdistinct (as @ [a] @ as2) rset"
and "rdistinct (ab # as @ [ab] @ as3) rset1 = rdistinct (ab # as @ as3) rset1"
   apply(induct as arbitrary: rset rset1 ab as2 as3 a)
     apply simp
    apply simp
   apply(case_tac "a \<in> rset")
    apply simp
    apply metis
   apply simp
   apply (metis insertI1)
  apply(case_tac "a = ab")
   apply simp
   apply(case_tac "ab \<in> rset")
    apply simp
    apply presburger
   apply (meson insertI1)
  apply(case_tac "a \<in> rset")
  apply (metis (no_types, opaque_lifting) Un_insert_left append_Cons insert_iff rdistinct.simps(2) sup_bot_left)
  apply(case_tac "ab \<in> rset")
  apply simp
   apply (meson insert_iff)
  apply simp
  by (metis insertI1)


lemma distinct_removes_middle3:
  shows  "\<lbrakk>a \<in> set as\<rbrakk>
    \<Longrightarrow> rdistinct (as @ a #as2) rset = rdistinct (as @ as2) rset"
  using distinct_removes_middle(1) by fastforce


lemma distinct_removes_list:
  shows "\<lbrakk> \<forall>r \<in> set rs. r \<in> set as\<rbrakk> \<Longrightarrow> rdistinct (as @ rs) {} = rdistinct as {}"
  apply(induct rs)
   apply simp+
  apply(subgoal_tac "rdistinct (as @ a # rs) {} = rdistinct (as @ rs) {}")
   prefer 2
  apply (metis append_Cons append_Nil distinct_removes_middle(1))
  by presburger


lemma spawn_simp_rsimpalts:
  shows "rsimp (rsimp_ALTs rs) = rsimp (rsimp_ALTs (map rsimp rs))"
  apply(cases rs)
   apply simp
  apply(case_tac list)
   apply simp
   apply(subst rsimp_idem[symmetric])
   apply simp
  apply(subgoal_tac "rsimp_ALTs rs = RALTS rs")
   apply(simp only:)
   apply(subgoal_tac "rsimp_ALTs (map rsimp rs) = RALTS (map rsimp rs)")
    apply(simp only:)
  prefer 2
  apply simp
   prefer 2
  using rsimp_ALTs.simps(3) apply presburger
  apply auto
  apply(subst rsimp_idem)+
  by (metis comp_apply rsimp_idem)


lemma simp_singlealt_flatten:
  shows "rsimp (RALTS [RALTS rsa]) = rsimp (RALTS (rsa @ []))"
  apply(induct rsa)
   apply simp
  apply simp
  by (metis idem_after_simp1 list.simps(9) rsimp.simps(2))


lemma good1_rsimpalts:
  shows "rsimp r = RALTS rs \<Longrightarrow> rsimp_ALTs rs = RALTS rs"
  by (metis no_alt_short_list_after_simp) 
  



lemma good1_flatten:
  shows "\<lbrakk> rsimp r =  (RALTS rs1)\<rbrakk>
       \<Longrightarrow> rflts (rsimp_ALTs rs1 # map rsimp rsb) = rflts (rs1 @ map rsimp rsb)"
  apply(subst good1_rsimpalts)
   apply simp+
  apply(subgoal_tac "rflts (rs1 @ map rsimp rsb) = rs1 @ rflts (map rsimp rsb)")
   apply simp
  using flts_append rsimp_inner_idem4 by presburger

  
lemma flatten_rsimpalts:
  shows "rflts (rsimp_ALTs (rdistinct (rflts (map rsimp rsa)) {}) # map rsimp rsb) = 
         rflts ( (rdistinct (rflts (map rsimp rsa)) {}) @ map rsimp rsb)"
proof -
  let ?xs = "rdistinct (rflts (map rsimp rsa)) {}"
  let ?ys = "map rsimp rsb"
  have good_or_zero: "\<forall>r \<in> set (map rsimp rsa). good r \<or> r = RZERO"
    using good1 by auto
  have flat_good: "\<forall>r \<in> set (rflts (map rsimp rsa)). good r \<and> nonalt r"
    using flts3_good_nonalt[OF good_or_zero] .
  have xs_props: "\<forall>r \<in> set ?xs. r \<noteq> RZERO \<and> nonalt r"
    using flat_good good_not_RZERO rdistinct_set_equality1 by fastforce
  have rflts_xs: "rflts ?xs = ?xs"
    using xs_props nonalt0_fltseq by blast
  show ?thesis
  proof (cases ?xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons a xs)
    note xs_cons = Cons
    then show ?thesis
    proof (cases xs)
      case Nil
      then show ?thesis
        using xs_cons by simp
    next
      case (Cons b ys)
      then have xs_shape: "?xs = a # b # ys"
        using xs_cons by simp
      have rhs: "rflts (?xs @ ?ys) = ?xs @ rflts ?ys"
        using rflts_xs flts_append[of ?xs ?ys] by simp
      show ?thesis
        using xs_shape rhs by simp
    qed
  qed
qed

lemma last_elem_out:
  shows "\<lbrakk>x \<notin> set xs; x \<notin> rset \<rbrakk> \<Longrightarrow> rdistinct (xs @ [x]) rset = rdistinct xs rset @ [x]"
  apply(induct xs arbitrary: rset)
  apply simp+
  done




lemma rdistinct_concat_general:
  shows "rdistinct (rs1 @ rs2) {} = (rdistinct rs1 {}) @ (rdistinct rs2 (set rs1))"
  apply(induct rs1 arbitrary: rs2 rule: rev_induct)
   apply simp
  apply(drule_tac x = "x # rs2" in meta_spec)
  apply simp
  apply(case_tac "x \<in> set xs")
   apply simp
  
   apply (simp add: distinct_removes_middle3 insert_absorb)
  apply simp
  by (simp add: last_elem_out)


  

lemma distinct_once_enough:
  shows "rdistinct (rs @ rsa) {} = rdistinct (rdistinct rs {} @ rsa) {}"
  apply(subgoal_tac "distinct (rdistinct rs {})")
   apply(subgoal_tac 
" rdistinct (rdistinct rs {} @ rsa) {} = rdistinct rs {} @ (rdistinct rsa (set rs))")
  apply(simp only:)
  using rdistinct_concat_general apply blast
  apply (simp add: distinct_rdistinct_append rdistinct_set_equality1)
  by (simp add: rdistinct_does_the_job)
  

lemma simp_flatten:
  shows "rsimp (RALTS ((RALTS rsa) # rsb)) = rsimp (RALTS (rsa @ rsb))"
  apply simp
  apply(subst flatten_rsimpalts)
  apply(simp add: flts_append)
  by (metis Diff_empty distinct_once_enough flts_append nonalt0_fltseq nonalt_flts_rd qqq1 rdistinct_set_equality1)

lemma basic_rsimp_SEQ_property1:
  shows "rsimp_SEQ RONE r = r"
  by (simp add: idiot)



lemma basic_rsimp_SEQ_property3:
  shows "rsimp_SEQ r RZERO = RZERO"  
  using rsimp_SEQ.elims by blast



fun vsuf :: "char list \<Rightarrow> rrexp \<Rightarrow> char list list" where
"vsuf [] _ = []"
|"vsuf (c#cs) r1 = (if (rnullable r1) then  (vsuf cs (rder c r1)) @ [c # cs]
                                      else  (vsuf cs (rder c r1))
                   ) "






fun star_update :: "char \<Rightarrow> rrexp \<Rightarrow> char list list \<Rightarrow> char list list" where
"star_update c r [] = []"
|"star_update c r (s # Ss) = (if (rnullable (rders r s)) 
                                then (s@[c]) # [c] # (star_update c r Ss) 
                               else   (s@[c]) # (star_update c r Ss) )"


fun star_updates :: "char list \<Rightarrow> rrexp \<Rightarrow> char list list \<Rightarrow> char list list"
  where
"star_updates [] r Ss = Ss"
| "star_updates (c # cs) r Ss = star_updates cs r (star_update c r Ss)"

lemma stupdates_append: shows 
"star_updates (s @ [c]) r Ss = star_update c r (star_updates s r Ss)"
  apply(induct s arbitrary: Ss)
   apply simp
  apply simp
  done

lemma flts_removes0:
  shows "  rflts (rs @ [RZERO])  =
           rflts rs"
  apply(induct rs)
   apply simp
  by (metis append_Cons rflts.simps(2) rflts.simps(3) rflts_def_idiot)
  

lemma rflts_spills_last:
  shows "rflts (rs1 @ [RALTS rs]) = rflts rs1 @ rs"
  apply (induct rs1 rule: rflts.induct)
  apply(auto)
  done

lemma flts_keeps1:
  shows "rflts (rs @ [RONE]) = rflts rs @ [RONE]"
  apply (induct rs rule: rflts.induct)
  apply(auto)
  done

lemma flts_keeps_others:
  shows "\<lbrakk>a \<noteq> RZERO; \<nexists>rs1. a = RALTS rs1\<rbrakk> \<Longrightarrow>rflts (rs @ [a]) = rflts rs @ [a]"
  apply(induct rs rule: rflts.induct)
  apply(auto)
  by (meson k0b nonalt.elims(3))

lemma distinct_removes_duplicate_flts_nonalt:
  assumes "a \<in> set rs" "a \<noteq> RZERO" "\<nexists>rs1. a = RALTS rs1"
  shows "rdistinct (rflts (rs @ [a])) {} = rdistinct (rflts rs) {}"
proof -
  have "a \<in> set (rflts rs)"
    using assms by (intro rflts_def_idiot2) auto
  moreover have "rflts (rs @ [a]) = rflts rs @ [a]"
    using assms by (intro flts_keeps_others) auto
  ultimately show ?thesis
    by (simp add: distinct_removes_last(1))
qed

lemma rflts_tail_subset:
  shows "set (rflts rs) \<subseteq> set (rflts (r # rs))"
  by (cases r) auto

lemma spilled_alts_contained:
  shows "\<lbrakk>a = RALTS rs ; a \<in> set rs1\<rbrakk> \<Longrightarrow> \<forall>r \<in> set rs. r \<in> set (rflts rs1)"
proof (induct rs1)
  case Nil
  then show ?case by simp
next
  case (Cons aa rs1)
  show ?case
  proof (cases "a = aa")
    case True
    then show ?thesis
      using Cons.prems by auto
  next
    case False
    then have a_in_tail: "a \<in> set rs1"
      using Cons.prems by simp
    have "\<forall>r \<in> set rs. r \<in> set (rflts rs1)"
      using Cons.hyps Cons.prems(1) a_in_tail by blast
    moreover have "set (rflts rs1) \<subseteq> set (rflts (aa # rs1))"
      by (rule rflts_tail_subset)
    ultimately show ?thesis
      by blast
  qed
qed
  

lemma distinct_removes_duplicate_flts:
  shows " a \<in> set rsa
       \<Longrightarrow> rdistinct (rflts (map rsimp rsa @ [rsimp a])) {} =
           rdistinct (rflts (map rsimp rsa)) {}"
proof -
  assume a_in: "a \<in> set rsa"
  then have simp_in: "rsimp a \<in> set (map rsimp rsa)"
    by simp
  have nonalt_case:
    "\<And>x. \<lbrakk>x \<in> set (map rsimp rsa); x \<noteq> RZERO; \<nexists>rs1. x = RALTS rs1\<rbrakk>
      \<Longrightarrow> rdistinct (rflts (map rsimp rsa @ [x])) {} =
          rdistinct (rflts (map rsimp rsa)) {}"
    by (rule distinct_removes_duplicate_flts_nonalt)
  show ?thesis
  proof (cases "rsimp a")
    case RZERO
    then show ?thesis
      using flts_removes0 by presburger
  next
    case RONE
    then show ?thesis
      using nonalt_case simp_in by simp
  next
    case (RCHAR c)
    then show ?thesis
      using nonalt_case simp_in by simp
  next
    case (RSEQ r1 r2)
    then show ?thesis
      using nonalt_case simp_in by simp
  next
    case (RALTS rs)
    have in_map: "RALTS rs \<in> set (map rsimp rsa)"
      using RALTS simp_in by simp
    have contained: "\<forall>r \<in> set rs. r \<in> set (rflts (map rsimp rsa))"
      using spilled_alts_contained[OF refl in_map] .
    have spill: "rflts (map rsimp rsa @ [RALTS rs]) =
      rflts (map rsimp rsa) @ rs"
      by (rule rflts_spills_last)
    show ?thesis
      using RALTS contained spill distinct_removes_list by simp
  next
    case (RSTAR r)
    then show ?thesis
      using nonalt_case simp_in by simp
  next
    case (RNTIMES r n)
    then show ?thesis
      using nonalt_case simp_in by simp
  next
    case (RBACKREF4 r1 r2 r3 r4 cs)
    then show ?thesis
      using nonalt_case simp_in by simp
  next
    case (RHALF r cs rep)
    then show ?thesis
      using nonalt_case simp_in by simp
  next
    case (RRESIDUE cs rep)
    then show ?thesis
      using nonalt_case simp_in by simp
  qed
qed
  

(*some basic facts about rsimp*)

end
