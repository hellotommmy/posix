   
theory PosixSpec
  imports RegLangs
begin

section \<open>"Plain" Values\<close>

(* BACKREF-MIGRATION-COMPLETED (definition augmentation, ADMIN APPROVAL REQUIRED):
   Extend the original val datatype with the approved BACKREF4/HALF/RESIDUE
   value shapes. Do not introduce bval, bval4, gbval, or bridge wrappers. *)
datatype val = 
  Void
| Char char
| Seq val val
| Right val
| Left val
| Stars "val list"
| Backref4 val val val val string
| Half val string string
| Residue string string


section \<open>The string behind a value\<close>

(* BACKREF-MIGRATION-COMPLETED (definition augmentation):
   Add flat cases for the new original value constructors so BACKREF4 flattens
   to s1 @ s2 @ s3 @ rev cs @ s2 @ s4, and HALF/RESIDUE flatten to their
   carried residual strings. *)
fun 
  flat :: "val \<Rightarrow> string"
where
  "flat (Void) = []"
| "flat (Char c) = [c]"
| "flat (Left v) = flat v"
| "flat (Right v) = flat v"
| "flat (Seq v1 v2) = (flat v1) @ (flat v2)"
| "flat (Stars []) = []"
| "flat (Stars (v#vs)) = (flat v) @ (flat (Stars vs))"
| "flat (Backref4 v1 v2 v3 v4 cs) =
    flat v1 @ flat v2 @ flat v3 @ rev cs @ flat v2 @ flat v4"
| "flat (Half v cs rep) = flat v @ cs"
| "flat (Residue cs rep) = cs"

abbreviation
  "flats vs \<equiv> concat (map flat vs)"

lemma flat_Stars [simp]:
 "flat (Stars vs) = flats vs"
by (induct vs) (auto)


section \<open>Lexical Values\<close>

(* BACKREF-MIGRATION-COMPLETED (definition augmentation):
   Add original Prf rules for BACKREF4/HALF/RESIDUE. This replaces
   BPrf/BPrf4/GPrf; direct Prf extension is bounty-eligible, wrappers are not. *)
inductive 
  Prf :: "val \<Rightarrow> rexp \<Rightarrow> bool" ("\<Turnstile> _ : _" [100, 100] 100)
where
 "\<lbrakk>\<Turnstile> v1 : r1; \<Turnstile> v2 : r2\<rbrakk> \<Longrightarrow> \<Turnstile>  Seq v1 v2 : SEQ r1 r2"
| "\<Turnstile> v1 : r1 \<Longrightarrow> \<Turnstile> Left v1 : ALT r1 r2"
| "\<Turnstile> v2 : r2 \<Longrightarrow> \<Turnstile> Right v2 : ALT r1 r2"
| "\<Turnstile> Void : ONE"
| "\<Turnstile> Char c : CH c"
| "\<forall>v \<in> set vs. \<Turnstile> v : r \<and> flat v \<noteq> [] \<Longrightarrow> \<Turnstile> Stars vs : STAR r"
| "\<lbrakk>\<forall>v \<in> set vs1. \<Turnstile> v : r \<and> flat v \<noteq> []; 
    \<forall>v \<in> set vs2. \<Turnstile> v : r \<and> flat v = []; 
    length (vs1 @ vs2) = n\<rbrakk> \<Longrightarrow> \<Turnstile> Stars (vs1 @ vs2) : NTIMES r n" 
| "\<lbrakk>\<Turnstile> v1 : r1; \<Turnstile> v2 : r2; \<Turnstile> v3 : r3; \<Turnstile> v4 : r4\<rbrakk>
    \<Longrightarrow> \<Turnstile> Backref4 v1 v2 v3 v4 cs : BACKREF4 r1 r2 r3 r4 cs"
| "\<Turnstile> v : r \<Longrightarrow> \<Turnstile> Half v cs rep : HALF r cs rep"
| "\<Turnstile> Residue cs rep : RESIDUE cs rep"



(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Add elimination rules for BACKREF4/HALF/RESIDUE after Prf is extended. *)
inductive_cases Prf_elims:
  "\<Turnstile> v : ZERO"
  "\<Turnstile> v : SEQ r1 r2"
  "\<Turnstile> v : ALT r1 r2"
  "\<Turnstile> v : ONE"
  "\<Turnstile> v : CH c"
  "\<Turnstile> vs : STAR r"
  "\<Turnstile> vs : NTIMES r n"
  "\<Turnstile> v : BACKREF4 r1 r2 r3 r4 cs"
  "\<Turnstile> v : HALF r cs rep"
  "\<Turnstile> v : RESIDUE cs rep"

lemma Prf_Stars_appendE:
  assumes "\<Turnstile> Stars (vs1 @ vs2) : STAR r"
  shows "\<Turnstile> Stars vs1 : STAR r \<and> \<Turnstile> Stars vs2 : STAR r" 
using assms
by (auto intro: Prf.intros elim!: Prf_elims)

lemma Pow_cstring:
  fixes A::"string set"
  assumes "s \<in> A ^^ n"
  shows "\<exists>ss1 ss2. concat (ss1 @ ss2) = s \<and> length (ss1 @ ss2) = n \<and> 
         (\<forall>s \<in> set ss1. s \<in> A \<and> s \<noteq> []) \<and> (\<forall>s \<in> set ss2. s \<in> A \<and> s = [])"
using assms
apply(induct n arbitrary: s)
  apply(auto)[1]
  apply(auto simp add: Sequ_def)
  apply(drule_tac x="s2" in meta_spec)
  apply(simp)
apply(erule exE)+
  apply(clarify)
apply(case_tac "s1 = []")
apply(simp)
apply(rule_tac x="ss1" in exI)
apply(rule_tac x="s1 # ss2" in exI)
apply(simp)
apply(rule_tac x="s1 # ss1" in exI)
apply(rule_tac x="ss2" in exI)
  apply(simp)
  done

lemma flats_Prf_value:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<Turnstile> v : r"
  shows "\<exists>vs. flats vs = concat ss \<and> (\<forall>v\<in>set vs. \<Turnstile> v : r \<and> flat v \<noteq> [])"
using assms
apply(induct ss)
apply(auto)
apply(rule_tac x="[]" in exI)
apply(simp)
apply(case_tac "flat v = []")
apply(rule_tac x="vs" in exI)
apply(simp)
apply(rule_tac x="v#vs" in exI)
apply(simp)
  done

lemma Aux:
  assumes "\<forall>s\<in>set ss. s = []"
  shows "concat ss = []"
using assms
by (induct ss) (auto)

lemma flats_cval:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<Turnstile> v : r"
  shows "\<exists>vs1 vs2. flats (vs1 @ vs2) = concat ss \<and> length (vs1 @ vs2) = length ss \<and> 
          (\<forall>v\<in>set vs1. \<Turnstile> v : r \<and> flat v \<noteq> []) \<and>
          (\<forall>v\<in>set vs2. \<Turnstile> v : r \<and> flat v = [])"
using assms
apply(induct ss rule: rev_induct)
apply(rule_tac x="[]" in exI)+
apply(simp)
apply(simp)
apply(clarify)
apply(case_tac "flat v = []")
apply(rule_tac x="vs1" in exI)
apply(rule_tac x="v#vs2" in exI)
apply(simp)
apply(rule_tac x="vs1 @ [v]" in exI)
apply(rule_tac x="vs2" in exI)
apply(simp)
by (simp add: Aux)

lemma pow_Prf:
  assumes "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> flat v \<in> A"
  shows "flats vs \<in> A ^^ (length vs)"
  using assms
  by (induct vs) (auto)

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend soundness of flat values with BACKREF4/HALF/RESIDUE cases. *)
lemma L_flat_Prf1:
  assumes "\<Turnstile> v : r" 
  shows "flat v \<in> L r"
  using assms
  apply (induct v r rule: Prf.induct) 
  apply(auto simp add: Sequ_def Star_concat lang_pow_add intro: backref_lang4I)
  apply (metis pow_Prf)
  done


  
(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend completeness of flat values with BACKREF4/HALF/RESIDUE cases. The
   BACKREF4 case should build one original val, not a bval4/gbval wrapper. *)
lemma L_flat_Prf2:
  assumes "s \<in> L r" 
  shows "\<exists>v. \<Turnstile> v : r \<and> flat v = s"
using assms
proof(induct r arbitrary: s)
  case (STAR r s)
  have IH: "\<And>s. s \<in> L r \<Longrightarrow> \<exists>v. \<Turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> L (STAR r)" by fact
  then obtain ss where "concat ss = s" "\<forall>s \<in> set ss. s \<in> L r \<and> s \<noteq> []"
  using Star_split by auto  
  then obtain vs where "flats vs = s" "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> flat v \<noteq> []"
  using IH flats_Prf_value by metis 
  then show "\<exists>v. \<Turnstile> v : STAR r \<and> flat v = s"
  using Prf.intros(6) flat_Stars by blast
next 
  case (SEQ r1 r2 s)
  then show "\<exists>v. \<Turnstile> v : SEQ r1 r2 \<and> flat v = s"
  unfolding Sequ_def L.simps by (fastforce intro: Prf.intros)
next
  case (ALT r1 r2 s)
  then show "\<exists>v. \<Turnstile> v : ALT r1 r2 \<and> flat v = s"
    unfolding L.simps by (fastforce intro: Prf.intros)
next
  case (NTIMES r n)
  have IH: "\<And>s. s \<in> L r \<Longrightarrow> \<exists>v. \<Turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> L (NTIMES r n)" by fact
  then obtain ss1 ss2 where "concat (ss1 @ ss2) = s" "length (ss1 @ ss2) = n" 
    "\<forall>s \<in> set ss1. s \<in> L r \<and> s \<noteq> []" "\<forall>s \<in> set ss2. s \<in> L r \<and> s = []"
  using Pow_cstring by force
  then obtain vs1 vs2 where "flats (vs1 @ vs2) = s" "length (vs1 @ vs2) = n" 
      "\<forall>v\<in>set vs1. \<Turnstile> v : r \<and> flat v \<noteq> []" "\<forall>v\<in>set vs2. \<Turnstile> v : r \<and> flat v = []"
    using IH flats_cval 
  apply -
  apply(drule_tac x="ss1 @ ss2" in meta_spec)
  apply(drule_tac x="r" in meta_spec)
  apply(drule meta_mp)
  apply(simp)
  apply (metis Un_iff)
  apply(clarify)
  apply(drule_tac x="vs1" in meta_spec)
  apply(drule_tac x="vs2" in meta_spec)
  apply(simp)
  done
  then show "\<exists>v. \<Turnstile> v : NTIMES r n \<and> flat v = s"
    using Prf.intros(7) flat_Stars by blast
next
  case (BACKREF4 r1 r2 r3 r4 cs s)
  then obtain s1 s2 s3 s4 where parts:
    "s1 \<in> L r1" "s2 \<in> L r2" "s3 \<in> L r3" "s4 \<in> L r4"
    "s = s1 @ s2 @ s3 @ rev cs @ s2 @ s4"
    by (auto simp add: backref_lang4_def)
  then obtain v1 v2 v3 v4 where
    "\<Turnstile> v1 : r1" "flat v1 = s1"
    "\<Turnstile> v2 : r2" "flat v2 = s2"
    "\<Turnstile> v3 : r3" "flat v3 = s3"
    "\<Turnstile> v4 : r4" "flat v4 = s4"
    using BACKREF4.hyps by metis
  then show "\<exists>v. \<Turnstile> v : BACKREF4 r1 r2 r3 r4 cs \<and> flat v = s"
    using parts by (intro exI[of _ "Backref4 v1 v2 v3 v4 cs"]) (auto intro: Prf.intros)
next
  case (HALF r cs rep s)
  then obtain s1 where parts: "s1 \<in> L r" "s = s1 @ cs"
    by (auto simp add: Sequ_def)
  then obtain v where "\<Turnstile> v : r" "flat v = s1"
    using HALF.hyps by blast
  then show "\<exists>v. \<Turnstile> v : HALF r cs rep \<and> flat v = s"
    using parts by (intro exI[of _ "Half v cs rep"]) (auto intro: Prf.intros)
next
  case (RESIDUE cs rep s)
  then show "\<exists>v. \<Turnstile> v : RESIDUE cs rep \<and> flat v = s"
    by (auto intro: Prf.intros)
qed (auto intro: Prf.intros)


(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Keep this as the original value-language correspondence theorem after the
   new constructors are added. Wrapper summaries do not count as bounty. *)
lemma L_flat_Prf:
  shows "L(r) = {flat v | v. \<Turnstile> v : r}"
using L_flat_Prf1 L_flat_Prf2 by blast



section \<open>Sets of Lexical Values\<close>

text \<open>
  Shows that lexical values are finite for a given regex and string.
\<close>

definition
  LV :: "rexp \<Rightarrow> string \<Rightarrow> val set"
where  "LV r s \<equiv> {v. \<Turnstile> v : r \<and> flat v = s}"

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Add LV facts for the new constructors where useful. Avoid huge fragile simp
   rules for BACKREF4 if split lemmas are clearer. *)
lemma LV_simps:
  shows "LV ZERO s = {}"
  and   "LV ONE s = (if s = [] then {Void} else {})"
  and   "LV (CH c) s = (if s = [c] then {Char c} else {})"
  and   "LV (ALT r1 r2) s = Left ` LV r1 s \<union> Right ` LV r2 s"
  and   "LV (NTIMES r 0) s = (if s = [] then {Stars []} else {})"
unfolding LV_def
  apply (auto intro: Prf.intros elim: Prf.cases)
  by (metis Prf.intros(7) append.right_neutral empty_iff list.set(1) list.size(3))
  

abbreviation
  "Prefixes s \<equiv> {s'. prefix s' s}"

abbreviation
  "Suffixes s \<equiv> {s'. suffix s' s}"

abbreviation
  "SSuffixes s \<equiv> {s'. strict_suffix s' s}"

lemma Suffixes_cons [simp]:
  shows "Suffixes (c # s) = Suffixes s \<union> {c # s}"
by (auto simp add: suffix_def Cons_eq_append_conv)


lemma finite_Suffixes: 
  shows "finite (Suffixes s)"
by (induct s) (simp_all)

lemma finite_SSuffixes: 
  shows "finite (SSuffixes s)"
proof -
  have "SSuffixes s \<subseteq> Suffixes s"
   unfolding strict_suffix_def suffix_def by auto
  then show "finite (SSuffixes s)"
   using finite_Suffixes finite_subset by blast
qed

lemma finite_Prefixes: 
  shows "finite (Prefixes s)"
proof -
  have "finite (Suffixes (rev s))" 
    by (rule finite_Suffixes)
  then have "finite (rev ` Suffixes (rev s))" by simp
  moreover
  have "rev ` (Suffixes (rev s)) = Prefixes s"
  unfolding suffix_def prefix_def image_def
   by (auto)(metis rev_append rev_rev_ident)+
  ultimately show "finite (Prefixes s)" by simp
qed

definition
  "Stars_Append Vs1 Vs2 \<equiv> {Stars (vs1 @ vs2) | vs1 vs2. Stars vs1 \<in> Vs1 \<and> Stars vs2 \<in> Vs2}"

lemma finite_Stars_Append:
  assumes "finite Vs1" "finite Vs2"
  shows "finite (Stars_Append Vs1 Vs2)"
  using assms  
proof -
  define UVs1 where "UVs1 \<equiv> Stars -` Vs1"
  define UVs2 where "UVs2 \<equiv> Stars -` Vs2"  
  from assms have "finite UVs1" "finite UVs2"
    unfolding UVs1_def UVs2_def
    by(simp_all add: finite_vimageI inj_on_def) 
  then have "finite ((\<lambda>(vs1, vs2). Stars (vs1 @ vs2)) ` (UVs1 \<times> UVs2))"
    by simp
  moreover 
    have "Stars_Append Vs1 Vs2 = (\<lambda>(vs1, vs2). Stars (vs1 @ vs2)) ` (UVs1 \<times> UVs2)"
    unfolding Stars_Append_def UVs1_def UVs2_def by auto    
  ultimately show "finite (Stars_Append Vs1 Vs2)"   
    by simp
qed 

lemma LV_NTIMES_subset:
  "LV (NTIMES r n) s \<subseteq> Stars_Append (LV (STAR r) s) (\<Union>i\<le>n. LV (NTIMES r i) [])"
apply(auto simp add: LV_def)
apply(auto elim!: Prf_elims)
  apply(auto simp add: Stars_Append_def)
  apply(rule_tac x="vs1" in exI)
  apply(rule_tac x="vs2" in exI)  
  apply(auto)
    using Prf.intros(6) apply(auto)
      apply(rule_tac x="length vs2" in bexI)
    thm Prf.intros
      apply(subst append.simps(1)[symmetric])
    apply(rule Prf.intros)
      apply(auto)[1]
      apply(auto)[1]
     apply(simp)
    apply(simp)
    done

lemma LV_NTIMES_Suc_empty:
  shows "LV (NTIMES r (Suc n)) [] = 
     (\<lambda>(v, vs). Stars (v#vs)) ` (LV r [] \<times> (Stars -` (LV (NTIMES r n) [])))"
unfolding LV_def
apply(auto elim!: Prf_elims simp add: image_def)
apply(case_tac vs1)
apply(auto)
apply(case_tac vs2)
apply(auto)
apply(subst append.simps(1)[symmetric])
apply(rule Prf.intros)
apply(auto)
apply(subst append.simps(1)[symmetric])
apply(rule Prf.intros)
apply(auto)
  done 

lemma LV_STAR_finite:
  assumes "\<forall>s. finite (LV r s)"
  shows "finite (LV (STAR r) s)"
proof(induct s rule: length_induct)
  fix s::"char list"
  assume "\<forall>s'. length s' < length s \<longrightarrow> finite (LV (STAR r) s')"
  then have IH: "\<forall>s' \<in> SSuffixes s. finite (LV (STAR r) s')"
    by (force simp add: strict_suffix_def suffix_def) 
  define f where "f \<equiv> \<lambda>(v, vs). Stars (v # vs)"
  define S1 where "S1 \<equiv> \<Union>s' \<in> Prefixes s. LV r s'"
  define S2 where "S2 \<equiv> \<Union>s2 \<in> SSuffixes s. Stars -` (LV (STAR r) s2)"
  have "finite S1" using assms
    unfolding S1_def by (simp_all add: finite_Prefixes)
  moreover 
  with IH have "finite S2" unfolding S2_def
    by (auto simp add: finite_SSuffixes inj_on_def finite_vimageI)
  ultimately 
  have "finite ({Stars []} \<union> f ` (S1 \<times> S2))" by simp
  moreover 
  have "LV (STAR r) s \<subseteq> {Stars []} \<union> f ` (S1 \<times> S2)" 
  unfolding S1_def S2_def f_def
  unfolding LV_def image_def prefix_def strict_suffix_def 
  apply(auto)
  apply(case_tac x)
  apply(auto elim: Prf_elims)
  apply(erule Prf_elims)
  apply(auto)
  apply(case_tac vs)
  apply(auto intro: Prf.intros)  
  apply(rule exI)
  apply(rule conjI)
  apply(rule_tac x="flat a" in exI)
  apply(rule conjI)
  apply(rule_tac x="flats list" in exI)
  apply(simp)
   apply(blast)
  apply(simp add: suffix_def)
  using Prf.intros(6) by blast  
  ultimately
  show "finite (LV (STAR r) s)" by (simp add: finite_subset)
qed  

lemma finite_NTimes_empty:
  assumes "\<And>s. finite (LV r s)" 
  shows "finite (LV (NTIMES r n) [])"
  using assms
  apply(induct n)
   apply(auto simp add: LV_simps)
  apply(subst LV_NTIMES_Suc_empty)
  apply(rule finite_imageI)
  apply(rule finite_cartesian_product)
  using assms apply simp 
  apply(rule finite_vimageI)
  apply(simp)
  apply(simp add: inj_on_def)
  done

definition
  "Stars_Cons V Vs \<equiv> {Stars (v # vs) | v vs. v \<in> V \<and> Stars vs \<in> Vs}"


fun Stars_Pow :: "val set \<Rightarrow> nat \<Rightarrow> val set"
where  
  "Stars_Pow Vs 0 = {Stars []}"
| "Stars_Pow Vs (Suc n) = Stars_Cons Vs (Stars_Pow Vs n)"

lemma finite_Stars_Cons:
  assumes "finite V" "finite Vs"
  shows "finite (Stars_Cons V Vs)"
  using assms  
proof -
  from assms(2) have "finite (Stars -` Vs)"
    by(simp add: finite_vimageI inj_on_def) 
  with assms(1) have "finite (V \<times> (Stars -` Vs))"
    by(simp)
  then have "finite ((\<lambda>(v, vs). Stars (v # vs)) ` (V \<times> (Stars -` Vs)))"
    by simp
  moreover have "Stars_Cons V Vs = (\<lambda>(v, vs). Stars (v # vs)) ` (V \<times> (Stars -` Vs))"
    unfolding Stars_Cons_def by auto    
  ultimately show "finite (Stars_Cons V Vs)"   
    by simp
qed

lemma finite_Stars_Pow:
  assumes "finite Vs"
  shows "finite (Stars_Pow Vs n)"    
by (induct n) (simp_all add: finite_Stars_Cons assms)

definition
  "Strings_le n \<equiv> {s :: string. length s \<le> n}"

lemma finite_Strings_le:
  "finite (Strings_le n)"
proof -
  have "Strings_le n \<subseteq> {s :: string. set s \<subseteq> (UNIV :: char set) \<and> length s \<le> n}"
    by (auto simp add: Strings_le_def)
  moreover have "finite {s :: string. set s \<subseteq> (UNIV :: char set) \<and> length s \<le> n}"
    by (rule finite_lists_length_le) simp
  ultimately show ?thesis
    by (rule finite_subset)
qed

lemma finite_LV_Union_Strings_le:
  assumes "\<And>s. finite (LV r s)"
  shows "finite (\<Union>s \<in> Strings_le n. LV r s)"
  using assms by (simp add: finite_Strings_le)

lemma LV_BACKREF4_subset:
  "LV (BACKREF4 r1 r2 r3 r4 cs) s \<subseteq>
    (\<lambda>(((v1, v2), v3), v4). Backref4 v1 v2 v3 v4 cs) `
      ((((\<Union>t \<in> Strings_le (length s). LV r1 t) \<times>
         (\<Union>t \<in> Strings_le (length s). LV r2 t)) \<times>
         (\<Union>t \<in> Strings_le (length s). LV r3 t)) \<times>
         (\<Union>t \<in> Strings_le (length s). LV r4 t))"
proof
  fix v
  assume "v \<in> LV (BACKREF4 r1 r2 r3 r4 cs) s"
  then obtain v1 v2 v3 v4 where v:
    "v = Backref4 v1 v2 v3 v4 cs"
    "\<Turnstile> v1 : r1" "\<Turnstile> v2 : r2" "\<Turnstile> v3 : r3" "\<Turnstile> v4 : r4"
    "s = flat v1 @ flat v2 @ flat v3 @ rev cs @ flat v2 @ flat v4"
    unfolding LV_def by (auto elim!: Prf_elims)
  have "v1 \<in> (\<Union>t \<in> Strings_le (length s). LV r1 t)"
    using v unfolding LV_def Strings_le_def by auto
  moreover have "v2 \<in> (\<Union>t \<in> Strings_le (length s). LV r2 t)"
    using v unfolding LV_def Strings_le_def by auto
  moreover have "v3 \<in> (\<Union>t \<in> Strings_le (length s). LV r3 t)"
    using v unfolding LV_def Strings_le_def by auto
  moreover have "v4 \<in> (\<Union>t \<in> Strings_le (length s). LV r4 t)"
    using v unfolding LV_def Strings_le_def by auto
  ultimately show "v \<in>
    (\<lambda>(((v1, v2), v3), v4). Backref4 v1 v2 v3 v4 cs) `
      ((((\<Union>t\<in>Strings_le (length s). LV r1 t) \<times>
         (\<Union>t\<in>Strings_le (length s). LV r2 t)) \<times>
         (\<Union>t\<in>Strings_le (length s). LV r3 t)) \<times>
         (\<Union>t\<in>Strings_le (length s). LV r4 t))"
    using v(1) by (intro image_eqI[of _ _ "(((v1, v2), v3), v4)"]) auto
qed

lemma LV_HALF_subset:
  "LV (HALF r cs rep) s \<subseteq>
    (\<lambda>v. Half v cs rep) ` (\<Union>t \<in> Strings_le (length s). LV r t)"
proof
  fix v
  assume "v \<in> LV (HALF r cs rep) s"
  then obtain v' where v:
    "v = Half v' cs rep" "\<Turnstile> v' : r" "s = flat v' @ cs"
    unfolding LV_def by (auto elim!: Prf_elims)
  have "v' \<in> (\<Union>t \<in> Strings_le (length s). LV r t)"
    using v unfolding LV_def Strings_le_def by auto
  then show "v \<in> (\<lambda>v. Half v cs rep) ` (\<Union>t \<in> Strings_le (length s). LV r t)"
    using v(1) by auto
qed




(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend LV_finite with BACKREF4/HALF/RESIDUE. Add finite split helper lemmas
   for possible s1/s2/s3/s4 decompositions of a fixed target string. *)
lemma LV_finite:
  shows "finite (LV r s)"
proof(induct r arbitrary: s)
  case (ZERO s) 
  show "finite (LV ZERO s)" by (simp add: LV_simps)
next
  case (ONE s)
  show "finite (LV ONE s)" by (simp add: LV_simps)
next
  case (CH c s)
  show "finite (LV (CH c) s)" by (simp add: LV_simps)
next 
  case (ALT r1 r2 s)
  then show "finite (LV (ALT r1 r2) s)" by (simp add: LV_simps)
next 
  case (SEQ r1 r2 s)
  define f where "f \<equiv> \<lambda>(v1, v2). Seq v1 v2"
  define S1 where "S1 \<equiv> \<Union>s' \<in> Prefixes s. LV r1 s'"
  define S2 where "S2 \<equiv> \<Union>s' \<in> Suffixes s. LV r2 s'"
  have IHs: "\<And>s. finite (LV r1 s)" "\<And>s. finite (LV r2 s)" by fact+
  then have "finite S1" "finite S2" unfolding S1_def S2_def
    by (simp_all add: finite_Prefixes finite_Suffixes)
  moreover
  have "LV (SEQ r1 r2) s \<subseteq> f ` (S1 \<times> S2)"
    unfolding f_def S1_def S2_def 
    unfolding LV_def image_def prefix_def suffix_def
    apply (auto elim!: Prf_elims)
    by (metis (mono_tags, lifting) mem_Collect_eq)  
  ultimately 
  show "finite (LV (SEQ r1 r2) s)"
    by (simp add: finite_subset)
next
  case (STAR r s)
  then show "finite (LV (STAR r) s)" by (simp add: LV_STAR_finite)
next
  case (NTIMES r n s)
  have "\<And>s. finite (LV r s)" by fact
  then have "finite (Stars_Append (LV (STAR r) s) (\<Union>i\<le>n. LV (NTIMES r i) []))" 
    apply(rule_tac finite_Stars_Append)
     apply (simp add: LV_STAR_finite)
    using finite_NTimes_empty by blast
  then show "finite (LV (NTIMES r n) s)"
    by (metis LV_NTIMES_subset finite_subset)
next
  case (BACKREF4 r1 r2 r3 r4 cs s)
  have "finite ((\<lambda>(((v1, v2), v3), v4). Backref4 v1 v2 v3 v4 cs) `
      ((((\<Union>t \<in> Strings_le (length s). LV r1 t) \<times>
         (\<Union>t \<in> Strings_le (length s). LV r2 t)) \<times>
         (\<Union>t \<in> Strings_le (length s). LV r3 t)) \<times>
         (\<Union>t \<in> Strings_le (length s). LV r4 t)))"
    using BACKREF4.hyps
    by (intro finite_imageI finite_cartesian_product finite_LV_Union_Strings_le)
  then show "finite (LV (BACKREF4 r1 r2 r3 r4 cs) s)"
    by (rule finite_subset[OF LV_BACKREF4_subset])
next
  case (HALF r cs rep s)
  have "finite ((\<lambda>v. Half v cs rep) ` (\<Union>t \<in> Strings_le (length s). LV r t))"
    using HALF.hyps by (intro finite_imageI finite_LV_Union_Strings_le)
  then show "finite (LV (HALF r cs rep) s)"
    by (rule finite_subset[OF LV_HALF_subset])
next
  case (RESIDUE cs rep s)
  then show "finite (LV (RESIDUE cs rep) s)"
    unfolding LV_def
    by (rule finite_subset[of _ "{Residue cs rep}"]) (auto elim!: Prf_elims)
qed



section \<open>Our inductive POSIX Definition\<close>

definition
  BACKREF4_longest ::
    "rexp \<Rightarrow> rexp \<Rightarrow> rexp \<Rightarrow> rexp \<Rightarrow> string \<Rightarrow>
      string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool"
where
  "BACKREF4_longest r1 r2 r3 r4 cs s1 s2 s3 s4 \<equiv>
    (\<forall>t1 t2 t3 t4.
      t1 \<in> L r1 \<and> t2 \<in> L r2 \<and> t3 \<in> L r3 \<and> t4 \<in> L r4 \<and>
      s1 @ s2 @ s3 @ rev cs @ s2 @ s4 =
        t1 @ t2 @ t3 @ rev cs @ t2 @ t4
      \<longrightarrow>
        length t1 \<le> length s1 \<and>
        (length t1 = length s1 \<longrightarrow> length t2 \<le> length s2) \<and>
        (length t1 = length s1 \<and> length t2 = length s2
          \<longrightarrow> length t3 \<le> length s3))"

(* BACKREF-MIGRATION-COMPLETED (definition augmentation, ADMIN APPROVAL REQUIRED):
   Add original Posix rules for BACKREF4/HALF/RESIDUE. The BACKREF4 rule must
   settle the intended POSIX priority/greediness over s1, s2, s3, s4 before
   proof work starts. Do not use BPosix as a parallel specification. *)
inductive 
  Posix :: "string \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ \<in> _ \<rightarrow> _" [100, 100, 100] 100)
where
  Posix_ONE: "[] \<in> ONE \<rightarrow> Void"
| Posix_CH: "[c] \<in> (CH c) \<rightarrow> (Char c)"
| Posix_ALT1: "s \<in> r1 \<rightarrow> v \<Longrightarrow> s \<in> (ALT r1 r2) \<rightarrow> (Left v)"
| Posix_ALT2: "\<lbrakk>s \<in> r2 \<rightarrow> v; s \<notin> L(r1)\<rbrakk> \<Longrightarrow> s \<in> (ALT r1 r2) \<rightarrow> (Right v)"
| Posix_SEQ: "\<lbrakk>s1 \<in> r1 \<rightarrow> v1; s2 \<in> r2 \<rightarrow> v2;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r1 \<and> s\<^sub>4 \<in> L r2)\<rbrakk> \<Longrightarrow> 
    (s1 @ s2) \<in> (SEQ r1 r2) \<rightarrow> (Seq v1 v2)"
| Posix_STAR1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> STAR r \<rightarrow> Stars vs; flat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> STAR r \<rightarrow> Stars (v # vs)"
| Posix_STAR2: "[] \<in> STAR r \<rightarrow> Stars []"
| Posix_NTIMES1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> NTIMES r (n - 1) \<rightarrow> Stars vs; flat v \<noteq> []; 0 < n;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (NTIMES r (n - 1)))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> NTIMES r n \<rightarrow> Stars (v # vs)"
| Posix_NTIMES2: "\<lbrakk>\<forall>v \<in> set vs. [] \<in> r \<rightarrow> v; length vs = n\<rbrakk>
    \<Longrightarrow> [] \<in> NTIMES r n \<rightarrow> Stars vs"  
| Posix_BACKREF4:
    "\<lbrakk>s1 \<in> r1 \<rightarrow> v1; s2 \<in> r2 \<rightarrow> v2; s3 \<in> r3 \<rightarrow> v3; s4 \<in> r4 \<rightarrow> v4;
      BACKREF4_longest r1 r2 r3 r4 cs s1 s2 s3 s4\<rbrakk>
    \<Longrightarrow> (s1 @ s2 @ s3 @ rev cs @ s2 @ s4) \<in>
      BACKREF4 r1 r2 r3 r4 cs \<rightarrow> Backref4 v1 v2 v3 v4 cs"
| Posix_HALF:
    "s \<in> r \<rightarrow> v \<Longrightarrow> (s @ cs) \<in> HALF r cs rep \<rightarrow> Half v cs rep"
| Posix_RESIDUE:
    "cs \<in> RESIDUE cs rep \<rightarrow> Residue cs rep"



(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Add Posix elimination cases for BACKREF4/HALF/RESIDUE. *)
inductive_cases Posix_elims:
  "s \<in> ZERO \<rightarrow> v"
  "s \<in> ONE \<rightarrow> v"
  "s \<in> CH c \<rightarrow> v"
  "s \<in> ALT r1 r2 \<rightarrow> v"
  "s \<in> SEQ r1 r2 \<rightarrow> v"
  "s \<in> STAR r \<rightarrow> v"
  "s \<in> NTIMES r n \<rightarrow> v"
  "s \<in> BACKREF4 r1 r2 r3 r4 cs \<rightarrow> v"
  "s \<in> HALF r cs rep \<rightarrow> v"
  "s \<in> RESIDUE cs rep \<rightarrow> v"

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend this original Posix theorem with BACKREF4/HALF/RESIDUE cases. *)
lemma Posix1:
  assumes "s \<in> r \<rightarrow> v"
  shows "s \<in> L r" "flat v = s"
using assms
  apply(induct s r v rule: Posix.induct)
  apply(auto intro: backref_lang4I simp add: pow_empty_iff)
  apply (metis Suc_pred concI lang_pow.simps(2))
  apply (meson ex_in_conv set_empty)
  done



(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend this original Posix theorem with BACKREF4/HALF/RESIDUE cases. *)
lemma Posix1a:
  assumes "s \<in> r \<rightarrow> v"
  shows "\<Turnstile> v : r"
using assms
  apply(induct s r v rule: Posix.induct)
  apply(auto intro: Prf.intros)
  apply (metis Prf.intros(6) Prf_elims(6) set_ConsD val.inject(5))
  prefer 2
  apply (metis Posix1(2) Prf.intros(7) append_Nil empty_iff list.set(1))
  apply(erule Prf_elims)
  apply(auto)
  apply(subst append.simps(2)[symmetric])
  apply(rule Prf.intros)
  apply(auto)
  done


text \<open>
  For a give value and string, our Posix definition 
  determines a unique value.
\<close>

lemma List_eq_zipI:
  assumes "\<forall>(v1, v2) \<in> set (zip vs1 vs2). v1 = v2" 
  and "length vs1 = length vs2"
  shows "vs1 = vs2"  
 using assms
  apply(induct vs1 arbitrary: vs2)
   apply(case_tac vs2)
   apply(simp)    
   apply(simp)
   apply(case_tac vs2)
   apply(simp)
  apply(simp)
done 


lemma BACKREF4_longest_split_unique:
  assumes eq:
    "s1 @ s2 @ s3 @ rev cs @ s2 @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    and longest1: "BACKREF4_longest r1 r2 r3 r4 cs s1 s2 s3 s4"
    and longest2: "BACKREF4_longest r1 r2 r3 r4 cs t1 t2 t3 t4"
    and s_lang:
      "s1 \<in> L r1" "s2 \<in> L r2" "s3 \<in> L r3" "s4 \<in> L r4"
    and t_lang:
      "t1 \<in> L r1" "t2 \<in> L r2" "t3 \<in> L r3" "t4 \<in> L r4"
  shows "s1 = t1" "s2 = t2" "s3 = t3" "s4 = t4"
proof -
  have len1a: "length t1 \<le> length s1"
    using longest1 t_lang eq unfolding BACKREF4_longest_def by blast
  have len1b: "length s1 \<le> length t1"
    using longest2 s_lang eq[symmetric] unfolding BACKREF4_longest_def by blast
  have len1: "length s1 = length t1"
    using len1a len1b by simp
  have s1_t1: "s1 = t1"
  proof -
    have "take (length s1) (s1 @ s2 @ s3 @ rev cs @ s2 @ s4) =
      take (length s1) (t1 @ t2 @ t3 @ rev cs @ t2 @ t4)"
      using eq by simp
    then show ?thesis using len1 by simp
  qed
  have eq2: "s2 @ s3 @ rev cs @ s2 @ s4 = t2 @ t3 @ rev cs @ t2 @ t4"
    using eq s1_t1 by simp
  have len2a: "length t2 \<le> length s2"
    using longest1 t_lang eq len1[symmetric] unfolding BACKREF4_longest_def by blast
  have len2b: "length s2 \<le> length t2"
    using longest2 s_lang eq[symmetric] len1 unfolding BACKREF4_longest_def by blast
  have len2: "length s2 = length t2"
    using len2a len2b by simp
  have s2_t2: "s2 = t2"
  proof -
    have "take (length s2) (s2 @ s3 @ rev cs @ s2 @ s4) =
      take (length s2) (t2 @ t3 @ rev cs @ t2 @ t4)"
      using eq2 by simp
    then show ?thesis using len2 by simp
  qed
  have eq3: "s3 @ rev cs @ s2 @ s4 = t3 @ rev cs @ t2 @ t4"
    using eq2 s2_t2 by simp
  have len3a: "length t3 \<le> length s3"
    using longest1 t_lang eq len1[symmetric] len2[symmetric]
    unfolding BACKREF4_longest_def by blast
  have len3b: "length s3 \<le> length t3"
    using longest2 s_lang eq[symmetric] len1 len2 unfolding BACKREF4_longest_def by blast
  have len3: "length s3 = length t3"
    using len3a len3b by simp
  have s3_t3: "s3 = t3"
  proof -
    have "take (length s3) (s3 @ rev cs @ s2 @ s4) =
      take (length s3) (t3 @ rev cs @ t2 @ t4)"
      using eq3 by simp
    then show ?thesis using len3 by simp
  qed
  have s4_t4: "s4 = t4"
    using eq3 s2_t2 s3_t3 by simp
  show "s1 = t1" by (rule s1_t1)
  show "s2 = t2" by (rule s2_t2)
  show "s3 = t3" by (rule s3_t3)
  show "s4 = t4" by (rule s4_t4)
qed


(*
lemma List_eq_zipI:
  assumes "list_all2 (\<lambda>v1 v2. v1 = v2) vs1 vs2" 
  and "length vs1 = length vs2"
  shows "vs1 = vs2"  
 using assms
  apply(induct vs1 vs2 rule: list_all2_induct)
  apply(auto)
  done 
*)

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension, ADMIN APPROVAL REQUIRED):
   Extend determinism with BACKREF4/HALF/RESIDUE cases only after the BACKREF4
   POSIX priority rule is approved. Add direct split-uniqueness lemmas here;
   do not rely on BPosix wrapper determinism. *)
lemma Posix_determ:
  assumes "s \<in> r \<rightarrow> v1" "s \<in> r \<rightarrow> v2"
  shows "v1 = v2"
using assms
proof (induct s r v1 arbitrary: v2 rule: Posix.induct)
  case (Posix_ONE v2)
  have "[] \<in> ONE \<rightarrow> v2" by fact
  then show "Void = v2" by cases auto
next 
  case (Posix_CH c v2)
  have "[c] \<in> CH c \<rightarrow> v2" by fact
  then show "Char c = v2" by cases auto
next 
  case (Posix_ALT1 s r1 v r2 v2)
  have "s \<in> ALT r1 r2 \<rightarrow> v2" by fact
  moreover
  have "s \<in> r1 \<rightarrow> v" by fact
  then have "s \<in> L r1" by (simp add: Posix1)
  ultimately obtain v' where eq: "v2 = Left v'" "s \<in> r1 \<rightarrow> v'" by cases auto 
  moreover
  have IH: "\<And>v2. s \<in> r1 \<rightarrow> v2 \<Longrightarrow> v = v2" by fact
  ultimately have "v = v'" by simp
  then show "Left v = v2" using eq by simp
next 
  case (Posix_ALT2 s r2 v r1 v2)
  have "s \<in> ALT r1 r2 \<rightarrow> v2" by fact
  moreover
  have "s \<notin> L r1" by fact
  ultimately obtain v' where eq: "v2 = Right v'" "s \<in> r2 \<rightarrow> v'" 
    by cases (auto simp add: Posix1) 
  moreover
  have IH: "\<And>v2. s \<in> r2 \<rightarrow> v2 \<Longrightarrow> v = v2" by fact
  ultimately have "v = v'" by simp
  then show "Right v = v2" using eq by simp
next
  case (Posix_SEQ s1 r1 v1 s2 r2 v2 v')
  have "(s1 @ s2) \<in> SEQ r1 r2 \<rightarrow> v'" 
       "s1 \<in> r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by fact+
  then obtain v1' v2' where "v' = Seq v1' v2'" "s1 \<in> r1 \<rightarrow> v1'" "s2 \<in> r2 \<rightarrow> v2'"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
  using Posix1(1) by fastforce+
  moreover
  have IHs: "\<And>v1'. s1 \<in> r1 \<rightarrow> v1' \<Longrightarrow> v1 = v1'"
            "\<And>v2'. s2 \<in> r2 \<rightarrow> v2' \<Longrightarrow> v2 = v2'" by fact+
  ultimately show "Seq v1 v2 = v'" by simp
next
  case (Posix_STAR1 s1 r v s2 vs v2)
  have "(s1 @ s2) \<in> STAR r \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> STAR r \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (STAR r) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
  using Posix1(1) apply fastforce
  apply (metis Posix1(1) Posix_STAR1.hyps(6) append_Nil append_Nil2)
  using Posix1(2) by blast
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> STAR r \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto
next
  case (Posix_STAR2 r v2)
  have "[] \<in> STAR r \<rightarrow> v2" by fact
  then show "Stars [] = v2" by cases (auto simp add: Posix1)
next
  case (Posix_NTIMES2 vs r n v2)
  then show "Stars vs = v2"
    apply(erule_tac Posix_elims)
    apply(auto)
    apply (simp add: Posix1(2))  
    apply(rule List_eq_zipI)
     apply(auto simp add: list_all2_iff)
    by (meson in_set_zipE)
next
  case (Posix_NTIMES1 s1 r v s2 n vs)
  have "(s1 @ s2) \<in> NTIMES r n \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> NTIMES r (n - 1) \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (NTIMES r (n - 1 )))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (NTIMES r (n - 1)) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(1) apply fastforce
    apply (metis One_nat_def Posix1(1) Posix_NTIMES1.hyps(7) append.right_neutral append_self_conv2)
  using Posix1(2) by blast
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> NTIMES r (n - 1) \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto 
next
  case (Posix_BACKREF4 s1 r1 v1 s2 r2 v2 s3 r3 v3 s4 r4 v4 cs v')
  have target:
    "(s1 @ s2 @ s3 @ rev cs @ s2 @ s4) \<in>
      BACKREF4 r1 r2 r3 r4 cs \<rightarrow> v'" by fact
  have left1: "s1 \<in> r1 \<rightarrow> v1" by fact
  have left2: "s2 \<in> r2 \<rightarrow> v2" by fact
  have left3: "s3 \<in> r3 \<rightarrow> v3" by fact
  have left4: "s4 \<in> r4 \<rightarrow> v4" by fact
  have longest: "BACKREF4_longest r1 r2 r3 r4 cs s1 s2 s3 s4" by fact
  from target obtain t1 t2 t3 t4 w1 w2 w3 w4 where decomp:
    "v' = Backref4 w1 w2 w3 w4 cs"
    "t1 \<in> r1 \<rightarrow> w1" "t2 \<in> r2 \<rightarrow> w2"
    "t3 \<in> r3 \<rightarrow> w3" "t4 \<in> r4 \<rightarrow> w4"
    "s1 @ s2 @ s3 @ rev cs @ s2 @ s4 =
      t1 @ t2 @ t3 @ rev cs @ t2 @ t4"
    "BACKREF4_longest r1 r2 r3 r4 cs t1 t2 t3 t4"
    by (auto elim!: Posix_elims(8))
  have split: "s1 = t1" "s2 = t2" "s3 = t3" "s4 = t4"
    using BACKREF4_longest_split_unique[OF decomp(6) longest decomp(7)
        Posix1(1)[OF left1] Posix1(1)[OF left2]
        Posix1(1)[OF left3] Posix1(1)[OF left4]
        Posix1(1)[OF decomp(2)] Posix1(1)[OF decomp(3)]
        Posix1(1)[OF decomp(4)] Posix1(1)[OF decomp(5)]]
    by simp_all
  have IH1: "\<And>w. s1 \<in> r1 \<rightarrow> w \<Longrightarrow> v1 = w" by fact
  have IH2: "\<And>w. s2 \<in> r2 \<rightarrow> w \<Longrightarrow> v2 = w" by fact
  have IH3: "\<And>w. s3 \<in> r3 \<rightarrow> w \<Longrightarrow> v3 = w" by fact
  have IH4: "\<And>w. s4 \<in> r4 \<rightarrow> w \<Longrightarrow> v4 = w" by fact
  have "v1 = w1" using IH1 decomp(2) split(1) by simp
  moreover have "v2 = w2" using IH2 decomp(3) split(2) by simp
  moreover have "v3 = w3" using IH3 decomp(4) split(3) by simp
  moreover have "v4 = w4" using IH4 decomp(5) split(4) by simp
  ultimately show "Backref4 v1 v2 v3 v4 cs = v'"
    using decomp(1) by simp
next
  case (Posix_HALF s r v cs rep v2)
  have target: "(s @ cs) \<in> HALF r cs rep \<rightarrow> v2" by fact
  have first: "s \<in> r \<rightarrow> v" by fact
  from target obtain t w where decomp:
    "v2 = Half w cs rep" "t \<in> r \<rightarrow> w" "s @ cs = t @ cs"
    by (auto elim!: Posix_elims(9))
  have "s = t" using decomp(3) by simp
  moreover have IH: "\<And>w. s \<in> r \<rightarrow> w \<Longrightarrow> v = w" by fact
  ultimately have "v = w" using IH decomp(2) by simp
  then show "Half v cs rep = v2" using decomp(1) by simp
next
  case (Posix_RESIDUE cs rep v2)
  then show "Residue cs rep = v2"
    by (auto elim!: Posix_elims(10))
qed


text \<open>
  Our POSIX values are lexical values.
\<close>

(* BACKREF-MIGRATION-COMPLETED (proof constructor-case extension):
   Extend this original Posix theorem with BACKREF4/HALF/RESIDUE cases. *)
lemma Posix_LV:
  assumes "s \<in> r \<rightarrow> v"
  shows "v \<in> LV r s"
  using assms Posix1(2) Posix1a unfolding LV_def by blast

end
