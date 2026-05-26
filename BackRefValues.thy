theory BackRefValues
  imports BackRefLang
begin

section \<open>Backreference Pilot Values\<close>

datatype bval =
  BVoid
| BChar char
| BSeq bval bval
| BLeft bval
| BRight bval
| BStars "bval list"
| BBackref bval bval string
| BHalf bval string string
| BResidue string string

fun bflat :: "bval \<Rightarrow> string"
where
  "bflat BVoid = []"
| "bflat (BChar c) = [c]"
| "bflat (BSeq v1 v2) = bflat v1 @ bflat v2"
| "bflat (BLeft v) = bflat v"
| "bflat (BRight v) = bflat v"
| "bflat (BStars []) = []"
| "bflat (BStars (v # vs)) = bflat v @ bflat (BStars vs)"
| "bflat (BBackref v1 v2 cs) = bflat v1 @ bflat v2 @ rev cs @ bflat v1"
| "bflat (BHalf v cs rep) = bflat v @ cs"
| "bflat (BResidue cs rep) = cs"

abbreviation bflats :: "bval list \<Rightarrow> string"
where
  "bflats vs \<equiv> concat (map bflat vs)"

lemma bflat_BStars [simp]:
  "bflat (BStars vs) = bflats vs"
  by (induct vs) auto

section \<open>Backreference Lexical Values\<close>

inductive BPrf :: "bval \<Rightarrow> brexp \<Rightarrow> bool" ("\<Turnstile>b _ : _" [100, 100] 100)
where
  "\<lbrakk>\<Turnstile>b v1 : r1; \<Turnstile>b v2 : r2\<rbrakk> \<Longrightarrow> \<Turnstile>b BSeq v1 v2 : BSEQ r1 r2"
| "\<Turnstile>b v1 : r1 \<Longrightarrow> \<Turnstile>b BLeft v1 : BALT r1 r2"
| "\<Turnstile>b v2 : r2 \<Longrightarrow> \<Turnstile>b BRight v2 : BALT r1 r2"
| "\<Turnstile>b BVoid : BONE"
| "\<Turnstile>b BChar c : BCH c"
| "\<forall>v \<in> set vs. \<Turnstile>b v : r \<and> bflat v \<noteq> [] \<Longrightarrow> \<Turnstile>b BStars vs : BSTAR r"
| "\<lbrakk>\<forall>v \<in> set vs1. \<Turnstile>b v : r \<and> bflat v \<noteq> [];
    \<forall>v \<in> set vs2. \<Turnstile>b v : r \<and> bflat v = [];
    length (vs1 @ vs2) = n\<rbrakk> \<Longrightarrow> \<Turnstile>b BStars (vs1 @ vs2) : BNTIMES r n"
| "\<lbrakk>\<Turnstile>b v1 : r; \<Turnstile>b v2 : mid\<rbrakk> \<Longrightarrow> \<Turnstile>b BBackref v1 v2 cs : BBACKREF r mid cs"
| "\<Turnstile>b v : mid \<Longrightarrow> \<Turnstile>b BHalf v cs rep : BHALF mid cs rep"
| "\<Turnstile>b BResidue cs rep : BRESIDUE cs rep"

inductive_cases BPrf_elims:
  "\<Turnstile>b v : BZERO"
  "\<Turnstile>b v : BSEQ r1 r2"
  "\<Turnstile>b v : BALT r1 r2"
  "\<Turnstile>b v : BONE"
  "\<Turnstile>b v : BCH c"
  "\<Turnstile>b v : BSTAR r"
  "\<Turnstile>b v : BNTIMES r n"
  "\<Turnstile>b v : BBACKREF r mid cs"
  "\<Turnstile>b v : BHALF mid cs rep"
  "\<Turnstile>b v : BRESIDUE cs rep"

lemma bpow_BPrf:
  assumes "\<forall>v \<in> set vs. \<Turnstile>b v : r \<and> bflat v \<in> A"
  shows "bflats vs \<in> A ^^ length vs"
  using assms
  by (induct vs) auto

lemma BL_flat_BPrf1:
  assumes "\<Turnstile>b v : r"
  shows "bflat v \<in> BL r"
  using assms
  apply (induct v r rule: BPrf.induct)
           apply (auto simp add: Sequ_def Star_concat lang_pow_add backref_lang_def)
  apply (metis bpow_BPrf)
  done

lemma bPow_cstring:
  fixes A :: "string set"
  assumes "s \<in> A ^^ n"
  shows "\<exists>ss1 ss2. concat (ss1 @ ss2) = s \<and> length (ss1 @ ss2) = n \<and>
         (\<forall>s \<in> set ss1. s \<in> A \<and> s \<noteq> []) \<and> (\<forall>s \<in> set ss2. s \<in> A \<and> s = [])"
  using assms
  apply (induct n arbitrary: s)
   apply auto
  apply (auto simp add: Sequ_def)
  apply (drule_tac x = s2 in meta_spec)
  apply simp
  apply (erule exE)+
  apply clarify
  apply (case_tac "s1 = []")
   apply simp
   apply (rule_tac x = ss1 in exI)
   apply (rule_tac x = "s1 # ss2" in exI)
   apply simp
  apply (rule_tac x = "s1 # ss1" in exI)
  apply (rule_tac x = ss2 in exI)
  apply simp
  done

lemma bflats_BPrf_value:
  assumes "\<forall>s \<in> set ss. \<exists>v. s = bflat v \<and> \<Turnstile>b v : r"
  shows "\<exists>vs. bflats vs = concat ss \<and> (\<forall>v \<in> set vs. \<Turnstile>b v : r \<and> bflat v \<noteq> [])"
  using assms
  apply (induct ss)
   apply auto
   apply (rule_tac x = "[]" in exI)
   apply simp
  apply (case_tac "bflat v = []")
   apply (rule_tac x = vs in exI)
   apply simp
  apply (rule_tac x = "v # vs" in exI)
  apply simp
  done

lemma bflat_empty_concat:
  assumes "\<forall>s \<in> set ss. s = []"
  shows "concat ss = []"
  using assms
  by (induct ss) auto

lemma bflats_cval:
  assumes "\<forall>s \<in> set ss. \<exists>v. s = bflat v \<and> \<Turnstile>b v : r"
  shows "\<exists>vs1 vs2. bflats (vs1 @ vs2) = concat ss \<and> length (vs1 @ vs2) = length ss \<and>
          (\<forall>v \<in> set vs1. \<Turnstile>b v : r \<and> bflat v \<noteq> []) \<and>
          (\<forall>v \<in> set vs2. \<Turnstile>b v : r \<and> bflat v = [])"
  using assms
  apply (induct ss rule: rev_induct)
   apply (rule_tac x = "[]" in exI)+
   apply simp
  apply simp
  apply clarify
  apply (case_tac "bflat v = []")
   apply (rule_tac x = vs1 in exI)
   apply (rule_tac x = "v # vs2" in exI)
   apply simp
  apply (rule_tac x = "vs1 @ [v]" in exI)
  apply (rule_tac x = vs2 in exI)
  apply simp
  apply (simp add: bflat_empty_concat)
  done

lemma BL_flat_BPrf2:
  assumes "s \<in> BL r"
  shows "\<exists>v. \<Turnstile>b v : r \<and> bflat v = s"
  using assms
proof (induct r arbitrary: s)
  case (BSTAR r s)
  have IH: "\<And>s. s \<in> BL r \<Longrightarrow> \<exists>v. \<Turnstile>b v : r \<and> bflat v = s" by fact
  have "s \<in> BL (BSTAR r)" by fact
  then obtain ss where "concat ss = s" "\<forall>s \<in> set ss. s \<in> BL r \<and> s \<noteq> []"
    using Star_split by auto
  then obtain vs where "bflats vs = s" "\<forall>v \<in> set vs. \<Turnstile>b v : r \<and> bflat v \<noteq> []"
    using IH bflats_BPrf_value by metis
  then show "\<exists>v. \<Turnstile>b v : BSTAR r \<and> bflat v = s"
    using BPrf.intros(6) bflat_BStars by blast
next
  case (BSEQ r1 r2 s)
  then show "\<exists>v. \<Turnstile>b v : BSEQ r1 r2 \<and> bflat v = s"
    unfolding Sequ_def BL.simps by (fastforce intro: BPrf.intros)
next
  case (BALT r1 r2 s)
  then show "\<exists>v. \<Turnstile>b v : BALT r1 r2 \<and> bflat v = s"
    unfolding BL.simps by (fastforce intro: BPrf.intros)
next
  case (BNTIMES r n)
  have IH: "\<And>s. s \<in> BL r \<Longrightarrow> \<exists>v. \<Turnstile>b v : r \<and> bflat v = s" by fact
  have "s \<in> BL (BNTIMES r n)" by fact
  then obtain ss1 ss2 where ss:
    "concat (ss1 @ ss2) = s" "length (ss1 @ ss2) = n"
    "\<forall>s \<in> set ss1. s \<in> BL r \<and> s \<noteq> []" "\<forall>s \<in> set ss2. s \<in> BL r \<and> s = []"
    using bPow_cstring by force
  then obtain vs1 vs2 where
    "bflats (vs1 @ vs2) = s" "length (vs1 @ vs2) = n"
    "\<forall>v \<in> set vs1. \<Turnstile>b v : r \<and> bflat v \<noteq> []"
    "\<forall>v \<in> set vs2. \<Turnstile>b v : r \<and> bflat v = []"
    using IH bflats_cval
    apply -
    apply (drule_tac x = "ss1 @ ss2" in meta_spec)
    apply (drule_tac x = r in meta_spec)
    apply (drule meta_mp)
     apply simp
     apply (metis Un_iff)
    apply clarify
    apply (drule_tac x = vs1 in meta_spec)
    apply (drule_tac x = vs2 in meta_spec)
    apply simp
    done
  then show "\<exists>v. \<Turnstile>b v : BNTIMES r n \<and> bflat v = s"
    using BPrf.intros(7) bflat_BStars by blast
next
  case (BBACKREF r mid cs s)
  then obtain x y where xy:
    "x \<in> BL r" "y \<in> BL mid" "s = x @ y @ rev cs @ x"
    by (auto simp add: backref_lang_def)
  then obtain vx where vx: "\<Turnstile>b vx : r" "bflat vx = x"
    using BBACKREF.hyps(1) by blast
  from xy obtain vy where vy: "\<Turnstile>b vy : mid" "bflat vy = y"
    using BBACKREF.hyps(2) by blast
  show "\<exists>v. \<Turnstile>b v : BBACKREF r mid cs \<and> bflat v = s"
    using xy vx vy by (intro exI[of _ "BBackref vx vy cs"]) (auto intro: BPrf.intros)
next
  case (BHALF mid cs rep s)
  then obtain x where x: "x \<in> BL mid" "s = x @ cs"
    by (auto simp add: Sequ_def)
  then obtain v where v: "\<Turnstile>b v : mid" "bflat v = x"
    using BHALF.hyps by blast
  show "\<exists>v. \<Turnstile>b v : BHALF mid cs rep \<and> bflat v = s"
    using x v by (intro exI[of _ "BHalf v cs rep"]) (auto intro: BPrf.intros)
qed (auto intro: BPrf.intros)

lemma BL_flat_BPrf:
  "BL r = {bflat v | v. \<Turnstile>b v : r}"
  using BL_flat_BPrf1 BL_flat_BPrf2 by blast

section \<open>Nullable Value Construction\<close>

fun bmkeps :: "brexp \<Rightarrow> bval"
where
  "bmkeps BZERO = BVoid"
| "bmkeps BONE = BVoid"
| "bmkeps (BCH c) = BChar c"
| "bmkeps (BSEQ r1 r2) = BSeq (bmkeps r1) (bmkeps r2)"
| "bmkeps (BALT r1 r2) =
     (if xnullable r1 then BLeft (bmkeps r1) else BRight (bmkeps r2))"
| "bmkeps (BSTAR r) = BStars []"
| "bmkeps (BNTIMES r n) = BStars (replicate n (bmkeps r))"
| "bmkeps (BBACKREF r mid cs) = BBackref (bmkeps r) (bmkeps mid) cs"
| "bmkeps (BHALF mid cs rep) = BHalf (bmkeps mid) cs rep"
| "bmkeps (BRESIDUE cs rep) = BResidue cs rep"

lemma bflat_BStars_replicate_empty:
  assumes "bflat v = []"
  shows "bflat (BStars (replicate n v)) = []"
  using assms
  by (induct n) auto

lemma bmkeps_flat:
  assumes "xnullable r"
  shows "bflat (bmkeps r) = []"
  using assms
  apply (induct r)
           apply (auto simp add: bflat_BStars_replicate_empty split: if_splits)
  done

lemma BPrf_BStars_empty_replicate:
  assumes "\<Turnstile>b v : r" "bflat v = []"
  shows "\<Turnstile>b BStars (replicate n v) : BNTIMES r n"
proof -
  have p1: "\<forall>v' \<in> set ([] :: bval list). \<Turnstile>b v' : r \<and> bflat v' \<noteq> []"
    by simp
  have p2: "\<forall>v' \<in> set (replicate n v). \<Turnstile>b v' : r \<and> bflat v' = []"
    using assms by auto
  have p3: "length ([] @ replicate n v) = n"
    by simp
  from p1 p2 p3 have "\<Turnstile>b BStars ([] @ replicate n v) : BNTIMES r n"
    by (rule BPrf.intros(7))
  then show ?thesis by simp
qed

lemma BPrf_BStars_NTIMES_zero:
  "\<Turnstile>b BStars [] : BNTIMES r 0"
proof -
  have p1: "\<forall>v' \<in> set ([] :: bval list). \<Turnstile>b v' : r \<and> bflat v' \<noteq> []"
    by simp
  have p2: "\<forall>v' \<in> set ([] :: bval list). \<Turnstile>b v' : r \<and> bflat v' = []"
    by simp
  have p3: "length ([] @ ([] :: bval list)) = 0"
    by simp
  from p1 p2 p3 have "\<Turnstile>b BStars ([] @ []) : BNTIMES r 0"
    by (rule BPrf.intros(7))
  then show ?thesis by simp
qed

lemma bmkeps_BPrf:
  assumes "xnullable r"
  shows "\<Turnstile>b bmkeps r : r"
  using assms
  apply (induct r)
           apply (auto intro!: BPrf.intros BPrf_BStars_empty_replicate BPrf_BStars_NTIMES_zero
                  simp add: bmkeps_flat split: if_splits)
  done

section \<open>Injection Value\<close>

fun (sequential) binjval :: "brexp \<Rightarrow> char \<Rightarrow> bval \<Rightarrow> bval"
where
  "binjval (BCH d) c BVoid = BChar d"
| "binjval (BALT r1 r2) c (BLeft v) = BLeft (binjval r1 c v)"
| "binjval (BALT r1 r2) c (BRight v) = BRight (binjval r2 c v)"
| "binjval (BSEQ r1 r2) c (BLeft (BSeq v1 v2)) = BSeq (binjval r1 c v1) v2"
| "binjval (BSEQ r1 r2) c (BRight v) = BSeq (bmkeps r1) (binjval r2 c v)"
| "binjval (BSEQ r1 r2) c (BSeq v1 v2) = BSeq (binjval r1 c v1) v2"
| "binjval (BSTAR r) c (BSeq v (BStars vs)) = BStars (binjval r c v # vs)"
| "binjval (BNTIMES r n) c (BSeq v (BStars vs)) = BStars (binjval r c v # vs)"
| "binjval (BBACKREF r mid cs) c (BLeft (BBackref v1 v2 cs')) =
     BBackref (binjval r c v1) v2 cs"
| "binjval (BBACKREF r mid cs) c (BRight (BLeft (BHalf v cs' rep))) =
     BBackref (bmkeps r) (binjval mid c v) cs"
| "binjval (BBACKREF r mid cs) c (BRight (BRight v)) =
     BBackref (bmkeps r) (bmkeps mid) cs"
| "binjval (BBACKREF r mid cs) c (BRight (BHalf v cs' rep)) =
     BBackref (bmkeps r) (binjval mid c v) cs"
| "binjval (BBACKREF r mid cs) c (BBackref v1 v2 cs') =
     BBackref (binjval r c v1) v2 cs"
| "binjval (BHALF mid cs rep) c (BLeft (BHalf v cs' rep')) =
     BHalf (binjval mid c v) cs rep"
| "binjval (BHALF mid cs rep) c (BRight v) =
     BHalf (bmkeps mid) cs rep"
| "binjval (BHALF mid cs rep) c (BHalf v cs' rep') =
     BHalf (binjval mid c v) cs rep"
| "binjval (BRESIDUE cs rep) c v = BResidue cs rep"
| "binjval _ _ _ = BVoid"

section \<open>Injection Value Correctness\<close>

lemma BPrf_xder_residue:
  assumes "\<Turnstile>b v : xder_residue c cs rep"
  shows "\<exists>ds. cs = c # ds \<and> v = BResidue ds rep"
  using assms
  by (cases cs) (auto elim: BPrf_elims split: if_splits)

lemma binjval_flat:
  assumes "\<Turnstile>b v : xder c r"
  shows "bflat (binjval r c v) = c # bflat v"
  using assms
  apply (induct r arbitrary: c v)
           apply (auto elim!: BPrf_elims dest: BPrf_xder_residue
                  simp add: bmkeps_flat split: if_splits)
  done

lemma BPrf_BNTIMES_prepend:
  assumes "\<Turnstile>b v : r" "bflat v \<noteq> []"
          "\<forall>w \<in> set ws1. \<Turnstile>b w : r \<and> bflat w \<noteq> []"
          "\<forall>w \<in> set ws2. \<Turnstile>b w : r \<and> bflat w = []"
          "n > 0"
          "length ws1 + length ws2 = n - Suc 0"
  shows "\<Turnstile>b BStars (v # ws1 @ ws2) : BNTIMES r n"
proof -
  have p1: "\<forall>w \<in> set (v # ws1). \<Turnstile>b w : r \<and> bflat w \<noteq> []"
    using assms(1-3) by auto
  have p2: "length ((v # ws1) @ ws2) = n"
    using assms(5,6) by auto
  have "\<Turnstile>b BStars ((v # ws1) @ ws2) : BNTIMES r n"
    using p1 assms(4) p2 by (rule BPrf.intros(7))
  then show ?thesis by simp
qed

lemma binjval_BPrf:
  assumes "\<Turnstile>b v : xder c r"
  shows "\<Turnstile>b binjval r c v : r"
  using assms
  apply (induct r arbitrary: c v)
           apply (auto intro!: BPrf.intros BPrf_BNTIMES_prepend bmkeps_BPrf
                  elim!: BPrf_elims dest: BPrf_xder_residue
                  simp add: binjval_flat bmkeps_flat split: if_splits)
  done

section \<open>Backreference Pilot Lexer\<close>

fun blexer :: "brexp \<Rightarrow> string \<Rightarrow> bval option"
where
  "blexer r [] = (if xnullable r then Some (bmkeps r) else None)"
| "blexer r (c # s) = (case blexer (xder c r) s of
    None \<Rightarrow> None
  | Some v \<Rightarrow> Some (binjval r c v))"

lemma blexer_BPrf:
  assumes "blexer r s = Some v"
  shows "\<Turnstile>b v : r"
  using assms
  apply (induct s arbitrary: r v)
   apply (auto intro: bmkeps_BPrf binjval_BPrf split: if_splits option.splits)
  done

lemma blexer_flat:
  assumes "blexer r s = Some v"
  shows "bflat v = s"
  using assms
proof (induct s arbitrary: r v)
  case Nil
  then show ?case by (simp add: bmkeps_flat split: if_splits)
next
  case (Cons c s)
  then obtain v' where v': "blexer (xder c r) s = Some v'" "v = binjval r c v'"
    by (auto split: option.splits)
  from v'(1) have "bflat v' = s" by (rule Cons.hyps)
  moreover from v'(1) have "\<Turnstile>b v' : xder c r" by (rule blexer_BPrf)
  ultimately show ?case using v'(2) by (simp add: binjval_flat)
qed

lemma blexer_correct_None:
  "s \<notin> BL r \<longleftrightarrow> blexer r s = None"
  apply (induct s arbitrary: r)
   apply (simp add: xnullable_correctness)
  apply (auto simp add: xder_correctness Der_def split: option.splits)
  done

lemma blexer_correct_Some:
  "s \<in> BL r \<longleftrightarrow> (\<exists>v. blexer r s = Some v \<and> \<Turnstile>b v : r \<and> bflat v = s)"
proof
  assume "s \<in> BL r"
  then have "blexer r s \<noteq> None" using blexer_correct_None by auto
  then obtain v where "blexer r s = Some v" by blast
  then show "\<exists>v. blexer r s = Some v \<and> \<Turnstile>b v : r \<and> bflat v = s"
    using blexer_BPrf blexer_flat by blast
next
  assume "\<exists>v. blexer r s = Some v \<and> \<Turnstile>b v : r \<and> bflat v = s"
  then show "s \<in> BL r" using blexer_correct_None by auto
qed

section \<open>POSIX Specification for Backreference Regex\<close>

inductive 
  BPosix :: "string \<Rightarrow> brexp \<Rightarrow> bval \<Rightarrow> bool" ("_ \<in> _ \<rightarrow> _" [100, 100, 100] 100)
where
  BPosix_BONE: "[] \<in> BONE \<rightarrow> BVoid"
| BPosix_BCH: "[c] \<in> (BCH c) \<rightarrow> (BChar c)"
| BPosix_BALT1: "s \<in> r1 \<rightarrow> v \<Longrightarrow> s \<in> (BALT r1 r2) \<rightarrow> (BLeft v)"
| BPosix_BALT2: "\<lbrakk>s \<in> r2 \<rightarrow> v; s \<notin> BL r1\<rbrakk> \<Longrightarrow> s \<in> (BALT r1 r2) \<rightarrow> (BRight v)"
| BPosix_BSEQ: "\<lbrakk>s1 \<in> r1 \<rightarrow> v1; s2 \<in> r2 \<rightarrow> v2;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2)\<rbrakk> \<Longrightarrow> 
    (s1 @ s2) \<in> (BSEQ r1 r2) \<rightarrow> (BSeq v1 v2)"
| BPosix_BSTAR1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> BSTAR r \<rightarrow> BStars vs; bflat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL (BSTAR r))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> BSTAR r \<rightarrow> BStars (v # vs)"
| BPosix_BSTAR2: "[] \<in> BSTAR r \<rightarrow> BStars []"
| BPosix_BNTIMES1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> BNTIMES r (n - 1) \<rightarrow> BStars vs; bflat v \<noteq> []; 0 < n;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL (BNTIMES r (n - 1)))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> BNTIMES r n \<rightarrow> BStars (v # vs)"
| BPosix_BNTIMES2: "\<lbrakk>\<forall>v \<in> set vs. [] \<in> r \<rightarrow> v; length vs = n\<rbrakk>
    \<Longrightarrow> [] \<in> BNTIMES r n \<rightarrow> BStars vs"
| BPosix_BBACKREF: "\<lbrakk>s1 \<in> r \<rightarrow> v1; s2 \<in> mid \<rightarrow> v2;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (s1 @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL mid \<and>
      s2 @ rev cs @ s1 = s\<^sub>3 @ s\<^sub>4 @ rev cs @ (s1 @ s\<^sub>3))\<rbrakk>
    \<Longrightarrow> (s1 @ s2 @ rev cs @ s1) \<in> BBACKREF r mid cs \<rightarrow> BBackref v1 v2 cs"
| BPosix_BHALF: "s \<in> mid \<rightarrow> v
    \<Longrightarrow> (s @ cs) \<in> BHALF mid cs rep \<rightarrow> BHalf v cs rep"
| BPosix_BRESIDUE: "cs \<in> BRESIDUE cs rep \<rightarrow> BResidue cs rep"

inductive_cases BPosix_elims:
  "s \<in> BZERO \<rightarrow> v"
  "s \<in> BONE \<rightarrow> v"
  "s \<in> BCH c \<rightarrow> v"
  "s \<in> BALT r1 r2 \<rightarrow> v"
  "s \<in> BSEQ r1 r2 \<rightarrow> v"
  "s \<in> BSTAR r \<rightarrow> v"
  "s \<in> BNTIMES r n \<rightarrow> v"
  "s \<in> BBACKREF r mid cs \<rightarrow> v"
  "s \<in> BHALF mid cs rep \<rightarrow> v"
  "s \<in> BRESIDUE cs rep \<rightarrow> v"

lemma BPosix1:
  assumes "s \<in> r \<rightarrow> v"
  shows "s \<in> BL r" "bflat v = s"
  using assms
  apply(induct s r v rule: BPosix.induct)
                apply(auto simp add: pow_empty_iff backref_lang_def Sequ_def)
  apply (metis Suc_pred concI lang_pow.simps(2))
  apply (meson ex_in_conv set_empty)
  done

lemma BPosix1a:
  assumes "s \<in> r \<rightarrow> v"
  shows "\<Turnstile>b v : r"
  using assms
  apply(induct s r v rule: BPosix.induct)
             apply(auto intro: BPrf.intros)
  apply (metis BPrf.intros(6) BPrf_elims(6) set_ConsD bval.inject(5))
  prefer 2
  apply (metis BPosix1(2) BPrf.intros(7) append_Nil empty_iff list.set(1))
  apply(erule BPrf_elims)
  apply(auto)
  apply(subst append.simps(2)[symmetric])
  apply(rule BPrf.intros)
    apply(auto)
  done

lemma BPosix_bmkeps:
  assumes "xnullable r"
  shows "[] \<in> r \<rightarrow> bmkeps r"
  using assms
  apply(induct r)
           apply(auto intro: BPosix.intros simp add: xnullable_correctness split: if_splits)
  apply(subst append.simps(1)[symmetric])
  apply(rule BPosix_BSEQ)
    apply(auto)
  apply(simp add: BPosix_BNTIMES2)
  apply(subst append.simps(1)[symmetric])
  apply(subst append.simps(1)[symmetric])
  apply(rule BPosix_BBACKREF)
    apply(auto)
  apply(subst append.simps(1)[symmetric])
  apply(rule BPosix_BHALF)
  apply(auto)
  done

end
