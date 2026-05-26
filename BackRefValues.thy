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

primrec binjval :: "brexp \<Rightarrow> char \<Rightarrow> bval \<Rightarrow> bval"
where
  "binjval BZERO c v = BVoid"
| "binjval BONE c v = BVoid"
| "binjval (BCH d) c v =
     (case v of BVoid \<Rightarrow> BChar d | _ \<Rightarrow> BVoid)"
| "binjval (BSEQ r1 r2) c v =
     (case v of
        BLeft (BSeq v1 v2) \<Rightarrow> BSeq (binjval r1 c v1) v2
      | BRight v' \<Rightarrow> BSeq (bmkeps r1) (binjval r2 c v')
      | BSeq v1 v2 \<Rightarrow> BSeq (binjval r1 c v1) v2
      | _ \<Rightarrow> BVoid)"
| "binjval (BALT r1 r2) c v =
     (case v of
        BLeft v' \<Rightarrow> BLeft (binjval r1 c v')
      | BRight v' \<Rightarrow> BRight (binjval r2 c v')
      | _ \<Rightarrow> BVoid)"
| "binjval (BSTAR r) c v =
     (case v of
        BSeq v' (BStars vs) \<Rightarrow> BStars (binjval r c v' # vs)
      | _ \<Rightarrow> BVoid)"
| "binjval (BNTIMES r n) c v =
     (case v of
        BSeq v' (BStars vs) \<Rightarrow> BStars (binjval r c v' # vs)
      | _ \<Rightarrow> BVoid)"
| "binjval (BBACKREF r mid cs) c v =
     (case v of
        BLeft (BBackref v1 v2 cs') \<Rightarrow> BBackref (binjval r c v1) v2 cs
      | BRight (BLeft (BHalf v' cs' rep)) \<Rightarrow>
          BBackref (bmkeps r) (binjval mid c v') cs
      | BRight (BRight v') \<Rightarrow> BBackref (bmkeps r) (bmkeps mid) cs
      | BRight (BHalf v' cs' rep) \<Rightarrow>
          BBackref (bmkeps r) (binjval mid c v') cs
      | BBackref v1 v2 cs' \<Rightarrow> BBackref (binjval r c v1) v2 cs
      | _ \<Rightarrow> BVoid)"
| "binjval (BHALF mid cs rep) c v =
     (case v of
        BLeft (BHalf v' cs' rep') \<Rightarrow> BHalf (binjval mid c v') cs rep
      | BRight v' \<Rightarrow> BHalf (bmkeps mid) cs rep
      | BHalf v' cs' rep' \<Rightarrow> BHalf (binjval mid c v') cs rep
      | _ \<Rightarrow> BVoid)"
| "binjval (BRESIDUE cs rep) c v = BResidue cs rep"

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
  then have "xnullable r" "v = bmkeps r"
    by (auto split: if_splits)
  then show ?case using bmkeps_flat by simp
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
proof (induct s arbitrary: r)
  case Nil
  then show ?case by (simp add: xnullable_correctness)
next
  case (Cons c s)
  have "c # s \<in> BL r \<longleftrightarrow> s \<in> BL (xder c r)"
    by (simp add: xder_correctness Der_def)
  also have "... \<longleftrightarrow> blexer (xder c r) s \<noteq> None"
    using Cons.hyps[of "xder c r"] by auto
  also have "... \<longleftrightarrow> blexer r (c # s) \<noteq> None"
    by (cases "blexer (xder c r) s") simp_all
  finally show ?case by blast
qed

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
  then show "s \<in> BL r" using BL_flat_BPrf1 by fastforce
qed

theorem blexer_correctness:
  shows blexer_correctness_None: "blexer r s = None \<longleftrightarrow> s \<notin> BL r"
    and blexer_correctness_Some:
      "blexer r s = Some v \<Longrightarrow> \<Turnstile>b v : r \<and> bflat v = s"
    and blexer_correctness_defined:
      "s \<in> BL r \<longleftrightarrow> (\<exists>v. blexer r s = Some v)"
proof -
  show "blexer r s = None \<longleftrightarrow> s \<notin> BL r"
    using blexer_correct_None by blast
  show "blexer r s = Some v \<Longrightarrow> \<Turnstile>b v : r \<and> bflat v = s"
    using blexer_BPrf blexer_flat by blast
  show "s \<in> BL r \<longleftrightarrow> (\<exists>v. blexer r s = Some v)"
  proof
    assume "s \<in> BL r"
    then have "blexer r s \<noteq> None"
      using blexer_correct_None by blast
    then show "\<exists>v. blexer r s = Some v"
      by (cases "blexer r s") auto
  next
    assume "\<exists>v. blexer r s = Some v"
    then obtain v where v: "blexer r s = Some v"
      by blast
    then have "\<Turnstile>b v : r" "bflat v = s"
      using blexer_BPrf blexer_flat by blast+
    then show "s \<in> BL r"
      using BL_flat_BPrf1 by blast
  qed
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

lemma lang_pow_empty_from_all:
  fixes A :: "string set"
  assumes "\<forall>x \<in> set xs. [] \<in> A"
  shows "[] \<in> A ^^ length xs"
  using assms
proof (induct xs)
  case Nil
  then show ?case by (simp add: lang_empty)
next
  case (Cons x xs)
  then have "[] \<in> A" and "[] \<in> A ^^ length xs"
    by auto
  then have "[] @ [] \<in> A ;; (A ^^ length xs)"
    by (rule concI)
  then show ?case by (simp add: lang_pow.simps(2))
qed

lemma BPosix1:
  assumes "s \<in> r \<rightarrow> v"
  shows "s \<in> BL r" "bflat v = s"
  using assms
  apply(induct s r v rule: BPosix.induct)
                apply(auto simp add: pow_empty_iff backref_lang_def Sequ_def)
  apply (metis Suc_pred concI lang_pow.simps(2))
  apply (rule lang_pow_empty_from_all)
  apply blast
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

lemma BPosix_BSTAR_value_shape:
  assumes "s \<in> BSTAR r \<rightarrow> v"
  obtains vs where "v = BStars vs"
  using assms
  apply (cases rule: BPosix_elims(6))
   apply (auto intro: that)
  done

lemma BPosix_BNTIMES_empty_replicate:
  assumes "[] \<in> r \<rightarrow> v"
  shows "[] \<in> BNTIMES r n \<rightarrow> BStars (replicate n v)"
  apply (rule BPosix_BNTIMES2)
   apply (use assms in auto)
  done

lemma BPosix_bmkeps:
  assumes "xnullable r"
  shows "[] \<in> r \<rightarrow> bmkeps r"
  using assms
proof (induct r)
  case BZERO
  then show ?case by simp
next
  case BONE
  then show ?case by (simp add: BPosix_BONE)
next
  case (BCH x)
  then show ?case by simp
next
  case (BSEQ r1 r2)
  then have r1: "[] \<in> r1 \<rightarrow> bmkeps r1"
    and r2: "[] \<in> r2 \<rightarrow> bmkeps r2"
    by simp_all
  have "([] @ []) \<in> BSEQ r1 r2 \<rightarrow> BSeq (bmkeps r1) (bmkeps r2)"
    using r1 r2 by (rule BPosix_BSEQ) auto
  then show ?case by simp
next
  case (BALT r1 r2)
  then show ?case
  proof (cases "xnullable r1")
    case True
    with BALT have "[] \<in> r1 \<rightarrow> bmkeps r1"
      by simp
    then show ?thesis using True by (simp add: BPosix_BALT1)
  next
    case False
    with BALT have r2: "[] \<in> r2 \<rightarrow> bmkeps r2"
      by simp
    from False have "[] \<notin> BL r1"
      by (simp add: xnullable_correctness)
    then show ?thesis using False r2 by (simp add: BPosix_BALT2)
  qed
next
  case (BSTAR r)
  then show ?case by (simp add: BPosix_BSTAR2)
next
  case (BNTIMES r n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis by (simp add: BPosix_BNTIMES2)
  next
    case (Suc m)
    with BNTIMES have "[] \<in> r \<rightarrow> bmkeps r"
      by simp
    then have "[] \<in> BNTIMES r (Suc m) \<rightarrow> BStars (replicate (Suc m) (bmkeps r))"
      by (rule BPosix_BNTIMES_empty_replicate)
    then show ?thesis using Suc by simp
  qed
next
  case (BBACKREF r mid cs)
  then have r: "[] \<in> r \<rightarrow> bmkeps r"
    and mid: "[] \<in> mid \<rightarrow> bmkeps mid"
    and cs: "cs = []"
    by simp_all
  have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> ([] @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL mid \<and>
      [] @ rev ([] :: string) @ [] = s\<^sub>3 @ s\<^sub>4 @ rev ([] :: string) @ ([] @ s\<^sub>3))"
    by auto
  have "([] @ [] @ rev ([] :: string) @ []) \<in> BBACKREF r mid [] \<rightarrow> BBackref (bmkeps r) (bmkeps mid) []"
    using r mid greedy by (rule BPosix_BBACKREF)
  then show ?case using cs by simp
next
  case (BHALF mid cs rep)
  then have mid: "[] \<in> mid \<rightarrow> bmkeps mid"
    and cs: "cs = []"
    by simp_all
  have "([] @ []) \<in> BHALF mid [] rep \<rightarrow> BHalf (bmkeps mid) [] rep"
    using mid by (rule BPosix_BHALF)
  then show ?case using cs by simp
next
  case (BRESIDUE cs rep)
  then show ?case by (cases cs) (auto intro: BPosix_BRESIDUE)
qed

lemma bval_list_eq_replicateI:
  assumes "\<forall>x \<in> set xs. x = a"
    and "length xs = n"
  shows "xs = replicate n a"
  using assms
  by (induct xs arbitrary: n) (auto split: nat.splits)

lemma BPosix_empty_bmkeps:
  assumes "[] \<in> r \<rightarrow> v"
  shows "v = bmkeps r"
  using assms
proof (induct r arbitrary: v)
  case BZERO
  then show ?case by (auto elim: BPosix_elims(1))
next
  case BONE
  then show ?case by (auto elim: BPosix_elims(2))
next
  case (BCH c)
  then show ?case by (auto elim: BPosix_elims(3))
next
  case (BSEQ r1 r2)
  from BSEQ.prems obtain s1 s2 v1 v2 where decomp:
    "v = BSeq v1 v2" "s1 \<in> r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "[] = s1 @ s2"
    apply (cases rule: BPosix_elims(5))
    apply auto
    done
  then have empty: "s1 = []" "s2 = []" by auto
  have "v1 = bmkeps r1" using BSEQ.hyps(1) decomp(2) empty(1) by simp
  moreover have "v2 = bmkeps r2" using BSEQ.hyps(2) decomp(3) empty(2) by simp
  ultimately show ?case using decomp(1) by simp
next
  case (BALT r1 r2)
  from BALT.prems consider
    (left) v1 where "v = BLeft v1" "[] \<in> r1 \<rightarrow> v1"
  | (right) v2 where "v = BRight v2" "[] \<in> r2 \<rightarrow> v2" "[] \<notin> BL r1"
    apply (cases rule: BPosix_elims(4))
    apply auto
    done
  then show ?case
  proof cases
    case left
    have "[] \<in> BL r1"
      using left(2) by (rule BPosix1(1))
    then have "xnullable r1"
      using xnullable_correctness by simp
    moreover have "v1 = bmkeps r1"
      using BALT.hyps(1) left(2) by simp
    ultimately show ?thesis using left(1) by simp
  next
    case right
    then have "\<not> xnullable r1"
      using xnullable_correctness by simp
    moreover have "v2 = bmkeps r2"
      using BALT.hyps(2) right(2) by simp
    ultimately show ?thesis using right(1) by simp
  qed
next
  case (BSTAR r)
  from BSTAR.prems show ?case
    apply (cases rule: BPosix_elims(6))
     apply (auto simp add: BPosix1(2))
    done
next
  case (BNTIMES r n)
  from BNTIMES.prems obtain vs where vs:
    "v = BStars vs" "\<forall>w \<in> set vs. [] \<in> r \<rightarrow> w" "length vs = n"
    apply (cases rule: BPosix_elims(7))
     apply (auto simp add: BPosix1(2))
    done
  have each: "\<forall>w \<in> set vs. w = bmkeps r"
  proof
    fix w
    assume "w \<in> set vs"
    then have "[] \<in> r \<rightarrow> w" using vs(2) by simp
    then show "w = bmkeps r" using BNTIMES.hyps by simp
  qed
  then have "vs = replicate n (bmkeps r)"
    using bval_list_eq_replicateI[OF each vs(3)] by simp
  then show ?case using vs(1) by simp
next
  case (BBACKREF r mid cs)
  from BBACKREF.prems obtain s1 s2 v1 v2 where decomp:
    "v = BBackref v1 v2 cs"
    "s1 \<in> r \<rightarrow> v1"
    "s2 \<in> mid \<rightarrow> v2"
    "[] = s1 @ s2 @ rev cs @ s1"
    apply (cases rule: BPosix_elims(8))
    apply auto
    done
  then have empty: "s1 = []" "s2 = []" "cs = []" by auto
  have "v1 = bmkeps r" using BBACKREF.hyps(1) decomp(2) empty(1) by simp
  moreover have "v2 = bmkeps mid" using BBACKREF.hyps(2) decomp(3) empty(2) by simp
  ultimately show ?case using decomp(1) empty(3) by simp
next
  case (BHALF mid cs rep)
  from BHALF.prems obtain s v' where decomp:
    "v = BHalf v' cs rep" "s \<in> mid \<rightarrow> v'" "[] = s @ cs"
    apply (cases rule: BPosix_elims(9))
    apply auto
    done
  then have empty: "s = []" "cs = []" by auto
  have "v' = bmkeps mid" using BHALF.hyps decomp(2) empty(1) by simp
  then show ?case using decomp(1) empty(2) by simp
next
  case (BRESIDUE cs rep)
  then show ?case by (auto elim: BPosix_elims(10))
qed

lemma bval_list_eq_zipI:
  assumes "\<forall>(v1, v2) \<in> set (zip vs1 vs2). v1 = v2"
    and "length vs1 = length vs2"
  shows "vs1 = vs2"
  using assms
  apply (induct vs1 arbitrary: vs2)
   apply (case_tac vs2)
    apply simp
   apply simp
  apply (case_tac vs2)
   apply simp
  apply simp
  done

lemma BBACKREF_split_cases:
  assumes "s1 @ s2 @ rev cs @ s1 = t1 @ t2 @ rev cs @ t1"
  obtains us where "s1 = t1 @ us" "us @ (s2 @ rev cs @ s1) = t2 @ rev cs @ t1"
    | us where "s1 @ us = t1" "s2 @ rev cs @ s1 = us @ (t2 @ rev cs @ t1)"
proof -
  have "s1 @ (s2 @ rev cs @ s1) = t1 @ (t2 @ rev cs @ t1)"
    using assms by (simp add: append_assoc)
  then have split:
    "\<exists>us. (s1 = t1 @ us \<and> us @ (s2 @ rev cs @ s1) = t2 @ rev cs @ t1) \<or>
      (s1 @ us = t1 \<and> s2 @ rev cs @ s1 = us @ (t2 @ rev cs @ t1))"
    by (rule iffD1[OF append_eq_append_conv2])
  from split show ?thesis
    using that by auto
qed

lemma BBACKREF_split_unique:
  assumes eq: "s1 @ s2 @ rev cs @ s1 = t1 @ t2 @ rev cs @ t1"
    and greedy1: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (s1 @ s\<^sub>3) \<in> BL r \<and>
      s\<^sub>4 \<in> BL mid \<and> s2 @ rev cs @ s1 = s\<^sub>3 @ s\<^sub>4 @ rev cs @ (s1 @ s\<^sub>3))"
    and greedy2: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (t1 @ s\<^sub>3) \<in> BL r \<and>
      s\<^sub>4 \<in> BL mid \<and> t2 @ rev cs @ t1 = s\<^sub>3 @ s\<^sub>4 @ rev cs @ (t1 @ s\<^sub>3))"
    and r1: "s1 \<in> BL r"
    and m1: "s2 \<in> BL mid"
    and r2: "t1 \<in> BL r"
    and m2: "t2 \<in> BL mid"
  shows "s1 = t1" "s2 = t2"
proof -
  have cap: "s1 = t1"
  proof (cases rule: BBACKREF_split_cases[OF eq])
    case (1 us)
    then show ?thesis
    proof (cases "us = []")
      case True
      then show ?thesis using 1 by simp
    next
      case False
      have eq2: "t2 @ rev cs @ t1 = us @ s2 @ rev cs @ (t1 @ us)"
        using 1 by (simp add: append_assoc)
      have "\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (t1 @ s\<^sub>3) \<in> BL r \<and>
        s\<^sub>4 \<in> BL mid \<and> t2 @ rev cs @ t1 =
          s\<^sub>3 @ s\<^sub>4 @ rev cs @ (t1 @ s\<^sub>3)"
        using False r1 m1 1 eq2
        apply (rule_tac x=us in exI)
        apply (rule_tac x=s2 in exI)
        apply (simp add: append_assoc)
        done
      then have False using greedy2 by simp
      then show ?thesis by simp
    qed
  next
    case (2 us)
    then show ?thesis
    proof (cases "us = []")
      case True
      then show ?thesis using 2 by simp
    next
      case False
      have eq2: "s2 @ rev cs @ s1 = us @ t2 @ rev cs @ (s1 @ us)"
        using 2 by (simp add: append_assoc)
      have "\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (s1 @ s\<^sub>3) \<in> BL r \<and>
        s\<^sub>4 \<in> BL mid \<and> s2 @ rev cs @ s1 =
          s\<^sub>3 @ s\<^sub>4 @ rev cs @ (s1 @ s\<^sub>3)"
        using False r2 m2 2 eq2
        apply (rule_tac x=us in exI)
        apply (rule_tac x=t2 in exI)
        apply (simp add: append_assoc)
        done
      then have False using greedy1 by simp
      then show ?thesis by simp
    qed
  qed
  then show "s1 = t1" by simp
  from eq cap show "s2 = t2"
    by (simp add: append_assoc)
qed

lemma BSEQ_split_unique:
  assumes eq: "s1 @ s2 = t1 @ t2"
    and greedy1: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and>
      (s1 @ s\<^sub>3) \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2)"
    and greedy2: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = t2 \<and>
      (t1 @ s\<^sub>3) \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2)"
    and r1: "s1 \<in> BL r1"
    and r2: "s2 \<in> BL r2"
    and t1: "t1 \<in> BL r1"
    and t2: "t2 \<in> BL r2"
  shows "s1 = t1" "s2 = t2"
proof -
  have split:
    "\<exists>us. (s1 = t1 @ us \<and> us @ s2 = t2) \<or>
      (s1 @ us = t1 \<and> s2 = us @ t2)"
    using eq by (rule iffD1[OF append_eq_append_conv2])
  have cap: "s1 = t1"
  proof -
    from split consider
      (left) us where "s1 = t1 @ us" "us @ s2 = t2"
    | (right) us where "s1 @ us = t1" "s2 = us @ t2"
      by blast
    then show ?thesis
    proof cases
      case (left us)
      then show ?thesis
      proof (cases "us = []")
        case True
        then show ?thesis using left by simp
      next
        case False
        have "\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = t2 \<and>
          (t1 @ s\<^sub>3) \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2"
          using False left r1 r2 by auto
        then have False using greedy2 by simp
        then show ?thesis by simp
      qed
    next
      case (right us)
      then show ?thesis
      proof (cases "us = []")
        case True
        then show ?thesis using right by simp
      next
        case False
        have "\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and>
          (s1 @ s\<^sub>3) \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2"
          using False right t1 t2 by auto
        then have False using greedy1 by simp
        then show ?thesis by simp
      qed
    qed
  qed
  then show "s1 = t1" by simp
  from eq cap show "s2 = t2" by simp
qed

lemma BPosix_BBACKREF_value_unique:
  assumes target: "(s1 @ s2 @ rev cs @ s1) \<in> BBACKREF r mid cs \<rightarrow> v"
    and left1: "s1 \<in> r \<rightarrow> v1"
    and left2: "s2 \<in> mid \<rightarrow> v2"
    and greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (s1 @ s\<^sub>3) \<in> BL r \<and>
      s\<^sub>4 \<in> BL mid \<and> s2 @ rev cs @ s1 =
        s\<^sub>3 @ s\<^sub>4 @ rev cs @ (s1 @ s\<^sub>3))"
    and IH1: "\<And>w. s1 \<in> r \<rightarrow> w \<Longrightarrow> v1 = w"
    and IH2: "\<And>w. s2 \<in> mid \<rightarrow> w \<Longrightarrow> v2 = w"
  shows "BBackref v1 v2 cs = v"
proof -
  from target obtain t1 t2 w1 w2 where decomp:
    "v = BBackref w1 w2 cs"
    "t1 \<in> r \<rightarrow> w1"
    "t2 \<in> mid \<rightarrow> w2"
    "s1 @ s2 @ rev cs @ s1 = t1 @ t2 @ rev cs @ t1"
    "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (t1 @ s\<^sub>3) \<in> BL r \<and>
      s\<^sub>4 \<in> BL mid \<and> t2 @ rev cs @ t1 =
        s\<^sub>3 @ s\<^sub>4 @ rev cs @ (t1 @ s\<^sub>3))"
    by (auto elim!: BPosix_elims(8))
  have bl1: "s1 \<in> BL r" using left1 by (rule BPosix1(1))
  have bl2: "s2 \<in> BL mid" using left2 by (rule BPosix1(1))
  have bl3: "t1 \<in> BL r" using decomp(2) by (rule BPosix1(1))
  have bl4: "t2 \<in> BL mid" using decomp(3) by (rule BPosix1(1))
  have split: "s1 = t1" "s2 = t2"
    using BBACKREF_split_unique[OF decomp(4) greedy decomp(5) bl1 bl2 bl3 bl4]
    by simp_all
  have "v1 = w1" using IH1 decomp(2) split(1) by simp
  moreover have "v2 = w2" using IH2 decomp(3) split(2) by simp
  ultimately show ?thesis using decomp(1) by simp
qed

lemma BPosix_determ:
  assumes "s \<in> r \<rightarrow> v1" "s \<in> r \<rightarrow> v2"
  shows "v1 = v2"
  using assms
proof (induct s r v1 arbitrary: v2 rule: BPosix.induct)
  case (BPosix_BONE v2)
  then show ?case by (auto elim: BPosix_elims(2))
next
  case (BPosix_BCH c v2)
  then show ?case by (auto elim: BPosix_elims(3))
next
  case (BPosix_BALT1 s r1 v r2 v2)
  have target: "s \<in> BALT r1 r2 \<rightarrow> v2" by fact
  have left: "s \<in> r1 \<rightarrow> v" by fact
  then have "s \<in> BL r1" by (rule BPosix1(1))
  with target obtain v' where eq: "v2 = BLeft v'" "s \<in> r1 \<rightarrow> v'"
    apply (cases rule: BPosix_elims(4))
    apply (auto dest: BPosix1(1))
    done
  have IH: "\<And>w. s \<in> r1 \<rightarrow> w \<Longrightarrow> v = w" by fact
  then have "v = v'" using eq(2) by simp
  then show ?case using eq(1) by simp
next
  case (BPosix_BALT2 s r2 v r1 v2)
  have target: "s \<in> BALT r1 r2 \<rightarrow> v2" by fact
  have not_left: "s \<notin> BL r1" by fact
  with target obtain v' where eq: "v2 = BRight v'" "s \<in> r2 \<rightarrow> v'"
    apply (cases rule: BPosix_elims(4))
    apply (auto dest: BPosix1(1))
    done
  have IH: "\<And>w. s \<in> r2 \<rightarrow> w \<Longrightarrow> v = w" by fact
  then have "v = v'" using eq(2) by simp
  then show ?case using eq(1) by simp
next
  case (BPosix_BSEQ s1 r1 v1 s2 r2 v2 v')
  have target: "(s1 @ s2) \<in> BSEQ r1 r2 \<rightarrow> v'" by fact
  have left: "s1 \<in> r1 \<rightarrow> v1" by fact
  have right: "s2 \<in> r2 \<rightarrow> v2" by fact
  have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and>
      (s1 @ s\<^sub>3) \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2)" by fact
  from target obtain t1 t2 w1 w2 where decomp:
    "v' = BSeq w1 w2"
    "t1 \<in> r1 \<rightarrow> w1"
    "t2 \<in> r2 \<rightarrow> w2"
    "s1 @ s2 = t1 @ t2"
    "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = t2 \<and>
      (t1 @ s\<^sub>3) \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2)"
    apply (cases rule: BPosix_elims(5))
    apply auto
    done
  have split: "s1 = t1" "s2 = t2"
    using BSEQ_split_unique[OF decomp(4) greedy decomp(5)
        BPosix1(1)[OF left] BPosix1(1)[OF right]
        BPosix1(1)[OF decomp(2)] BPosix1(1)[OF decomp(3)]]
    by simp_all
  have IH1: "\<And>w. s1 \<in> r1 \<rightarrow> w \<Longrightarrow> v1 = w" by fact
  have IH2: "\<And>w. s2 \<in> r2 \<rightarrow> w \<Longrightarrow> v2 = w" by fact
  have "v1 = w1" using IH1 decomp(2) split(1) by simp
  moreover have "v2 = w2" using IH2 decomp(3) split(2) by simp
  ultimately show ?case using decomp(1) by simp
next
  case (BPosix_BSTAR1 s1 r v s2 vs v2)
  have target: "(s1 @ s2) \<in> BSTAR r \<rightarrow> v2" by fact
  have first: "s1 \<in> r \<rightarrow> v" by fact
  have rest: "s2 \<in> BSTAR r \<rightarrow> BStars vs" by fact
  have nonempty: "bflat v \<noteq> []" by fact
  have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and>
      (s1 @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL (BSTAR r))" by fact
  have whole_nonempty: "s1 @ s2 \<noteq> []"
    using BPosix1(2)[OF first] nonempty by auto
  from target whole_nonempty obtain t1 t2 w ws where decomp:
    "v2 = BStars (w # ws)"
    "t1 \<in> r \<rightarrow> w"
    "t2 \<in> BSTAR r \<rightarrow> BStars ws"
    "s1 @ s2 = t1 @ t2"
    "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = t2 \<and>
      (t1 @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL (BSTAR r))"
    apply (cases rule: BPosix_elims(6))
    apply auto
    done
  have split: "s1 = t1" "s2 = t2"
    using BSEQ_split_unique[OF decomp(4) greedy decomp(5)
        BPosix1(1)[OF first] BPosix1(1)[OF rest]
        BPosix1(1)[OF decomp(2)] BPosix1(1)[OF decomp(3)]]
    by simp_all
  have IH1: "\<And>w. s1 \<in> r \<rightarrow> w \<Longrightarrow> v = w" by fact
  have IH2: "\<And>w. s2 \<in> BSTAR r \<rightarrow> w \<Longrightarrow> BStars vs = w" by fact
  have "v = w" using IH1 decomp(2) split(1) by simp
  moreover have "BStars vs = BStars ws" using IH2 decomp(3) split(2) by simp
  ultimately show ?case using decomp(1) by simp
next
  case (BPosix_BSTAR2 r v2)
  have target: "[] \<in> BSTAR r \<rightarrow> v2" by fact
  from target show ?case
    apply (cases rule: BPosix_elims(6))
     apply (auto simp add: BPosix1)
    done
next
  case (BPosix_BNTIMES1 s1 r v s2 n vs v2)
  have target: "(s1 @ s2) \<in> BNTIMES r n \<rightarrow> v2" by fact
  have first: "s1 \<in> r \<rightarrow> v" by fact
  have rest: "s2 \<in> BNTIMES r (n - 1) \<rightarrow> BStars vs" by fact
  have nonempty: "bflat v \<noteq> []" by fact
  have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and>
      (s1 @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL (BNTIMES r (n - 1)))" by fact
  have whole_nonempty: "s1 @ s2 \<noteq> []"
    using BPosix1(2)[OF first] nonempty by auto
  from target whole_nonempty obtain t1 t2 w ws where decomp:
    "v2 = BStars (w # ws)"
    "t1 \<in> r \<rightarrow> w"
    "t2 \<in> BNTIMES r (n - 1) \<rightarrow> BStars ws"
    "s1 @ s2 = t1 @ t2"
    "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = t2 \<and>
      (t1 @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL (BNTIMES r (n - 1)))"
    apply (cases rule: BPosix_elims(7))
    apply auto
    done
  have split: "s1 = t1" "s2 = t2"
    using BSEQ_split_unique[OF decomp(4) greedy decomp(5)
        BPosix1(1)[OF first] BPosix1(1)[OF rest]
        BPosix1(1)[OF decomp(2)] BPosix1(1)[OF decomp(3)]]
    by simp_all
  have IH1: "\<And>w. s1 \<in> r \<rightarrow> w \<Longrightarrow> v = w" by fact
  have IH2: "\<And>w. s2 \<in> BNTIMES r (n - 1) \<rightarrow> w \<Longrightarrow> BStars vs = w" by fact
  have "v = w" using IH1 decomp(2) split(1) by simp
  moreover have "BStars vs = BStars ws" using IH2 decomp(3) split(2) by simp
  ultimately show ?case using decomp(1) by simp
next
  case (BPosix_BNTIMES2 vs r n v2)
  have target: "[] \<in> BNTIMES r n \<rightarrow> v2" by fact
  have all_vs: "\<And>v. v \<in> set vs \<Longrightarrow> [] \<in> r \<rightarrow> v"
    using BPosix_BNTIMES2.hyps(1) by simp
  have len_vs: "length vs = n"
    using BPosix_BNTIMES2.hyps(2) by simp
  from target obtain ws where ws:
    "v2 = BStars ws" "\<forall>w \<in> set ws. [] \<in> r \<rightarrow> w" "length ws = n"
    apply (cases rule: BPosix_elims(7))
     apply (auto simp add: BPosix1(2))
    done
  have each_vs: "\<forall>v \<in> set vs. v = bmkeps r"
  proof
    fix v
    assume "v \<in> set vs"
    then have "[] \<in> r \<rightarrow> v" by (rule all_vs)
    then show "v = bmkeps r" by (rule BPosix_empty_bmkeps)
  qed
  have each_ws: "\<forall>w \<in> set ws. w = bmkeps r"
  proof
    fix w
    assume "w \<in> set ws"
    then have "[] \<in> r \<rightarrow> w" using ws(2) by simp
    then show "w = bmkeps r" by (rule BPosix_empty_bmkeps)
  qed
  have "vs = replicate n (bmkeps r)"
    using bval_list_eq_replicateI[OF each_vs len_vs] by simp
  moreover have "ws = replicate n (bmkeps r)"
    using bval_list_eq_replicateI[OF each_ws ws(3)] by simp
  ultimately have "vs = ws" by simp
  then show ?case using ws(1) by simp
next
  case (BPosix_BBACKREF s1 r v1 s2 mid v2 cs v')
  have target: "(s1 @ s2 @ rev cs @ s1) \<in> BBACKREF r mid cs \<rightarrow> v'" by fact
  have left1: "s1 \<in> r \<rightarrow> v1" by fact
  have left2: "s2 \<in> mid \<rightarrow> v2" by fact
  have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (s1 @ s\<^sub>3) \<in> BL r \<and>
      s\<^sub>4 \<in> BL mid \<and> s2 @ rev cs @ s1 =
        s\<^sub>3 @ s\<^sub>4 @ rev cs @ (s1 @ s\<^sub>3))" by fact
  have IH1: "\<And>w. s1 \<in> r \<rightarrow> w \<Longrightarrow> v1 = w" by fact
  have IH2: "\<And>w. s2 \<in> mid \<rightarrow> w \<Longrightarrow> v2 = w" by fact
  show ?case
    using BPosix_BBACKREF_value_unique[OF target left1 left2 greedy IH1 IH2]
    by simp
next
  case (BPosix_BHALF s mid v cs rep v2)
  have target: "(s @ cs) \<in> BHALF mid cs rep \<rightarrow> v2" by fact
  have first: "s \<in> mid \<rightarrow> v" by fact
  from target obtain t w where decomp:
    "v2 = BHalf w cs rep" "t \<in> mid \<rightarrow> w" "s @ cs = t @ cs"
    apply (cases rule: BPosix_elims(9))
    apply auto
    done
  have "s = t" using decomp(3) by simp
  moreover have IH: "\<And>w. s \<in> mid \<rightarrow> w \<Longrightarrow> v = w" by fact
  ultimately have "v = w" using IH decomp(2) by simp
  then show ?case using decomp(1) by simp
next
  case (BPosix_BRESIDUE cs rep v2)
  then show ?case by (auto elim: BPosix_elims(10))
qed

section \<open>Injection Preserves POSIX\<close>

lemma BPosix_binjval:
  assumes "s \<in> (xder c r) \<rightarrow> v"
  shows "(c # s) \<in> r \<rightarrow> (binjval r c v)"
  using assms
proof (induct r arbitrary: s v c)
  case BZERO
  then show ?case by (auto elim: BPosix_elims)
next
  case BONE
  then show ?case by (auto elim: BPosix_elims)
next
  case (BCH d)
  then show ?case
    by (auto intro: BPosix.intros elim!: BPosix_elims split: if_splits)
next
  case (BALT r1 r2)
  have IH1: "\<And>s v c. s \<in> xder c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> binjval r1 c v" by fact
  have IH2: "\<And>s v c. s \<in> xder c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> binjval r2 c v" by fact
  have "s \<in> xder c (BALT r1 r2) \<rightarrow> v" by fact
  then have "s \<in> BALT (xder c r1) (xder c r2) \<rightarrow> v" by simp
  then consider
    (left) v' where "v = BLeft v'" "s \<in> xder c r1 \<rightarrow> v'"
  | (right) v' where "v = BRight v'" "s \<notin> BL (xder c r1)" "s \<in> xder c r2 \<rightarrow> v'"
    by (auto elim: BPosix_elims)
  then show "(c # s) \<in> BALT r1 r2 \<rightarrow> binjval (BALT r1 r2) c v"
  proof cases
    case left
    then have "(c # s) \<in> r1 \<rightarrow> binjval r1 c v'" using IH1 by simp
    then show ?thesis using left by (auto intro: BPosix.intros)
  next
    case right
    then have "(c # s) \<in> r2 \<rightarrow> binjval r2 c v'" using IH2 by simp
    moreover have "c # s \<notin> BL r1" using right by (simp add: xder_correctness Der_def)
    ultimately show ?thesis using right by (auto intro: BPosix.intros)
  qed
next
  case (BSEQ r1 r2)
  have IH1: "\<And>s v c. s \<in> xder c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> binjval r1 c v" by fact
  have IH2: "\<And>s v c. s \<in> xder c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> binjval r2 c v" by fact
  have "s \<in> xder c (BSEQ r1 r2) \<rightarrow> v" by fact
  then consider
    (left_nullable) v1 v2 s1 s2 where
      "v = BLeft (BSeq v1 v2)" "s = s1 @ s2" "xnullable r1"
      "s1 \<in> xder c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2"
      "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> BL (xder c r1) \<and> s\<^sub>4 \<in> BL r2)"
  | (right_nullable) v1 where
      "v = BRight v1" "xnullable r1"
      "s \<in> xder c r2 \<rightarrow> v1" "s \<notin> BL (BSEQ (xder c r1) r2)"
  | (not_nullable) v1 v2 s1 s2 where
      "v = BSeq v1 v2" "s = s1 @ s2" "\<not>xnullable r1"
      "s1 \<in> xder c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2"
      "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> BL (xder c r1) \<and> s\<^sub>4 \<in> BL r2)"
    by (force split: if_splits elim!: BPosix_elims simp add: Sequ_def xder_correctness Der_def)
  then show "(c # s) \<in> BSEQ r1 r2 \<rightarrow> binjval (BSEQ r1 r2) c v"
  proof cases
    case left_nullable
    have r1: "(c # s1) \<in> r1 \<rightarrow> binjval r1 c v1" using IH1 left_nullable by simp
    have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2)"
    proof
      assume "\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2"
      then obtain s\<^sub>3 s\<^sub>4 where "s\<^sub>3 \<noteq> []" "s\<^sub>3 @ s\<^sub>4 = s2" "(c # s1) @ s\<^sub>3 \<in> BL r1" "s\<^sub>4 \<in> BL r2"
        by blast
      then have "s1 @ s\<^sub>3 \<in> BL (xder c r1)"
        by (simp add: xder_correctness Der_def)
      then show False using left_nullable \<open>s\<^sub>3 \<noteq> []\<close> \<open>s\<^sub>3 @ s\<^sub>4 = s2\<close> \<open>s\<^sub>4 \<in> BL r2\<close>
        by blast
    qed
    have "((c # s1) @ s2) \<in> BSEQ r1 r2 \<rightarrow> BSeq (binjval r1 c v1) v2"
      using r1 left_nullable(5) greedy by (rule BPosix_BSEQ)
    then show ?thesis using left_nullable by simp
  next
    case right_nullable
    have "[] \<in> r1 \<rightarrow> bmkeps r1" using right_nullable BPosix_bmkeps by simp
    moreover have "(c # s) \<in> r2 \<rightarrow> binjval r2 c v1" using IH2 right_nullable by simp
    moreover have "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = c # s \<and> [] @ s\<^sub>3 \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2)"
      using right_nullable
      by (auto simp add: xder_correctness Der_def append_eq_Cons_conv Sequ_def)
    ultimately have "([] @ (c # s)) \<in> BSEQ r1 r2 \<rightarrow> BSeq (bmkeps r1) (binjval r2 c v1)"
      by (rule BPosix.intros)
    then show ?thesis using right_nullable by simp
  next
    case not_nullable
    have r1: "(c # s1) \<in> r1 \<rightarrow> binjval r1 c v1" using IH1 not_nullable by simp
    have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2)"
    proof
      assume "\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> BL r1 \<and> s\<^sub>4 \<in> BL r2"
      then obtain s\<^sub>3 s\<^sub>4 where "s\<^sub>3 \<noteq> []" "s\<^sub>3 @ s\<^sub>4 = s2" "(c # s1) @ s\<^sub>3 \<in> BL r1" "s\<^sub>4 \<in> BL r2"
        by blast
      then have "s1 @ s\<^sub>3 \<in> BL (xder c r1)"
        by (simp add: xder_correctness Der_def)
      then show False using not_nullable \<open>s\<^sub>3 \<noteq> []\<close> \<open>s\<^sub>3 @ s\<^sub>4 = s2\<close> \<open>s\<^sub>4 \<in> BL r2\<close>
        by blast
    qed
    have "((c # s1) @ s2) \<in> BSEQ r1 r2 \<rightarrow> BSeq (binjval r1 c v1) v2"
      using r1 not_nullable(5) greedy by (rule BPosix_BSEQ)
    then show ?thesis using not_nullable by simp
  qed
next
  case (BSTAR r)
  have IH: "\<And>s v c. s \<in> xder c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> binjval r c v" by fact
  have "s \<in> xder c (BSTAR r) \<rightarrow> v" by fact
  then have seq_posix: "s \<in> BSEQ (xder c r) (BSTAR r) \<rightarrow> v"
    by simp
  then obtain v1 v2 s1 s2 where seq:
    "v = BSeq v1 v2" "s = s1 @ s2"
    "s1 \<in> xder c r \<rightarrow> v1" "s2 \<in> BSTAR r \<rightarrow> v2"
    "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> BL (xder c r) \<and> s\<^sub>4 \<in> BL (BSTAR r))"
    by (auto elim!: BPosix_elims(5))
  from seq(4) obtain vs where v2: "v2 = BStars vs"
    by (rule BPosix_BSTAR_value_shape)
  have r: "(c # s1) \<in> r \<rightarrow> binjval r c v1" using IH seq by simp
  have nonempty: "bflat (binjval r c v1) \<noteq> []"
    using BPosix1(2) r by force
  have s2: "s2 \<in> BSTAR r \<rightarrow> BStars vs"
    using seq(4) v2 by simp
  have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> BL r \<and> s\<^sub>4 \<in> BL (BSTAR r))"
  proof
    assume "\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> BL r \<and> s\<^sub>4 \<in> BL (BSTAR r)"
    then obtain s\<^sub>3 s\<^sub>4 where "s\<^sub>3 \<noteq> []" "s\<^sub>3 @ s\<^sub>4 = s2" "(c # s1) @ s\<^sub>3 \<in> BL r" "s\<^sub>4 \<in> BL (BSTAR r)"
      by blast
    then have "s1 @ s\<^sub>3 \<in> BL (xder c r)"
      by (simp add: xder_correctness Der_def)
    then show False using seq \<open>s\<^sub>3 \<noteq> []\<close> \<open>s\<^sub>3 @ s\<^sub>4 = s2\<close> \<open>s\<^sub>4 \<in> BL (BSTAR r)\<close>
      by blast
  qed
  have "((c # s1) @ s2) \<in> BSTAR r \<rightarrow> BStars (binjval r c v1 # vs)"
    using r s2 nonempty greedy by (rule BPosix_BSTAR1)
  then show "(c # s) \<in> BSTAR r \<rightarrow> binjval (BSTAR r) c v"
    using seq v2 by simp
next
  case (BNTIMES r n)
  have IH: "\<And>s v c. s \<in> xder c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> binjval r c v" by fact
  have "s \<in> xder c (BNTIMES r n) \<rightarrow> v" by fact
  then consider (cons) v1 vs s1 s2 where
    "v = BSeq v1 (BStars vs)" "s = s1 @ s2"
    "s1 \<in> xder c r \<rightarrow> v1" "s2 \<in> BNTIMES r (n - 1) \<rightarrow> BStars vs" "0 < n"
    "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> BL (xder c r) \<and> s\<^sub>4 \<in> BL (BNTIMES r (n - 1)))"
    apply (auto elim: BPosix_elims simp add: xder_correctness Der_def intro: BPosix.intros split: if_splits)
    apply (erule BPosix_elims)
    apply simp
    apply (subgoal_tac "\<exists>vss. v2 = BStars vss")
     apply clarify
     apply (drule_tac x = vss in meta_spec)
     apply (drule_tac x = s1 in meta_spec)
     apply (drule_tac x = s2 in meta_spec)
     apply (simp add: xder_correctness Der_def)
    apply (erule BPosix_elims)
    apply auto
    done
  then show "(c # s) \<in> BNTIMES r n \<rightarrow> binjval (BNTIMES r n) c v"
  proof cases
    case cons
    have "(c # s1) \<in> r \<rightarrow> binjval r c v1" using IH cons by simp
    moreover have "bflat (binjval r c v1) \<noteq> []"
      using BPosix1(2) calculation by force
    moreover have "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> BL r \<and> s\<^sub>4 \<in> BL (BNTIMES r (n - 1)))"
      using cons by (simp add: xder_correctness Der_def)
    ultimately have "((c # s1) @ s2) \<in> BNTIMES r n \<rightarrow> BStars (binjval r c v1 # vs)"
      using cons by (metis One_nat_def BPosix_BNTIMES1 Suc_eq_plus1 Suc_pred)
    then show ?thesis using cons by simp
  qed
next
  case (BBACKREF r mid cs)
  have IH1: "\<And>s v c. s \<in> xder c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> binjval r c v" by fact
  have IH2: "\<And>s v c. s \<in> xder c mid \<rightarrow> v \<Longrightarrow> (c # s) \<in> mid \<rightarrow> binjval mid c v" by fact
  have asm: "s \<in> xder c (BBACKREF r mid cs) \<rightarrow> v" by fact
  show "(c # s) \<in> BBACKREF r mid cs \<rightarrow> binjval (BBACKREF r mid cs) c v"
  proof (cases "xnullable r")
    case False
    then have der: "xder c (BBACKREF r mid cs) = BBACKREF (xder c r) mid (c # cs)" by simp
    from asm[unfolded der] obtain v1 v2 s1 s2 where decomp:
      "v = BBackref v1 v2 (c # cs)" "s1 \<in> xder c r \<rightarrow> v1" "s2 \<in> mid \<rightarrow> v2"
      "s = s1 @ s2 @ rev (c # cs) @ s1"
      "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (s1 @ s\<^sub>3) \<in> BL (xder c r) \<and> s\<^sub>4 \<in> BL mid \<and>
        s2 @ rev (c # cs) @ s1 = s\<^sub>3 @ s\<^sub>4 @ rev (c # cs) @ (s1 @ s\<^sub>3))"
      by (auto elim!: BPosix_elims)
    have inj1: "(c # s1) \<in> r \<rightarrow> binjval r c v1" using IH1 decomp by simp
    have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> ((c # s1) @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL mid \<and>
        s2 @ rev cs @ (c # s1) = s\<^sub>3 @ s\<^sub>4 @ rev cs @ ((c # s1) @ s\<^sub>3))"
      using decomp(5) by (simp add: xder_correctness Der_def)
    have "((c # s1) @ s2 @ rev cs @ (c # s1)) \<in> BBACKREF r mid cs \<rightarrow>
        BBackref (binjval r c v1) v2 cs"
      using inj1 decomp(3) greedy by (rule BPosix_BBACKREF)
    moreover have "c # s = (c # s1) @ s2 @ rev cs @ (c # s1)"
      using decomp(4) by simp
    ultimately show ?thesis using decomp(1) False by simp
  next
    case True
    then have der: "xder c (BBACKREF r mid cs) = BALT (BBACKREF (xder c r) mid (c # cs))
        (if xnullable mid
         then BALT (BHALF (xder c mid) (rev cs) (rev cs)) (xder_residue c (rev cs) (rev cs))
         else BHALF (xder c mid) (rev cs) (rev cs))"
      by simp
    from asm[unfolded der] consider
      (left) v' where "v = BLeft v'" "s \<in> BBACKREF (xder c r) mid (c # cs) \<rightarrow> v'"
    | (right) v' where "v = BRight v'" "s \<notin> BL (BBACKREF (xder c r) mid (c # cs))"
        "s \<in> (if xnullable mid
                then BALT (BHALF (xder c mid) (rev cs) (rev cs)) (xder_residue c (rev cs) (rev cs))
                else BHALF (xder c mid) (rev cs) (rev cs)) \<rightarrow> v'"
      by (auto elim!: BPosix_elims(4))
    then show ?thesis
    proof cases
      case left
      from left(2) obtain v1 v2 s1 s2 where decomp:
        "v' = BBackref v1 v2 (c # cs)" "s1 \<in> xder c r \<rightarrow> v1" "s2 \<in> mid \<rightarrow> v2"
        "s = s1 @ s2 @ rev (c # cs) @ s1"
        "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (s1 @ s\<^sub>3) \<in> BL (xder c r) \<and> s\<^sub>4 \<in> BL mid \<and>
          s2 @ rev (c # cs) @ s1 = s\<^sub>3 @ s\<^sub>4 @ rev (c # cs) @ (s1 @ s\<^sub>3))"
        by (auto elim!: BPosix_elims)
      have inj1: "(c # s1) \<in> r \<rightarrow> binjval r c v1" using IH1 decomp by simp
      have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> ((c # s1) @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL mid \<and>
          s2 @ rev cs @ (c # s1) = s\<^sub>3 @ s\<^sub>4 @ rev cs @ ((c # s1) @ s\<^sub>3))"
        using decomp(5) by (simp add: xder_correctness Der_def)
      have "((c # s1) @ s2 @ rev cs @ (c # s1)) \<in> BBACKREF r mid cs \<rightarrow>
          BBackref (binjval r c v1) v2 cs"
        using inj1 decomp(3) greedy by (rule BPosix_BBACKREF)
      moreover have "c # s = (c # s1) @ s2 @ rev cs @ (c # s1)"
        using decomp(4) by simp
      ultimately show ?thesis using left decomp(1) by simp
    next
      case right
      have not_left: "s \<notin> BL (BBACKREF (xder c r) mid (c # cs))" by fact
      show ?thesis
      proof (cases "xnullable mid")
        case True
        from right(3)[unfolded if_P[OF True]] consider
          (bhalf) v'' where "v' = BLeft v''" "s \<in> BHALF (xder c mid) (rev cs) (rev cs) \<rightarrow> v''"
        | (residue) v'' where "v' = BRight v''"
            "s \<notin> BL (BHALF (xder c mid) (rev cs) (rev cs))"
            "s \<in> xder_residue c (rev cs) (rev cs) \<rightarrow> v''"
          by (auto elim!: BPosix_elims(4))
        then show ?thesis
        proof cases
          case bhalf
          from bhalf(2) obtain vm sm where hm:
            "v'' = BHalf vm (rev cs) (rev cs)" "sm \<in> xder c mid \<rightarrow> vm" "s = sm @ rev cs"
            by (auto elim!: BPosix_elims)
          have inj_mid: "(c # sm) \<in> mid \<rightarrow> binjval mid c vm" using IH2 hm by simp
          have mkeps_r: "[] \<in> r \<rightarrow> bmkeps r" using \<open>xnullable r\<close> BPosix_bmkeps by simp
          have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> ([] @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL mid \<and>
              (c # sm) @ rev cs @ [] = s\<^sub>3 @ s\<^sub>4 @ rev cs @ ([] @ s\<^sub>3))"
          proof
            assume "\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> ([] @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL mid \<and>
              (c # sm) @ rev cs @ [] = s\<^sub>3 @ s\<^sub>4 @ rev cs @ ([] @ s\<^sub>3)"
            then obtain s\<^sub>3 s\<^sub>4 where a: "s\<^sub>3 \<noteq> []" "s\<^sub>3 \<in> BL r" "s\<^sub>4 \<in> BL mid"
              "(c # sm) @ rev cs = s\<^sub>3 @ s\<^sub>4 @ rev cs @ s\<^sub>3"
              by auto
            from a(1,4) obtain x where x: "s\<^sub>3 = c # x"
              by (cases s\<^sub>3) auto
            then have "x \<in> Der c (BL r)" using a(2) by (simp add: Der_def)
            then have "x \<in> BL (xder c r)" by (simp add: xder_correctness)
            moreover have "sm @ rev cs = x @ s\<^sub>4 @ rev cs @ c # x"
              using a(4) x by simp
            then have "s = x @ s\<^sub>4 @ rev (c # cs) @ x"
              using hm(3) by simp
            ultimately have "s \<in> backref_lang (BL (xder c r)) (BL mid) (c # cs)"
              using a(3) by (auto simp: backref_lang_def)
            then show False using not_left by simp
          qed
          have "([] @ (c # sm) @ rev cs @ []) \<in> BBACKREF r mid cs \<rightarrow>
              BBackref (bmkeps r) (binjval mid c vm) cs"
            using mkeps_r inj_mid greedy by (rule BPosix_BBACKREF)
          moreover have "c # s = [] @ (c # sm) @ rev cs @ []"
            using hm(3) by simp
          ultimately show ?thesis using right(1) bhalf(1) hm(1) by simp
        next
          case residue
          from residue(3) obtain ds where ds:
            "rev cs = c # ds" "v'' = BResidue ds (rev cs)" "s = ds"
            by (cases "rev cs") (auto elim!: BPosix_elims split: if_splits)
          have mkeps_r: "[] \<in> r \<rightarrow> bmkeps r" using \<open>xnullable r\<close> BPosix_bmkeps by simp
          have mkeps_mid: "[] \<in> mid \<rightarrow> bmkeps mid" using True BPosix_bmkeps by simp
          have str: "c # s = [] @ [] @ rev cs @ []" using ds(1,3) by simp
          have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> ([] @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL mid \<and>
              [] @ rev cs @ [] = s\<^sub>3 @ s\<^sub>4 @ rev cs @ ([] @ s\<^sub>3))"
            by (auto dest: arg_cong[where f = length])
          have "([] @ [] @ rev cs @ []) \<in> BBACKREF r mid cs \<rightarrow>
              BBackref (bmkeps r) (bmkeps mid) cs"
            using mkeps_r mkeps_mid greedy by (rule BPosix_BBACKREF)
          then show ?thesis using right(1) residue(1) ds(1,2,3) str by simp
        qed
      next
        case False
        from right(3)[unfolded if_not_P[OF False]] obtain vm sm where hm:
          "v' = BHalf vm (rev cs) (rev cs)" "sm \<in> xder c mid \<rightarrow> vm" "s = sm @ rev cs"
          by (auto elim!: BPosix_elims(9))
        have inj_mid: "(c # sm) \<in> mid \<rightarrow> binjval mid c vm" using IH2 hm by simp
        have mkeps_r: "[] \<in> r \<rightarrow> bmkeps r" using \<open>xnullable r\<close> BPosix_bmkeps by simp
        have greedy: "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> ([] @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL mid \<and>
            (c # sm) @ rev cs @ [] = s\<^sub>3 @ s\<^sub>4 @ rev cs @ ([] @ s\<^sub>3))"
        proof
          assume "\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> ([] @ s\<^sub>3) \<in> BL r \<and> s\<^sub>4 \<in> BL mid \<and>
            (c # sm) @ rev cs @ [] = s\<^sub>3 @ s\<^sub>4 @ rev cs @ ([] @ s\<^sub>3)"
          then obtain s\<^sub>3 s\<^sub>4 where a: "s\<^sub>3 \<noteq> []" "s\<^sub>3 \<in> BL r" "s\<^sub>4 \<in> BL mid"
            "(c # sm) @ rev cs = s\<^sub>3 @ s\<^sub>4 @ rev cs @ s\<^sub>3"
            by auto
          from a(1,4) obtain x where x: "s\<^sub>3 = c # x"
            by (cases s\<^sub>3) auto
          then have "x \<in> Der c (BL r)" using a(2) by (simp add: Der_def)
          then have "x \<in> BL (xder c r)" by (simp add: xder_correctness)
          moreover have "sm @ rev cs = x @ s\<^sub>4 @ rev cs @ c # x"
            using a(4) x by simp
          then have "s = x @ s\<^sub>4 @ rev (c # cs) @ x"
            using hm(3) by simp
          ultimately have "s \<in> backref_lang (BL (xder c r)) (BL mid) (c # cs)"
            using a(3) by (auto simp: backref_lang_def)
          then show False using not_left by simp
        qed
        have "([] @ (c # sm) @ rev cs @ []) \<in> BBACKREF r mid cs \<rightarrow>
            BBackref (bmkeps r) (binjval mid c vm) cs"
          using mkeps_r inj_mid greedy by (rule BPosix_BBACKREF)
        moreover have "c # s = [] @ (c # sm) @ rev cs @ []"
          using hm(3) by simp
        ultimately show ?thesis using right(1) hm(1) by simp
      qed
    qed
  qed
next
  case (BHALF mid cs rep)
  have IH: "\<And>s v c. s \<in> xder c mid \<rightarrow> v \<Longrightarrow> (c # s) \<in> mid \<rightarrow> binjval mid c v" by fact
  have asm: "s \<in> xder c (BHALF mid cs rep) \<rightarrow> v" by fact
  show "(c # s) \<in> BHALF mid cs rep \<rightarrow> binjval (BHALF mid cs rep) c v"
  proof (cases "xnullable mid")
    case False
    then have der: "xder c (BHALF mid cs rep) = BHALF (xder c mid) cs rep" by simp
    from asm[unfolded der] obtain vm sm where hm:
      "v = BHalf vm cs rep" "sm \<in> xder c mid \<rightarrow> vm" "s = sm @ cs"
      by (auto elim!: BPosix_elims(9))
    have "(c # sm) \<in> mid \<rightarrow> binjval mid c vm" using IH hm by simp
    then have "((c # sm) @ cs) \<in> BHALF mid cs rep \<rightarrow> BHalf (binjval mid c vm) cs rep"
      by (rule BPosix_BHALF)
    then show ?thesis using hm by simp
  next
    case True
    then have der: "xder c (BHALF mid cs rep) = BALT (BHALF (xder c mid) cs rep) (xder_residue c cs rep)"
      by simp
    from asm[unfolded der] consider
      (left) v' where "v = BLeft v'" "s \<in> BHALF (xder c mid) cs rep \<rightarrow> v'"
    | (right) v' where "v = BRight v'" "s \<notin> BL (BHALF (xder c mid) cs rep)"
        "s \<in> xder_residue c cs rep \<rightarrow> v'"
      by (auto elim!: BPosix_elims(4))
    then show ?thesis
    proof cases
      case left
      from left(2) obtain vm sm where hm:
        "v' = BHalf vm cs rep" "sm \<in> xder c mid \<rightarrow> vm" "s = sm @ cs"
        by (auto elim!: BPosix_elims(9))
      have "(c # sm) \<in> mid \<rightarrow> binjval mid c vm" using IH hm by simp
      then have "((c # sm) @ cs) \<in> BHALF mid cs rep \<rightarrow> BHalf (binjval mid c vm) cs rep"
        by (rule BPosix_BHALF)
      then show ?thesis using left hm by simp
    next
      case right
      from right(3) obtain ds where ds:
        "cs = c # ds" "v' = BResidue ds rep" "s = ds"
        by (cases cs) (auto elim!: BPosix_elims split: if_splits)
      have "[] \<in> mid \<rightarrow> bmkeps mid" using True BPosix_bmkeps by simp
      then have "([] @ cs) \<in> BHALF mid cs rep \<rightarrow> BHalf (bmkeps mid) cs rep"
        by (rule BPosix_BHALF)
      then have "(c # ds) \<in> BHALF mid cs rep \<rightarrow> BHalf (bmkeps mid) cs rep"
        using ds(1) by simp
      then show ?thesis using right(1) ds by simp
    qed
  qed
next
  case (BRESIDUE cs rep)
  have "s \<in> xder c (BRESIDUE cs rep) \<rightarrow> v" by fact
  then have "s \<in> xder_residue c cs rep \<rightarrow> v" by simp
  then obtain ds where ds: "cs = c # ds" "v = BResidue ds rep" "s = ds"
    by (cases cs) (auto elim!: BPosix_elims split: if_splits)
  have "(c # ds) \<in> BRESIDUE (c # ds) rep \<rightarrow> BResidue (c # ds) rep"
    by (rule BPosix_BRESIDUE)
  then show "(c # s) \<in> BRESIDUE cs rep \<rightarrow> binjval (BRESIDUE cs rep) c v"
    using ds by simp
qed

lemma blexer_POSIX:
  assumes "blexer r s = Some v"
  shows "s \<in> r \<rightarrow> v"
  using assms
proof (induct s arbitrary: r v)
  case Nil
  then have "xnullable r" and "v = bmkeps r"
    by (auto split: if_splits)
  then show "[] \<in> r \<rightarrow> v" using BPosix_bmkeps by simp
next
  case (Cons c s)
  then obtain v' where v': "blexer (xder c r) s = Some v'" "v = binjval r c v'"
    by (auto split: option.splits)
  from v'(1) have "s \<in> (xder c r) \<rightarrow> v'" by (rule Cons.hyps)
  then have "(c # s) \<in> r \<rightarrow> binjval r c v'" by (rule BPosix_binjval)
  then show "(c # s) \<in> r \<rightarrow> v" using v'(2) by simp
qed

theorem blexer_POSIX_correctness:
  "blexer r s = Some v \<longleftrightarrow> s \<in> r \<rightarrow> v"
proof
  assume "blexer r s = Some v"
  then show "s \<in> r \<rightarrow> v"
    by (rule blexer_POSIX)
next
  assume pos: "s \<in> r \<rightarrow> v"
  then have "s \<in> BL r"
    by (rule BPosix1(1))
  then obtain w where w: "blexer r s = Some w"
    using blexer_correctness_defined by blast
  then have "s \<in> r \<rightarrow> w"
    by (rule blexer_POSIX)
  then have "w = v"
    using pos by (rule BPosix_determ)
  with w show "blexer r s = Some v"
    by simp
qed

lemma blexer_POSIX_iff:
  "s \<in> BL r \<longleftrightarrow> (\<exists>v. blexer r s = Some v \<and> s \<in> r \<rightarrow> v)"
proof
  assume "s \<in> BL r"
  then obtain v where "blexer r s = Some v" using blexer_correct_None by blast
  then show "\<exists>v. blexer r s = Some v \<and> s \<in> r \<rightarrow> v"
    using blexer_POSIX by blast
next
  assume "\<exists>v. blexer r s = Some v \<and> s \<in> r \<rightarrow> v"
  then show "s \<in> BL r" using BPosix1(1) by blast
qed

end
