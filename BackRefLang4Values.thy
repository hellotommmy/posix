theory BackRefLang4Values
  imports BackRefValues BackRefLang4Pilot
begin

section \<open>Generalized Backreference Value Blueprint\<close>

datatype bval4 =
  BBackref4 bval bval bval bval string

fun bflat4 :: "bval4 \<Rightarrow> string"
where
  "bflat4 (BBackref4 v1 v2 v3 v4 cs) =
    bflat v1 @ bflat v2 @ bflat v3 @ rev cs @ bflat v2 @ bflat v4"

inductive BPrf4 ::
  "bval4 \<Rightarrow> brexp \<Rightarrow> brexp \<Rightarrow> brexp \<Rightarrow> brexp \<Rightarrow> string \<Rightarrow> bool"
where
  BPrf4_backref:
    "\<lbrakk>\<Turnstile>b v1 : r1; \<Turnstile>b v2 : r2; \<Turnstile>b v3 : r3; \<Turnstile>b v4 : r4\<rbrakk> \<Longrightarrow>
      BPrf4 (BBackref4 v1 v2 v3 v4 cs) r1 r2 r3 r4 cs"

inductive_cases BPrf4_elims:
  "BPrf4 v r1 r2 r3 r4 cs"

lemma backref_lang4_flat_BPrf4_1:
  assumes "BPrf4 v r1 r2 r3 r4 cs"
  shows "bflat4 v \<in> backref_lang4 (BL r1) (BL r2) (BL r3) (BL r4) cs"
proof -
  from assms obtain v1 v2 v3 v4 where v:
    "v = BBackref4 v1 v2 v3 v4 cs"
    "\<Turnstile>b v1 : r1" "\<Turnstile>b v2 : r2" "\<Turnstile>b v3 : r3" "\<Turnstile>b v4 : r4"
    by (auto elim: BPrf4_elims)
  have "bflat v1 @ bflat v2 @ bflat v3 @ rev cs @ bflat v2 @ bflat v4
    \<in> backref_lang4 (BL r1) (BL r2) (BL r3) (BL r4) cs"
    using v(2-5) by (intro backref_lang4I BL_flat_BPrf1)
  then show ?thesis
    using v(1) by simp
qed

lemma backref_lang4_flat_BPrf4_2:
  assumes "s \<in> backref_lang4 (BL r1) (BL r2) (BL r3) (BL r4) cs"
  shows "\<exists>v. BPrf4 v r1 r2 r3 r4 cs \<and> bflat4 v = s"
proof -
  from assms obtain s1 s2 s3 s4 where parts:
    "s1 \<in> BL r1" "s2 \<in> BL r2" "s3 \<in> BL r3" "s4 \<in> BL r4"
    "s = s1 @ s2 @ s3 @ rev cs @ s2 @ s4"
    by (auto simp add: backref_lang4_def)
  from parts obtain v1 where v1: "\<Turnstile>b v1 : r1" "bflat v1 = s1"
    using BL_flat_BPrf2 by blast
  from parts obtain v2 where v2: "\<Turnstile>b v2 : r2" "bflat v2 = s2"
    using BL_flat_BPrf2 by blast
  from parts obtain v3 where v3: "\<Turnstile>b v3 : r3" "bflat v3 = s3"
    using BL_flat_BPrf2 by blast
  from parts obtain v4 where v4: "\<Turnstile>b v4 : r4" "bflat v4 = s4"
    using BL_flat_BPrf2 by blast
  show ?thesis
    using parts v1 v2 v3 v4
    by (intro exI[of _ "BBackref4 v1 v2 v3 v4 cs"]) (auto intro: BPrf4.intros)
qed

theorem backref_lang4_flat_BPrf4:
  "backref_lang4 (BL r1) (BL r2) (BL r3) (BL r4) cs =
    {bflat4 v | v. BPrf4 v r1 r2 r3 r4 cs}"
  using backref_lang4_flat_BPrf4_1 backref_lang4_flat_BPrf4_2 by blast

corollary backref_lang_flat_BPrf4_special:
  "backref_lang (BL r) (BL mid) cs =
    {bflat4 v | v. BPrf4 v BONE r mid BONE cs}"
  using backref_lang4_flat_BPrf4[of BONE r mid BONE cs]
  by (simp add: backref_lang_as_backref_lang4)

section \<open>Bridge to Generalized Constructor Pilot\<close>

theorem GBACKREF4_flat_BPrf4:
  "GBL (GBACKREF4 r1 r2 r3 r4 cs) =
    {bflat4 v | v. BPrf4 v r1 r2 r3 r4 cs}"
  by (simp add: backref_lang4_flat_BPrf4)

theorem gxders_GBACKREF4_flat_BPrf4:
  "GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) =
    Ders s {bflat4 v | v. BPrf4 v r1 r2 r3 r4 cs}"
proof -
  have "GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) =
    Ders s (GBL (GBACKREF4 r1 r2 r3 r4 cs))"
    by (simp add: gxders_correctness)
  also have "... = Ders s {bflat4 v | v. BPrf4 v r1 r2 r3 r4 cs}"
    by (simp add: Ders_def backref_lang4_flat_BPrf4)
  finally show ?thesis .
qed

end
