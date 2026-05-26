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

section \<open>Generalized Constructor Value Correspondence\<close>

datatype gbval =
  GVBase bval
| GVLeft gbval
| GVRight gbval
| GVBackref4 bval4

fun gflat :: "gbval \<Rightarrow> string"
where
  "gflat (GVBase v) = bflat v"
| "gflat (GVLeft v) = gflat v"
| "gflat (GVRight v) = gflat v"
| "gflat (GVBackref4 v) = bflat4 v"

inductive GPrf :: "gbval \<Rightarrow> gbrexp \<Rightarrow> bool" ("\<Turnstile>g _ : _" [100, 100] 100)
where
  GPrf_base:
    "\<Turnstile>b v : r \<Longrightarrow> \<Turnstile>g (GVBase v) : (GBASE r)"
| GPrf_left:
    "\<Turnstile>g v : r1 \<Longrightarrow> \<Turnstile>g (GVLeft v) : (GALT r1 r2)"
| GPrf_right:
    "\<Turnstile>g v : r2 \<Longrightarrow> \<Turnstile>g (GVRight v) : (GALT r1 r2)"
| GPrf_backref4:
    "BPrf4 v r1 r2 r3 r4 cs \<Longrightarrow>
      \<Turnstile>g (GVBackref4 v) : (GBACKREF4 r1 r2 r3 r4 cs)"

inductive_cases GPrf_elims:
  "\<Turnstile>g v : r"

fun gmkeps :: "gbrexp \<Rightarrow> gbval"
where
  "gmkeps (GBASE r) = GVBase (bmkeps r)"
| "gmkeps (GALT r1 r2) =
    (if gnullable r1 then GVLeft (gmkeps r1) else GVRight (gmkeps r2))"
| "gmkeps (GBACKREF4 r1 r2 r3 r4 cs) =
    GVBackref4 (BBackref4 (bmkeps r1) (bmkeps r2) (bmkeps r3) (bmkeps r4) cs)"

definition gbackref4_from_tail :: "bval \<Rightarrow> bval \<Rightarrow> string \<Rightarrow> bval \<Rightarrow> gbval"
where
  "gbackref4_from_tail v1 v2 cs tail =
    (case tail of
      BSeq v3 (BSeq res v4) \<Rightarrow> GVBackref4 (BBackref4 v1 v2 v3 v4 cs)
    | _ \<Rightarrow> GVBase BVoid)"

primrec ginjval :: "gbrexp \<Rightarrow> char \<Rightarrow> gbval \<Rightarrow> gbval"
where
  "ginjval (GBASE r) c v =
    (case v of
      GVBase v' \<Rightarrow> GVBase (binjval r c v')
    | _ \<Rightarrow> GVBase BVoid)"
| "ginjval (GALT r1 r2) c v =
    (case v of
      GVLeft v' \<Rightarrow> GVLeft (ginjval r1 c v')
    | GVRight v' \<Rightarrow> GVRight (ginjval r2 c v')
    | _ \<Rightarrow> GVBase BVoid)"
| "ginjval (GBACKREF4 r1 r2 r3 r4 cs) c v =
    (case v of
      GVBackref4 (BBackref4 v1 v2 v3 v4 cs') \<Rightarrow>
        GVBackref4 (BBackref4 (binjval r1 c v1) v2 v3 v4 cs)
    | GVLeft (GVBackref4 (BBackref4 v1 v2 v3 v4 cs')) \<Rightarrow>
        GVBackref4 (BBackref4 (binjval r1 c v1) v2 v3 v4 cs)
    | GVRight (GVBackref4 (BBackref4 v1 v2 v3 v4 cs')) \<Rightarrow>
        GVBackref4 (BBackref4 (bmkeps r1) (binjval r2 c v2) v3 v4 cs)
    | GVRight (GVLeft (GVBackref4 (BBackref4 v1 v2 v3 v4 cs'))) \<Rightarrow>
        GVBackref4 (BBackref4 (bmkeps r1) (binjval r2 c v2) v3 v4 cs)
    | GVRight (GVRight (GVBase tail)) \<Rightarrow>
        gbackref4_from_tail (bmkeps r1) (bmkeps r2) cs
          (binjval (gtail4 r3 (rev cs) r4) c tail)
    | _ \<Rightarrow> GVBase BVoid)"

lemma gbackref4_from_tail_flat:
  assumes "BPrf tail (gtail4 r3 (rev cs) r4)"
    and "bflat v1 = []"
    and "bflat v2 = []"
  shows "gflat (gbackref4_from_tail v1 v2 cs tail) = bflat tail"
  using assms
  unfolding gbackref4_from_tail_def gtail4_def
  by (auto elim!: BPrf_elims)

lemma gbackref4_from_tail_GPrf:
  assumes "\<Turnstile>b v1 : r1"
    and "\<Turnstile>b v2 : r2"
    and "BPrf tail (gtail4 r3 (rev cs) r4)"
  shows "GPrf (gbackref4_from_tail v1 v2 cs tail) (GBACKREF4 r1 r2 r3 r4 cs)"
  using assms
  unfolding gbackref4_from_tail_def gtail4_def
  by (auto intro!: GPrf.intros BPrf4.intros elim!: BPrf_elims)

lemma gbackref4_from_xder_tail_flat:
  assumes "BPrf tail (xder c (gtail4 r3 (rev cs) r4))"
    and "xnullable r1"
    and "xnullable r2"
  shows "gflat (gbackref4_from_tail (bmkeps r1) (bmkeps r2) cs
    (binjval (gtail4 r3 (rev cs) r4) c tail)) = c # bflat tail"
proof -
  define ft where "ft = binjval (gtail4 r3 (rev cs) r4) c tail"
  have tail_prf: "\<Turnstile>b ft : gtail4 r3 (rev cs) r4"
    unfolding ft_def using assms(1) by (rule binjval_BPrf)
  have flat: "bflat ft = c # bflat tail"
    unfolding ft_def using assms(1) by (rule binjval_flat)
  have empty1: "bflat (bmkeps r1) = []"
    using assms(2) by (rule bmkeps_flat)
  have empty2: "bflat (bmkeps r2) = []"
    using assms(3) by (rule bmkeps_flat)
  show ?thesis
    using gbackref4_from_tail_flat[OF tail_prf empty1 empty2] flat
    unfolding ft_def by simp
qed

lemma gbackref4_from_xder_tail_GPrf:
  assumes "BPrf tail (xder c (gtail4 r3 (rev cs) r4))"
    and "xnullable r1"
    and "xnullable r2"
  shows "GPrf (gbackref4_from_tail (bmkeps r1) (bmkeps r2) cs
    (binjval (gtail4 r3 (rev cs) r4) c tail)) (GBACKREF4 r1 r2 r3 r4 cs)"
  using assms
  by (auto intro!: gbackref4_from_tail_GPrf bmkeps_BPrf binjval_BPrf)

lemma gmkeps_flat:
  assumes "gnullable r"
  shows "gflat (gmkeps r) = []"
  using assms
  by (induct r) (auto simp add: bmkeps_flat)

lemma gmkeps_GPrf:
  assumes "gnullable r"
  shows "\<Turnstile>g gmkeps r : r"
  using assms
  by (induct r) (auto intro: GPrf.intros BPrf4.intros bmkeps_BPrf)

lemma ginjval_flat:
  assumes "GPrf v (gxder c r)"
  shows "gflat (ginjval r c v) = c # gflat v"
  using assms
proof (induct r arbitrary: c v)
  case (GBASE r)
  then show ?case
    by (auto elim!: GPrf_elims simp add: binjval_flat)
next
  case (GALT r1 r2)
  show ?case
  proof (cases v)
    case (GVLeft v1)
    then have "\<Turnstile>g v1 : gxder c r1"
      using GALT.prems by (auto elim: GPrf_elims)
    then show ?thesis
      using GALT(1) GVLeft by simp
  next
    case (GVRight v2)
    then have "\<Turnstile>g v2 : gxder c r2"
      using GALT.prems by (auto elim: GPrf_elims)
    then show ?thesis
      using GALT(2) GVRight by simp
  qed (use GALT.prems in \<open>auto elim: GPrf_elims\<close>)
next
  case (GBACKREF4 r1 r2 r3 r4 cs)
  show ?case
  proof (cases "xnullable r1")
    case False
    with GBACKREF4.prems show ?thesis
      by (auto elim!: GPrf_elims BPrf4_elims simp add: binjval_flat)
  next
    case r1_null: True
    show ?thesis
    proof (cases "xnullable r2")
      case False
      with r1_null GBACKREF4.prems show ?thesis
        by (auto elim!: GPrf_elims BPrf4_elims BPrf_elims
            simp add: binjval_flat bmkeps_flat)
    next
      case r2_null: True
      with r1_null GBACKREF4.prems show ?thesis
        by (auto elim!: GPrf_elims BPrf4_elims BPrf_elims
            simp add: binjval_flat bmkeps_flat gbackref4_from_xder_tail_flat)
    qed
  qed
qed

lemma ginjval_GPrf:
  assumes "GPrf v (gxder c r)"
  shows "GPrf (ginjval r c v) r"
  using assms
proof (induct r arbitrary: c v)
  case (GBASE r)
  then show ?case
    by (auto intro!: GPrf.intros binjval_BPrf elim!: GPrf_elims)
next
  case (GALT r1 r2)
  show ?case
  proof (cases v)
    case (GVLeft v1)
    then have "\<Turnstile>g v1 : gxder c r1"
      using GALT.prems by (auto elim: GPrf_elims)
    then show ?thesis
      using GALT(1) GVLeft by (auto intro!: GPrf.intros)
  next
    case (GVRight v2)
    then have "\<Turnstile>g v2 : gxder c r2"
      using GALT.prems by (auto elim: GPrf_elims)
    then show ?thesis
      using GALT(2) GVRight by (auto intro!: GPrf.intros)
  qed (use GALT.prems in \<open>auto elim: GPrf_elims\<close>)
next
  case (GBACKREF4 r1 r2 r3 r4 cs)
  show ?case
  proof (cases "xnullable r1")
    case False
    with GBACKREF4.prems show ?thesis
      by (auto intro!: GPrf.intros BPrf4.intros binjval_BPrf
          elim!: GPrf_elims BPrf4_elims)
  next
    case r1_null: True
    show ?thesis
    proof (cases "xnullable r2")
      case False
      with r1_null GBACKREF4.prems show ?thesis
        by (auto intro!: GPrf.intros BPrf4.intros bmkeps_BPrf binjval_BPrf
            elim!: GPrf_elims BPrf4_elims)
    next
      case r2_null: True
      with r1_null GBACKREF4.prems show ?thesis
        by (auto intro!: GPrf.intros BPrf4.intros bmkeps_BPrf binjval_BPrf
            gbackref4_from_xder_tail_GPrf
            elim!: GPrf_elims BPrf4_elims)
    qed
  qed
qed

lemma GBL_flat_GPrf1:
  assumes "\<Turnstile>g v : r"
  shows "gflat v \<in> GBL r"
  using assms
  by (induct rule: GPrf.induct) (auto intro: BL_flat_BPrf1 backref_lang4_flat_BPrf4_1)

lemma GBL_flat_GPrf2:
  assumes "s \<in> GBL r"
  shows "\<exists>v. \<Turnstile>g v : r \<and> gflat v = s"
  using assms
proof (induct r arbitrary: s)
  case (GBASE r)
  then have "s \<in> BL r"
    by simp
  then obtain v where "\<Turnstile>b v : r" "bflat v = s"
    using BL_flat_BPrf2 by blast
  then show ?case
    by (intro exI[of _ "GVBase v"]) (auto intro: GPrf.intros)
next
  case (GALT r1 r2)
  then show ?case
  proof (cases "s \<in> GBL r1")
    case True
    then obtain v where "\<Turnstile>g v : r1" "gflat v = s"
      using GALT(1) by blast
    then show ?thesis
      by (intro exI[of _ "GVLeft v"]) (auto intro: GPrf.intros)
  next
    case False
    with GALT(3) have "s \<in> GBL r2"
      by simp
    then obtain v where "\<Turnstile>g v : r2" "gflat v = s"
      using GALT(2) by blast
    then show ?thesis
      by (intro exI[of _ "GVRight v"]) (auto intro: GPrf.intros)
  qed
next
  case (GBACKREF4 r1 r2 r3 r4 cs)
  then have "s \<in> backref_lang4 (BL r1) (BL r2) (BL r3) (BL r4) cs"
    by simp
  then obtain v where "BPrf4 v r1 r2 r3 r4 cs" "bflat4 v = s"
    using backref_lang4_flat_BPrf4_2 by blast
  then show ?case
    by (intro exI[of _ "GVBackref4 v"]) (auto intro: GPrf.intros)
qed

theorem GBL_flat_GPrf:
  "GBL r = {gflat v | v. \<Turnstile>g v : r}"
  using GBL_flat_GPrf1 GBL_flat_GPrf2 by blast

theorem gxders_GBL_flat_GPrf:
  "GBL (gxders r s) = Ders s {gflat v | v. \<Turnstile>g v : r}"
proof -
  have "GBL (gxders r s) = Ders s (GBL r)"
    by (simp add: gxders_correctness)
  also have "... = Ders s {gflat v | v. \<Turnstile>g v : r}"
    by (simp add: Ders_def GBL_flat_GPrf)
  finally show ?thesis .
qed

end
