theory BackRefBoundedBlueprint
  imports BackRefLang4Pilot
begin

section \<open>Bounded-Fragment Statement Blueprint\<close>

definition bounded_language :: "nat \<Rightarrow> string set \<Rightarrow> bool"
where
  "bounded_language n A \<longleftrightarrow> (\<forall>s\<in>A. length s \<le> n)"

definition finite_left_quotients :: "string set \<Rightarrow> bool"
where
  "finite_left_quotients A \<longleftrightarrow> finite {Ders s A | s. True}"

definition suffix_closure :: "string set \<Rightarrow> string set"
where
  "suffix_closure A = {t. \<exists>w\<in>A. suffix t w}"

definition finite_BL_derivatives :: "brexp \<Rightarrow> bool"
where
  "finite_BL_derivatives r \<longleftrightarrow> finite {BL (xders r s) | s. True}"

definition finite_GBL_derivatives :: "gbrexp \<Rightarrow> bool"
where
  "finite_GBL_derivatives r \<longleftrightarrow> finite {GBL (gxders r s) | s. True}"

definition BL_bounded :: "nat \<Rightarrow> brexp \<Rightarrow> bool"
where
  "BL_bounded n r \<longleftrightarrow> bounded_language n (BL r)"

definition GBL_bounded :: "nat \<Rightarrow> gbrexp \<Rightarrow> bool"
where
  "GBL_bounded n r \<longleftrightarrow> bounded_language n (GBL r)"

definition bounded_backref4_components ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> brexp \<Rightarrow> brexp \<Rightarrow> brexp \<Rightarrow> brexp \<Rightarrow> bool"
where
  "bounded_backref4_components n1 n2 n3 n4 r1 r2 r3 r4 \<longleftrightarrow>
    BL_bounded n1 r1 \<and> BL_bounded n2 r2 \<and>
    BL_bounded n3 r3 \<and> BL_bounded n4 r4"

lemma bounded_language_mono:
  assumes "bounded_language n A" "n \<le> m"
  shows "bounded_language m A"
  using assms by (auto simp add: bounded_language_def)

lemma bounded_language_finite:
  assumes "bounded_language n A"
  shows "finite A"
proof -
  have "A \<subseteq> {s :: string. set s \<subseteq> (UNIV :: char set) \<and> length s \<le> n}"
    using assms by (auto simp add: bounded_language_def)
  moreover have "finite {s :: string. set s \<subseteq> (UNIV :: char set) \<and> length s \<le> n}"
    by (rule finite_lists_length_le) simp
  ultimately show ?thesis
    by (rule finite_subset)
qed

lemma suffix_closure_eq_UN:
  "suffix_closure A = (\<Union>w\<in>A. set (suffixes w))"
  by (auto simp add: suffix_closure_def)

lemma finite_suffix_closure:
  assumes "finite A"
  shows "finite (suffix_closure A)"
  using assms by (simp add: suffix_closure_eq_UN)

lemma Ders_subset_suffix_closure:
  "Ders s A \<subseteq> suffix_closure A"
  by (auto simp add: Ders_def suffix_closure_def suffix_def)

lemma finite_left_quotients_if_finite_language:
  assumes "finite A"
  shows "finite_left_quotients A"
proof -
  have suffix_fin: "finite (suffix_closure A)"
    using assms by (rule finite_suffix_closure)
  have quotient_sub: "{Ders s A | s. True} \<subseteq> Pow (suffix_closure A)"
    using Ders_subset_suffix_closure by blast
  have "finite {Ders s A | s. True}"
    using finite_subset[OF quotient_sub] suffix_fin by simp
  then show ?thesis
    by (simp add: finite_left_quotients_def)
qed

lemma finite_left_quotients_if_bounded_language:
  assumes "bounded_language n A"
  shows "finite_left_quotients A"
  using assms
  by (intro finite_left_quotients_if_finite_language bounded_language_finite)

lemma Ders_append:
  "Ders t (Ders s A) = Ders (s @ t) A"
  by (auto simp add: Ders_def append_assoc)

lemma left_quotient_family_Ders_subset:
  "{Ders t (Ders s A) | t. True} \<subseteq> {Ders u A | u. True}"
  by (auto simp add: Ders_append)

lemma finite_left_quotient_family_Ders:
  assumes "finite_left_quotients A"
  shows "finite {Ders t (Ders s A) | t. True}"
proof -
  have quotient_fin: "finite {Ders u A | u. True}"
    using assms by (simp add: finite_left_quotients_def)
  show ?thesis
    using finite_subset[OF left_quotient_family_Ders_subset quotient_fin] .
qed

lemma left_quotient_family_Ders_card_le:
  assumes "finite_left_quotients A"
  shows "card {Ders t (Ders s A) | t. True} \<le> card {Ders u A | u. True}"
proof -
  have quotient_fin: "finite {Ders u A | u. True}"
    using assms by (simp add: finite_left_quotients_def)
  show ?thesis
    by (rule card_mono[OF quotient_fin left_quotient_family_Ders_subset])
qed

lemma finite_left_quotients_Ders:
  assumes "finite_left_quotients A"
  shows "finite_left_quotients (Ders s A)"
proof -
  have quotient_sub: "{Ders t (Ders s A) | t. True} \<subseteq> {Ders u A | u. True}"
    by (auto simp add: Ders_append)
  have quotient_fin: "finite {Ders u A | u. True}"
    using assms by (simp add: finite_left_quotients_def)
  have "finite {Ders t (Ders s A) | t. True}"
    using finite_subset[OF quotient_sub quotient_fin] .
  then show ?thesis
    by (simp add: finite_left_quotients_def)
qed

lemma finite_BL_derivatives_if_left_quotients:
  assumes "finite_left_quotients (BL r)"
  shows "finite_BL_derivatives r"
proof -
  have "{BL (xders r s) | s. True} = {Ders s (BL r) | s. True}"
    by (auto simp add: xders_correctness)
  then show ?thesis
    using assms by (simp add: finite_BL_derivatives_def finite_left_quotients_def)
qed

lemma finite_GBL_derivatives_if_left_quotients:
  assumes "finite_left_quotients (GBL r)"
  shows "finite_GBL_derivatives r"
proof -
  have "{GBL (gxders r s) | s. True} = {Ders s (GBL r) | s. True}"
    by (auto simp add: gxders_correctness)
  then show ?thesis
    using assms by (simp add: finite_GBL_derivatives_def finite_left_quotients_def)
qed

lemma finite_BL_derivatives_iff_left_quotients:
  "finite_BL_derivatives r \<longleftrightarrow> finite_left_quotients (BL r)"
proof -
  have "{BL (xders r s) | s. True} = {Ders s (BL r) | s. True}"
    by (auto simp add: xders_correctness)
  then show ?thesis
    by (simp add: finite_BL_derivatives_def finite_left_quotients_def)
qed

lemma finite_GBL_derivatives_iff_left_quotients:
  "finite_GBL_derivatives r \<longleftrightarrow> finite_left_quotients (GBL r)"
proof -
  have "{GBL (gxders r s) | s. True} = {Ders s (GBL r) | s. True}"
    by (auto simp add: gxders_correctness)
  then show ?thesis
    by (simp add: finite_GBL_derivatives_def finite_left_quotients_def)
qed

lemma finite_BL_derivatives_xders:
  assumes "finite_BL_derivatives r"
  shows "finite_BL_derivatives (xders r s)"
proof -
  have "finite_left_quotients (BL r)"
    using assms by (simp add: finite_BL_derivatives_iff_left_quotients)
  then have "finite_left_quotients (Ders s (BL r))"
    by (rule finite_left_quotients_Ders)
  then have "finite_left_quotients (BL (xders r s))"
    by (simp add: xders_correctness)
  then show ?thesis
    by (simp add: finite_BL_derivatives_iff_left_quotients)
qed

lemma finite_GBL_derivatives_gxders:
  assumes "finite_GBL_derivatives r"
  shows "finite_GBL_derivatives (gxders r s)"
proof -
  have "finite_left_quotients (GBL r)"
    using assms by (simp add: finite_GBL_derivatives_iff_left_quotients)
  then have "finite_left_quotients (Ders s (GBL r))"
    by (rule finite_left_quotients_Ders)
  then have "finite_left_quotients (GBL (gxders r s))"
    by (simp add: gxders_correctness)
  then show ?thesis
    by (simp add: finite_GBL_derivatives_iff_left_quotients)
qed

lemma BL_residual_derivative_family_subset:
  "{BL (xders (xders r s) t) | t. True} \<subseteq> {BL (xders r u) | u. True}"
proof
  fix A
  assume "A \<in> {BL (xders (xders r s) t) | t. True}"
  then obtain t where "A = BL (xders (xders r s) t)"
    by blast
  then have "A = BL (xders r (s @ t))"
    by (simp add: xders_append)
  then show "A \<in> {BL (xders r u) | u. True}"
    by blast
qed

lemma GBL_residual_derivative_family_subset:
  "{GBL (gxders (gxders r s) t) | t. True} \<subseteq> {GBL (gxders r u) | u. True}"
proof
  fix A
  assume "A \<in> {GBL (gxders (gxders r s) t) | t. True}"
  then obtain t where "A = GBL (gxders (gxders r s) t)"
    by blast
  then have "A = GBL (gxders r (s @ t))"
    by (simp add: gxders_append)
  then show "A \<in> {GBL (gxders r u) | u. True}"
    by blast
qed

lemma finite_BL_residual_derivative_family:
  assumes "finite_BL_derivatives r"
  shows "finite {BL (xders (xders r s) t) | t. True}"
proof -
  have fin: "finite {BL (xders r u) | u. True}"
    using assms by (simp add: finite_BL_derivatives_def)
  show ?thesis
    using finite_subset[OF BL_residual_derivative_family_subset fin] .
qed

lemma finite_GBL_residual_derivative_family:
  assumes "finite_GBL_derivatives r"
  shows "finite {GBL (gxders (gxders r s) t) | t. True}"
proof -
  have fin: "finite {GBL (gxders r u) | u. True}"
    using assms by (simp add: finite_GBL_derivatives_def)
  show ?thesis
    using finite_subset[OF GBL_residual_derivative_family_subset fin] .
qed

lemma BL_residual_derivative_family_card_le:
  assumes "finite_BL_derivatives r"
  shows "card {BL (xders (xders r s) t) | t. True} \<le>
    card {BL (xders r u) | u. True}"
proof -
  have fin: "finite {BL (xders r u) | u. True}"
    using assms by (simp add: finite_BL_derivatives_def)
  show ?thesis
    by (rule card_mono[OF fin BL_residual_derivative_family_subset])
qed

lemma GBL_residual_derivative_family_card_le:
  assumes "finite_GBL_derivatives r"
  shows "card {GBL (gxders (gxders r s) t) | t. True} \<le>
    card {GBL (gxders r u) | u. True}"
proof -
  have fin: "finite {GBL (gxders r u) | u. True}"
    using assms by (simp add: finite_GBL_derivatives_def)
  show ?thesis
    by (rule card_mono[OF fin GBL_residual_derivative_family_subset])
qed

theorem bounded_BL_finite_derivative_languages:
  assumes "BL_bounded n r"
  shows "finite_BL_derivatives r"
  using assms
  by (auto simp add: BL_bounded_def
      intro: finite_BL_derivatives_if_left_quotients
        finite_left_quotients_if_bounded_language)

theorem bounded_GBL_finite_derivative_languages:
  assumes "GBL_bounded n r"
  shows "finite_GBL_derivatives r"
  using assms
  by (auto simp add: GBL_bounded_def
      intro: finite_GBL_derivatives_if_left_quotients
        finite_left_quotients_if_bounded_language)

lemma bounded_language_Ders:
  assumes "bounded_language n A"
  shows "bounded_language n (Ders s A)"
proof (unfold bounded_language_def, intro ballI)
  fix t
  assume t: "t \<in> Ders s A"
  then have st: "s @ t \<in> A"
    by (simp add: Ders_def)
  have len_st: "length (s @ t) \<le> n"
    using assms st unfolding bounded_language_def by blast
  have "length t \<le> length (s @ t)"
    by simp
  also note len_st
  finally show "length t \<le> n" .
qed

lemma BL_bounded_xders:
  assumes "BL_bounded n r"
  shows "BL_bounded n (xders r s)"
  using assms bounded_language_Ders[of n "BL r" s]
  by (simp add: BL_bounded_def xders_correctness)

lemma GBL_bounded_gxders:
  assumes "GBL_bounded n r"
  shows "GBL_bounded n (gxders r s)"
  using assms bounded_language_Ders[of n "GBL r" s]
  by (simp add: GBL_bounded_def gxders_correctness)

lemma finite_Sequ_language:
  assumes "finite A" "finite B"
  shows "finite (A ;; B)"
proof -
  have "A ;; B = (\<lambda>(s1, s2). s1 @ s2) ` (A \<times> B)"
    by (auto simp add: Sequ_def)
  then show ?thesis
    using assms by simp
qed

lemma finite_backref_lang:
  assumes "finite A" "finite B"
  shows "finite (backref_lang A B cs)"
proof -
  have "backref_lang A B cs =
    (\<lambda>(x, y). x @ y @ rev cs @ x) ` (A \<times> B)"
    by (auto simp add: backref_lang_def)
  then show ?thesis
    using assms by simp
qed

lemma bounded_language_backref_lang:
  assumes "bounded_language n1 A" "bounded_language n2 B"
  shows "bounded_language (n1 + n2 + length cs + n1) (backref_lang A B cs)"
  unfolding bounded_language_def
proof
  fix s
  assume "s \<in> backref_lang A B cs"
  then obtain x y where xy:
    "x \<in> A" "y \<in> B" "s = x @ y @ rev cs @ x"
    by (auto simp add: backref_lang_def)
  have "length x \<le> n1"
    using assms(1) xy(1) by (simp add: bounded_language_def)
  moreover have "length y \<le> n2"
    using assms(2) xy(2) by (simp add: bounded_language_def)
  moreover have "length s = length x + length y + length cs + length x"
    using xy(3) by simp
  ultimately show "length s \<le> n1 + n2 + length cs + n1"
    by linarith
qed

lemma bounded_language_backref_lang4:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
  shows "bounded_language (n1 + n2 + n3 + length cs + n2 + n4)
    (backref_lang4 L1 L2 L3 L4 cs)"
  unfolding bounded_language_def
proof
  fix s
  assume "s \<in> backref_lang4 L1 L2 L3 L4 cs"
  then obtain s1 s2 s3 s4 where parts:
    "s1 \<in> L1" "s2 \<in> L2" "s3 \<in> L3" "s4 \<in> L4"
    "s = s1 @ s2 @ s3 @ rev cs @ s2 @ s4"
    by (auto simp add: backref_lang4_def)
  have "length s1 \<le> n1"
    using assms(1) parts(1) by (simp add: bounded_language_def)
  moreover have "length s2 \<le> n2"
    using assms(2) parts(2) by (simp add: bounded_language_def)
  moreover have "length s3 \<le> n3"
    using assms(3) parts(3) by (simp add: bounded_language_def)
  moreover have "length s4 \<le> n4"
    using assms(4) parts(4) by (simp add: bounded_language_def)
  moreover have "length s = length s1 + length s2 + length s3 + length cs + length s2 + length s4"
    using parts(5) by simp
  ultimately show "length s \<le> n1 + n2 + n3 + length cs + n2 + n4"
    by linarith
qed

theorem finite_components_backref_lang_left_quotients:
  assumes "finite A" "finite B"
  shows "finite_left_quotients (backref_lang A B cs)"
  using assms
  by (intro finite_left_quotients_if_finite_language finite_backref_lang)

theorem bounded_backref_lang_finite_left_quotients:
  assumes "bounded_language n1 A" "bounded_language n2 B"
  shows "finite_left_quotients (backref_lang A B cs)"
proof -
  have "bounded_language (n1 + n2 + length cs + n1) (backref_lang A B cs)"
    using assms by (rule bounded_language_backref_lang)
  then show ?thesis
    by (rule finite_left_quotients_if_bounded_language)
qed

theorem bounded_backref_lang4_finite_left_quotients:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
  shows "finite_left_quotients (backref_lang4 L1 L2 L3 L4 cs)"
proof -
  have "bounded_language (n1 + n2 + n3 + length cs + n2 + n4)
    (backref_lang4 L1 L2 L3 L4 cs)"
    using assms by (rule bounded_language_backref_lang4)
  then show ?thesis
    by (rule finite_left_quotients_if_bounded_language)
qed

theorem bounded_BBACKREF_finite_derivative_languages:
  assumes "BL_bounded n_capture r" "BL_bounded n_mid mid"
  shows "finite_BL_derivatives (BBACKREF r mid cs)"
proof -
  have cap: "bounded_language n_capture (BL r)"
    using assms(1) by (simp add: BL_bounded_def)
  have mid_bound: "bounded_language n_mid (BL mid)"
    using assms(2) by (simp add: BL_bounded_def)
  have "finite_left_quotients (backref_lang (BL r) (BL mid) cs)"
    using cap mid_bound by (rule bounded_backref_lang_finite_left_quotients)
  then have "finite_left_quotients (BL (BBACKREF r mid cs))"
    by simp
  then show ?thesis
    by (rule finite_BL_derivatives_if_left_quotients)
qed

theorem bounded_GBACKREF4_finite_derivative_languages:
  assumes "bounded_backref4_components n1 n2 n3 n4 r1 r2 r3 r4"
  shows "finite_GBL_derivatives (GBACKREF4 r1 r2 r3 r4 cs)"
proof -
  have b1: "bounded_language n1 (BL r1)"
    using assms by (simp add: bounded_backref4_components_def BL_bounded_def)
  have b2: "bounded_language n2 (BL r2)"
    using assms by (simp add: bounded_backref4_components_def BL_bounded_def)
  have b3: "bounded_language n3 (BL r3)"
    using assms by (simp add: bounded_backref4_components_def BL_bounded_def)
  have b4: "bounded_language n4 (BL r4)"
    using assms by (simp add: bounded_backref4_components_def BL_bounded_def)
  have "finite_left_quotients (backref_lang4 (BL r1) (BL r2) (BL r3) (BL r4) cs)"
    using b1 b2 b3 b4 by (rule bounded_backref_lang4_finite_left_quotients)
  then have "finite_left_quotients (GBL (GBACKREF4 r1 r2 r3 r4 cs))"
    by simp
  then show ?thesis
    by (rule finite_GBL_derivatives_if_left_quotients)
qed

section \<open>Syntactic Bounded Fragment\<close>

lemma bounded_language_empty [simp]:
  "bounded_language n {}"
  by (simp add: bounded_language_def)

lemma bounded_language_singleton [simp]:
  "bounded_language (length s) {s}"
  by (simp add: bounded_language_def)

lemma bounded_language_union:
  assumes "bounded_language n A" "bounded_language m B"
  shows "bounded_language (max n m) (A \<union> B)"
  using assms by (auto simp add: bounded_language_def)

lemma bounded_language_Sequ:
  assumes "bounded_language n A" "bounded_language m B"
  shows "bounded_language (n + m) (A ;; B)"
  unfolding bounded_language_def
proof
  fix s
  assume "s \<in> A ;; B"
  then obtain s1 s2 where parts: "s1 \<in> A" "s2 \<in> B" "s = s1 @ s2"
    by (auto simp add: Sequ_def)
  have "length s1 \<le> n"
    using assms(1) parts(1) by (simp add: bounded_language_def)
  moreover have "length s2 \<le> m"
    using assms(2) parts(2) by (simp add: bounded_language_def)
  ultimately show "length s \<le> n + m"
    using parts(3) by simp
qed

lemma bounded_language_pow:
  assumes "bounded_language n A"
  shows "bounded_language (k * n) (A ^^ k)"
proof (induct k)
  case 0
  show ?case
    by (simp add: bounded_language_def)
next
  case (Suc k)
  have tail: "bounded_language (k * n) (A ^^ k)"
    using Suc.hyps .
  have "bounded_language (n + k * n) (A ;; (A ^^ k))"
    by (rule bounded_language_Sequ[OF assms tail])
  then show ?case
    by simp
qed

lemma bounded_language_star_zero:
  assumes "bounded_language 0 A"
  shows "bounded_language 0 (A\<star>)"
  unfolding bounded_language_def
proof
  fix s
  assume s: "s \<in> A\<star>"
  then obtain ss where ss:
    "concat ss = s" "\<forall>t \<in> set ss. t \<in> A \<and> t \<noteq> []"
    using Star_split by blast
  have no_mem: False if "t \<in> set ss" for t
  proof -
    have "t \<in> A" "t \<noteq> []"
      using ss that by auto
    moreover have "length t \<le> 0"
      using assms calculation(1) by (simp add: bounded_language_def)
    ultimately show False
      by (cases t) simp_all
  qed
  have no_set_mem: "t \<notin> set ss" for t
    using no_mem[of t] by blast
  have "ss = []"
  proof (cases ss)
    case Nil
    then show ?thesis
      by simp
  next
    case (Cons t ts)
    then have "t \<in> set ss"
      by simp
    then have False
      using no_set_mem[of t] by simp
    then show ?thesis
      by simp
  qed
  then show "length s \<le> 0"
    using ss by simp
qed

lemma BL_bounded_BZERO [simp]:
  "BL_bounded n BZERO"
  by (simp add: BL_bounded_def bounded_language_def)

lemma BL_bounded_BONE [simp]:
  "BL_bounded 0 BONE"
  by (simp add: BL_bounded_def bounded_language_def)

lemma BL_bounded_BCH [simp]:
  "BL_bounded 1 (BCH c)"
  by (simp add: BL_bounded_def bounded_language_def)

lemma BL_bounded_BALT:
  assumes "BL_bounded n r1" "BL_bounded m r2"
  shows "BL_bounded (max n m) (BALT r1 r2)"
  using assms
  by (auto simp add: BL_bounded_def intro: bounded_language_union)

lemma BL_bounded_BSEQ:
  assumes "BL_bounded n r1" "BL_bounded m r2"
  shows "BL_bounded (n + m) (BSEQ r1 r2)"
  using assms
  by (auto simp add: BL_bounded_def intro: bounded_language_Sequ)

lemma BL_bounded_BSTAR_zero:
  assumes "BL_bounded 0 r"
  shows "BL_bounded 0 (BSTAR r)"
  using assms
  by (auto simp add: BL_bounded_def intro: bounded_language_star_zero)

lemma BL_bounded_BNTIMES:
  assumes "BL_bounded n r"
  shows "BL_bounded (k * n) (BNTIMES r k)"
  using assms
  by (auto simp add: BL_bounded_def intro: bounded_language_pow)

lemma BL_bounded_BBACKREF:
  assumes "BL_bounded n_capture r" "BL_bounded n_mid mid"
  shows "BL_bounded (n_capture + n_mid + length cs + n_capture) (BBACKREF r mid cs)"
  using assms
  by (auto simp add: BL_bounded_def intro: bounded_language_backref_lang)

lemma BL_bounded_BHALF:
  assumes "BL_bounded n mid"
  shows "BL_bounded (n + length cs) (BHALF mid cs rep)"
  using assms
  by (auto simp add: BL_bounded_def intro: bounded_language_Sequ)

lemma BL_bounded_BRESIDUE [simp]:
  "BL_bounded (length cs) (BRESIDUE cs rep)"
  by (simp add: BL_bounded_def)

lemma GBL_bounded_GBASE:
  assumes "BL_bounded n r"
  shows "GBL_bounded n (GBASE r)"
  using assms by (simp add: GBL_bounded_def BL_bounded_def)

lemma GBL_bounded_GALT:
  assumes "GBL_bounded n r1" "GBL_bounded m r2"
  shows "GBL_bounded (max n m) (GALT r1 r2)"
  using assms
  by (auto simp add: GBL_bounded_def intro: bounded_language_union)

lemma GBL_bounded_GBACKREF4:
  assumes "BL_bounded n1 r1"
    and "BL_bounded n2 r2"
    and "BL_bounded n3 r3"
    and "BL_bounded n4 r4"
  shows "GBL_bounded (n1 + n2 + n3 + length cs + n2 + n4)
    (GBACKREF4 r1 r2 r3 r4 cs)"
  using assms
  by (auto simp add: GBL_bounded_def BL_bounded_def
      intro: bounded_language_backref_lang4)

primrec BL_bound :: "brexp \<Rightarrow> nat option"
where
  "BL_bound BZERO = Some 0"
| "BL_bound BONE = Some 0"
| "BL_bound (BCH c) = Some 1"
| "BL_bound (BSEQ r1 r2) =
    (case BL_bound r1 of
      Some n1 \<Rightarrow> (case BL_bound r2 of Some n2 \<Rightarrow> Some (n1 + n2) | None \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "BL_bound (BALT r1 r2) =
    (case BL_bound r1 of
      Some n1 \<Rightarrow> (case BL_bound r2 of Some n2 \<Rightarrow> Some (max n1 n2) | None \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "BL_bound (BSTAR r) =
    (case BL_bound r of Some n \<Rightarrow> if n = 0 then Some 0 else None | None \<Rightarrow> None)"
| "BL_bound (BNTIMES r k) =
    (case BL_bound r of Some n \<Rightarrow> Some (k * n) | None \<Rightarrow> None)"
| "BL_bound (BBACKREF r mid cs) =
    (case BL_bound r of
      Some n_capture \<Rightarrow>
        (case BL_bound mid of
          Some n_mid \<Rightarrow> Some (n_capture + n_mid + length cs + n_capture)
        | None \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "BL_bound (BHALF mid cs rep) =
    (case BL_bound mid of Some n \<Rightarrow> Some (n + length cs) | None \<Rightarrow> None)"
| "BL_bound (BRESIDUE cs rep) = Some (length cs)"

primrec GBL_bound :: "gbrexp \<Rightarrow> nat option"
where
  "GBL_bound (GBASE r) = BL_bound r"
| "GBL_bound (GALT r1 r2) =
    (case GBL_bound r1 of
      Some n1 \<Rightarrow> (case GBL_bound r2 of Some n2 \<Rightarrow> Some (max n1 n2) | None \<Rightarrow> None)
    | None \<Rightarrow> None)"
| "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    (case BL_bound r1 of
      Some n1 \<Rightarrow>
        (case BL_bound r2 of
          Some n2 \<Rightarrow>
            (case BL_bound r3 of
              Some n3 \<Rightarrow>
                (case BL_bound r4 of
                  Some n4 \<Rightarrow> Some (n1 + n2 + n3 + length cs + n2 + n4)
                | None \<Rightarrow> None)
            | None \<Rightarrow> None)
        | None \<Rightarrow> None)
    | None \<Rightarrow> None)"

lemma BL_bound_sound:
  assumes "BL_bound r = Some n"
  shows "BL_bounded n r"
  using assms
proof (induct r arbitrary: n)
  case BZERO
  then show ?case
    by simp
next
  case BONE
  then show ?case
    by (auto simp add: BL_bounded_def bounded_language_def)
next
  case (BCH c)
  then show ?case
    by (auto simp add: BL_bounded_def bounded_language_def)
next
  case (BSEQ r1 r2)
  then show ?case
    by (auto split: option.splits intro: BL_bounded_BSEQ)
next
  case (BALT r1 r2)
  then show ?case
    by (auto split: option.splits intro: BL_bounded_BALT)
next
  case (BSTAR r)
  then show ?case
    by (auto split: option.splits if_splits intro: BL_bounded_BSTAR_zero)
next
  case (BNTIMES r k)
  then show ?case
    by (auto split: option.splits intro: BL_bounded_BNTIMES)
next
  case (BBACKREF r mid cs)
  then show ?case
    by (auto split: option.splits intro: BL_bounded_BBACKREF)
next
  case (BHALF mid cs rep)
  then show ?case
    by (auto split: option.splits intro: BL_bounded_BHALF)
next
  case (BRESIDUE cs rep)
  then show ?case
    by (auto simp add: BL_bounded_def bounded_language_def)
qed

lemma GBL_bound_sound:
  assumes "GBL_bound r = Some n"
  shows "GBL_bounded n r"
  using assms
proof (induct r arbitrary: n)
  case (GBASE r)
  then show ?case
    using BL_bound_sound by (auto intro: GBL_bounded_GBASE)
next
  case (GALT r1 r2)
  then show ?case
    by (auto split: option.splits intro: GBL_bounded_GALT)
next
  case (GBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
    using BL_bound_sound
    by (auto split: option.splits intro: GBL_bounded_GBACKREF4)
qed

lemma BL_bound_xder_residue_defined:
  "\<exists>n. BL_bound (xder_residue c cs rep) = Some n"
  by (cases cs) simp_all

lemma BL_bound_xder_defined:
  assumes "BL_bound r = Some n"
  shows "\<exists>m. BL_bound (xder c r) = Some m"
  using assms
proof (induct r arbitrary: n c)
  case BZERO
  then show ?case
    by simp
next
  case BONE
  then show ?case
    by simp
next
  case (BCH d)
  then show ?case
    by simp
next
  case (BSEQ r1 r2)
  then obtain n1 n2 where bounds:
    "BL_bound r1 = Some n1" "BL_bound r2 = Some n2"
    by (auto split: option.splits)
  then obtain m1 where d1: "BL_bound (xder c r1) = Some m1"
    using BSEQ.hyps(1) by blast
  from bounds obtain m2 where d2: "BL_bound (xder c r2) = Some m2"
    using BSEQ.hyps(2) by blast
  show ?case
    using bounds d1 d2 by (auto split: if_splits)
next
  case (BALT r1 r2)
  then obtain n1 n2 where bounds:
    "BL_bound r1 = Some n1" "BL_bound r2 = Some n2"
    by (auto split: option.splits)
  then obtain m1 where d1: "BL_bound (xder c r1) = Some m1"
    using BALT.hyps(1) by blast
  from bounds obtain m2 where d2: "BL_bound (xder c r2) = Some m2"
    using BALT.hyps(2) by blast
  show ?case
    using d1 d2 by simp
next
  case (BSTAR r)
  then obtain n0 where bound: "BL_bound r = Some n0" "n0 = 0"
    by (auto split: option.splits if_splits)
  then obtain m where d: "BL_bound (xder c r) = Some m"
    using BSTAR.hyps by blast
  show ?case
    using bound d by simp
next
  case (BNTIMES r k)
  show ?case
  proof (cases k)
    case 0
    then show ?thesis
      by simp
  next
    case (Suc k')
    from BNTIMES.prems obtain n0 where bound: "BL_bound r = Some n0"
      by (auto split: option.splits)
    then obtain m where d: "BL_bound (xder c r) = Some m"
      using BNTIMES.hyps by blast
    show ?thesis
      using Suc bound d by simp
  qed
next
  case (BBACKREF r mid cs)
  then obtain n_capture n_mid where bounds:
    "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
    by (auto split: option.splits)
  then obtain m_capture where d_capture: "BL_bound (xder c r) = Some m_capture"
    using BBACKREF.hyps(1) by blast
  from bounds obtain m_mid where d_mid: "BL_bound (xder c mid) = Some m_mid"
    using BBACKREF.hyps(2) by blast
  obtain m_res where d_res: "BL_bound (xder_residue c (rev cs) (rev cs)) = Some m_res"
    using BL_bound_xder_residue_defined by blast
  show ?case
    using bounds d_capture d_mid d_res by (auto split: if_splits)
next
  case (BHALF mid cs rep)
  then obtain n_mid where bound: "BL_bound mid = Some n_mid"
    by (auto split: option.splits)
  then obtain m_mid where d_mid: "BL_bound (xder c mid) = Some m_mid"
    using BHALF.hyps by blast
  obtain m_res where d_res: "BL_bound (xder_residue c cs rep) = Some m_res"
    using BL_bound_xder_residue_defined by blast
  show ?case
    using bound d_mid d_res by (auto split: if_splits)
next
  case (BRESIDUE cs rep)
  show ?case
    by (cases cs) simp_all
qed

lemma GBL_bound_gxder_defined:
  assumes "GBL_bound r = Some n"
  shows "\<exists>m. GBL_bound (gxder c r) = Some m"
  using assms
proof (induct r arbitrary: n c)
  case (GBASE r)
  then show ?case
    using BL_bound_xder_defined by simp
next
  case (GALT r1 r2)
  then obtain n1 n2 where bounds:
    "GBL_bound r1 = Some n1" "GBL_bound r2 = Some n2"
    by (auto split: option.splits)
  then obtain m1 where d1: "GBL_bound (gxder c r1) = Some m1"
    using GALT.hyps(1) by blast
  from bounds obtain m2 where d2: "GBL_bound (gxder c r2) = Some m2"
    using GALT.hyps(2) by blast
  show ?case
    using d1 d2 by simp
next
  case (GBACKREF4 r1 r2 r3 r4 cs)
  then obtain n1 n2 n3 n4 where bounds:
    "BL_bound r1 = Some n1" "BL_bound r2 = Some n2"
    "BL_bound r3 = Some n3" "BL_bound r4 = Some n4"
    by (auto split: option.splits)
  then obtain m1 where d1: "BL_bound (xder c r1) = Some m1"
    using BL_bound_xder_defined by blast
  from bounds obtain m2 where d2: "BL_bound (xder c r2) = Some m2"
    using BL_bound_xder_defined by blast
  from bounds obtain n_tail where tail_bound:
    "BL_bound (gtail4 r3 (rev cs) r4) = Some n_tail"
    by (auto simp add: gtail4_def)
  then obtain m_tail where d_tail:
    "BL_bound (xder c (gtail4 r3 (rev cs) r4)) = Some m_tail"
    using BL_bound_xder_defined by blast
  show ?case
    using bounds d1 d2 d_tail by (auto simp add: Let_def split: if_splits)
qed

theorem BL_bound_xders_defined:
  assumes "BL_bound r = Some n"
  shows "\<exists>m. BL_bound (xders r s) = Some m"
  using assms
proof (induct s arbitrary: r n)
  case Nil
  then show ?case
    by (intro exI[of _ n]) simp
next
  case (Cons c s)
  then obtain m where d: "BL_bound (xder c r) = Some m"
    using BL_bound_xder_defined by blast
  show ?case
    using Cons.hyps[OF d] by simp
qed

theorem GBL_bound_gxders_defined:
  assumes "GBL_bound r = Some n"
  shows "\<exists>m. GBL_bound (gxders r s) = Some m"
  using assms
proof (induct s arbitrary: r n)
  case Nil
  then show ?case
    by (intro exI[of _ n]) simp
next
  case (Cons c s)
  then obtain m where d: "GBL_bound (gxder c r) = Some m"
    using GBL_bound_gxder_defined by blast
  show ?case
    using Cons.hyps[OF d] by simp
qed

theorem BL_bound_finite_derivative_languages:
  assumes "BL_bound r = Some n"
  shows "finite_BL_derivatives r"
  using BL_bound_sound[OF assms]
  by (rule bounded_BL_finite_derivative_languages)

theorem GBL_bound_finite_derivative_languages:
  assumes "GBL_bound r = Some n"
  shows "finite_GBL_derivatives r"
  using GBL_bound_sound[OF assms]
  by (rule bounded_GBL_finite_derivative_languages)

theorem BL_bound_xders_finite_derivative_languages:
  assumes "BL_bound r = Some n"
  shows "\<exists>m. BL_bound (xders r s) = Some m \<and> finite_BL_derivatives (xders r s)"
proof -
  obtain m where "BL_bound (xders r s) = Some m"
    using BL_bound_xders_defined[OF assms] by blast
  then show ?thesis
    using BL_bound_finite_derivative_languages by blast
qed

theorem GBL_bound_gxders_finite_derivative_languages:
  assumes "GBL_bound r = Some n"
  shows "\<exists>m. GBL_bound (gxders r s) = Some m \<and> finite_GBL_derivatives (gxders r s)"
proof -
  obtain m where "GBL_bound (gxders r s) = Some m"
    using GBL_bound_gxders_defined[OF assms] by blast
  then show ?thesis
    using GBL_bound_finite_derivative_languages by blast
qed

theorem BL_bound_xders_bounded:
  assumes "BL_bound r = Some n"
  shows "BL_bounded n (xders r s)"
  using BL_bound_sound[OF assms]
  by (rule BL_bounded_xders)

theorem GBL_bound_gxders_bounded:
  assumes "GBL_bound r = Some n"
  shows "GBL_bounded n (gxders r s)"
  using GBL_bound_sound[OF assms]
  by (rule GBL_bounded_gxders)

theorem BL_bound_derivative_family_bounded:
  assumes "BL_bound r = Some n"
  shows "\<forall>A \<in> {BL (xders r s) | s. True}. bounded_language n A"
  using BL_bound_xders_bounded[OF assms]
  by (auto simp add: BL_bounded_def)

theorem GBL_bound_derivative_family_bounded:
  assumes "GBL_bound r = Some n"
  shows "\<forall>A \<in> {GBL (gxders r s) | s. True}. bounded_language n A"
  using GBL_bound_gxders_bounded[OF assms]
  by (auto simp add: GBL_bounded_def)

theorem BL_bound_finite_left_quotients:
  assumes "BL_bound r = Some n"
  shows "finite_left_quotients (BL r)"
  using BL_bound_sound[OF assms]
  by (auto simp add: BL_bounded_def intro: finite_left_quotients_if_bounded_language)

theorem GBL_bound_finite_left_quotients:
  assumes "GBL_bound r = Some n"
  shows "finite_left_quotients (GBL r)"
  using GBL_bound_sound[OF assms]
  by (auto simp add: GBL_bounded_def intro: finite_left_quotients_if_bounded_language)

theorem BL_bound_xders_finite_left_quotients:
  assumes "BL_bound r = Some n"
  shows "finite_left_quotients (BL (xders r s))"
  using BL_bound_xders_bounded[OF assms]
  by (auto simp add: BL_bounded_def intro: finite_left_quotients_if_bounded_language)

theorem GBL_bound_gxders_finite_left_quotients:
  assumes "GBL_bound r = Some n"
  shows "finite_left_quotients (GBL (gxders r s))"
  using GBL_bound_gxders_bounded[OF assms]
  by (auto simp add: GBL_bounded_def intro: finite_left_quotients_if_bounded_language)

theorem BL_bound_BBACKREF_finite_left_quotients:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "finite_left_quotients (BL (BBACKREF r mid cs))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_finite_left_quotients)
qed

theorem GBL_bound_GBACKREF4_finite_left_quotients:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "finite_left_quotients (GBL (GBACKREF4 r1 r2 r3 r4 cs))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_finite_left_quotients)
qed

theorem BL_bound_BBACKREF_xders_finite_left_quotients:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "finite_left_quotients (BL (xders (BBACKREF r mid cs) s))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_xders_finite_left_quotients)
qed

theorem GBL_bound_GBACKREF4_gxders_finite_left_quotients:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "finite_left_quotients (GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_gxders_finite_left_quotients)
qed

theorem BL_bound_BBACKREF_finite_derivative_languages:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "finite_BL_derivatives (BBACKREF r mid cs)"
proof -
  have "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_finite_derivative_languages)
qed

theorem GBL_bound_GBACKREF4_finite_derivative_languages:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "finite_GBL_derivatives (GBACKREF4 r1 r2 r3 r4 cs)"
proof -
  have "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_finite_derivative_languages)
qed

section \<open>Finite Derivative Family Universe\<close>

definition bounded_strings :: "nat \<Rightarrow> string set"
where
  "bounded_strings n = {s. length s \<le> n}"

lemma finite_bounded_strings:
  "finite (bounded_strings n)"
proof -
  have "bounded_strings n =
    {s :: string. set s \<subseteq> (UNIV :: char set) \<and> length s \<le> n}"
    by (auto simp add: bounded_strings_def)
  then show ?thesis
    by (simp only:) (rule finite_lists_length_le, simp)
qed

lemma bounded_language_subset_bounded_strings:
  assumes "bounded_language n A"
  shows "A \<subseteq> bounded_strings n"
  using assms by (auto simp add: bounded_language_def bounded_strings_def)

lemma bounded_strings_mono:
  assumes "n \<le> m"
  shows "bounded_strings n \<subseteq> bounded_strings m"
  using assms by (auto simp add: bounded_strings_def)

lemma bounded_language_subset_bounded_strings_mono:
  assumes "bounded_language n A" "n \<le> m"
  shows "A \<subseteq> bounded_strings m"
  using bounded_language_subset_bounded_strings[OF assms(1)]
    bounded_strings_mono[OF assms(2)]
  by blast

lemma card_Pow_finite:
  assumes "finite A"
  shows "card (Pow A) = 2 ^ card A"
  using assms
proof induct
  case empty
  then show ?case
    by simp
next
  case (insert a A)
  have split: "Pow (insert a A) = Pow A \<union> insert a ` Pow A"
    by (simp add: Pow_insert)
  have disjoint: "Pow A \<inter> insert a ` Pow A = {}"
    using insert.hyps by auto
  have finite_A: "finite (Pow A)"
    using insert.hyps by simp
  have finite_insert_A: "finite (insert a ` Pow A)"
    using finite_A by simp
  have card_insert_A: "card (insert a ` Pow A) = card (Pow A)"
    by (rule card_image) (use insert.hyps in \<open>auto simp add: inj_on_def\<close>)
  show ?case
    using insert.hyps card_insert_A
    by (simp add: split card_Un_disjoint[OF finite_A finite_insert_A disjoint])
qed

theorem bounded_language_left_quotient_family_subset_bounded_strings:
  assumes "bounded_language n A"
  shows "{Ders s A | s. True} \<subseteq> Pow (bounded_strings n)"
  using bounded_language_Ders[OF assms] bounded_language_subset_bounded_strings
  by blast

theorem bounded_language_left_quotient_family_subset_bounded_strings_mono:
  assumes "bounded_language n A" "n \<le> m"
  shows "{Ders s A | s. True} \<subseteq> Pow (bounded_strings m)"
  using bounded_language_Ders[OF assms(1)]
    bounded_language_subset_bounded_strings_mono[OF _ assms(2)]
  by blast

theorem bounded_language_left_quotient_family_card_bound:
  assumes "bounded_language n A"
  shows "card {Ders s A | s. True} \<le> 2 ^ card (bounded_strings n)"
proof -
  have sub: "{Ders s A | s. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule bounded_language_left_quotient_family_subset_bounded_strings)
  have fin_pow: "finite (Pow (bounded_strings n))"
    using finite_bounded_strings by simp
  have "card {Ders s A | s. True} \<le> card (Pow (bounded_strings n))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings n)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem bounded_language_left_quotient_family_card_bound_mono:
  assumes "bounded_language n A" "n \<le> m"
  shows "card {Ders s A | s. True} \<le> 2 ^ card (bounded_strings m)"
proof -
  have sub: "{Ders s A | s. True} \<subseteq> Pow (bounded_strings m)"
    using assms
    by (rule bounded_language_left_quotient_family_subset_bounded_strings_mono)
  have fin_pow: "finite (Pow (bounded_strings m))"
    using finite_bounded_strings by simp
  have "card {Ders s A | s. True} \<le> card (Pow (bounded_strings m))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings m)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem bounded_language_left_quotient_family_finite:
  assumes "bounded_language n A"
  shows "finite {Ders s A | s. True}"
  using finite_left_quotients_if_bounded_language[OF assms]
  by (simp add: finite_left_quotients_def)

theorem bounded_language_residual_left_quotient_family_subset_bounded_strings:
  assumes "bounded_language n A"
  shows "{Ders t (Ders s A) | t. True} \<subseteq> Pow (bounded_strings n)"
proof -
  have sub: "{Ders t (Ders s A) | t. True} \<subseteq> {Ders u A | u. True}"
    by (rule left_quotient_family_Ders_subset)
  have universe: "{Ders u A | u. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule bounded_language_left_quotient_family_subset_bounded_strings)
  show ?thesis
    using sub universe by blast
qed

theorem bounded_language_residual_left_quotient_family_subset_bounded_strings_mono:
  assumes "bounded_language n A" "n \<le> m"
  shows "{Ders t (Ders s A) | t. True} \<subseteq> Pow (bounded_strings m)"
proof -
  have sub: "{Ders t (Ders s A) | t. True} \<subseteq> {Ders u A | u. True}"
    by (rule left_quotient_family_Ders_subset)
  have universe: "{Ders u A | u. True} \<subseteq> Pow (bounded_strings m)"
    using assms by (rule bounded_language_left_quotient_family_subset_bounded_strings_mono)
  show ?thesis
    using sub universe by blast
qed

theorem bounded_language_residual_left_quotient_family_card_bound:
  assumes "bounded_language n A"
  shows "card {Ders t (Ders s A) | t. True} \<le> 2 ^ card (bounded_strings n)"
proof -
  have sub: "{Ders t (Ders s A) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms
    by (rule bounded_language_residual_left_quotient_family_subset_bounded_strings)
  have fin_pow: "finite (Pow (bounded_strings n))"
    using finite_bounded_strings by simp
  have "card {Ders t (Ders s A) | t. True} \<le> card (Pow (bounded_strings n))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings n)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem bounded_language_residual_left_quotient_family_card_bound_mono:
  assumes "bounded_language n A" "n \<le> m"
  shows "card {Ders t (Ders s A) | t. True} \<le> 2 ^ card (bounded_strings m)"
proof -
  have sub: "{Ders t (Ders s A) | t. True} \<subseteq> Pow (bounded_strings m)"
    using assms
    by (rule bounded_language_residual_left_quotient_family_subset_bounded_strings_mono)
  have fin_pow: "finite (Pow (bounded_strings m))"
    using finite_bounded_strings by simp
  have "card {Ders t (Ders s A) | t. True} \<le> card (Pow (bounded_strings m))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings m)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem bounded_language_residual_left_quotient_family_finite:
  assumes "bounded_language n A"
  shows "finite {Ders t (Ders s A) | t. True}"
proof -
  have sub: "{Ders t (Ders s A) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms
    by (rule bounded_language_residual_left_quotient_family_subset_bounded_strings)
  show ?thesis
    using finite_subset[OF sub] finite_bounded_strings by simp
qed

theorem bounded_backref_lang_left_quotient_family_subset_bounded_strings:
  assumes "bounded_language n_capture A" "bounded_language n_mid B"
  shows "{Ders s (backref_lang A B cs) | s. True} \<subseteq>
    Pow (bounded_strings (n_capture + n_mid + length cs + n_capture))"
  using bounded_language_backref_lang[OF assms]
  by (rule bounded_language_left_quotient_family_subset_bounded_strings)

theorem bounded_backref_lang4_left_quotient_family_subset_bounded_strings:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
  shows "{Ders s (backref_lang4 L1 L2 L3 L4 cs) | s. True} \<subseteq>
    Pow (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
  using bounded_language_backref_lang4[OF assms]
  by (rule bounded_language_left_quotient_family_subset_bounded_strings)

theorem bounded_backref_lang_left_quotient_family_card_bound:
  assumes "bounded_language n_capture A" "bounded_language n_mid B"
  shows "card {Ders s (backref_lang A B cs) | s. True} \<le>
    2 ^ card (bounded_strings (n_capture + n_mid + length cs + n_capture))"
  using bounded_language_backref_lang[OF assms]
  by (rule bounded_language_left_quotient_family_card_bound)

theorem bounded_backref_lang4_left_quotient_family_card_bound:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
  shows "card {Ders s (backref_lang4 L1 L2 L3 L4 cs) | s. True} \<le>
    2 ^ card (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
  using bounded_language_backref_lang4[OF assms]
  by (rule bounded_language_left_quotient_family_card_bound)

theorem bounded_backref_lang_left_quotient_family_subset_bounded_strings_mono:
  assumes "bounded_language n_capture A"
    and "bounded_language n_mid B"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "{Ders s (backref_lang A B cs) | s. True} \<subseteq> Pow (bounded_strings m)"
  using bounded_language_backref_lang[OF assms(1,2)] assms(3)
  by (rule bounded_language_left_quotient_family_subset_bounded_strings_mono)

theorem bounded_backref_lang4_left_quotient_family_subset_bounded_strings_mono:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "{Ders s (backref_lang4 L1 L2 L3 L4 cs) | s. True} \<subseteq>
    Pow (bounded_strings m)"
  using bounded_language_backref_lang4[OF assms(1-4)] assms(5)
  by (rule bounded_language_left_quotient_family_subset_bounded_strings_mono)

theorem bounded_backref_lang_left_quotient_family_card_bound_mono:
  assumes "bounded_language n_capture A"
    and "bounded_language n_mid B"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "card {Ders s (backref_lang A B cs) | s. True} \<le>
    2 ^ card (bounded_strings m)"
  using bounded_language_backref_lang[OF assms(1,2)] assms(3)
  by (rule bounded_language_left_quotient_family_card_bound_mono)

theorem bounded_backref_lang4_left_quotient_family_card_bound_mono:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "card {Ders s (backref_lang4 L1 L2 L3 L4 cs) | s. True} \<le>
    2 ^ card (bounded_strings m)"
  using bounded_language_backref_lang4[OF assms(1-4)] assms(5)
  by (rule bounded_language_left_quotient_family_card_bound_mono)

theorem bounded_backref_lang_left_quotient_family_finite:
  assumes "bounded_language n_capture A" "bounded_language n_mid B"
  shows "finite {Ders s (backref_lang A B cs) | s. True}"
  using bounded_backref_lang_finite_left_quotients[OF assms]
  by (simp add: finite_left_quotients_def)

theorem bounded_backref_lang4_left_quotient_family_finite:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
  shows "finite {Ders s (backref_lang4 L1 L2 L3 L4 cs) | s. True}"
  using bounded_backref_lang4_finite_left_quotients[OF assms]
  by (simp add: finite_left_quotients_def)

theorem bounded_backref_lang_residual_left_quotient_family_subset_bounded_strings:
  assumes "bounded_language n_capture A" "bounded_language n_mid B"
  shows "{Ders t (Ders s (backref_lang A B cs)) | t. True} \<subseteq>
    Pow (bounded_strings (n_capture + n_mid + length cs + n_capture))"
  using bounded_language_backref_lang[OF assms]
  by (rule bounded_language_residual_left_quotient_family_subset_bounded_strings)

theorem bounded_backref_lang4_residual_left_quotient_family_subset_bounded_strings:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
  shows "{Ders t (Ders s (backref_lang4 L1 L2 L3 L4 cs)) | t. True} \<subseteq>
    Pow (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
  using bounded_language_backref_lang4[OF assms]
  by (rule bounded_language_residual_left_quotient_family_subset_bounded_strings)

theorem bounded_backref_lang_residual_left_quotient_family_card_bound:
  assumes "bounded_language n_capture A" "bounded_language n_mid B"
  shows "card {Ders t (Ders s (backref_lang A B cs)) | t. True} \<le>
    2 ^ card (bounded_strings (n_capture + n_mid + length cs + n_capture))"
  using bounded_language_backref_lang[OF assms]
  by (rule bounded_language_residual_left_quotient_family_card_bound)

theorem bounded_backref_lang4_residual_left_quotient_family_card_bound:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
  shows "card {Ders t (Ders s (backref_lang4 L1 L2 L3 L4 cs)) | t. True} \<le>
    2 ^ card (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
  using bounded_language_backref_lang4[OF assms]
  by (rule bounded_language_residual_left_quotient_family_card_bound)

theorem bounded_backref_lang_residual_left_quotient_family_subset_bounded_strings_mono:
  assumes "bounded_language n_capture A"
    and "bounded_language n_mid B"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "{Ders t (Ders s (backref_lang A B cs)) | t. True} \<subseteq>
    Pow (bounded_strings m)"
  using bounded_language_backref_lang[OF assms(1,2)] assms(3)
  by (rule bounded_language_residual_left_quotient_family_subset_bounded_strings_mono)

theorem bounded_backref_lang4_residual_left_quotient_family_subset_bounded_strings_mono:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "{Ders t (Ders s (backref_lang4 L1 L2 L3 L4 cs)) | t. True} \<subseteq>
    Pow (bounded_strings m)"
  using bounded_language_backref_lang4[OF assms(1-4)] assms(5)
  by (rule bounded_language_residual_left_quotient_family_subset_bounded_strings_mono)

theorem bounded_backref_lang_residual_left_quotient_family_card_bound_mono:
  assumes "bounded_language n_capture A"
    and "bounded_language n_mid B"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "card {Ders t (Ders s (backref_lang A B cs)) | t. True} \<le>
    2 ^ card (bounded_strings m)"
  using bounded_language_backref_lang[OF assms(1,2)] assms(3)
  by (rule bounded_language_residual_left_quotient_family_card_bound_mono)

theorem bounded_backref_lang4_residual_left_quotient_family_card_bound_mono:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "card {Ders t (Ders s (backref_lang4 L1 L2 L3 L4 cs)) | t. True} \<le>
    2 ^ card (bounded_strings m)"
  using bounded_language_backref_lang4[OF assms(1-4)] assms(5)
  by (rule bounded_language_residual_left_quotient_family_card_bound_mono)

theorem bounded_backref_lang_residual_left_quotient_family_finite:
  assumes "bounded_language n_capture A" "bounded_language n_mid B"
  shows "finite {Ders t (Ders s (backref_lang A B cs)) | t. True}"
  using bounded_language_backref_lang[OF assms]
  by (rule bounded_language_residual_left_quotient_family_finite)

theorem bounded_backref_lang4_residual_left_quotient_family_finite:
  assumes "bounded_language n1 L1"
    and "bounded_language n2 L2"
    and "bounded_language n3 L3"
    and "bounded_language n4 L4"
  shows "finite {Ders t (Ders s (backref_lang4 L1 L2 L3 L4 cs)) | t. True}"
  using bounded_language_backref_lang4[OF assms]
  by (rule bounded_language_residual_left_quotient_family_finite)

theorem BL_bound_derivative_family_subset_bounded_strings:
  assumes "BL_bound r = Some n"
  shows "{BL (xders r s) | s. True} \<subseteq> Pow (bounded_strings n)"
  using BL_bound_derivative_family_bounded[OF assms]
    bounded_language_subset_bounded_strings
  by blast

theorem GBL_bound_derivative_family_subset_bounded_strings:
  assumes "GBL_bound r = Some n"
  shows "{GBL (gxders r s) | s. True} \<subseteq> Pow (bounded_strings n)"
  using GBL_bound_derivative_family_bounded[OF assms]
    bounded_language_subset_bounded_strings
  by blast

theorem BL_bound_derivative_family_card_bound:
  assumes "BL_bound r = Some n"
  shows "card {BL (xders r s) | s. True} \<le> 2 ^ card (bounded_strings n)"
proof -
  have sub: "{BL (xders r s) | s. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule BL_bound_derivative_family_subset_bounded_strings)
  have fin_pow: "finite (Pow (bounded_strings n))"
    using finite_bounded_strings by simp
  have "card {BL (xders r s) | s. True} \<le> card (Pow (bounded_strings n))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings n)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem GBL_bound_derivative_family_card_bound:
  assumes "GBL_bound r = Some n"
  shows "card {GBL (gxders r s) | s. True} \<le> 2 ^ card (bounded_strings n)"
proof -
  have sub: "{GBL (gxders r s) | s. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule GBL_bound_derivative_family_subset_bounded_strings)
  have fin_pow: "finite (Pow (bounded_strings n))"
    using finite_bounded_strings by simp
  have "card {GBL (gxders r s) | s. True} \<le> card (Pow (bounded_strings n))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings n)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem BL_bound_derivative_family_subset_bounded_strings_mono:
  assumes "BL_bound r = Some n" "n \<le> m"
  shows "{BL (xders r s) | s. True} \<subseteq> Pow (bounded_strings m)"
  using BL_bound_derivative_family_bounded[OF assms(1)]
    bounded_language_subset_bounded_strings_mono[OF _ assms(2)]
  by blast

theorem GBL_bound_derivative_family_subset_bounded_strings_mono:
  assumes "GBL_bound r = Some n" "n \<le> m"
  shows "{GBL (gxders r s) | s. True} \<subseteq> Pow (bounded_strings m)"
  using GBL_bound_derivative_family_bounded[OF assms(1)]
    bounded_language_subset_bounded_strings_mono[OF _ assms(2)]
  by blast

theorem BL_bound_derivative_family_card_bound_mono:
  assumes "BL_bound r = Some n" "n \<le> m"
  shows "card {BL (xders r s) | s. True} \<le> 2 ^ card (bounded_strings m)"
proof -
  have sub: "{BL (xders r s) | s. True} \<subseteq> Pow (bounded_strings m)"
    using assms by (rule BL_bound_derivative_family_subset_bounded_strings_mono)
  have fin_pow: "finite (Pow (bounded_strings m))"
    using finite_bounded_strings by simp
  have "card {BL (xders r s) | s. True} \<le> card (Pow (bounded_strings m))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings m)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem GBL_bound_derivative_family_card_bound_mono:
  assumes "GBL_bound r = Some n" "n \<le> m"
  shows "card {GBL (gxders r s) | s. True} \<le> 2 ^ card (bounded_strings m)"
proof -
  have sub: "{GBL (gxders r s) | s. True} \<subseteq> Pow (bounded_strings m)"
    using assms by (rule GBL_bound_derivative_family_subset_bounded_strings_mono)
  have fin_pow: "finite (Pow (bounded_strings m))"
    using finite_bounded_strings by simp
  have "card {GBL (gxders r s) | s. True} \<le> card (Pow (bounded_strings m))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings m)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem BL_bound_derivative_family_finite:
  assumes "BL_bound r = Some n"
  shows "finite {BL (xders r s) | s. True}"
  using BL_bound_finite_derivative_languages[OF assms]
  by (simp add: finite_BL_derivatives_def)

theorem GBL_bound_derivative_family_finite:
  assumes "GBL_bound r = Some n"
  shows "finite {GBL (gxders r s) | s. True}"
  using GBL_bound_finite_derivative_languages[OF assms]
  by (simp add: finite_GBL_derivatives_def)

theorem BL_bound_residual_derivative_family_subset_bounded_strings:
  assumes "BL_bound r = Some n"
  shows "{BL (xders (xders r s) t) | t. True} \<subseteq> Pow (bounded_strings n)"
proof
  fix A
  assume "A \<in> {BL (xders (xders r s) t) | t. True}"
  then obtain t where A: "A = BL (xders (xders r s) t)"
    by blast
  then have "A = BL (xders r (s @ t))"
    by (simp add: xders_append)
  then show "A \<in> Pow (bounded_strings n)"
    using BL_bound_derivative_family_subset_bounded_strings[OF assms] by blast
qed

theorem GBL_bound_residual_derivative_family_subset_bounded_strings:
  assumes "GBL_bound r = Some n"
  shows "{GBL (gxders (gxders r s) t) | t. True} \<subseteq> Pow (bounded_strings n)"
proof
  fix A
  assume "A \<in> {GBL (gxders (gxders r s) t) | t. True}"
  then obtain t where A: "A = GBL (gxders (gxders r s) t)"
    by blast
  then have "A = GBL (gxders r (s @ t))"
    by (simp add: gxders_append)
  then show "A \<in> Pow (bounded_strings n)"
    using GBL_bound_derivative_family_subset_bounded_strings[OF assms] by blast
qed

theorem BL_bound_residual_derivative_family_card_bound:
  assumes "BL_bound r = Some n"
  shows "card {BL (xders (xders r s) t) | t. True} \<le>
    2 ^ card (bounded_strings n)"
proof -
  have sub: "{BL (xders (xders r s) t) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule BL_bound_residual_derivative_family_subset_bounded_strings)
  have fin_pow: "finite (Pow (bounded_strings n))"
    using finite_bounded_strings by simp
  have "card {BL (xders (xders r s) t) | t. True} \<le> card (Pow (bounded_strings n))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings n)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem GBL_bound_residual_derivative_family_card_bound:
  assumes "GBL_bound r = Some n"
  shows "card {GBL (gxders (gxders r s) t) | t. True} \<le>
    2 ^ card (bounded_strings n)"
proof -
  have sub: "{GBL (gxders (gxders r s) t) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule GBL_bound_residual_derivative_family_subset_bounded_strings)
  have fin_pow: "finite (Pow (bounded_strings n))"
    using finite_bounded_strings by simp
  have "card {GBL (gxders (gxders r s) t) | t. True} \<le> card (Pow (bounded_strings n))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings n)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem BL_bound_residual_derivative_family_finite:
  assumes "BL_bound r = Some n"
  shows "finite {BL (xders (xders r s) t) | t. True}"
proof -
  have sub: "{BL (xders (xders r s) t) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule BL_bound_residual_derivative_family_subset_bounded_strings)
  show ?thesis
    using finite_subset[OF sub] finite_bounded_strings by simp
qed

theorem GBL_bound_residual_derivative_family_finite:
  assumes "GBL_bound r = Some n"
  shows "finite {GBL (gxders (gxders r s) t) | t. True}"
proof -
  have sub: "{GBL (gxders (gxders r s) t) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule GBL_bound_residual_derivative_family_subset_bounded_strings)
  show ?thesis
    using finite_subset[OF sub] finite_bounded_strings by simp
qed

theorem BL_bound_xders_finite_BL_derivatives:
  assumes "BL_bound r = Some n"
  shows "finite_BL_derivatives (xders r s)"
  using BL_bound_residual_derivative_family_finite[OF assms]
  by (simp add: finite_BL_derivatives_def)

theorem GBL_bound_gxders_finite_GBL_derivatives:
  assumes "GBL_bound r = Some n"
  shows "finite_GBL_derivatives (gxders r s)"
  using GBL_bound_residual_derivative_family_finite[OF assms]
  by (simp add: finite_GBL_derivatives_def)

theorem BL_bound_residual_derivative_family_subset_bounded_strings_mono:
  assumes "BL_bound r = Some n" "n \<le> m"
  shows "{BL (xders (xders r s) t) | t. True} \<subseteq> Pow (bounded_strings m)"
proof
  fix A
  assume "A \<in> {BL (xders (xders r s) t) | t. True}"
  then obtain t where A: "A = BL (xders (xders r s) t)"
    by blast
  then have "A = BL (xders r (s @ t))"
    by (simp add: xders_append)
  then show "A \<in> Pow (bounded_strings m)"
    using BL_bound_derivative_family_subset_bounded_strings_mono[OF assms] by blast
qed

theorem GBL_bound_residual_derivative_family_subset_bounded_strings_mono:
  assumes "GBL_bound r = Some n" "n \<le> m"
  shows "{GBL (gxders (gxders r s) t) | t. True} \<subseteq> Pow (bounded_strings m)"
proof
  fix A
  assume "A \<in> {GBL (gxders (gxders r s) t) | t. True}"
  then obtain t where A: "A = GBL (gxders (gxders r s) t)"
    by blast
  then have "A = GBL (gxders r (s @ t))"
    by (simp add: gxders_append)
  then show "A \<in> Pow (bounded_strings m)"
    using GBL_bound_derivative_family_subset_bounded_strings_mono[OF assms] by blast
qed

theorem BL_bound_residual_derivative_family_card_bound_mono:
  assumes "BL_bound r = Some n" "n \<le> m"
  shows "card {BL (xders (xders r s) t) | t. True} \<le>
    2 ^ card (bounded_strings m)"
proof -
  have sub: "{BL (xders (xders r s) t) | t. True} \<subseteq> Pow (bounded_strings m)"
    using assms by (rule BL_bound_residual_derivative_family_subset_bounded_strings_mono)
  have fin_pow: "finite (Pow (bounded_strings m))"
    using finite_bounded_strings by simp
  have "card {BL (xders (xders r s) t) | t. True} \<le> card (Pow (bounded_strings m))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings m)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem GBL_bound_residual_derivative_family_card_bound_mono:
  assumes "GBL_bound r = Some n" "n \<le> m"
  shows "card {GBL (gxders (gxders r s) t) | t. True} \<le>
    2 ^ card (bounded_strings m)"
proof -
  have sub: "{GBL (gxders (gxders r s) t) | t. True} \<subseteq> Pow (bounded_strings m)"
    using assms by (rule GBL_bound_residual_derivative_family_subset_bounded_strings_mono)
  have fin_pow: "finite (Pow (bounded_strings m))"
    using finite_bounded_strings by simp
  have "card {GBL (gxders (gxders r s) t) | t. True} \<le> card (Pow (bounded_strings m))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings m)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem BL_bound_BBACKREF_residual_derivative_family_subset_bounded_strings:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "{BL (xders (xders (BBACKREF r mid cs) s) t) | t. True} \<subseteq>
    Pow (bounded_strings (n_capture + n_mid + length cs + n_capture))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_residual_derivative_family_subset_bounded_strings)
qed

theorem GBL_bound_GBACKREF4_residual_derivative_family_subset_bounded_strings:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "{GBL (gxders (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) t) | t. True} \<subseteq>
    Pow (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_residual_derivative_family_subset_bounded_strings)
qed

theorem BL_bound_BBACKREF_residual_derivative_family_card_bound:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "card {BL (xders (xders (BBACKREF r mid cs) s) t) | t. True} \<le>
    2 ^ card (bounded_strings (n_capture + n_mid + length cs + n_capture))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_residual_derivative_family_card_bound)
qed

theorem GBL_bound_GBACKREF4_residual_derivative_family_card_bound:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "card {GBL (gxders (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) t) | t. True} \<le>
    2 ^ card (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_residual_derivative_family_card_bound)
qed

theorem BL_bound_BBACKREF_residual_derivative_family_subset_bounded_strings_mono:
  assumes "BL_bound r = Some n_capture"
    and "BL_bound mid = Some n_mid"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "{BL (xders (xders (BBACKREF r mid cs) s) t) | t. True} \<subseteq>
    Pow (bounded_strings m)"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    using assms(3) by (rule BL_bound_residual_derivative_family_subset_bounded_strings_mono)
qed

theorem GBL_bound_GBACKREF4_residual_derivative_family_subset_bounded_strings_mono:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "{GBL (gxders (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) t) | t. True} \<subseteq>
    Pow (bounded_strings m)"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    using assms(5) by (rule GBL_bound_residual_derivative_family_subset_bounded_strings_mono)
qed

theorem BL_bound_BBACKREF_residual_derivative_family_card_bound_mono:
  assumes "BL_bound r = Some n_capture"
    and "BL_bound mid = Some n_mid"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "card {BL (xders (xders (BBACKREF r mid cs) s) t) | t. True} \<le>
    2 ^ card (bounded_strings m)"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    using assms(3) by (rule BL_bound_residual_derivative_family_card_bound_mono)
qed

theorem GBL_bound_GBACKREF4_residual_derivative_family_card_bound_mono:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "card {GBL (gxders (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) t) | t. True} \<le>
    2 ^ card (bounded_strings m)"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    using assms(5) by (rule GBL_bound_residual_derivative_family_card_bound_mono)
qed

theorem BL_bound_BBACKREF_residual_derivative_family_finite:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "finite {BL (xders (xders (BBACKREF r mid cs) s) t) | t. True}"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_residual_derivative_family_finite)
qed

theorem GBL_bound_GBACKREF4_residual_derivative_family_finite:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "finite {GBL (gxders (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) t) | t. True}"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_residual_derivative_family_finite)
qed

theorem BL_bound_BBACKREF_xders_finite_BL_derivatives:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "finite_BL_derivatives (xders (BBACKREF r mid cs) s)"
  using BL_bound_BBACKREF_residual_derivative_family_finite[OF assms]
  by (simp add: finite_BL_derivatives_def)

theorem GBL_bound_GBACKREF4_gxders_finite_GBL_derivatives:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "finite_GBL_derivatives (gxders (GBACKREF4 r1 r2 r3 r4 cs) s)"
  using GBL_bound_GBACKREF4_residual_derivative_family_finite[OF assms]
  by (simp add: finite_GBL_derivatives_def)

theorem BL_bound_BBACKREF_derivative_family_subset_bounded_strings:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "{BL (xders (BBACKREF r mid cs) s) | s. True} \<subseteq>
    Pow (bounded_strings (n_capture + n_mid + length cs + n_capture))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_derivative_family_subset_bounded_strings)
qed

theorem GBL_bound_GBACKREF4_derivative_family_subset_bounded_strings:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "{GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) | s. True} \<subseteq>
    Pow (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_derivative_family_subset_bounded_strings)
qed

theorem BL_bound_BBACKREF_derivative_family_card_bound:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "card {BL (xders (BBACKREF r mid cs) s) | s. True} \<le>
    2 ^ card (bounded_strings (n_capture + n_mid + length cs + n_capture))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_derivative_family_card_bound)
qed

theorem GBL_bound_GBACKREF4_derivative_family_card_bound:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "card {GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) | s. True} \<le>
    2 ^ card (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_derivative_family_card_bound)
qed

theorem BL_bound_BBACKREF_derivative_family_subset_bounded_strings_mono:
  assumes "BL_bound r = Some n_capture"
    and "BL_bound mid = Some n_mid"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "{BL (xders (BBACKREF r mid cs) s) | s. True} \<subseteq>
    Pow (bounded_strings m)"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    using assms(3) by (rule BL_bound_derivative_family_subset_bounded_strings_mono)
qed

theorem GBL_bound_GBACKREF4_derivative_family_subset_bounded_strings_mono:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "{GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) | s. True} \<subseteq>
    Pow (bounded_strings m)"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    using assms(5) by (rule GBL_bound_derivative_family_subset_bounded_strings_mono)
qed

theorem BL_bound_BBACKREF_derivative_family_card_bound_mono:
  assumes "BL_bound r = Some n_capture"
    and "BL_bound mid = Some n_mid"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "card {BL (xders (BBACKREF r mid cs) s) | s. True} \<le>
    2 ^ card (bounded_strings m)"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    using assms(3) by (rule BL_bound_derivative_family_card_bound_mono)
qed

theorem GBL_bound_GBACKREF4_derivative_family_card_bound_mono:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "card {GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) | s. True} \<le>
    2 ^ card (bounded_strings m)"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    using assms(5) by (rule GBL_bound_derivative_family_card_bound_mono)
qed

theorem BL_bound_BBACKREF_derivative_family_finite:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "finite {BL (xders (BBACKREF r mid cs) s) | s. True}"
  using BL_bound_BBACKREF_finite_derivative_languages[OF assms]
  by (simp add: finite_BL_derivatives_def)

theorem GBL_bound_GBACKREF4_derivative_family_finite:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "finite {GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) | s. True}"
  using GBL_bound_GBACKREF4_finite_derivative_languages[OF assms]
  by (simp add: finite_GBL_derivatives_def)

section \<open>Semantic Quotient Wrappers From Bound Calculators\<close>

theorem BL_bound_left_quotient_family_subset_bounded_strings:
  assumes "BL_bound r = Some n"
  shows "{Ders s (BL r) | s. True} \<subseteq> Pow (bounded_strings n)"
proof -
  have "bounded_language n (BL r)"
    using BL_bound_sound[OF assms] by (simp add: BL_bounded_def)
  then show ?thesis
    by (rule bounded_language_left_quotient_family_subset_bounded_strings)
qed

theorem GBL_bound_left_quotient_family_subset_bounded_strings:
  assumes "GBL_bound r = Some n"
  shows "{Ders s (GBL r) | s. True} \<subseteq> Pow (bounded_strings n)"
proof -
  have "bounded_language n (GBL r)"
    using GBL_bound_sound[OF assms] by (simp add: GBL_bounded_def)
  then show ?thesis
    by (rule bounded_language_left_quotient_family_subset_bounded_strings)
qed

theorem BL_bound_left_quotient_family_card_bound:
  assumes "BL_bound r = Some n"
  shows "card {Ders s (BL r) | s. True} \<le> 2 ^ card (bounded_strings n)"
proof -
  have "bounded_language n (BL r)"
    using BL_bound_sound[OF assms] by (simp add: BL_bounded_def)
  then show ?thesis
    by (rule bounded_language_left_quotient_family_card_bound)
qed

theorem GBL_bound_left_quotient_family_card_bound:
  assumes "GBL_bound r = Some n"
  shows "card {Ders s (GBL r) | s. True} \<le> 2 ^ card (bounded_strings n)"
proof -
  have "bounded_language n (GBL r)"
    using GBL_bound_sound[OF assms] by (simp add: GBL_bounded_def)
  then show ?thesis
    by (rule bounded_language_left_quotient_family_card_bound)
qed

theorem BL_bound_left_quotient_family_subset_bounded_strings_mono:
  assumes "BL_bound r = Some n" "n \<le> m"
  shows "{Ders s (BL r) | s. True} \<subseteq> Pow (bounded_strings m)"
proof -
  have "bounded_language n (BL r)"
    using BL_bound_sound[OF assms(1)] by (simp add: BL_bounded_def)
  then show ?thesis
    using assms(2)
    by (rule bounded_language_left_quotient_family_subset_bounded_strings_mono)
qed

theorem GBL_bound_left_quotient_family_subset_bounded_strings_mono:
  assumes "GBL_bound r = Some n" "n \<le> m"
  shows "{Ders s (GBL r) | s. True} \<subseteq> Pow (bounded_strings m)"
proof -
  have "bounded_language n (GBL r)"
    using GBL_bound_sound[OF assms(1)] by (simp add: GBL_bounded_def)
  then show ?thesis
    using assms(2)
    by (rule bounded_language_left_quotient_family_subset_bounded_strings_mono)
qed

theorem BL_bound_left_quotient_family_card_bound_mono:
  assumes "BL_bound r = Some n" "n \<le> m"
  shows "card {Ders s (BL r) | s. True} \<le> 2 ^ card (bounded_strings m)"
proof -
  have "bounded_language n (BL r)"
    using BL_bound_sound[OF assms(1)] by (simp add: BL_bounded_def)
  then show ?thesis
    using assms(2)
    by (rule bounded_language_left_quotient_family_card_bound_mono)
qed

theorem GBL_bound_left_quotient_family_card_bound_mono:
  assumes "GBL_bound r = Some n" "n \<le> m"
  shows "card {Ders s (GBL r) | s. True} \<le> 2 ^ card (bounded_strings m)"
proof -
  have "bounded_language n (GBL r)"
    using GBL_bound_sound[OF assms(1)] by (simp add: GBL_bounded_def)
  then show ?thesis
    using assms(2)
    by (rule bounded_language_left_quotient_family_card_bound_mono)
qed

theorem BL_bound_left_quotient_family_finite:
  assumes "BL_bound r = Some n"
  shows "finite {Ders s (BL r) | s. True}"
proof -
  have "bounded_language n (BL r)"
    using BL_bound_sound[OF assms] by (simp add: BL_bounded_def)
  then show ?thesis
    by (rule bounded_language_left_quotient_family_finite)
qed

theorem GBL_bound_left_quotient_family_finite:
  assumes "GBL_bound r = Some n"
  shows "finite {Ders s (GBL r) | s. True}"
proof -
  have "bounded_language n (GBL r)"
    using GBL_bound_sound[OF assms] by (simp add: GBL_bounded_def)
  then show ?thesis
    by (rule bounded_language_left_quotient_family_finite)
qed

theorem BL_bound_BBACKREF_left_quotient_family_subset_bounded_strings:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "{Ders s (BL (BBACKREF r mid cs)) | s. True} \<subseteq>
    Pow (bounded_strings (n_capture + n_mid + length cs + n_capture))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_left_quotient_family_subset_bounded_strings)
qed

theorem GBL_bound_GBACKREF4_left_quotient_family_subset_bounded_strings:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "{Ders s (GBL (GBACKREF4 r1 r2 r3 r4 cs)) | s. True} \<subseteq>
    Pow (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_left_quotient_family_subset_bounded_strings)
qed

theorem BL_bound_BBACKREF_left_quotient_family_card_bound:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "card {Ders s (BL (BBACKREF r mid cs)) | s. True} \<le>
    2 ^ card (bounded_strings (n_capture + n_mid + length cs + n_capture))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_left_quotient_family_card_bound)
qed

theorem GBL_bound_GBACKREF4_left_quotient_family_card_bound:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "card {Ders s (GBL (GBACKREF4 r1 r2 r3 r4 cs)) | s. True} \<le>
    2 ^ card (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_left_quotient_family_card_bound)
qed

theorem BL_bound_BBACKREF_left_quotient_family_subset_bounded_strings_mono:
  assumes "BL_bound r = Some n_capture"
    and "BL_bound mid = Some n_mid"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "{Ders s (BL (BBACKREF r mid cs)) | s. True} \<subseteq> Pow (bounded_strings m)"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    using assms(3) by (rule BL_bound_left_quotient_family_subset_bounded_strings_mono)
qed

theorem GBL_bound_GBACKREF4_left_quotient_family_subset_bounded_strings_mono:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "{Ders s (GBL (GBACKREF4 r1 r2 r3 r4 cs)) | s. True} \<subseteq>
    Pow (bounded_strings m)"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    using assms(5) by (rule GBL_bound_left_quotient_family_subset_bounded_strings_mono)
qed

theorem BL_bound_BBACKREF_left_quotient_family_card_bound_mono:
  assumes "BL_bound r = Some n_capture"
    and "BL_bound mid = Some n_mid"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "card {Ders s (BL (BBACKREF r mid cs)) | s. True} \<le>
    2 ^ card (bounded_strings m)"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    using assms(3) by (rule BL_bound_left_quotient_family_card_bound_mono)
qed

theorem GBL_bound_GBACKREF4_left_quotient_family_card_bound_mono:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "card {Ders s (GBL (GBACKREF4 r1 r2 r3 r4 cs)) | s. True} \<le>
    2 ^ card (bounded_strings m)"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    using assms(5) by (rule GBL_bound_left_quotient_family_card_bound_mono)
qed

theorem BL_bound_BBACKREF_left_quotient_family_finite:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "finite {Ders s (BL (BBACKREF r mid cs)) | s. True}"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_left_quotient_family_finite)
qed

theorem GBL_bound_GBACKREF4_left_quotient_family_finite:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "finite {Ders s (GBL (GBACKREF4 r1 r2 r3 r4 cs)) | s. True}"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_left_quotient_family_finite)
qed

section \<open>Derivative Residue Quotient Wrappers From Bound Calculators\<close>

theorem BL_bound_xders_left_quotient_family_subset_bounded_strings:
  assumes "BL_bound r = Some n"
  shows "{Ders t (BL (xders r s)) | t. True} \<subseteq> Pow (bounded_strings n)"
proof -
  have bounded: "bounded_language n (BL r)"
    using BL_bound_sound[OF assms] by (simp add: BL_bounded_def)
  have residual:
    "{Ders t (Ders s (BL r)) | t. True} \<subseteq> Pow (bounded_strings n)"
    using bounded
    by (rule bounded_language_residual_left_quotient_family_subset_bounded_strings)
  have "{Ders t (BL (xders r s)) | t. True} =
    {Ders t (Ders s (BL r)) | t. True}"
    by (simp add: xders_correctness)
  then show ?thesis
    using residual by simp
qed

theorem GBL_bound_gxders_left_quotient_family_subset_bounded_strings:
  assumes "GBL_bound r = Some n"
  shows "{Ders t (GBL (gxders r s)) | t. True} \<subseteq> Pow (bounded_strings n)"
proof -
  have bounded: "bounded_language n (GBL r)"
    using GBL_bound_sound[OF assms] by (simp add: GBL_bounded_def)
  have residual:
    "{Ders t (Ders s (GBL r)) | t. True} \<subseteq> Pow (bounded_strings n)"
    using bounded
    by (rule bounded_language_residual_left_quotient_family_subset_bounded_strings)
  have "{Ders t (GBL (gxders r s)) | t. True} =
    {Ders t (Ders s (GBL r)) | t. True}"
    by (simp add: gxders_correctness)
  then show ?thesis
    using residual by simp
qed

theorem BL_bound_xders_left_quotient_family_card_bound:
  assumes "BL_bound r = Some n"
  shows "card {Ders t (BL (xders r s)) | t. True} \<le> 2 ^ card (bounded_strings n)"
proof -
  have sub: "{Ders t (BL (xders r s)) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule BL_bound_xders_left_quotient_family_subset_bounded_strings)
  have fin_pow: "finite (Pow (bounded_strings n))"
    using finite_bounded_strings by simp
  have "card {Ders t (BL (xders r s)) | t. True} \<le> card (Pow (bounded_strings n))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings n)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem GBL_bound_gxders_left_quotient_family_card_bound:
  assumes "GBL_bound r = Some n"
  shows "card {Ders t (GBL (gxders r s)) | t. True} \<le> 2 ^ card (bounded_strings n)"
proof -
  have sub: "{Ders t (GBL (gxders r s)) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule GBL_bound_gxders_left_quotient_family_subset_bounded_strings)
  have fin_pow: "finite (Pow (bounded_strings n))"
    using finite_bounded_strings by simp
  have "card {Ders t (GBL (gxders r s)) | t. True} \<le> card (Pow (bounded_strings n))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings n)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem BL_bound_xders_left_quotient_family_subset_bounded_strings_mono:
  assumes "BL_bound r = Some n" "n \<le> m"
  shows "{Ders t (BL (xders r s)) | t. True} \<subseteq> Pow (bounded_strings m)"
proof -
  have sub: "{Ders t (BL (xders r s)) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms(1) by (rule BL_bound_xders_left_quotient_family_subset_bounded_strings)
  have "Pow (bounded_strings n) \<subseteq> Pow (bounded_strings m)"
    using bounded_strings_mono[OF assms(2)] by blast
  then show ?thesis
    using sub by blast
qed

theorem GBL_bound_gxders_left_quotient_family_subset_bounded_strings_mono:
  assumes "GBL_bound r = Some n" "n \<le> m"
  shows "{Ders t (GBL (gxders r s)) | t. True} \<subseteq> Pow (bounded_strings m)"
proof -
  have sub: "{Ders t (GBL (gxders r s)) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms(1) by (rule GBL_bound_gxders_left_quotient_family_subset_bounded_strings)
  have "Pow (bounded_strings n) \<subseteq> Pow (bounded_strings m)"
    using bounded_strings_mono[OF assms(2)] by blast
  then show ?thesis
    using sub by blast
qed

theorem BL_bound_xders_left_quotient_family_card_bound_mono:
  assumes "BL_bound r = Some n" "n \<le> m"
  shows "card {Ders t (BL (xders r s)) | t. True} \<le> 2 ^ card (bounded_strings m)"
proof -
  have sub: "{Ders t (BL (xders r s)) | t. True} \<subseteq> Pow (bounded_strings m)"
    using assms by (rule BL_bound_xders_left_quotient_family_subset_bounded_strings_mono)
  have fin_pow: "finite (Pow (bounded_strings m))"
    using finite_bounded_strings by simp
  have "card {Ders t (BL (xders r s)) | t. True} \<le> card (Pow (bounded_strings m))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings m)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem GBL_bound_gxders_left_quotient_family_card_bound_mono:
  assumes "GBL_bound r = Some n" "n \<le> m"
  shows "card {Ders t (GBL (gxders r s)) | t. True} \<le> 2 ^ card (bounded_strings m)"
proof -
  have sub: "{Ders t (GBL (gxders r s)) | t. True} \<subseteq> Pow (bounded_strings m)"
    using assms by (rule GBL_bound_gxders_left_quotient_family_subset_bounded_strings_mono)
  have fin_pow: "finite (Pow (bounded_strings m))"
    using finite_bounded_strings by simp
  have "card {Ders t (GBL (gxders r s)) | t. True} \<le> card (Pow (bounded_strings m))"
    by (rule card_mono[OF fin_pow sub])
  also have "... = 2 ^ card (bounded_strings m)"
    by (rule card_Pow_finite[OF finite_bounded_strings])
  finally show ?thesis .
qed

theorem BL_bound_xders_left_quotient_family_finite:
  assumes "BL_bound r = Some n"
  shows "finite {Ders t (BL (xders r s)) | t. True}"
proof -
  have sub: "{Ders t (BL (xders r s)) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule BL_bound_xders_left_quotient_family_subset_bounded_strings)
  show ?thesis
    using finite_subset[OF sub] finite_bounded_strings by simp
qed

theorem GBL_bound_gxders_left_quotient_family_finite:
  assumes "GBL_bound r = Some n"
  shows "finite {Ders t (GBL (gxders r s)) | t. True}"
proof -
  have sub: "{Ders t (GBL (gxders r s)) | t. True} \<subseteq> Pow (bounded_strings n)"
    using assms by (rule GBL_bound_gxders_left_quotient_family_subset_bounded_strings)
  show ?thesis
    using finite_subset[OF sub] finite_bounded_strings by simp
qed

theorem BL_bound_BBACKREF_xders_left_quotient_family_subset_bounded_strings:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "{Ders t (BL (xders (BBACKREF r mid cs) s)) | t. True} \<subseteq>
    Pow (bounded_strings (n_capture + n_mid + length cs + n_capture))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_xders_left_quotient_family_subset_bounded_strings)
qed

theorem GBL_bound_GBACKREF4_gxders_left_quotient_family_subset_bounded_strings:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "{Ders t (GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s)) | t. True} \<subseteq>
    Pow (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_gxders_left_quotient_family_subset_bounded_strings)
qed

theorem BL_bound_BBACKREF_xders_left_quotient_family_card_bound:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "card {Ders t (BL (xders (BBACKREF r mid cs) s)) | t. True} \<le>
    2 ^ card (bounded_strings (n_capture + n_mid + length cs + n_capture))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_xders_left_quotient_family_card_bound)
qed

theorem GBL_bound_GBACKREF4_gxders_left_quotient_family_card_bound:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "card {Ders t (GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s)) | t. True} \<le>
    2 ^ card (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_gxders_left_quotient_family_card_bound)
qed

theorem BL_bound_BBACKREF_xders_left_quotient_family_subset_bounded_strings_mono:
  assumes "BL_bound r = Some n_capture"
    and "BL_bound mid = Some n_mid"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "{Ders t (BL (xders (BBACKREF r mid cs) s)) | t. True} \<subseteq>
    Pow (bounded_strings m)"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    using assms(3) by (rule BL_bound_xders_left_quotient_family_subset_bounded_strings_mono)
qed

theorem GBL_bound_GBACKREF4_gxders_left_quotient_family_subset_bounded_strings_mono:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "{Ders t (GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s)) | t. True} \<subseteq>
    Pow (bounded_strings m)"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    using assms(5) by (rule GBL_bound_gxders_left_quotient_family_subset_bounded_strings_mono)
qed

theorem BL_bound_BBACKREF_xders_left_quotient_family_card_bound_mono:
  assumes "BL_bound r = Some n_capture"
    and "BL_bound mid = Some n_mid"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "card {Ders t (BL (xders (BBACKREF r mid cs) s)) | t. True} \<le>
    2 ^ card (bounded_strings m)"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    using assms(3) by (rule BL_bound_xders_left_quotient_family_card_bound_mono)
qed

theorem GBL_bound_GBACKREF4_gxders_left_quotient_family_card_bound_mono:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "card {Ders t (GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s)) | t. True} \<le>
    2 ^ card (bounded_strings m)"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    using assms(5) by (rule GBL_bound_gxders_left_quotient_family_card_bound_mono)
qed

theorem BL_bound_BBACKREF_xders_left_quotient_family_finite:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "finite {Ders t (BL (xders (BBACKREF r mid cs) s)) | t. True}"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_xders_left_quotient_family_finite)
qed

theorem GBL_bound_GBACKREF4_gxders_left_quotient_family_finite:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "finite {Ders t (GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s)) | t. True}"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_gxders_left_quotient_family_finite)
qed

theorem BL_bound_xders_subset_bounded_strings:
  assumes "BL_bound r = Some n"
  shows "BL (xders r s) \<subseteq> bounded_strings n"
  using BL_bound_xders_bounded[OF assms, of s]
  by (auto simp add: BL_bounded_def bounded_language_def bounded_strings_def)

theorem GBL_bound_gxders_subset_bounded_strings:
  assumes "GBL_bound r = Some n"
  shows "GBL (gxders r s) \<subseteq> bounded_strings n"
  using GBL_bound_gxders_bounded[OF assms, of s]
  by (auto simp add: GBL_bounded_def bounded_language_def bounded_strings_def)

theorem BL_bound_xders_card_bound:
  assumes "BL_bound r = Some n"
  shows "card (BL (xders r s)) \<le> card (bounded_strings n)"
proof -
  have sub: "BL (xders r s) \<subseteq> bounded_strings n"
    using assms by (rule BL_bound_xders_subset_bounded_strings)
  show ?thesis
    by (rule card_mono[OF finite_bounded_strings sub])
qed

theorem GBL_bound_gxders_card_bound:
  assumes "GBL_bound r = Some n"
  shows "card (GBL (gxders r s)) \<le> card (bounded_strings n)"
proof -
  have sub: "GBL (gxders r s) \<subseteq> bounded_strings n"
    using assms by (rule GBL_bound_gxders_subset_bounded_strings)
  show ?thesis
    by (rule card_mono[OF finite_bounded_strings sub])
qed

theorem BL_bound_xders_subset_bounded_strings_mono:
  assumes "BL_bound r = Some n" "n \<le> m"
  shows "BL (xders r s) \<subseteq> bounded_strings m"
  using BL_bound_xders_bounded[OF assms(1), of s] assms(2)
  by (auto simp add: BL_bounded_def bounded_language_def bounded_strings_def)

theorem GBL_bound_gxders_subset_bounded_strings_mono:
  assumes "GBL_bound r = Some n" "n \<le> m"
  shows "GBL (gxders r s) \<subseteq> bounded_strings m"
  using GBL_bound_gxders_bounded[OF assms(1), of s] assms(2)
  by (auto simp add: GBL_bounded_def bounded_language_def bounded_strings_def)

theorem BL_bound_xders_card_bound_mono:
  assumes "BL_bound r = Some n" "n \<le> m"
  shows "card (BL (xders r s)) \<le> card (bounded_strings m)"
proof -
  have sub: "BL (xders r s) \<subseteq> bounded_strings m"
    using assms by (rule BL_bound_xders_subset_bounded_strings_mono)
  show ?thesis
    by (rule card_mono[OF finite_bounded_strings sub])
qed

theorem GBL_bound_gxders_card_bound_mono:
  assumes "GBL_bound r = Some n" "n \<le> m"
  shows "card (GBL (gxders r s)) \<le> card (bounded_strings m)"
proof -
  have sub: "GBL (gxders r s) \<subseteq> bounded_strings m"
    using assms by (rule GBL_bound_gxders_subset_bounded_strings_mono)
  show ?thesis
    by (rule card_mono[OF finite_bounded_strings sub])
qed

theorem BL_bound_xders_finite:
  assumes "BL_bound r = Some n"
  shows "finite (BL (xders r s))"
proof -
  have sub: "BL (xders r s) \<subseteq> bounded_strings n"
    using assms by (rule BL_bound_xders_subset_bounded_strings)
  show ?thesis
    using finite_subset[OF sub] finite_bounded_strings by simp
qed

theorem GBL_bound_gxders_finite:
  assumes "GBL_bound r = Some n"
  shows "finite (GBL (gxders r s))"
proof -
  have sub: "GBL (gxders r s) \<subseteq> bounded_strings n"
    using assms by (rule GBL_bound_gxders_subset_bounded_strings)
  show ?thesis
    using finite_subset[OF sub] finite_bounded_strings by simp
qed

theorem BL_bound_BBACKREF_xders_subset_bounded_strings:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "BL (xders (BBACKREF r mid cs) s) \<subseteq>
    bounded_strings (n_capture + n_mid + length cs + n_capture)"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_xders_subset_bounded_strings)
qed

theorem GBL_bound_GBACKREF4_gxders_subset_bounded_strings:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) \<subseteq>
    bounded_strings (n1 + n2 + n3 + length cs + n2 + n4)"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_gxders_subset_bounded_strings)
qed

theorem BL_bound_BBACKREF_xders_card_bound:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "card (BL (xders (BBACKREF r mid cs) s)) \<le>
    card (bounded_strings (n_capture + n_mid + length cs + n_capture))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_xders_card_bound)
qed

theorem GBL_bound_GBACKREF4_gxders_card_bound:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "card (GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s)) \<le>
    card (bounded_strings (n1 + n2 + n3 + length cs + n2 + n4))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_gxders_card_bound)
qed

theorem BL_bound_BBACKREF_xders_subset_bounded_strings_mono:
  assumes "BL_bound r = Some n_capture"
    and "BL_bound mid = Some n_mid"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "BL (xders (BBACKREF r mid cs) s) \<subseteq> bounded_strings m"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    using assms(3) by (rule BL_bound_xders_subset_bounded_strings_mono)
qed

theorem GBL_bound_GBACKREF4_gxders_subset_bounded_strings_mono:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s) \<subseteq> bounded_strings m"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    using assms(5) by (rule GBL_bound_gxders_subset_bounded_strings_mono)
qed

theorem BL_bound_BBACKREF_xders_card_bound_mono:
  assumes "BL_bound r = Some n_capture"
    and "BL_bound mid = Some n_mid"
    and "n_capture + n_mid + length cs + n_capture \<le> m"
  shows "card (BL (xders (BBACKREF r mid cs) s)) \<le> card (bounded_strings m)"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    using assms(3) by (rule BL_bound_xders_card_bound_mono)
qed

theorem GBL_bound_GBACKREF4_gxders_card_bound_mono:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
    and "n1 + n2 + n3 + length cs + n2 + n4 \<le> m"
  shows "card (GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s)) \<le>
    card (bounded_strings m)"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    using assms(5) by (rule GBL_bound_gxders_card_bound_mono)
qed

theorem BL_bound_BBACKREF_xders_finite:
  assumes "BL_bound r = Some n_capture" "BL_bound mid = Some n_mid"
  shows "finite (BL (xders (BBACKREF r mid cs) s))"
proof -
  have bound: "BL_bound (BBACKREF r mid cs) =
    Some (n_capture + n_mid + length cs + n_capture)"
    using assms by simp
  then show ?thesis
    by (rule BL_bound_xders_finite)
qed

theorem GBL_bound_GBACKREF4_gxders_finite:
  assumes "BL_bound r1 = Some n1"
    and "BL_bound r2 = Some n2"
    and "BL_bound r3 = Some n3"
    and "BL_bound r4 = Some n4"
  shows "finite (GBL (gxders (GBACKREF4 r1 r2 r3 r4 cs) s))"
proof -
  have bound: "GBL_bound (GBACKREF4 r1 r2 r3 r4 cs) =
    Some (n1 + n2 + n3 + length cs + n2 + n4)"
    using assms by simp
  then show ?thesis
    by (rule GBL_bound_gxders_finite)
qed

end
