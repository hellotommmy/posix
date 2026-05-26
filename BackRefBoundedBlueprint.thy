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

end
