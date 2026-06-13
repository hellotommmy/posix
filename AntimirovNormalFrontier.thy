theory AntimirovNormalFrontier
  imports AntimirovFactoredTransition
begin

section \<open>Normal Antimirov Frontier\<close>

text \<open>
  This file records the first-stage invariant in the usual Antimirov shape:
  alternatives are exposed, but product residuals are kept whole.  Thus a
  residual such as @{term "RSEQ (RCHAR a) (RSEQ (RCHAR a) (RCHAR a))"} is a
  frontier term at the empty front; it is not replaced by its alphabetic atoms.
\<close>

definition normal_antimirov_frontier :: "rrexp \<Rightarrow> rrexp set" where
  "normal_antimirov_frontier r = apder_frontier r"

definition normal_antimirov_rows :: "rrexp \<Rightarrow> rrexp set" where
  "normal_antimirov_rows r = apder_rows r"

definition normal_frontier_canonical_rows :: "rrexp list \<Rightarrow> rrexp list" where
  "normal_frontier_canonical_rows rs =
    rdistinct (rfrontiers_list rs) {}"

definition normal_canonical_derivative :: "rrexp \<Rightarrow> string \<Rightarrow> rrexp" where
  "normal_canonical_derivative r s =
    rsimp_ALTs (normal_frontier_canonical_rows (afactored1 r s))"

definition normal_same_front_prune_closure :: "rrexp \<Rightarrow> rrexp set" where
  "normal_same_front_prune_closure r =
    raw_shared_prune_same_suffix_closure (normal_antimirov_frontier r)"

definition normal_strong_scan_owner :: "rrexp \<Rightarrow> rrexp set" where
  "normal_strong_scan_owner r =
    raw_shared_prune_active_suffix_owner (apder_strong_frontier r)"

definition normal_strong_dlfrontier :: "rrexp \<Rightarrow> rrexp set" where
  "normal_strong_dlfrontier r = apder_strong_dlfrontier r"

lemma finite_normal_antimirov_frontier [simp]:
  "finite (normal_antimirov_frontier r)"
  by (simp add: normal_antimirov_frontier_def)

lemma finite_normal_antimirov_rows [simp]:
  "finite (normal_antimirov_rows r)"
  by (simp add: normal_antimirov_rows_def)

lemma finite_normal_same_front_prune_closure [simp]:
  "finite (normal_same_front_prune_closure r)"
  by (simp add: normal_same_front_prune_closure_def)

lemma finite_normal_strong_dlfrontier [simp]:
  "finite (normal_strong_dlfrontier r)"
  by (simp add: normal_strong_dlfrontier_def)

lemma distinct_normal_frontier_canonical_rows [simp]:
  "distinct (normal_frontier_canonical_rows rs)"
  by (simp add: normal_frontier_canonical_rows_def
      rdistinct_does_the_job)

lemma set_normal_frontier_canonical_rows [simp]:
  "set (normal_frontier_canonical_rows rs) = rfrontiers rs"
  by (simp add: normal_frontier_canonical_rows_def
      rdistinct_set_equality)

lemma RL_RALTS_normal_frontier_canonical_rows:
  "RL (RALTS (normal_frontier_canonical_rows rs)) = RL (RALTS rs)"
proof -
  have "RL (RALTS (normal_frontier_canonical_rows rs)) =
      (\<Union>x \<in> rfrontiers rs. RL x)"
    by simp
  also have "... = RL (RALTS rs)"
    by (rule RL_rfrontiers_UN)
  finally show ?thesis .
qed

lemma RLS_set_normal_frontier_canonical_rows:
  "RLS (set (normal_frontier_canonical_rows rs)) = RLS (set rs)"
  using RL_RALTS_normal_frontier_canonical_rows[of rs]
  by (simp add: RLS_def)

lemma rsizes_normal_frontier_canonical_rows_boundI:
  assumes finite: "finite U"
    and front: "rfrontiers rs \<subseteq> U"
  shows "rsizes (normal_frontier_canonical_rows rs) \<le> rsize_set U"
  by (rule rsizes_distinct_subset_rsize_set)
    (use finite front in auto)

lemma normal_frontier_subset_same_front_prune_closure:
  "normal_antimirov_frontier r \<subseteq>
    normal_same_front_prune_closure r"
  by (simp add: normal_same_front_prune_closure_def
      raw_shared_prune_same_suffix_closure_extensive)

lemma apder_strong_frontier_subset_normal_strong_scan_owner:
  "apder_strong_frontier r \<subseteq> normal_strong_scan_owner r"
  by (simp add: normal_strong_scan_owner_def
      raw_shared_prune_active_suffix_owner_extensive)

lemma apder_rows_rflts_single_subset_apder_frontier:
  assumes nf: "apder_nf r"
    and p: "p \<in> apder_rows r"
  shows "set (rflts [p]) \<subseteq> apder_frontier r"
proof -
  have p_nf: "rtail_nf p"
    by (rule apder_rows_member_rtail_nf[OF nf p])
  have "set (rflts [p]) = rfrontier p"
    by (rule rtail_nf_rflts_singleton_eq_rfrontier[OF p_nf])
  also have "... \<subseteq> apder_frontier r"
    by (rule rfrontier_apder_rows_subset[OF nf p])
  finally show ?thesis .
qed

lemma normal_strong_dlfrontier_subset_frontier_dlform_closure:
  assumes nf: "apder_nf r"
  shows "normal_strong_dlfrontier r \<subseteq>
    rsimpStrong_dlform_closure (normal_antimirov_frontier r)"
proof
  fix x
  assume x: "x \<in> normal_strong_dlfrontier r"
  obtain p where p:
      "p \<in> apder_rows r"
      "x \<in> row_dlforms (rsimpStrong_raw p)"
    using x
    by (auto simp add: normal_strong_dlfrontier_def
        apder_strong_dlfrontier_def rsimpStrong_dlform_closure_def)
  have flat: "set (rflts [p]) \<subseteq> apder_frontier r"
    by (rule apder_rows_rflts_single_subset_apder_frontier[OF nf p(1)])
  have strong:
      "row_dlforms (rsimpStrong_raw p) \<subseteq>
        rsimpStrong_dlform_closure (apder_frontier r)"
    by (rule row_dlforms_rsimpStrong_raw_subset_dlform_closure_rflts_single
        [OF flat])
  have "x \<in> rsimpStrong_dlform_closure (apder_frontier r)"
    using strong p(2) by blast
  show "x \<in> rsimpStrong_dlform_closure (normal_antimirov_frontier r)"
    using \<open>x \<in> rsimpStrong_dlform_closure (apder_frontier r)\<close>
    by (simp add: normal_antimirov_frontier_def)
qed

lemma rsize_set_normal_strong_dlfrontier_le_frontier_dlform_closure:
  assumes nf: "apder_nf r"
  shows "rsize_set (normal_strong_dlfrontier r) \<le>
    rsize_set (rsimpStrong_dlform_closure (normal_antimirov_frontier r))"
  by (rule rsize_set_mono)
    (use normal_strong_dlfrontier_subset_frontier_dlform_closure[OF nf]
      in auto)

lemma rsize_set_normal_strong_dlfrontier_cubic_from_frontier_closureI:
  assumes nf: "apder_nf r"
    and closure_cubic:
      "rsize_set
        (rsimpStrong_dlform_closure (normal_antimirov_frontier r)) \<le>
        C * (apder_awidth r + rsize r + 3) ^ 3"
  shows "rsize_set (normal_strong_dlfrontier r) \<le>
    C * (apder_awidth r + rsize r + 3) ^ 3"
proof -
  have "rsize_set (normal_strong_dlfrontier r) \<le>
      rsize_set
        (rsimpStrong_dlform_closure (normal_antimirov_frontier r))"
    by (rule rsize_set_normal_strong_dlfrontier_le_frontier_dlform_closure
        [OF nf])
  also have "... \<le> C * (apder_awidth r + rsize r + 3) ^ 3"
    by (rule closure_cubic)
  finally show ?thesis .
qed

lemma rsize_set_normal_frontier_strong_dlclosure_le_sum:
  "rsize_set
      (rsimpStrong_dlform_closure (normal_antimirov_frontier r)) \<le>
    (\<Sum>p \<in> normal_antimirov_frontier r.
      rsize_set (row_dlforms (rsimpStrong_raw p)))"
  by (rule rsize_set_rsimpStrong_dlform_closure_le_sum) simp

lemma rsize_set_normal_frontier_strong_dlclosure_cubic_from_sumI:
  assumes sum_cubic:
      "(\<Sum>p \<in> normal_antimirov_frontier r.
        rsize_set (row_dlforms (rsimpStrong_raw p))) \<le>
        C * (apder_awidth r + rsize r + 3) ^ 3"
  shows "rsize_set
      (rsimpStrong_dlform_closure (normal_antimirov_frontier r)) \<le>
    C * (apder_awidth r + rsize r + 3) ^ 3"
proof -
  have "rsize_set
      (rsimpStrong_dlform_closure (normal_antimirov_frontier r)) \<le>
      (\<Sum>p \<in> normal_antimirov_frontier r.
        rsize_set (row_dlforms (rsimpStrong_raw p)))"
    by (rule rsize_set_normal_frontier_strong_dlclosure_le_sum)
  also have "... \<le> C * (apder_awidth r + rsize r + 3) ^ 3"
    by (rule sum_cubic)
  finally show ?thesis .
qed

lemma card_rsimpStrong_dlform_closure_le_card_plus_rsize_set:
  assumes finite: "finite U"
  shows "card (rsimpStrong_dlform_closure U) \<le>
    card U + rsize_set U"
proof -
  have "card (rsimpStrong_dlform_closure U) \<le>
      (\<Sum>p \<in> U. card (row_dlforms (rsimpStrong_raw p)))"
    unfolding rsimpStrong_dlform_closure_def
    by (rule card_UN_le[OF finite])
  also have "... \<le> (\<Sum>p \<in> U. Suc (rsize p))"
  proof (rule sum_mono)
    fix p
    assume "p \<in> U"
    have "card (row_dlforms (rsimpStrong_raw p)) \<le>
        Suc (rsize (rsimpStrong_raw p))"
      by (rule card_row_dlforms_rtail_nf_le_Suc_rsize)
        (rule rtail_nf_rsimpStrong_raw)
    also have "... \<le> Suc (rsize p)"
      using rsize_rsimpStrong_raw_le[of p] by simp
    finally show "card (row_dlforms (rsimpStrong_raw p)) \<le>
        Suc (rsize p)" .
  qed
  also have "... = card U + rsize_set U"
    using finite
  proof (induct U rule: finite_induct)
    case empty
    then show ?case
      by (simp add: rsize_set_def)
  next
    case (insert x F)
    then show ?case
      by (simp add: rsize_set_def)
  qed
  finally show ?thesis .
qed

lemma card_normal_frontier_strong_dlclosure_cubic:
  assumes nf: "apder_nf r"
  shows "card
      (rsimpStrong_dlform_closure (normal_antimirov_frontier r)) \<le>
    2 * (apder_awidth r + rsize r + 3) ^ 3"
proof -
  let ?U = "normal_antimirov_frontier r"
  let ?B = "(apder_awidth r + rsize r + 3) ^ 3"
  have card_closure:
      "card (rsimpStrong_dlform_closure ?U) \<le>
        card ?U + rsize_set ?U"
    by (rule card_rsimpStrong_dlform_closure_le_card_plus_rsize_set)
      simp
  have card_U: "card ?U \<le> ?B"
  proof -
    have "card ?U \<le> rsize_set ?U"
      by (rule card_le_rsize_set) simp
    also have "... = rsize_set (apder_frontier r)"
      by (simp add: normal_antimirov_frontier_def)
    also have "... \<le> ?B"
      by (rule apder_frontier_expanded_cubic_size_bound[OF nf])
    finally show ?thesis .
  qed
  have size_U: "rsize_set ?U \<le> ?B"
    by (simp add: normal_antimirov_frontier_def
        apder_frontier_expanded_cubic_size_bound[OF nf])
  have "card (rsimpStrong_dlform_closure ?U) \<le> ?B + ?B"
    using card_closure card_U size_U by linarith
  then show ?thesis
    by simp
qed

lemma normal_frontier_strong_dlclosure_member_cubic_size:
  assumes nf: "apder_nf r"
    and x: "x \<in>
      rsimpStrong_dlform_closure (normal_antimirov_frontier r)"
  shows "rsize x \<le> (apder_awidth r + rsize r + 3) ^ 3"
proof (rule rsimpStrong_dlform_closure_member_size_bound[OF _ x])
  fix p
  assume p: "p \<in> normal_antimirov_frontier r"
  have "rsize p = rsize_set {p}"
    by (simp add: rsize_set_def)
  also have "... \<le> rsize_set (normal_antimirov_frontier r)"
    by (rule rsize_set_mono) (use p in auto)
  also have "... = rsize_set (apder_frontier r)"
    by (simp add: normal_antimirov_frontier_def)
  also have "... \<le> (apder_awidth r + rsize r + 3) ^ 3"
    by (rule apder_frontier_expanded_cubic_size_bound[OF nf])
  finally show "rsize p \<le>
      (apder_awidth r + rsize r + 3) ^ 3" .
qed

lemma rsize_set_normal_frontier_strong_dlclosure_sixth:
  assumes nf: "apder_nf r"
  shows "rsize_set
      (rsimpStrong_dlform_closure (normal_antimirov_frontier r)) \<le>
    2 * ((apder_awidth r + rsize r + 3) ^ 3) ^ 2"
proof -
  let ?U = "rsimpStrong_dlform_closure (normal_antimirov_frontier r)"
  let ?B = "(apder_awidth r + rsize r + 3) ^ 3"
  have card: "card ?U \<le> 2 * ?B"
    by (rule card_normal_frontier_strong_dlclosure_cubic[OF nf])
  have member: "\<And>x. x \<in> ?U \<Longrightarrow> rsize x \<le> ?B"
    by (rule normal_frontier_strong_dlclosure_member_cubic_size[OF nf])
  have "rsize_set ?U \<le> card ?U * ?B"
    by (rule rsize_set_le_card_times_bound) (use member in auto)
  also have "... \<le> (2 * ?B) * ?B"
    by (rule mult_right_mono[OF card]) simp
  also have "... = 2 * ?B ^ 2"
    by (simp add: algebra_simps power2_eq_square)
  finally show ?thesis .
qed

lemma legacy_apder_terms:
  assumes legacy: "legacy_rrexp r"
    and p: "p \<in> apder_terms r"
  shows "legacy_rrexp p"
  using legacy p
proof (induct r arbitrary: p)
  case RZERO
  have False
    using RZERO.prems(2) by (simp only: apder_terms.simps empty_iff)
  then show ?case ..
next
  case RONE
  have False
    using RONE.prems(2) by (simp only: apder_terms.simps empty_iff)
  then show ?case ..
next
  case (RCHAR c)
  have p_eq: "p = RONE"
    using RCHAR.prems(2)
    by (simp only: apder_terms.simps singleton_iff)
  show ?case
    using p_eq by simp
next
  case (RALTS rs)
  then obtain q where q: "q \<in> set rs" "p \<in> apder_terms q"
    by auto
  have q_legacy: "legacy_rrexp q"
    using RALTS.prems q by simp
  show ?case
    by (rule RALTS.hyps[OF q(1) q_legacy q(2)])
next
  case (RSEQ r1 r2)
  have p_cases:
      "p \<in> (\<lambda>x. rsimp4_SEQ_atom x r2) ` apder_terms r1 \<or>
      p \<in> apder_terms r2"
    using RSEQ.prems(2) by simp
  then show ?case
  proof
    assume left: "p \<in> (\<lambda>x. rsimp4_SEQ_atom x r2) ` apder_terms r1"
    then obtain x where x: "x \<in> apder_terms r1"
        "p = rsimp4_SEQ_atom x r2"
      by blast
    have x_legacy: "legacy_rrexp x"
      by (rule RSEQ.hyps(1)[OF _ x(1)])
        (use RSEQ.prems in simp)
    have r2_legacy: "legacy_rrexp r2"
      using RSEQ.prems by simp
    show ?thesis
      using x(2) legacy_rsimp4_SEQ_atom[OF x_legacy r2_legacy]
      by simp
  next
    assume right: "p \<in> apder_terms r2"
    show ?thesis
      by (rule RSEQ.hyps(2)[OF _ right])
        (use RSEQ.prems in simp)
  qed
next
  case (RSTAR r)
  then obtain x where x: "x \<in> apder_terms r"
      "p = rsimp4_SEQ_atom x (RSTAR r)"
    by auto
  have x_legacy: "legacy_rrexp x"
    by (rule RSTAR.hyps[OF _ x(1)])
      (use RSTAR.prems in simp)
  have star_legacy: "legacy_rrexp (RSTAR r)"
    using RSTAR.prems by simp
  show ?case
    using x(2) legacy_rsimp4_SEQ_atom[OF x_legacy star_legacy]
    by simp
next
  case (RNTIMES r n)
  then obtain m x where x: "m < n" "x \<in> apder_terms r"
      "p = rsimp4_SEQ_atom x (RNTIMES r m)"
    by auto
  have x_legacy: "legacy_rrexp x"
    by (rule RNTIMES.hyps[OF _ x(2)])
      (use RNTIMES.prems in simp)
  have ntimes_legacy: "legacy_rrexp (RNTIMES r m)"
    using RNTIMES.prems by simp
  show ?case
    using x(3) legacy_rsimp4_SEQ_atom[OF x_legacy ntimes_legacy]
    by simp
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have False
    using RBACKREF4.prems(2)
    by (simp only: apder_terms.simps empty_iff)
  then show ?case ..
next
  case (RHALF r cs rep)
  have False
    using RHALF.prems(2)
    by (simp only: apder_terms.simps empty_iff)
  then show ?case ..
next
  case (RRESIDUE cs rep)
  have False
    using RRESIDUE.prems(2)
    by (simp only: apder_terms.simps empty_iff)
  then show ?case ..
qed

lemma legacy_apder_frontier:
  assumes legacy: "legacy_rrexp r"
    and x: "x \<in> apder_frontier r"
  shows "legacy_rrexp x"
proof -
  have cases:
      "x \<in> rfrontier r \<or>
      (\<exists>p \<in> apder_terms r. x \<in> rfrontier p)"
    using x unfolding apder_frontier_def by blast
  then show ?thesis
  proof
    assume xr: "x \<in> rfrontier r"
    have "x \<in> rsubterms r"
      using xr rfrontier_subset_rsubterms by blast
    then show ?thesis
      by (rule legacy_rrexp_rsubterms[OF legacy])
  next
    assume "\<exists>p \<in> apder_terms r. x \<in> rfrontier p"
    then obtain p where p: "p \<in> apder_terms r" "x \<in> rfrontier p"
      by blast
    have p_legacy: "legacy_rrexp p"
      by (rule legacy_apder_terms[OF legacy p(1)])
    have "x \<in> rsubterms p"
      using p(2) rfrontier_subset_rsubterms by blast
    then show ?thesis
      by (rule legacy_rrexp_rsubterms[OF p_legacy])
  qed
qed

lemma legacy_apder_rows:
  assumes legacy: "legacy_rrexp r"
    and x: "x \<in> apder_rows r"
  shows "legacy_rrexp x"
  using x legacy legacy_apder_frontier
  by (auto simp add: apder_rows_def)

lemma legacy_apder_strong_frontier:
  assumes legacy: "legacy_rrexp r"
    and x: "x \<in> apder_strong_frontier r"
  shows "legacy_rrexp x"
proof -
  obtain p where p:
      "p \<in> apder_rows r"
      "x \<in> rfrontier (rsimpStrong_raw p)"
    using x
    by (auto simp add: apder_strong_frontier_def
        rsimpStrong_frontier_closure_def)
  have p_legacy: "legacy_rrexp p"
    by (rule legacy_apder_rows[OF legacy p(1)])
  have simp_legacy: "legacy_rrexp (rsimpStrong_raw p)"
    by (rule legacy_rsimpStrong_raw[OF p_legacy])
  have "x \<in> rsubterms (rsimpStrong_raw p)"
    using p(2) rfrontier_subset_rsubterms by blast
  then show ?thesis
    by (rule legacy_rrexp_rsubterms[OF simp_legacy])
qed

lemma apder_strong_frontier_member_rtail_nf_props:
  assumes x: "x \<in> apder_strong_frontier r"
  shows "rtail_nf x \<and> nonalt x \<and> x \<noteq> RZERO"
proof -
  obtain p where p:
      "p \<in> apder_rows r"
      "x \<in> rfrontier (rsimpStrong_raw p)"
    using x
    by (auto simp add: apder_strong_frontier_def
        rsimpStrong_frontier_closure_def)
  show ?thesis
    by (rule rtail_nf_rfrontier_member_props
        [OF rtail_nf_rsimpStrong_raw p(2)])
qed

lemma normal_strong_scan_owner_member_rtail_nf_props:
  assumes x: "x \<in> normal_strong_scan_owner r"
  shows "rtail_nf x \<and> nonalt x \<and> x \<noteq> RZERO"
  using x unfolding normal_strong_scan_owner_def
proof (induct rule: raw_shared_prune_active_suffix_owner.induct)
  case (base q)
  then show ?case
    by (rule apder_strong_frontier_member_rtail_nf_props)
next
  case (step earlier later k q)
  have later_nf: "rtail_nf later"
    using step.hyps by blast
  have pruned_nf: "rtail_nf (rsimpStrong_prune_pair_raw earlier later)"
    by (rule rtail_nf_rsimpStrong_prune_pair_raw[OF later_nf])
  have q_flat:
      "q \<in> set (rflts [rsimpStrong_prune_pair_raw earlier later])"
    using step.hyps
    by (simp add: raw_shared_prune_pair_outputs_def)
  show ?case
    by (rule rtail_nf_flat_member_props[OF pruned_nf q_flat])
qed

lemma normal_strong_scan_owner_flat_closed:
  assumes q: "q \<in> normal_strong_scan_owner r"
  shows "set (rflts [q]) \<subseteq> normal_strong_scan_owner r"
proof -
  have props: "rtail_nf q \<and> nonalt q \<and> q \<noteq> RZERO"
    by (rule normal_strong_scan_owner_member_rtail_nf_props[OF q])
  then have "set (rflts [q]) = {q}"
    by (cases q) auto
  then show ?thesis
    using q by simp
qed

lemma rflts_rsimp_ALTs_subset_flat_closed:
  assumes rows: "set rs \<subseteq> U"
    and flat: "\<And>q. q \<in> U \<Longrightarrow> set (rflts [q]) \<subseteq> U"
  shows "set (rflts [rsimp_ALTs rs]) \<subseteq> U"
proof (cases rs)
  case Nil
  then show ?thesis by simp
next
  case (Cons x xs)
  note rs_cons = Cons
  then show ?thesis
  proof (cases xs)
    case Nil
    then show ?thesis
      using Cons rows by (simp add: flat)
  next
    case (Cons y ys)
    have rs_shape: "rs = x # y # ys"
      using rs_cons Cons by simp
    have elems: "set (x # y # ys) \<subseteq> U"
      using rows rs_shape by simp
    have "set (rflts (x # y # ys)) \<subseteq> U"
    proof (rule set_rflts_subset_singletonsI)
      fix q
      assume "q \<in> set (x # y # ys)"
      then have "q \<in> U"
        using elems by blast
      then show "set (rflts [q]) \<subseteq> U"
        by (rule flat)
    qed
    then show ?thesis
      using rs_shape elems by simp
  qed
qed

lemma rflts_rsimpStrong_raw_subset_normal_strong_scan_owner:
  assumes nf: "apder_nf r"
    and flat: "set (rflts [p]) \<subseteq> apder_rows r"
  shows "set (rflts [rsimpStrong_raw p]) \<subseteq>
    normal_strong_scan_owner r"
  using flat
proof (induct p)
  case RZERO
  then show ?case by simp
next
  case RONE
  have row: "RONE \<in> apder_rows r"
    using RONE.prems by simp
  have "set (rflts [rsimpStrong_raw RONE]) \<subseteq>
      apder_strong_frontier r"
    using row
    by (auto intro: rsimpStrong_frontier_closureI
        simp add: apder_strong_frontier_def)
  then show ?case
    using apder_strong_frontier_subset_normal_strong_scan_owner
    by blast
next
  case (RCHAR c)
  have row: "RCHAR c \<in> apder_rows r"
    using RCHAR.prems by simp
  have "set (rflts [rsimpStrong_raw (RCHAR c)]) \<subseteq>
      apder_strong_frontier r"
    using row
    by (auto intro: rsimpStrong_frontier_closureI
        simp add: apder_strong_frontier_def)
  then show ?case
    using apder_strong_frontier_subset_normal_strong_scan_owner
    by blast
next
  case (RSEQ p1 p2)
  have row: "RSEQ p1 p2 \<in> apder_rows r"
    using RSEQ.prems by simp
  have strong_nf: "rtail_nf (rsimpStrong_raw (RSEQ p1 p2))"
    by (rule rtail_nf_rsimpStrong_raw)
  have "set (rflts [rsimpStrong_raw (RSEQ p1 p2)]) =
      rfrontier (rsimpStrong_raw (RSEQ p1 p2))"
    by (rule rtail_nf_rflts_singleton_eq_rfrontier[OF strong_nf])
  also have "... \<subseteq> apder_strong_frontier r"
    using row
    by (auto intro: rsimpStrong_frontier_closureI
        simp add: apder_strong_frontier_def)
  finally show ?case
    using apder_strong_frontier_subset_normal_strong_scan_owner
    by blast
next
  case (RALTS rs)
  let ?rows = "rflts (map rsimpStrong_raw rs)"
  let ?U = "normal_strong_scan_owner r"
  have row_flat:
    "\<And>x. x \<in> set ?rows \<Longrightarrow> set (rflts [x]) \<subseteq> ?U"
  proof -
    fix x
    assume x: "x \<in> set ?rows"
    obtain q where q:
        "q \<in> set rs"
        "x \<in> set (rflts [rsimpStrong_raw q])"
      using x by (rule set_rflts_map_memberE)
    have q_flat: "set (rflts [q]) \<subseteq> apder_rows r"
    proof -
      have rows_subset: "set rs \<subseteq> apder_rows r"
        using RALTS.prems by simp
      have q_row: "q \<in> apder_rows r"
        using rows_subset q(1) by blast
      have q_nf: "rtail_nf q"
        by (rule apder_nf_imp_rtail_nf)
          (rule apder_rows_member_apder_nf[OF nf q_row])
      have "set (rflts [q]) = rfrontier q"
        by (rule rtail_nf_rflts_singleton_eq_rfrontier[OF q_nf])
      also have "... \<subseteq> apder_frontier r"
        by (rule rfrontier_apder_rows_subset[OF nf q_row])
      also have "... \<subseteq> apder_rows r"
        by (auto simp add: apder_rows_def)
      finally show ?thesis .
    qed
    have strong_q: "set (rflts [rsimpStrong_raw q]) \<subseteq> ?U"
      by (rule RALTS.hyps[OF q(1) q_flat])
    then have "x \<in> ?U"
      using q(2) by blast
    then show "set (rflts [x]) \<subseteq> ?U"
      by (rule normal_strong_scan_owner_flat_closed)
  qed
  have pruned:
      "set (rflts (rsimpStrong_prune_rows_raw ?rows)) \<subseteq> ?U"
  proof (rule rsimpStrong_prune_rows_raw_closed_subsetI)
    fix x
    assume "x \<in> set ?rows"
    then show "set (rflts [x]) \<subseteq> ?U"
      by (rule row_flat)
  next
    show "raw_shared_prune_closed ?U"
      by (simp add: normal_strong_scan_owner_def
          raw_shared_prune_active_suffix_owner_prune_closed)
  qed
  let ?xs = "rdistinct (rflts (rsimpStrong_prune_rows_raw ?rows)) {}"
  have xs: "set ?xs \<subseteq> ?U"
    by (rule set_rdistinct_subset[OF pruned])
  have "set (rflts [rsimp_ALTs ?xs]) \<subseteq> ?U"
    by (rule rflts_rsimp_ALTs_subset_flat_closed
        [OF xs normal_strong_scan_owner_flat_closed])
  then show ?case
    by (simp add: rsimpStrong_ALTs_raw_def)
next
  case (RSTAR p)
  have row: "RSTAR p \<in> apder_rows r"
    using RSTAR.prems by simp
  have strong_nf: "rtail_nf (rsimpStrong_raw (RSTAR p))"
    by (rule rtail_nf_rsimpStrong_raw)
  have "set (rflts [rsimpStrong_raw (RSTAR p)]) =
      rfrontier (rsimpStrong_raw (RSTAR p))"
    by (rule rtail_nf_rflts_singleton_eq_rfrontier[OF strong_nf])
  also have "... \<subseteq> apder_strong_frontier r"
    using row
    by (auto intro: rsimpStrong_frontier_closureI
        simp add: apder_strong_frontier_def)
  finally show ?case
    using apder_strong_frontier_subset_normal_strong_scan_owner
    by blast
next
  case (RNTIMES p n)
  have row: "RNTIMES p n \<in> apder_rows r"
    using RNTIMES.prems by simp
  have strong_nf: "rtail_nf (rsimpStrong_raw (RNTIMES p n))"
    by (rule rtail_nf_rsimpStrong_raw)
  have "set (rflts [rsimpStrong_raw (RNTIMES p n)]) =
      rfrontier (rsimpStrong_raw (RNTIMES p n))"
    by (rule rtail_nf_rflts_singleton_eq_rfrontier[OF strong_nf])
  also have "... \<subseteq> apder_strong_frontier r"
    using row
    by (auto intro: rsimpStrong_frontier_closureI
        simp add: apder_strong_frontier_def)
  finally show ?case
    using apder_strong_frontier_subset_normal_strong_scan_owner
    by blast
next
  case (RBACKREF4 p1 p2 p3 p4 cs)
  have row: "RBACKREF4 p1 p2 p3 p4 cs \<in> apder_rows r"
    using RBACKREF4.prems by simp
  have "set (rflts [rsimpStrong_raw (RBACKREF4 p1 p2 p3 p4 cs)]) \<subseteq>
      apder_strong_frontier r"
    using row
    by (auto intro: rsimpStrong_frontier_closureI
        simp add: apder_strong_frontier_def)
  then show ?case
    using apder_strong_frontier_subset_normal_strong_scan_owner
    by blast
next
  case (RHALF p cs rep)
  have row: "RHALF p cs rep \<in> apder_rows r"
    using RHALF.prems by simp
  have "set (rflts [rsimpStrong_raw (RHALF p cs rep)]) \<subseteq>
      apder_strong_frontier r"
    using row
    by (auto intro: rsimpStrong_frontier_closureI
        simp add: apder_strong_frontier_def)
  then show ?case
    using apder_strong_frontier_subset_normal_strong_scan_owner
    by blast
next
  case (RRESIDUE cs rep)
  have row: "RRESIDUE cs rep \<in> apder_rows r"
    using RRESIDUE.prems by simp
  have "set (rflts [rsimpStrong_raw (RRESIDUE cs rep)]) \<subseteq>
      apder_strong_frontier r"
    using row
    by (auto intro: rsimpStrong_frontier_closureI
        simp add: apder_strong_frontier_def)
  then show ?case
    using apder_strong_frontier_subset_normal_strong_scan_owner
    by blast
qed

theorem normal_derivative_frontier_subset:
  assumes nf: "apder_nf r"
  shows "rfrontier (rders_pder_norm r s) \<subseteq>
    normal_antimirov_frontier r"
  using rfrontier_rders_pder_norm_subset_apder_frontier[OF nf, of s]
  by (simp add: normal_antimirov_frontier_def)

theorem normal_derivative_frontier_cubic_size:
  assumes nf: "apder_nf r"
  shows "rsize_set (rfrontier (rders_pder_norm r s)) \<le>
    (apder_awidth r + rsize r + 3) ^ 3"
  by (rule rfrontier_rders_pder_norm_expanded_cubic_size_bound[OF nf])

theorem normal_factored_rows_subset:
  assumes nf: "apder_nf r"
  shows "set (afactored1 r s) \<subseteq> normal_antimirov_rows r"
  using afactored1_apder_rows_subset[OF nf, of s]
  by (simp add: normal_antimirov_rows_def)

theorem normal_factored_rows_cubic_budget:
  assumes nf: "apder_nf r"
  shows "length (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    card (set (afactored1 r s)) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rlinear_termss (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rsizes (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3"
  using afactored1_apder_rows_expanded_cubic_budget[OF nf, of s]
  by blast

theorem normal_factored_rows_contract:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
  shows "RLS (set (afactored1 r s)) = Ders s (RL r) \<and>
    set (afactored1 r s) \<subseteq> normal_antimirov_rows r \<and>
    length (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    card (set (afactored1 r s)) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rlinear_termss (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rsizes (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3"
proof (intro conjI)
  show "RLS (set (afactored1 r s)) = Ders s (RL r)"
    by (rule RLS_afactored1[OF legacy])
  show "set (afactored1 r s) \<subseteq> normal_antimirov_rows r"
    by (rule normal_factored_rows_subset[OF nf])
  have budgets: "length (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    card (set (afactored1 r s)) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rlinear_termss (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rsizes (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3"
    by (rule normal_factored_rows_cubic_budget[OF nf])
  show "length (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3"
    using budgets by simp
  show "card (set (afactored1 r s)) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3"
    using budgets by simp
  show "rlinear_termss (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3"
    using budgets by simp
  show "rsizes (afactored1 r s) \<le>
      2 * (apder_awidth r + rsize r + 3) ^ 3"
    using budgets by simp
qed

theorem normal_canonical_factored_rows_contract:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
  shows "RL (RALTS (normal_frontier_canonical_rows (afactored1 r s))) =
      Ders s (RL r) \<and>
    set (normal_frontier_canonical_rows (afactored1 r s)) \<subseteq>
      normal_antimirov_frontier r \<and>
    distinct (normal_frontier_canonical_rows (afactored1 r s)) \<and>
    length (normal_frontier_canonical_rows (afactored1 r s)) \<le>
      (apder_awidth r + rsize r + 3) ^ 3 \<and>
    card (set (normal_frontier_canonical_rows (afactored1 r s))) \<le>
      (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rlinear_termss (normal_frontier_canonical_rows (afactored1 r s)) \<le>
      (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rsizes (normal_frontier_canonical_rows (afactored1 r s)) \<le>
      (apder_awidth r + rsize r + 3) ^ 3"
proof (intro conjI)
  let ?rows = "afactored1 r s"
  let ?canon = "normal_frontier_canonical_rows ?rows"
  let ?B = "(apder_awidth r + rsize r + 3) ^ 3"
  have rows_lang: "RLS (set ?rows) = Ders s (RL r)"
    by (rule RLS_afactored1[OF legacy])
  have "RL (RALTS ?canon) = RLS (set ?rows)"
    using RLS_set_normal_frontier_canonical_rows[of ?rows]
    by (simp add: RLS_def)
  then show "RL (RALTS ?canon) = Ders s (RL r)"
    using rows_lang by simp
  show "set ?canon \<subseteq> normal_antimirov_frontier r"
    using ader_front_subset_apder_frontier[OF nf, of s]
    by (simp add: ader_front_def normal_antimirov_frontier_def)
  show "distinct ?canon"
    by simp
  have size: "rsizes ?canon \<le> ?B"
  proof -
    have "rsizes ?canon \<le> rsize_set (normal_antimirov_frontier r)"
    proof (rule rsizes_normal_frontier_canonical_rows_boundI)
      show "finite (normal_antimirov_frontier r)"
        by simp
      show "rfrontiers ?rows \<subseteq> normal_antimirov_frontier r"
        using ader_front_subset_apder_frontier[OF nf, of s]
        by (simp add: ader_front_def normal_antimirov_frontier_def)
    qed
    also have "rsize_set (normal_antimirov_frontier r) \<le> ?B"
    proof -
    have "rsize_set (normal_antimirov_frontier r) =
        rsize_set (apder_frontier r)"
      by (simp add: normal_antimirov_frontier_def)
    also have "... \<le> ?B"
      by (rule apder_frontier_expanded_cubic_size_bound[OF nf])
    finally show "rsize_set (normal_antimirov_frontier r) \<le> ?B" .
    qed
    finally show ?thesis .
  qed
  show "length ?canon \<le> ?B"
    using length_le_rsizes[of ?canon] size by linarith
  show "card (set ?canon) \<le> ?B"
    using card_set_le_rsizes_early[of ?canon] size by linarith
  show "rlinear_termss ?canon \<le> ?B"
    using rlinear_termss_le_rsizes[of ?canon] size by linarith
  show "rsizes ?canon \<le> ?B"
    by (rule size)
qed

lemma normal_antimirov_frontier_member_props:
  assumes nf: "apder_nf r"
    and x: "x \<in> normal_antimirov_frontier r"
  shows "apder_nf x \<and> nonalt x \<and> x \<noteq> RZERO"
proof -
  have cases:
      "x \<in> rfrontier r \<or>
      (\<exists>p \<in> apder_terms r. x \<in> rfrontier p)"
    using x by (auto simp add: normal_antimirov_frontier_def
        apder_frontier_def)
  then show ?thesis
  proof
    assume "x \<in> rfrontier r"
    then show ?thesis
      by (rule apder_nf_rfrontier_member_props[OF nf])
  next
    assume "\<exists>p \<in> apder_terms r. x \<in> rfrontier p"
    then obtain p where p: "p \<in> apder_terms r"
        "x \<in> rfrontier p"
      by blast
    have p_nf: "apder_nf p"
      by (rule apder_nf_apder_terms[OF nf p(1)])
    show ?thesis
      by (rule apder_nf_rfrontier_member_props[OF p_nf p(2)])
  qed
qed

lemma rfrontiers_nonzero_nonalt_eq_set:
  assumes "\<forall>q \<in> set rs. q \<noteq> RZERO \<and> nonalt q"
  shows "rfrontiers rs = set rs"
  using assms
  by (induct rs) (simp_all add: rfrontier_nonzero_nonalt_eq)

theorem normal_canonical_derivative_cubic_contract:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
  shows "RL (normal_canonical_derivative r s) = Ders s (RL r) \<and>
    rfrontier (normal_canonical_derivative r s) \<subseteq>
      normal_antimirov_frontier r \<and>
    rsize (normal_canonical_derivative r s) \<le>
      Suc ((apder_awidth r + rsize r + 3) ^ 3)"
proof (intro conjI)
  let ?rows = "afactored1 r s"
  let ?canon = "normal_frontier_canonical_rows ?rows"
  let ?B = "(apder_awidth r + rsize r + 3) ^ 3"
  have contract:
      "RL (RALTS ?canon) = Ders s (RL r) \<and>
       set ?canon \<subseteq> normal_antimirov_frontier r \<and>
       distinct ?canon \<and>
       length ?canon \<le> ?B \<and>
       card (set ?canon) \<le> ?B \<and>
       rlinear_termss ?canon \<le> ?B \<and>
       rsizes ?canon \<le> ?B"
    by (rule normal_canonical_factored_rows_contract[OF legacy nf])
  show "RL (normal_canonical_derivative r s) = Ders s (RL r)"
  proof -
    have "RL (normal_canonical_derivative r s) =
        (\<Union> (set (map RL ?canon)))"
      by (simp add: normal_canonical_derivative_def
          RL_rsimp_RALTS)
    also have "... = RL (RALTS ?canon)"
      by simp
    also have "... = Ders s (RL r)"
      using contract by blast
    finally show ?thesis .
  qed
  show "rfrontier (normal_canonical_derivative r s) \<subseteq>
      normal_antimirov_frontier r"
  proof -
    have "rfrontier (normal_canonical_derivative r s) =
        rfrontiers ?canon"
      by (simp add: normal_canonical_derivative_def)
    also have "... \<subseteq> normal_antimirov_frontier r"
    proof (rule rfrontiers_subsetI)
      fix q
      assume q: "q \<in> set ?canon"
      have q_row: "q \<in> apder_rows r"
        using contract q
        by (auto simp add: normal_antimirov_frontier_def
            apder_rows_def)
      have "rfrontier q \<subseteq> apder_frontier r"
        by (rule rfrontier_apder_rows_subset[OF nf q_row])
      then show "rfrontier q \<subseteq> normal_antimirov_frontier r"
        by (simp add: normal_antimirov_frontier_def)
    qed
    finally show ?thesis .
  qed
  show "rsize (normal_canonical_derivative r s) \<le> Suc ?B"
  proof -
    have "rsize (normal_canonical_derivative r s) \<le>
        Suc (rsizes ?canon)"
      by (simp add: normal_canonical_derivative_def
          rsize_rsimp_ALTs_le)
    also have "... \<le> Suc ?B"
      using contract by simp
    finally show ?thesis .
  qed
qed

theorem normal_canonical_derivative_exact_frontier_contract:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
  shows "rfrontier (normal_canonical_derivative r s) =
      set (normal_frontier_canonical_rows (afactored1 r s)) \<and>
    distinct (normal_frontier_canonical_rows (afactored1 r s)) \<and>
    set (normal_frontier_canonical_rows (afactored1 r s)) \<subseteq>
      normal_antimirov_frontier r \<and>
    card (rfrontier (normal_canonical_derivative r s)) \<le>
      (apder_awidth r + rsize r + 3) ^ 3"
proof (intro conjI)
  let ?rows = "afactored1 r s"
  let ?canon = "normal_frontier_canonical_rows ?rows"
  let ?B = "(apder_awidth r + rsize r + 3) ^ 3"
  have contract:
      "RL (RALTS ?canon) = Ders s (RL r) \<and>
       set ?canon \<subseteq> normal_antimirov_frontier r \<and>
       distinct ?canon \<and>
       length ?canon \<le> ?B \<and>
       card (set ?canon) \<le> ?B \<and>
       rlinear_termss ?canon \<le> ?B \<and>
       rsizes ?canon \<le> ?B"
    by (rule normal_canonical_factored_rows_contract[OF legacy nf])
  have props: "\<forall>q \<in> set ?canon. q \<noteq> RZERO \<and> nonalt q"
  proof
    fix q
    assume q: "q \<in> set ?canon"
    have "q \<in> normal_antimirov_frontier r"
      using contract q by blast
    then show "q \<noteq> RZERO \<and> nonalt q"
      using normal_antimirov_frontier_member_props[OF nf] by blast
  qed
  show "rfrontier (normal_canonical_derivative r s) =
      set ?canon"
    by (simp add: normal_canonical_derivative_def
        rfrontiers_nonzero_nonalt_eq_set[OF props])
  show "distinct ?canon"
    using contract by blast
  show "set ?canon \<subseteq> normal_antimirov_frontier r"
    using contract by blast
  show "card (rfrontier (normal_canonical_derivative r s)) \<le> ?B"
    using contract
    by (simp add: normal_canonical_derivative_def
        rfrontiers_nonzero_nonalt_eq_set[OF props])
qed

theorem normal_canonical_derivative_frontier_eq_ader_front:
  assumes nf: "apder_nf r"
  shows "rfrontier (normal_canonical_derivative r s) =
    ader_front r s"
proof -
  let ?rows = "afactored1 r s"
  let ?canon = "normal_frontier_canonical_rows ?rows"
  have props: "\<forall>q \<in> set ?canon. q \<noteq> RZERO \<and> nonalt q"
  proof
    fix q
    assume q: "q \<in> set ?canon"
    have q_front: "q \<in> ader_front r s"
      using q by (simp add: ader_front_def)
    have q_apder: "q \<in> apder_frontier r"
      using ader_front_subset_apder_frontier[OF nf, of s] q_front
      by blast
    have q_normal: "q \<in> normal_antimirov_frontier r"
      using q_apder by (simp add: normal_antimirov_frontier_def)
    show "q \<noteq> RZERO \<and> nonalt q"
      using normal_antimirov_frontier_member_props[OF nf q_normal]
      by blast
  qed
  have "rfrontier (normal_canonical_derivative r s) =
      set ?canon"
    by (simp add: normal_canonical_derivative_def
        rfrontiers_nonzero_nonalt_eq_set[OF props])
  also have "... = ader_front r s"
    by (simp add: ader_front_def)
  finally show ?thesis .
qed

theorem normal_frontier_canonical_rows_same_front:
  assumes nf: "apder_nf r"
  shows "same_front_rows r s
    (normal_frontier_canonical_rows (afactored1 r s))"
proof (rule same_front_rowsI)
  let ?canon = "normal_frontier_canonical_rows (afactored1 r s)"
  fix row
  assume row: "row \<in> set ?canon"
  have row_front: "row \<in> ader_front r s"
    using row by (simp add: ader_front_def)
  have row_apder: "row \<in> apder_frontier r"
    using ader_front_subset_apder_frontier[OF nf, of s] row_front
    by blast
  have row_normal: "row \<in> normal_antimirov_frontier r"
    using row_apder by (simp add: normal_antimirov_frontier_def)
  have props: "row \<noteq> RZERO \<and> nonalt row"
    using normal_antimirov_frontier_member_props[OF nf row_normal]
    by blast
  have "rfrontier row = {row}"
    using props by (simp add: rfrontier_nonzero_nonalt_eq)
  then show "rfrontier row \<subseteq> ader_front r s"
    using row_front by simp
qed

theorem normal_canonical_derivative_same_front_row:
  assumes nf: "apder_nf r"
  shows "same_front_row r s (normal_canonical_derivative r s)"
  using normal_canonical_derivative_frontier_eq_ader_front[OF nf, of s]
  by (simp add: same_front_row_def)

theorem normal_canonical_derivative_equiv_rders_pder_norm:
  assumes legacy: "legacy_rrexp r"
  shows "RL (normal_canonical_derivative r s) =
    RL (rders_pder_norm r s)"
proof -
  let ?rows = "afactored1 r s"
  let ?canon = "normal_frontier_canonical_rows ?rows"
  have "RL (normal_canonical_derivative r s) =
      (\<Union> (set (map RL ?canon)))"
    by (simp add: normal_canonical_derivative_def
        RL_rsimp_RALTS)
  also have "... = RL (RALTS ?canon)"
    by simp
  also have "... = RLS (set ?rows)"
    using RLS_set_normal_frontier_canonical_rows[of ?rows]
    by (simp add: RLS_def)
  also have "... = Ders s (RL r)"
    by (rule RLS_afactored1[OF legacy])
  also have "... = RL (rders_pder_norm r s)"
    by (simp add: RL_rders_pder_norm[OF legacy])
  finally show ?thesis .
qed

theorem rsimpStrong_raw_normal_canonical_derivative_cubic_contract:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
  shows "RL (rsimpStrong_raw (normal_canonical_derivative r s)) =
      Ders s (RL r) \<and>
    rsize (rsimpStrong_raw (normal_canonical_derivative r s)) \<le>
      Suc ((apder_awidth r + rsize r + 3) ^ 3)"
proof
  let ?B = "(apder_awidth r + rsize r + 3) ^ 3"
  have contract:
      "RL (normal_canonical_derivative r s) = Ders s (RL r) \<and>
      rfrontier (normal_canonical_derivative r s) \<subseteq>
        normal_antimirov_frontier r \<and>
      rsize (normal_canonical_derivative r s) \<le> Suc ?B"
    by (rule normal_canonical_derivative_cubic_contract[OF legacy nf])
  show "RL (rsimpStrong_raw (normal_canonical_derivative r s)) =
      Ders s (RL r)"
    using contract by (simp add: RL_rsimpStrong_raw)
  show "rsize (rsimpStrong_raw (normal_canonical_derivative r s)) \<le>
      Suc ?B"
  proof -
    have "rsize (rsimpStrong_raw (normal_canonical_derivative r s)) \<le>
        rsize (normal_canonical_derivative r s)"
      by (rule rsize_rsimpStrong_raw_le)
    also have "... \<le> Suc ?B"
      using contract by blast
    finally show ?thesis .
  qed
qed

theorem normal_canonical_then_strong_main_cubic_bound:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
  shows "RL (rsimpStrong_raw (normal_canonical_derivative r s)) =
      RL (rders_pder_norm r s) \<and>
    RL (rsimpStrong_raw (normal_canonical_derivative r s)) =
      Ders s (RL r) \<and>
    rsize (rsimpStrong_raw (normal_canonical_derivative r s)) \<le>
      Suc ((apder_awidth r + rsize r + 3) ^ 3)"
proof (intro conjI)
  let ?B = "(apder_awidth r + rsize r + 3) ^ 3"
  have strong:
      "RL (rsimpStrong_raw (normal_canonical_derivative r s)) =
        Ders s (RL r) \<and>
      rsize (rsimpStrong_raw (normal_canonical_derivative r s)) \<le>
        Suc ?B"
    by (rule rsimpStrong_raw_normal_canonical_derivative_cubic_contract
        [OF legacy nf])
  show "RL (rsimpStrong_raw (normal_canonical_derivative r s)) =
      RL (rders_pder_norm r s)"
    using strong by (simp add: RL_rders_pder_norm[OF legacy])
  show "RL (rsimpStrong_raw (normal_canonical_derivative r s)) =
      Ders s (RL r)"
    using strong by blast
  show "rsize (rsimpStrong_raw (normal_canonical_derivative r s)) \<le>
      Suc ?B"
    using strong by blast
qed

theorem normal_canonical_derivative_main_cubic_bound:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
  shows "RL (normal_canonical_derivative r s) =
      RL (rders_pder_norm r s) \<and>
    RL (normal_canonical_derivative r s) = Ders s (RL r) \<and>
    rfrontier (normal_canonical_derivative r s) =
      ader_front r s \<and>
    rfrontier (normal_canonical_derivative r s) \<subseteq>
      normal_antimirov_frontier r \<and>
    same_front_row r s (normal_canonical_derivative r s) \<and>
    card (rfrontier (normal_canonical_derivative r s)) \<le>
      (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rsize (normal_canonical_derivative r s) \<le>
      Suc ((apder_awidth r + rsize r + 3) ^ 3)"
proof (intro conjI)
  let ?B = "(apder_awidth r + rsize r + 3) ^ 3"
  have cubic:
      "RL (normal_canonical_derivative r s) = Ders s (RL r) \<and>
      rfrontier (normal_canonical_derivative r s) \<subseteq>
        normal_antimirov_frontier r \<and>
      rsize (normal_canonical_derivative r s) \<le> Suc ?B"
    by (rule normal_canonical_derivative_cubic_contract[OF legacy nf])
  have exact:
      "rfrontier (normal_canonical_derivative r s) =
        set (normal_frontier_canonical_rows (afactored1 r s)) \<and>
      distinct (normal_frontier_canonical_rows (afactored1 r s)) \<and>
      set (normal_frontier_canonical_rows (afactored1 r s)) \<subseteq>
        normal_antimirov_frontier r \<and>
      card (rfrontier (normal_canonical_derivative r s)) \<le> ?B"
    by (rule normal_canonical_derivative_exact_frontier_contract
        [OF legacy nf])
  show "RL (normal_canonical_derivative r s) =
      RL (rders_pder_norm r s)"
    by (rule normal_canonical_derivative_equiv_rders_pder_norm[OF legacy])
  show "RL (normal_canonical_derivative r s) = Ders s (RL r)"
    using cubic by blast
  show "rfrontier (normal_canonical_derivative r s) =
      ader_front r s"
    by (rule normal_canonical_derivative_frontier_eq_ader_front[OF nf])
  show "rfrontier (normal_canonical_derivative r s) \<subseteq>
      normal_antimirov_frontier r"
    using cubic by blast
  show "same_front_row r s (normal_canonical_derivative r s)"
    by (rule normal_canonical_derivative_same_front_row[OF nf])
  show "card (rfrontier (normal_canonical_derivative r s)) \<le> ?B"
    using exact by blast
  show "rsize (normal_canonical_derivative r s) \<le> Suc ?B"
    using cubic by blast
qed

theorem row_dlformss_normal_frontier_canonical_rows_subset_adlform_front:
  "row_dlformss
      (normal_frontier_canonical_rows (afactored1 r s)) \<subseteq>
    adlform_front r s"
proof
  let ?rows = "afactored1 r s"
  let ?canon = "normal_frontier_canonical_rows ?rows"
  fix x
  assume x: "x \<in> row_dlformss ?canon"
  obtain q where q: "q \<in> set ?canon" "x \<in> row_dlforms q"
    using x by (auto simp add: row_dlformss_member_iff)
  have q_front: "q \<in> rfrontiers ?rows"
    using q(1) by simp
  obtain row where row: "row \<in> set ?rows" "q \<in> rfrontier row"
    using q_front by (auto simp add: rfrontiers_member_iff)
  have "row_dlforms q \<subseteq> row_dlforms row"
    by (rule row_dlforms_rfrontier_member_subset[OF row(2)])
  then have "x \<in> row_dlforms row"
    using q(2) by blast
  then show "x \<in> adlform_front r s"
    using row(1)
    by (auto simp add: adlform_front_def row_dlformss_member_iff)
qed

theorem normal_canonical_derivative_same_dlfront_row:
  "same_dlfront_row r s (normal_canonical_derivative r s)"
proof -
  have "row_dlforms (normal_canonical_derivative r s) \<subseteq>
      adlform_front r s"
    by (simp add: normal_canonical_derivative_def
        row_dlformss_normal_frontier_canonical_rows_subset_adlform_front)
  then show ?thesis
    by (simp add: same_dlfront_row_def)
qed

theorem normal_canonical_derivative_row_dlforms_subset_apder_dlfrontier:
  assumes nf: "apder_nf r"
  shows "row_dlforms (normal_canonical_derivative r s) \<subseteq>
    apder_dlfrontier r"
proof -
  have "row_dlforms (normal_canonical_derivative r s) \<subseteq>
      adlform_front r s"
    using normal_canonical_derivative_same_dlfront_row[of r s]
    by (simp add: same_dlfront_row_def)
  also have "... \<subseteq> apder_dlfrontier r"
    by (rule adlform_front_subset_apder_dlfrontier[OF nf])
  finally show ?thesis .
qed

lemma normal_same_front_prune_closure_member_cubic_size:
  assumes nf: "apder_nf r"
    and x: "x \<in> normal_same_front_prune_closure r"
  shows "rsize x \<le> (apder_awidth r + rsize r + 3) ^ 3"
proof -
  let ?U = "normal_antimirov_frontier r"
  let ?B = "(apder_awidth r + rsize r + 3) ^ 3"
  have member_size: "\<And>q. q \<in> ?U \<Longrightarrow> rsize q \<le> ?B"
  proof -
    fix q
    assume q: "q \<in> ?U"
    have "rsize q = rsize_set {q}"
      by (simp add: rsize_set_def)
    also have "... \<le> rsize_set ?U"
      by (rule rsize_set_mono) (use q in auto)
    also have "... = rsize_set (apder_frontier r)"
      by (simp add: normal_antimirov_frontier_def)
    also have "... \<le> ?B"
      by (rule apder_frontier_expanded_cubic_size_bound[OF nf])
    finally show "rsize q \<le> ?B" .
  qed
  have x_closure:
    "x \<in> raw_shared_prune_same_suffix_closure ?U"
    using x by (simp add: normal_same_front_prune_closure_def)
  show ?thesis
    by (rule raw_shared_prune_same_suffix_closure_member_size_bound
        [OF member_size x_closure])
qed

lemma normal_strong_scan_owner_member_expanded_cubic_size:
  assumes nf: "apder_nf r"
    and x: "x \<in> normal_strong_scan_owner r"
  shows "rsize x \<le>
    2 * (apder_awidth r + rsize r + 3) ^ 3"
proof -
  let ?U = "apder_strong_frontier r"
  let ?B = "2 * (apder_awidth r + rsize r + 3) ^ 3"
  have member_size: "\<And>q. q \<in> ?U \<Longrightarrow> rsize q \<le> ?B"
  proof -
    fix q
    assume q: "q \<in> ?U"
    have "rsize q = rsize_set {q}"
      by (simp add: rsize_set_def)
    also have "... \<le> rsize_set ?U"
      by (rule rsize_set_mono) (use q in auto)
    also have "... \<le> ?B"
      by (rule rsize_set_apder_strong_frontier_expanded_cubic_size_bound
          [OF nf])
    finally show "rsize q \<le> ?B" .
  qed
  have x_owner: "x \<in> raw_shared_prune_active_suffix_owner ?U"
    using x by (simp add: normal_strong_scan_owner_def)
  show ?thesis
    by (rule raw_shared_prune_active_suffix_owner_member_size_bound
        [OF member_size x_owner])
qed

theorem rpder_strong_rows_raw_afactored1_subset_normal_strong_scan_owner:
  assumes nf: "apder_nf r"
  shows "set (rpder_strong_rows_raw c (afactored1 r s)) \<subseteq>
    normal_strong_scan_owner r"
proof (rule rpder_strong_rows_raw_norm_closed_subsetI)
  fix q p
  assume q: "q \<in> set (afactored1 r s)"
    and p: "p \<in> set (rpder_norm_list c q)"
  have rows_subset: "set (afactored1 r s) \<subseteq> apder_rows r"
    by (rule afactored1_apder_rows_subset[OF nf])
  have q_row: "q \<in> apder_rows r"
    using rows_subset q by blast
  have step_subset: "set (afactored_step c [q]) \<subseteq> apder_rows r"
    by (rule afactored_step_apder_rows_subset[OF nf]) (use q_row in simp)
  have flat_p: "set (rflts [p]) \<subseteq> apder_rows r"
  proof -
    have "set (rflts [p]) \<subseteq> set (rflts (rpder_norm_list c q))"
      by (rule rflts_single_member_subset_rflts_list[OF p])
    also have "... \<subseteq> set (afactored_step c [q])"
      by (simp add: afactored_step_def rpder_norm_rows_def
          rdistinct_set_equality)
    also have "... \<subseteq> apder_rows r"
      by (rule step_subset)
    finally show ?thesis .
  qed
  show "set (rflts [rsimpStrong_raw p]) \<subseteq>
      normal_strong_scan_owner r"
    by (rule rflts_rsimpStrong_raw_subset_normal_strong_scan_owner
        [OF nf flat_p])
next
  fix q
  assume q: "q \<in> normal_strong_scan_owner r"
  show "set (rflts [q]) \<subseteq> normal_strong_scan_owner r"
    by (rule normal_strong_scan_owner_flat_closed[OF q])
next
  show "raw_shared_prune_closed (normal_strong_scan_owner r)"
    by (simp add: normal_strong_scan_owner_def
        raw_shared_prune_active_suffix_owner_prune_closed)
qed

theorem rpder_strong_rows_raw_afactored1_member_cubic:
  assumes nf: "apder_nf r"
    and x: "x \<in> set (rpder_strong_rows_raw c (afactored1 r s))"
  shows "rsize x \<le>
    2 * (apder_awidth r + rsize r + 3) ^ 3"
proof -
  have rows:
      "set (rpder_strong_rows_raw c (afactored1 r s)) \<subseteq>
        normal_strong_scan_owner r"
    by (rule rpder_strong_rows_raw_afactored1_subset_normal_strong_scan_owner
        [OF nf])
  have "x \<in> normal_strong_scan_owner r"
    using rows x by blast
  then show ?thesis
    by (rule normal_strong_scan_owner_member_expanded_cubic_size[OF nf])
qed

theorem rpder_strong_rows_raw_afactored1_normal_owner_contract:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
  shows "RLS (set (rpder_strong_rows_raw c (afactored1 r s))) =
      Ders (s @ [c]) (RL r) \<and>
    set (rpder_strong_rows_raw c (afactored1 r s)) \<subseteq>
      normal_strong_scan_owner r \<and>
    (\<forall>x \<in> set (rpder_strong_rows_raw c (afactored1 r s)).
      rsize x \<le> 2 * (apder_awidth r + rsize r + 3) ^ 3)"
proof (intro conjI ballI)
  let ?rows = "rpder_strong_rows_raw c (afactored1 r s)"
  have raw_lang: "RLS (set ?rows) = Der c (RLS (set (afactored1 r s)))"
    by (rule RLS_rpder_strong_rows_raw)
      (rule legacy_afactored1[OF legacy])
  have front_lang: "RLS (set (afactored1 r s)) = Ders s (RL r)"
    by (rule RLS_afactored1[OF legacy])
  show "RLS (set ?rows) = Ders (s @ [c]) (RL r)"
    using raw_lang front_lang by (simp add: Ders_snoc)
  show "set ?rows \<subseteq> normal_strong_scan_owner r"
    by (rule rpder_strong_rows_raw_afactored1_subset_normal_strong_scan_owner
        [OF nf])
next
  fix x
  assume "x \<in> set (rpder_strong_rows_raw c (afactored1 r s))"
  show "rsize x \<le> 2 * (apder_awidth r + rsize r + 3) ^ 3"
    by (rule rpder_strong_rows_raw_afactored1_member_cubic
        [OF nf \<open>x \<in> set (rpder_strong_rows_raw c (afactored1 r s))\<close>])
qed

theorem rpder_strong_rows_raw_afactored1_owner_card_budget_contract:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
    and owner_card: "card (normal_strong_scan_owner r) \<le> C"
  shows "RLS (set (rpder_strong_rows_raw c (afactored1 r s))) =
      Ders (s @ [c]) (RL r) \<and>
    set (rpder_strong_rows_raw c (afactored1 r s)) \<subseteq>
      normal_strong_scan_owner r \<and>
    length (rpder_strong_rows_raw c (afactored1 r s)) \<le> C \<and>
    card (set (rpder_strong_rows_raw c (afactored1 r s))) \<le> C \<and>
    rlinear_termss (rpder_strong_rows_raw c (afactored1 r s)) \<le>
      C * (2 * (apder_awidth r + rsize r + 3) ^ 3) \<and>
    rsizes (rpder_strong_rows_raw c (afactored1 r s)) \<le>
      C * (2 * (apder_awidth r + rsize r + 3) ^ 3)"
proof (intro conjI)
  let ?rows = "rpder_strong_rows_raw c (afactored1 r s)"
  let ?U = "normal_strong_scan_owner r"
  let ?B = "2 * (apder_awidth r + rsize r + 3) ^ 3"
  have contract:
      "RLS (set ?rows) = Ders (s @ [c]) (RL r) \<and>
      set ?rows \<subseteq> ?U \<and>
      (\<forall>x \<in> set ?rows. rsize x \<le> ?B)"
    by (rule rpder_strong_rows_raw_afactored1_normal_owner_contract
        [OF legacy nf])
  have rows_subset: "set ?rows \<subseteq> ?U"
    using contract by blast
  have finite_owner: "finite ?U"
  proof -
    have seed_subset:
        "apder_strong_frontier r \<subseteq> sizeNregex ?B"
    proof
      fix x
      assume x: "x \<in> apder_strong_frontier r"
      have x_legacy: "legacy_rrexp x"
        by (rule legacy_apder_strong_frontier[OF legacy x])
      have "rsize x = rsize_set {x}"
        by (simp add: rsize_set_def)
      also have "... \<le> rsize_set (apder_strong_frontier r)"
        by (rule rsize_set_mono) (use x in auto)
      also have "... \<le> ?B"
        by (rule rsize_set_apder_strong_frontier_expanded_cubic_size_bound
            [OF nf])
      finally have x_size: "rsize x \<le> ?B" .
      show "x \<in> sizeNregex ?B"
        using x_legacy x_size by (simp add: sizeNregex_def)
    qed
    show ?thesis
      unfolding normal_strong_scan_owner_def
      by (rule finite_raw_shared_prune_active_suffix_owner_sizeNregex
          [OF seed_subset])
  qed
  have rows_size: "rsizes ?rows \<le> C * ?B"
  proof -
    have member_size: "\<And>x. x \<in> ?U \<Longrightarrow> rsize x \<le> ?B"
      by (rule normal_strong_scan_owner_member_expanded_cubic_size[OF nf])
    have "rsizes ?rows \<le> rsize_set ?U"
      by (rule rsizes_distinct_subset_rsize_set)
        (use rows_subset finite_owner in auto)
    also have "... \<le> card ?U * ?B"
      by (rule rsize_set_le_card_times_bound[OF finite_owner member_size])
    also have "... \<le> C * ?B"
      by (rule mult_right_mono[OF owner_card]) simp
    finally show ?thesis .
  qed
  show "RLS (set ?rows) = Ders (s @ [c]) (RL r)"
    using contract by blast
  show "set ?rows \<subseteq> ?U"
    by (rule rows_subset)
  show "length ?rows \<le> C"
  proof -
    have rows_distinct: "distinct ?rows"
      by (rule distinct_rpder_strong_rows_raw)
    have "length ?rows = card (set ?rows)"
      using rows_distinct by (simp add: distinct_card)
    also have "... \<le> card ?U"
      by (rule card_mono[OF finite_owner rows_subset])
    also have "... \<le> C"
      by (rule owner_card)
    finally show ?thesis .
  qed
  show "card (set ?rows) \<le> C"
  proof -
    have "card (set ?rows) \<le> card ?U"
      by (rule card_mono[OF finite_owner rows_subset])
    also have "... \<le> C"
      by (rule owner_card)
    finally show ?thesis .
  qed
  show "rlinear_termss ?rows \<le> C * ?B"
    using rlinear_termss_le_rsizes[of ?rows] rows_size by linarith
  show "rsizes ?rows \<le> C * ?B"
    by (rule rows_size)
qed

theorem rpder_strong_dcanon_afactored1_dlform_cubic_interface:
  assumes legacy: "legacy_rrexp r"
    and dlform_cubic:
      "rsize_set (afactored1_strong_dlform_universe r s c) \<le>
        2 * (rsize r + 3) ^ 3"
  shows "RLS (set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s))) =
      Ders (s @ [c]) (RL r) \<and>
    row_dlformss_disjoint
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<and>
    (\<forall>q \<in> set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)).
      row_dlforms_live q) \<and>
    (\<forall>q \<in> set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)).
      row_dlforms_size_paid q) \<and>
    row_dlformss
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) =
      row_dlformss (rpder_strong_rows_raw c (afactored1 r s)) \<and>
    row_dlformss
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<subseteq>
      afactored1_strong_dlform_universe r s c \<and>
    length
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      6 * (rsize r + 3) ^ 3 \<and>
    card (set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s))) \<le>
      6 * (rsize r + 3) ^ 3 \<and>
    rlinear_termss
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      6 * (rsize r + 3) ^ 3 \<and>
    rsizes
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      6 * (rsize r + 3) ^ 3"
proof (intro conjI)
  let ?rows = "rpder_strong_dcanon_rows_raw c (afactored1 r s)"
  have contract:
      "RLS (set ?rows) = Ders (s @ [c]) (RL r) \<and>
      row_dlformss_disjoint ?rows \<and>
      (\<forall>q \<in> set ?rows. row_dlforms_live q) \<and>
      (\<forall>q \<in> set ?rows. row_dlforms_size_paid q) \<and>
      row_dlformss ?rows =
        row_dlformss (rpder_strong_rows_raw c (afactored1 r s)) \<and>
      row_dlformss ?rows \<subseteq>
        afactored1_strong_dlform_universe r s c \<and>
      rsizes ?rows \<le> 6 * (rsize r + 3) ^ 3"
    by (rule
        rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_cubic_contractI
        [OF legacy dlform_cubic])
  have budgets:
      "length ?rows \<le> 6 * (rsize r + 3) ^ 3 \<and>
      card (set ?rows) \<le> 6 * (rsize r + 3) ^ 3 \<and>
      rlinear_termss ?rows \<le> 6 * (rsize r + 3) ^ 3 \<and>
      rsizes ?rows \<le> 6 * (rsize r + 3) ^ 3"
    by (rule
        rpder_strong_dcanon_rows_raw_afactored1_dlform_universe_cubic_budgetsI
        [OF legacy dlform_cubic])
  show "RLS (set ?rows) = Ders (s @ [c]) (RL r)"
    using contract by blast
  show "row_dlformss_disjoint ?rows"
    using contract by blast
  show "\<forall>q \<in> set ?rows. row_dlforms_live q"
    using contract by blast
  show "\<forall>q \<in> set ?rows. row_dlforms_size_paid q"
    using contract by blast
  show "row_dlformss ?rows =
      row_dlformss (rpder_strong_rows_raw c (afactored1 r s))"
    using contract by blast
  show "row_dlformss ?rows \<subseteq>
      afactored1_strong_dlform_universe r s c"
    using contract by blast
  show "length ?rows \<le> 6 * (rsize r + 3) ^ 3"
    using budgets by blast
  show "card (set ?rows) \<le> 6 * (rsize r + 3) ^ 3"
    using budgets by blast
  show "rlinear_termss ?rows \<le> 6 * (rsize r + 3) ^ 3"
    using budgets by blast
  show "rsizes ?rows \<le> 6 * (rsize r + 3) ^ 3"
    using budgets by blast
qed

theorem rpder_strong_dcanon_afactored1_normal_strong_dlfrontier_cubic_interface:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
    and dlfrontier_cubic:
      "rsize_set (normal_strong_dlfrontier r) \<le>
        C * (apder_awidth r + rsize r + 3) ^ 3"
  shows "RLS (set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s))) =
      Ders (s @ [c]) (RL r) \<and>
    row_dlformss_disjoint
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<and>
    (\<forall>q \<in> set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)).
      row_dlforms_live q) \<and>
    (\<forall>q \<in> set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)).
      row_dlforms_size_paid q) \<and>
    row_dlformss
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<subseteq>
      normal_strong_dlfrontier r \<and>
    length
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    card (set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s))) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rlinear_termss
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rsizes
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3"
proof (intro conjI)
  let ?rows = "rpder_strong_dcanon_rows_raw c (afactored1 r s)"
  let ?B = "(apder_awidth r + rsize r + 3) ^ 3"
  have apder_cubic:
      "rsize_set (apder_strong_dlfrontier r) \<le> C * ?B"
    using dlfrontier_cubic
    by (simp add: normal_strong_dlfrontier_def)
  have contract:
      "RLS (set ?rows) = Ders (s @ [c]) (RL r) \<and>
      row_dlformss_disjoint ?rows \<and>
      row_dlformss ?rows \<subseteq> apder_strong_dlfrontier r \<and>
      rsizes ?rows \<le> 3 * C * ?B"
    by (rule
        rpder_strong_dcanon_rows_raw_afactored1_apder_strong_dlfrontier_cubic_contractI
        [OF legacy nf apder_cubic])
  have budgets:
      "length ?rows \<le> 3 * C * ?B \<and>
      card (set ?rows) \<le> 3 * C * ?B \<and>
      rlinear_termss ?rows \<le> 3 * C * ?B \<and>
      rsizes ?rows \<le> 3 * C * ?B"
    by (rule
        rpder_strong_dcanon_rows_raw_afactored1_apder_strong_dlfrontier_cubic_budgetsI
        [OF legacy nf apder_cubic])
  show "RLS (set ?rows) = Ders (s @ [c]) (RL r)"
    using contract by blast
  show "row_dlformss_disjoint ?rows"
    using contract by blast
  show "\<forall>q \<in> set ?rows. row_dlforms_live q"
    using row_dlforms_live_paid_rpder_strong_dcanon_rows_raw by blast
  show "\<forall>q \<in> set ?rows. row_dlforms_size_paid q"
    using row_dlforms_live_paid_rpder_strong_dcanon_rows_raw by blast
  show "row_dlformss ?rows \<subseteq> normal_strong_dlfrontier r"
    using contract by (simp add: normal_strong_dlfrontier_def)
  show "length ?rows \<le> 3 * C * ?B"
    using budgets by blast
  show "card (set ?rows) \<le> 3 * C * ?B"
    using budgets by blast
  show "rlinear_termss ?rows \<le> 3 * C * ?B"
    using budgets by blast
  show "rsizes ?rows \<le> 3 * C * ?B"
    using budgets by blast
qed

theorem rpder_strong_dcanon_afactored1_normal_frontier_dlclosure_cubic_interface:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
    and closure_cubic:
      "rsize_set
        (rsimpStrong_dlform_closure (normal_antimirov_frontier r)) \<le>
        C * (apder_awidth r + rsize r + 3) ^ 3"
  shows "RLS (set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s))) =
      Ders (s @ [c]) (RL r) \<and>
    row_dlformss_disjoint
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<and>
    (\<forall>q \<in> set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)).
      row_dlforms_live q) \<and>
    (\<forall>q \<in> set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)).
      row_dlforms_size_paid q) \<and>
    row_dlformss
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<subseteq>
      normal_strong_dlfrontier r \<and>
    length
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    card (set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s))) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rlinear_termss
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rsizes
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3"
proof -
  have dlfrontier_cubic:
      "rsize_set (normal_strong_dlfrontier r) \<le>
        C * (apder_awidth r + rsize r + 3) ^ 3"
    by (rule
        rsize_set_normal_strong_dlfrontier_cubic_from_frontier_closureI
        [OF nf closure_cubic])
  show ?thesis
    by (rule
        rpder_strong_dcanon_afactored1_normal_strong_dlfrontier_cubic_interface
        [OF legacy nf dlfrontier_cubic])
qed

theorem rpder_strong_dcanon_afactored1_normal_frontier_sum_cubic_interface:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
    and sum_cubic:
      "(\<Sum>p \<in> normal_antimirov_frontier r.
        rsize_set (row_dlforms (rsimpStrong_raw p))) \<le>
        C * (apder_awidth r + rsize r + 3) ^ 3"
  shows "RLS (set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s))) =
      Ders (s @ [c]) (RL r) \<and>
    row_dlformss_disjoint
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<and>
    (\<forall>q \<in> set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)).
      row_dlforms_live q) \<and>
    (\<forall>q \<in> set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)).
      row_dlforms_size_paid q) \<and>
    row_dlformss
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<subseteq>
      normal_strong_dlfrontier r \<and>
    length
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    card (set
      (rpder_strong_dcanon_rows_raw c (afactored1 r s))) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rlinear_termss
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3 \<and>
    rsizes
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<le>
      3 * C * (apder_awidth r + rsize r + 3) ^ 3"
proof -
  have closure_cubic:
      "rsize_set
        (rsimpStrong_dlform_closure (normal_antimirov_frontier r)) \<le>
        C * (apder_awidth r + rsize r + 3) ^ 3"
    by (rule
        rsize_set_normal_frontier_strong_dlclosure_cubic_from_sumI
        [OF sum_cubic])
  show ?thesis
    by (rule
        rpder_strong_dcanon_afactored1_normal_frontier_dlclosure_cubic_interface
        [OF legacy nf closure_cubic])
qed

theorem rpder_strong_dcanon_afactored1_same_front_contract:
  assumes legacy: "legacy_rrexp r"
  shows "same_strong_aseq_front_rows r (s @ [c])
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<and>
    aseq_termss
      (rpder_strong_dcanon_rows_raw c (afactored1 r s)) \<subseteq>
      strong_derivative_front_terms r (s @ [c]) \<and>
    card (strong_derivative_front_terms r (s @ [c])) \<le>
      2 * (rsize r + 2) ^ 3 \<and>
    rsize_set (strong_derivative_front_terms r (s @ [c])) \<le>
      2 * (rsize r + 2) ^ 3 \<and>
    (\<forall>q \<in> strong_derivative_front_terms r (s @ [c]).
      rsize q \<le> Suc (rsize r + rsize r))"
proof -
  have contract:
      "same_strong_aseq_front_rows r (s @ [c])
        (row_dlform_canonical_rows
          (rpder_strong_rows_raw c (afactored1 r s))) \<and>
      aseq_termss
        (row_dlform_canonical_rows
          (rpder_strong_rows_raw c (afactored1 r s))) \<subseteq>
        strong_derivative_front_terms r (s @ [c]) \<and>
      card (strong_derivative_front_terms r (s @ [c])) \<le>
        2 * (rsize r + 2) ^ 3 \<and>
      rsize_set (strong_derivative_front_terms r (s @ [c])) \<le>
        2 * (rsize r + 2) ^ 3 \<and>
      (\<forall>q \<in> strong_derivative_front_terms r (s @ [c]).
        rsize q \<le> Suc (rsize r + rsize r))"
    by (rule
        row_dlform_canonical_rpder_strong_rows_raw_afactored1_same_strong_budget_contract
        [OF legacy])
  show ?thesis
    using contract
    by (simp add: rpder_strong_dcanon_rows_raw_def)
qed

theorem strong_once_after_normal_derivative_cubic:
  assumes legacy: "legacy_rrexp r"
    and nf: "apder_nf r"
  shows "RL (rsimpStrong_raw (rders_pder_norm r s)) =
      Ders s (RL r) \<and>
    rsize (rsimpStrong_raw (rders_pder_norm r s)) \<le>
      Suc (2 * (apder_awidth r + rsize r + 3) ^ 3)"
  using rsimpStrong_raw_rders_pder_norm_expanded_cubic_contract
    [OF legacy nf, of s]
  by blast

lemma normal_frontier_keeps_whole_residuals_a_aa:
  fixes a :: char
  defines "r \<equiv> RSEQ (RCHAR a) (RSEQ (RCHAR a) (RCHAR a))"
  shows "r \<in> normal_antimirov_frontier r"
    and "RSEQ (RCHAR a) (RCHAR a) \<in> normal_antimirov_frontier r"
    and "RCHAR a \<in> normal_antimirov_frontier r"
  by (simp_all add: r_def normal_antimirov_frontier_def
      apder_frontier_def)

lemma normal_frontier_keeps_whole_residuals_a_alt_tail:
  fixes a b :: char
  assumes neq: "a \<noteq> b"
  defines "r \<equiv> RSEQ (RCHAR a)
    (RALTS [RCHAR b, RCHAR b, RCHAR b])"
  shows "r \<in> normal_antimirov_frontier r"
    and "RCHAR b \<in> normal_antimirov_frontier r"
    and "RCHAR a \<notin> normal_antimirov_frontier r"
  using neq by (auto simp add: r_def normal_antimirov_frontier_def
      apder_frontier_def)

lemma normal_frontier_keeps_alt_prefix_tail_whole:
  fixes a b c :: char
  defines "r \<equiv> RSEQ (RALTS [RCHAR a, RCHAR b]) (RCHAR c)"
  shows "r \<in> normal_antimirov_frontier r"
    and "RCHAR c \<in> normal_antimirov_frontier r"
    and "RSEQ (RCHAR a) (RCHAR c) \<notin>
      normal_antimirov_frontier r"
    and "RSEQ (RCHAR b) (RCHAR c) \<notin>
      normal_antimirov_frontier r"
  by (simp_all add: r_def normal_antimirov_frontier_def
      apder_frontier_def rsimp7_SEQ_atom_def)

lemma row_dlforms_splits_alt_prefix_tail:
  fixes a b c :: char
  defines "r \<equiv> RSEQ (RALTS [RCHAR a, RCHAR b]) (RCHAR c)"
  shows "RSEQ (RCHAR a) (RCHAR c) \<in> row_dlforms r"
    and "RSEQ (RCHAR b) (RCHAR c) \<in> row_dlforms r"
  by (simp_all add: r_def rsimp7_SEQ_atom_def)

lemma normal_frontier_contains_reassociated_star_residual:
  fixes a b d :: char
  assumes "a \<noteq> b"
  defines "root \<equiv>
    RSEQ (RSEQ (RSTAR (RCHAR a)) (RCHAR b)) (RCHAR d)"
  defines "residual \<equiv>
    RSEQ (RSTAR (RCHAR a)) (RSEQ (RCHAR b) (RCHAR d))"
  shows "residual \<in> normal_antimirov_frontier root"
  using assms
  by (simp add: root_def residual_def normal_antimirov_frontier_def
      apder_frontier_def rsimp7_SEQ_atom_def)

section \<open>Strong-Prune Gap for the Normal Frontier\<close>

text \<open>
  The normal frontier above is the right first-stage Antimirov universe, but
  it is not itself closed under the row-pruning operation used by
  @{const rsimpStrong_prune_pair_raw}.  The missing objects are exactly the
  same-front combinations that the second stage has to account for.
\<close>

lemma raw_shared_prune_bad_result_notin_normal_antimirov_frontier:
  "raw_shared_prune_bad_result \<notin>
    normal_antimirov_frontier raw_shared_prune_bad_root"
  by (simp add: raw_shared_prune_bad_root_def
      raw_shared_prune_bad_result_def
      normal_antimirov_frontier_def apder_frontier_def
      rsimp7_SEQ_atom_def)

lemma normal_antimirov_frontier_not_raw_shared_prune_closed:
  "\<not> raw_shared_prune_closed
    (normal_antimirov_frontier raw_shared_prune_bad_root)"
proof
  let ?a = "RCHAR (CHR ''a'')"
  let ?b = "RCHAR (CHR ''b'')"
  let ?c = "RCHAR (CHR ''c'')"
  let ?d = "RCHAR (CHR ''d'')"
  let ?z = "RCHAR (CHR ''z'')"
  let ?U = "normal_antimirov_frontier raw_shared_prune_bad_root"
  assume closed: "raw_shared_prune_closed ?U"
  have earlier: "RSEQ (RALTS [?a, ?b, ?c]) ?z \<in> ?U"
    by (simp add: raw_shared_prune_bad_root_def
        normal_antimirov_frontier_def apder_frontier_def)
  have later: "RSEQ (RALTS [?a, ?b, ?c, ?d]) ?z \<in> ?U"
    by (simp add: raw_shared_prune_bad_root_def
        normal_antimirov_frontier_def apder_frontier_def)
  have closedD:
    "\<And>lrs rrs k. RSEQ (RALTS lrs) k \<in> ?U \<Longrightarrow>
      RSEQ (RALTS rrs) k \<in> ?U \<Longrightarrow>
      set (rflts [rsimp7_SEQ_atom
        (rsimp_ALTs (rprune_eq_against lrs rrs)) k]) \<subseteq> ?U"
    using closed by (simp add: raw_shared_prune_closed_def)
  have result: "set (rflts [rsimp7_SEQ_atom
      (rsimp_ALTs (rprune_eq_against [?a, ?b, ?c] [?a, ?b, ?c, ?d])) ?z])
      \<subseteq> ?U"
    by (rule closedD[OF earlier later])
  have "raw_shared_prune_bad_result \<in> ?U"
    using result by (simp add: raw_shared_prune_bad_result_def
        rsimp7_SEQ_atom_def)
  then show False
    using raw_shared_prune_bad_result_notin_normal_antimirov_frontier
    by blast
qed

lemma raw_shared_prune_bad_result_in_normal_same_front_prune_closure:
  "raw_shared_prune_bad_result \<in>
    normal_same_front_prune_closure raw_shared_prune_bad_root"
proof -
  let ?a = "RCHAR (CHR ''a'')"
  let ?b = "RCHAR (CHR ''b'')"
  let ?c = "RCHAR (CHR ''c'')"
  let ?d = "RCHAR (CHR ''d'')"
  let ?z = "RCHAR (CHR ''z'')"
  let ?earlier = "RSEQ (RALTS [?a, ?b, ?c]) ?z"
  let ?later = "RSEQ (RALTS [?a, ?b, ?c, ?d]) ?z"
  let ?U = "normal_antimirov_frontier raw_shared_prune_bad_root"
  have earlier: "?earlier \<in> ?U"
    by (simp add: raw_shared_prune_bad_root_def
        normal_antimirov_frontier_def apder_frontier_def)
  have later: "?later \<in> ?U"
    by (simp add: raw_shared_prune_bad_root_def
        normal_antimirov_frontier_def apder_frontier_def)
  have same_key:
    "raw_shared_prune_suffix_key ?earlier =
      raw_shared_prune_suffix_key ?later"
    by (simp add: raw_shared_prune_suffix_key_def)
  have out: "raw_shared_prune_bad_result \<in>
      raw_shared_prune_pair_outputs ?earlier ?later"
    by (simp add: raw_shared_prune_pair_outputs_def
        raw_shared_prune_bad_result_def rsimpStrong_prune_pair_raw_def
        rsimp7_SEQ_atom_def)
  have "raw_shared_prune_pair_outputs ?earlier ?later \<subseteq>
      raw_shared_prune_same_suffix_closure ?U"
    by (rule raw_shared_prune_same_suffix_pair_outputs_subset_closureI
        [OF earlier later same_key])
  then have "raw_shared_prune_bad_result \<in>
      raw_shared_prune_same_suffix_closure ?U"
    using out by blast
  then show ?thesis
    by (simp add: normal_same_front_prune_closure_def)
qed

text \<open>
  Clean-domain propagation to the static row carrier.  The cubic gate applies
  the clean-domain D law at each actual row (rows live in @{term "apder_rows r"}
  via @{thm afactored1_apder_rows_subset}) and at the continuations produced by
  @{const rsimp4_SEQ_atom}; for that the rows must be @{const apder_clean}.
  Cleanliness is PROPAGATED from an assumed-clean root: @{const apder_nf} alone
  does not force @{const apder_zero_budget_trivial} (for instance
  @{term "RALTS [RONE]"} is nf, legacy and rntimes-free, yet
  @{term "apder_zw2 (RALTS [RONE]) = 0"}), so the root carries the budget and
  every subterm/term inherits it.
\<close>

lemma apder_clean_RONE: "apder_clean RONE"
  by (simp add: apder_clean_def)

lemma rntimes_free_apder_terms:
  assumes free: "rntimes_free r"
    and p: "p \<in> apder_terms r"
  shows "rntimes_free p"
  using free p
proof (induct r arbitrary: p)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR c)
  then have "p = RONE" by simp
  then show ?case by simp
next
  case (RALTS rs)
  then obtain q where q: "q \<in> set rs" "p \<in> apder_terms q"
    by auto
  have "rntimes_free q"
    using RALTS.prems q by simp
  then show ?case
    using RALTS.hyps[OF q(1)] q by blast
next
  case (RSEQ r1 r2)
  have p_cases:
      "p \<in> (\<lambda>x. rsimp4_SEQ_atom x r2) ` apder_terms r1 \<or>
        p \<in> apder_terms r2"
    using RSEQ.prems by simp
  show ?case
  proof (rule disjE[OF p_cases])
    assume "p \<in> (\<lambda>x. rsimp4_SEQ_atom x r2) ` apder_terms r1"
    then obtain x where x: "x \<in> apder_terms r1"
        "p = rsimp4_SEQ_atom x r2"
      by blast
    have "rntimes_free x"
      by (rule RSEQ.hyps(1)[OF _ x(1)]) (use RSEQ.prems in simp)
    moreover have "rntimes_free r2"
      using RSEQ.prems by simp
    ultimately show "rntimes_free p"
      by (simp add: x(2) rntimes_free_rsimp4_SEQ_atom)
  next
    assume right: "p \<in> apder_terms r2"
    show "rntimes_free p"
      by (rule RSEQ.hyps(2)[OF _ right]) (use RSEQ.prems in simp)
  qed
next
  case (RSTAR r)
  then obtain x where x: "x \<in> apder_terms r"
      "p = rsimp4_SEQ_atom x (RSTAR r)"
    by auto
  have "rntimes_free x"
    by (rule RSTAR.hyps[OF _ x(1)]) (use RSTAR.prems in simp)
  moreover have "rntimes_free (RSTAR r)"
    using RSTAR.prems by simp
  ultimately show ?case
    by (simp add: x(2) rntimes_free_rsimp4_SEQ_atom)
next
  case (RNTIMES r n)
  have False
    using RNTIMES.prems(1) by simp
  then show ?case ..
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have False
    using RBACKREF4.prems(2) by (simp only: apder_terms.simps empty_iff)
  then show ?case ..
next
  case (RHALF r cs rep)
  have False
    using RHALF.prems(2) by (simp only: apder_terms.simps empty_iff)
  then show ?case ..
next
  case (RRESIDUE cs rep)
  have False
    using RRESIDUE.prems(2) by (simp only: apder_terms.simps empty_iff)
  then show ?case ..
qed

lemma apder_zero_budget_trivial_rsubterms:
  assumes "apder_zero_budget_trivial r"
    and "q \<in> rsubterms r"
  shows "apder_zero_budget_trivial q"
  using assms
proof (induct r arbitrary: q)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR c)
  then show ?case by simp
next
  case (RALTS rs)
  show ?case
  proof (cases "q = RALTS rs")
    case True
    then show ?thesis using RALTS.prems by simp
  next
    case False
    then obtain p where p: "p \<in> set rs" "q \<in> rsubterms p"
      using RALTS.prems by auto
    have p_zbt: "apder_zero_budget_trivial p"
      by (rule apder_zero_budget_trivial_RALTS_member[OF RALTS.prems(1) p(1)])
    show ?thesis
      using RALTS.hyps p p_zbt by auto
  qed
next
  case (RSEQ r1 r2)
  show ?case
  proof (cases "q = RSEQ r1 r2")
    case True
    then show ?thesis using RSEQ.prems by simp
  next
    case False
    then have q_cases: "q \<in> rsubterms r1 \<or> q \<in> rsubterms r2"
      using RSEQ.prems by simp
    show ?thesis
    proof (rule disjE[OF q_cases])
      assume q1: "q \<in> rsubterms r1"
      have "apder_zero_budget_trivial r1"
        using RSEQ.prems(1) by simp
      then show ?thesis by (rule RSEQ.hyps(1)[OF _ q1])
    next
      assume q2: "q \<in> rsubterms r2"
      have "apder_zero_budget_trivial r2"
        using RSEQ.prems(1) by simp
      then show ?thesis by (rule RSEQ.hyps(2)[OF _ q2])
    qed
  qed
next
  case (RSTAR r)
  show ?case
  proof (cases "q = RSTAR r")
    case True
    then show ?thesis using RSTAR.prems by simp
  next
    case False
    then have qsub: "q \<in> rsubterms r"
      using RSTAR.prems(2) by simp
    have "apder_zero_budget_trivial r"
      using RSTAR.prems(1) by simp
    then show ?thesis by (rule RSTAR.hyps[OF _ qsub])
  qed
next
  case (RNTIMES r n)
  have False using RNTIMES.prems(1) by simp
  then show ?case ..
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have False using RBACKREF4.prems(1) by simp
  then show ?case ..
next
  case (RHALF r cs rep)
  have False using RHALF.prems(1) by simp
  then show ?case ..
next
  case (RRESIDUE cs rep)
  have False using RRESIDUE.prems(1) by simp
  then show ?case ..
qed

lemma apder_zero_budget_trivial_apder_terms:
  assumes zbt: "apder_zero_budget_trivial r"
    and p: "p \<in> apder_terms r"
  shows "apder_zero_budget_trivial p"
  using zbt p
proof (induct r arbitrary: p)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR c)
  then have "p = RONE" by simp
  then show ?case by simp
next
  case (RALTS rs)
  then obtain q where q: "q \<in> set rs" "p \<in> apder_terms q"
    by auto
  have "apder_zero_budget_trivial q"
    by (rule apder_zero_budget_trivial_RALTS_member[OF RALTS.prems(1) q(1)])
  then show ?case
    using RALTS.hyps[OF q(1)] q by blast
next
  case (RSEQ r1 r2)
  have p_cases:
      "p \<in> (\<lambda>x. rsimp4_SEQ_atom x r2) ` apder_terms r1 \<or>
        p \<in> apder_terms r2"
    using RSEQ.prems by simp
  show ?case
  proof (rule disjE[OF p_cases])
    assume "p \<in> (\<lambda>x. rsimp4_SEQ_atom x r2) ` apder_terms r1"
    then obtain x where x: "x \<in> apder_terms r1"
        "p = rsimp4_SEQ_atom x r2"
      by blast
    have "apder_zero_budget_trivial x"
      by (rule RSEQ.hyps(1)[OF _ x(1)]) (use RSEQ.prems in simp)
    moreover have "apder_zero_budget_trivial r2"
      using RSEQ.prems by simp
    ultimately show "apder_zero_budget_trivial p"
      by (simp add: x(2) apder_zero_budget_trivial_rsimp4_SEQ_atom)
  next
    assume right: "p \<in> apder_terms r2"
    show "apder_zero_budget_trivial p"
      by (rule RSEQ.hyps(2)[OF _ right]) (use RSEQ.prems in simp)
  qed
next
  case (RSTAR r)
  then obtain x where x: "x \<in> apder_terms r"
      "p = rsimp4_SEQ_atom x (RSTAR r)"
    by auto
  have "apder_zero_budget_trivial x"
    by (rule RSTAR.hyps[OF _ x(1)]) (use RSTAR.prems in simp)
  moreover have "apder_zero_budget_trivial (RSTAR r)"
    using RSTAR.prems by simp
  ultimately show ?case
    by (simp add: x(2) apder_zero_budget_trivial_rsimp4_SEQ_atom)
next
  case (RNTIMES r n)
  have False using RNTIMES.prems(1) by simp
  then show ?case ..
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  have False using RBACKREF4.prems(1) by simp
  then show ?case ..
next
  case (RHALF r cs rep)
  have False using RHALF.prems(1) by simp
  then show ?case ..
next
  case (RRESIDUE cs rep)
  have False using RRESIDUE.prems(1) by simp
  then show ?case ..
qed

lemma apder_clean_apder_rows:
  assumes clean: "apder_clean r"
    and x: "x \<in> apder_rows r"
  shows "apder_clean x"
proof -
  have legacy: "legacy_rrexp r" and free: "rntimes_free r"
    and nf: "apder_nf r" and zbt: "apder_zero_budget_trivial r"
    using clean by (simp_all add: apder_clean_def)
  from x consider
      "x = r"
    | "x \<in> rfrontier r"
    | q where "q \<in> apder_terms r" "x \<in> rfrontier q"
    by (auto simp add: apder_rows_def apder_frontier_def)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using clean by simp
  next
    case 2
    have xsub: "x \<in> rsubterms r"
      using 2 rfrontier_subset_rsubterms by blast
    have "legacy_rrexp x"
      by (rule legacy_rrexp_rsubterms[OF legacy xsub])
    moreover have "rntimes_free x"
      by (rule rntimes_free_legacy_rsubterms[OF legacy free xsub])
    moreover have "apder_zero_budget_trivial x"
      by (rule apder_zero_budget_trivial_rsubterms[OF zbt xsub])
    moreover have "apder_nf x"
      using apder_nf_rfrontier_member_props[OF nf 2] by blast
    ultimately show ?thesis
      by (simp add: apder_clean_def)
  next
    case 3
    have q_legacy: "legacy_rrexp q"
      by (rule legacy_apder_terms[OF legacy 3(1)])
    have q_free: "rntimes_free q"
      by (rule rntimes_free_apder_terms[OF free 3(1)])
    have q_nf: "apder_nf q"
      by (rule apder_nf_apder_terms[OF nf 3(1)])
    have q_zbt: "apder_zero_budget_trivial q"
      by (rule apder_zero_budget_trivial_apder_terms[OF zbt 3(1)])
    have xsub: "x \<in> rsubterms q"
      using 3(2) rfrontier_subset_rsubterms by blast
    have "legacy_rrexp x"
      by (rule legacy_rrexp_rsubterms[OF q_legacy xsub])
    moreover have "rntimes_free x"
      by (rule rntimes_free_legacy_rsubterms[OF q_legacy q_free xsub])
    moreover have "apder_zero_budget_trivial x"
      by (rule apder_zero_budget_trivial_rsubterms[OF q_zbt xsub])
    moreover have "apder_nf x"
      using apder_nf_rfrontier_member_props[OF q_nf 3(2)] by blast
    ultimately show ?thesis
      by (simp add: apder_clean_def)
  qed
qed

end
