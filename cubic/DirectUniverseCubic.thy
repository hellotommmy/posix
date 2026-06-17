theory DirectUniverseCubic
  imports "Posix_Antimirov.AntimirovFactoredTransition" DirectUniverseCubic_L3
begin

(* Owner: WORKER-OPUS.  DIRECT-UNIVERSE CUBIC route (see DIRECT_UNIVERSE_CUBIC_ROUTE.md).

   The Gate's actual target universe is the strong-opened frontier over the DEDUPLICATED
   Antimirov rows `apder_rows r` (NOT the full live-row universe `D r`): the gate rows are
   contained in `apder_strong_dlfrontier r = (UN q : apder_rows r. row_dlforms (rsimpStrong_raw q))`
   (row_dlformss_rpder_strong_rows_raw_afactored1_subset_apder_strong_dlfrontier @19490).
   `apder_rows r` is the set whose CARD is linear (card_apder_rows_clean_le_rsize_plus_2 @37190),
   so the linear-count x quadratic-opening decomposition lands the cube.  (The full
   `partial_derivative_live_row_universe r` has only QUADRATIC card, so the assembly is done over
   `apder_rows r`; the gate-rows inclusion goes through exactly this set.)

   L1 (subadditivity of rsize_set over a finite union) ALREADY EXISTS as
   `rsize_set_UN_le` @537 -- reused directly, no new lemma needed.

   L3 (per-member opening <= (rsize r+2)^2, provenance-based) is owned by WORKER-CODEX in
   DirectUniverseCubic_L3 as `member_opened_quadratic`.  Here we carry it as a local `assumes`
   hypothesis on the members of `apder_rows r`, then discharge it unconditionally once L3 lands. *)

subsection \<open>Cube arithmetic\<close>

lemma cube_plus2_le_two_cube_plus3:
  fixes n :: nat
  shows "(n + 2) ^ 3 \<le> 2 * (n + 3) ^ 3"
proof -
  have "(n + 2) ^ 3 \<le> (n + 3) ^ 3"
    by (rule power_mono) simp_all
  also have "... \<le> 2 * (n + 3) ^ 3"
    by simp
  finally show ?thesis .
qed

lemma card_times_quadratic_le_cube:
  fixes n :: nat
  assumes "c \<le> n + 2"
  shows "c * (n + 2) ^ 2 \<le> 2 * (n + 3) ^ 3"
proof -
  have "c * (n + 2) ^ 2 \<le> (n + 2) * (n + 2) ^ 2"
    by (rule mult_right_mono[OF assms]) simp
  also have "... = (n + 2) ^ 3"
    by (simp add: power3_eq_cube power2_eq_square)
  also have "... \<le> 2 * (n + 3) ^ 3"
    by (rule cube_plus2_le_two_cube_plus3)
  finally show ?thesis .
qed

subsection \<open>ASSEMBLE -- the direct cubic bound on the strong-opened gate universe\<close>

text \<open>
  Carry L3 (per-member opening) as a hypothesis on the members of @{term "apder_rows r"}.
  The chain is: unfold the strong dlfrontier to a finite union over @{term "apder_rows r"},
  apply L1 (@{thm rsize_set_UN_le}), bound each opening by @{term "(rsize r + 2)\<^sup>2"} (L3),
  collapse the constant sum to @{term "card (apder_rows r) * (rsize r + 2)\<^sup>2"}, bound the
  card by @{term "rsize r + 2"} (@{thm card_apder_rows_clean_le_rsize_plus_2}), and finish
  with cube arithmetic.
\<close>

lemma universe_le_cubic:
  assumes clean: "apder_clean r"
    and L3: "\<And>q. q \<in> apder_rows r \<Longrightarrow>
      rsize_set (row_dlforms (rsimpStrong_raw q)) \<le> (rsize r + 2)\<^sup>2"
  shows "rsize_set (apder_strong_dlfrontier r) \<le> 2 * (rsize r + 3) ^ 3"
proof -
  let ?D = "apder_rows r"
  let ?f = "\<lambda>q. row_dlforms (rsimpStrong_raw q)"
  have fin: "finite ?D"
    by simp
  have unfold: "apder_strong_dlfrontier r = (\<Union>q \<in> ?D. ?f q)"
    by (simp add: apder_strong_dlfrontier_def rsimpStrong_dlform_closure_def)
  have "rsize_set (apder_strong_dlfrontier r) =
      rsize_set (\<Union>q \<in> ?D. ?f q)"
    by (simp add: unfold)
  also have "... \<le> (\<Sum>q \<in> ?D. rsize_set (?f q))"
    by (rule rsize_set_UN_le[OF fin]) simp
  also have "... \<le> (\<Sum>q \<in> ?D. (rsize r + 2)\<^sup>2)"
    by (rule sum_mono) (rule L3)
  also have "... = card ?D * (rsize r + 2)\<^sup>2"
    by simp
  also have "... \<le> 2 * (rsize r + 3) ^ 3"
    by (rule card_times_quadratic_le_cube)
      (rule card_apder_rows_clean_le_rsize_plus_2[OF clean])
  finally show ?thesis .
qed

subsection \<open>BRIDGE -- the Gate from the direct universe bound\<close>

text \<open>
  Combine the GREEN gate-rows inclusion
  @{thm row_dlformss_rpder_strong_rows_raw_afactored1_subset_apder_strong_dlfrontier}
  (gate rows are contained in the strong dlfrontier) with @{thm rsize_set_mono} and the
  finite strong dlfrontier, then feed @{thm universe_le_cubic}.  This is the Gate, modulo L3.
\<close>

lemma actual_gate_from_direct_universe:
  assumes clean: "apder_clean r"
    and L3: "\<And>q. q \<in> apder_rows r \<Longrightarrow>
      rsize_set (row_dlforms (rsimpStrong_raw q)) \<le> (rsize r + 2)\<^sup>2"
  shows "rsize_set
      (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))) \<le>
    2 * (rsize r + 3) ^ 3"
proof -
  have nf: "apder_nf r"
    using clean unfolding apder_clean_def by simp
  have sub: "row_dlformss (rpder_strong_rows_raw c (afactored1 r s)) \<subseteq>
      apder_strong_dlfrontier r"
    by (rule row_dlformss_rpder_strong_rows_raw_afactored1_subset_apder_strong_dlfrontier
        [OF nf])
  have "rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))) \<le>
      rsize_set (apder_strong_dlfrontier r)"
    by (rule rsize_set_mono) (use sub in auto)
  also have "... \<le> 2 * (rsize r + 3) ^ 3"
    by (rule universe_le_cubic[OF clean L3])
  finally show ?thesis .
qed

subsection \<open>ROW-LEVEL bound -- cubic via (linear card) x (per-row quadratic), no cancellation\<close>

text \<open>
  The per-member route above carries the dead L3 (per-member opening, which composes to a quartic).
  This row-level route splits @{term "rsize_set (apder_strong_dlfrontier r)"} into
  COUNT x PER-ROW-SIZE via @{thm rsize_set_le_card_member_budgetI}: every row has size at most
  @{term "Suc ((rsize r + 2)\<^sup>2)"} (quadratic, EASY), and the row COUNT is linear -- carried here as
  the hypothesis @{term CARD}, to be discharged by the D-law-style linear count (the remaining crux).
\<close>

lemma budget_suc_quad_le_cube:
  fixes n :: nat
  shows "Suc n * Suc ((n + 2)\<^sup>2) \<le> 2 * (n + 3) ^ 3"
proof -
  have "2 * (n + 3) ^ 3 =
      Suc n * Suc ((n + 2)\<^sup>2) + (n ^ 3 + 13 * n\<^sup>2 + 45 * n + 49)"
    by (simp add: power2_eq_square power3_eq_cube algebra_simps)
  then show ?thesis by linarith
qed

lemma per_row_size_le_quadratic:
  assumes nf: "apder_nf r"
    and x: "x \<in> apder_strong_dlfrontier r"
  shows "rsize x \<le> Suc ((rsize r + 2)\<^sup>2)"
proof -
  from x obtain q where q: "q \<in> apder_rows r"
      and xq: "x \<in> row_dlforms (rsimpStrong_raw q)"
    by (auto simp: apder_strong_dlfrontier_def rsimpStrong_dlform_closure_def)
  have "rsize x \<le> rsize (rsimpStrong_raw q)"
    by (rule row_dlforms_member_size_le_rsize[OF xq])
  also have "... \<le> rsize q"
    by (rule rsize_rsimpStrong_raw_le)
  also have "... \<le> Suc ((rsize r + 2)\<^sup>2)"
    by (rule apder_rows_member_size_quadratic[OF nf q])
  finally show ?thesis .
qed

lemma universe_le_cubic_rowlevel:
  assumes clean: "apder_clean r"
    and CARD: "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
  shows "rsize_set (apder_strong_dlfrontier r) \<le> 2 * (rsize r + 3) ^ 3"
proof -
  have nf: "apder_nf r" using clean unfolding apder_clean_def by simp
  have fin: "finite (apder_strong_dlfrontier r)" by simp
  show ?thesis
  proof (rule rsize_set_le_card_member_budgetI[OF fin CARD])
    fix q assume "q \<in> apder_strong_dlfrontier r"
    then show "rsize q \<le> Suc ((rsize r + 2)\<^sup>2)"
      by (rule per_row_size_le_quadratic[OF nf])
  next
    show "Suc (rsize r) * Suc ((rsize r + 2)\<^sup>2) \<le> 2 * (rsize r + 3) ^ 3"
      by (rule budget_suc_quad_le_cube)
  qed
qed

lemma actual_gate_from_direct_universe_rowlevel:
  assumes clean: "apder_clean r"
    and CARD: "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
  shows "rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))) \<le>
    2 * (rsize r + 3) ^ 3"
proof -
  have nf: "apder_nf r" using clean unfolding apder_clean_def by simp
  have sub: "row_dlformss (rpder_strong_rows_raw c (afactored1 r s)) \<subseteq>
      apder_strong_dlfrontier r"
    by (rule row_dlformss_rpder_strong_rows_raw_afactored1_subset_apder_strong_dlfrontier[OF nf])
  have "rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))) \<le>
      rsize_set (apder_strong_dlfrontier r)"
    by (rule rsize_set_mono) (use sub in auto)
  also have "... \<le> 2 * (rsize r + 3) ^ 3"
    by (rule universe_le_cubic_rowlevel[OF clean CARD])
  finally show ?thesis .
qed

subsection \<open>D-law card migration for opened boundary forms\<close>

lemma card_opened_boundary_forms_le_apder_zw2:
  assumes clean_r: "apder_clean r"
    and clean_k: "apder_clean k"
  shows "card (opened_boundary_forms r k) \<le> apder_zw2 r"
  using clean_r clean_k
proof (induct r arbitrary: k)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR c)
  have "card (opened_boundary_forms (RCHAR c) k) =
      card (row_dlforms (rsimp4_SEQ_atom (RCHAR c) k) - row_dlforms k)"
    by (simp add: opened_boundary_forms_RCHAR_eq)
  also have "... \<le> 1"
    by (rule card_row_dlforms_rsimp4_SEQ_atom_RCHAR_diff_le_one)
  finally show ?case
    by simp
next
  case (RSEQ r1 r2)
  let ?m = "rsimp4_SEQ_atom r2 k"
  have c1: "apder_clean r1"
    using RSEQ.prems(1) by (rule apder_clean_RSEQ_left)
  have c2: "apder_clean r2"
    using RSEQ.prems(1) by (rule apder_clean_RSEQ_right)
  have cm: "apder_clean ?m"
    using c2 RSEQ.prems(2) by (rule sigma_clean)
  have sub: "opened_boundary_forms (RSEQ r1 r2) k \<subseteq>
      opened_boundary_forms r1 ?m \<union> opened_boundary_forms r2 k"
    by (rule opened_boundary_forms_RSEQ_subset)
  have "card (opened_boundary_forms (RSEQ r1 r2) k) \<le>
      card (opened_boundary_forms r1 ?m \<union> opened_boundary_forms r2 k)"
    by (rule card_mono) (use sub in auto)
  also have "... \<le>
      card (opened_boundary_forms r1 ?m) +
      card (opened_boundary_forms r2 k)"
    by (rule card_Un_le)
  also have "... \<le> apder_zw2 r1 + apder_zw2 r2"
    using RSEQ.hyps(1)[OF c1 cm] RSEQ.hyps(2)[OF c2 RSEQ.prems(2)]
    by simp
  finally show ?case
    by simp
next
  case (RALTS rs)
  have nf_r: "apder_nf (RALTS rs)"
    using RALTS.prems(1) unfolding apder_clean_def by simp
  have nf_k: "apder_nf k"
    using RALTS.prems(2) unfolding apder_clean_def by simp
  have sub: "opened_boundary_forms (RALTS rs) k \<subseteq>
      (\<Union>q \<in> set rs. opened_boundary_forms q k)"
    by (rule opened_boundary_forms_RALTS_subset[OF nf_r nf_k])
  have "card (opened_boundary_forms (RALTS rs) k) \<le>
      card (\<Union>q \<in> set rs. opened_boundary_forms q k)"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> (\<Sum>q \<in> set rs. card (opened_boundary_forms q k))"
    by (rule card_UN_le) auto
  also have "... \<le> (\<Sum>q \<in> set rs. apder_zw2 q)"
  proof (rule sum_mono)
    fix q
    assume q: "q \<in> set rs"
    have cq: "apder_clean q"
      using RALTS.prems(1) q by (rule apder_clean_RALTS_member)
    show "card (opened_boundary_forms q k) \<le> apder_zw2 q"
      using RALTS.hyps q cq RALTS.prems(2) by blast
  qed
  also have "... \<le> sum_list (map apder_zw2 rs)"
    by (rule sum_set_le_sum_list_nat)
  finally show ?case
    by simp
next
  case (RSTAR r)
  let ?m = "rsimp4_SEQ_atom (RSTAR r) k"
  let ?B = "row_dlformss_set (rfrontier ?m) - odfront k"
  have cr: "apder_clean r"
    using RSTAR.prems(1) by (rule apder_clean_RSTAR_body)
  have cm: "apder_clean ?m"
    using RSTAR.prems by (rule sigma_clean)
  have bcard: "card ?B \<le> 1"
  proof -
    have "?B = row_dlforms ?m - row_dlforms k"
      by simp
    then show ?thesis
      using card_row_dlforms_rsimp4_SEQ_atom_RSTAR_diff_le_one[of r k]
      by simp
  qed
  have sub: "opened_boundary_forms (RSTAR r) k \<subseteq>
      ?B \<union> opened_boundary_forms r ?m"
    by (rule opened_boundary_forms_RSTAR_subset)
  have "card (opened_boundary_forms (RSTAR r) k) \<le>
      card (?B \<union> opened_boundary_forms r ?m)"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> card ?B + card (opened_boundary_forms r ?m)"
    by (rule card_Un_le)
  also have "... \<le> 1 + apder_zw2 r"
    using bcard RSTAR.hyps[OF cr cm] by simp
  finally show ?case
    by simp
next
  case (RNTIMES r n)
  then show ?case by (simp add: apder_clean_def)
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case by (simp add: apder_clean_def)
next
  case (RHALF r cs rep)
  then show ?case by (simp add: apder_clean_def)
next
  case (RRESIDUE cs rep)
  then show ?case by (simp add: apder_clean_def)
qed

lemma card_le_Suc_card_Diff_singleton:
  assumes fin: "finite A"
  shows "card A \<le> Suc (card (A - {x}))"
proof -
  show ?thesis
  proof (cases "x \<in> A")
    case True
    have "A = insert x (A - {x})"
      using True by auto
    then have "card A = Suc (card (A - {x}))"
      using card_insert_disjoint[of "A - {x}" x] fin by simp
    then show ?thesis by simp
  next
    case False
    then have "A - {x} = A"
      by auto
    then show ?thesis
      by simp
  qed
qed

lemma card_le_rsize_set:
  assumes fin: "finite A"
  shows "card A \<le> rsize_set A"
proof -
  have "card A = (\<Sum>q \<in> A. 1)"
    by simp
  also have "... \<le> (\<Sum>q \<in> A. rsize q)"
    by (rule sum_mono) (rule size_geq1)
  also have "... = rsize_set A"
    by (simp add: rsize_set_def)
  finally show ?thesis .
qed

definition strong_apder_acc :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "strong_apder_acc r k =
    rsimpStrong_dlform_closure
      (rfrontier (rsimp4_SEQ_atom r k) \<union> apder_term_frontier_acc r k)"

lemma finite_strong_apder_acc [simp]:
  "finite (strong_apder_acc r k)"
  by (simp add: strong_apder_acc_def)

lemma strong_apder_acc_RSEQ_subset:
  "strong_apder_acc (RSEQ r1 r2) k \<subseteq>
    strong_apder_acc r1 (rsimp4_SEQ_atom r2 k) \<union>
    strong_apder_acc r2 k"
  by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

lemma rsimpStrong_dlform_closure_rfrontier_sigma_RCHAR_subset:
  "rsimpStrong_dlform_closure
      (rfrontier (rsimp4_SEQ_atom (RCHAR c) k)) \<subseteq>
    row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RCHAR c) k))"
  by (cases k)
    (auto simp add: rsimpStrong_dlform_closure_def)

lemma rsimpStrong_dlform_closure_rfrontier_sigma_RSTAR_subset:
  "rsimpStrong_dlform_closure
      (rfrontier (rsimp4_SEQ_atom (RSTAR r) k)) \<subseteq>
    row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))"
  by (cases k)
    (auto simp add: rsimpStrong_dlform_closure_def)

lemma strong_apder_acc_RSTAR_subset:
  "strong_apder_acc (RSTAR r) k \<subseteq>
    row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k)) \<union>
    strong_apder_acc r (rsimp4_SEQ_atom (RSTAR r) k)"
  using rsimpStrong_dlform_closure_rfrontier_sigma_RSTAR_subset[of r k]
  by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

lemma strong_apder_acc_RCHAR_subset:
  "strong_apder_acc (RCHAR c) k \<subseteq>
    row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RCHAR c) k)) \<union>
    row_dlformss_set (rsimpStrong_raw ` rfrontier k)"
  using rsimpStrong_dlform_closure_rfrontier_sigma_RCHAR_subset[of c k]
  by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
      row_dlformss_set_def)

lemma strong_apder_acc_RONE_RONE [simp]:
  "strong_apder_acc RONE RONE = {RONE}"
  by (simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

lemma apder_strong_dlfrontier_subset_strong_apder_acc_RONE:
  assumes nf: "apder_nf r"
  shows "apder_strong_dlfrontier r \<subseteq> strong_apder_acc r RONE"
proof
  fix x
  assume x: "x \<in> apder_strong_dlfrontier r"
  obtain p where p: "p \<in> apder_rows r"
      and xp: "x \<in> row_dlforms (rsimpStrong_raw p)"
    using x
    by (auto simp add: apder_strong_dlfrontier_def
        rsimpStrong_dlform_closure_def)
  have sigma: "rsimp4_SEQ_atom r RONE = r"
    by (rule sigma_RONE_id_nf[OF nf])
  have front_eq: "apder_frontier r =
      rfrontier r \<union> apder_term_frontier_acc r RONE"
    using apder_frontier_eq_rfrontier_union_acc[OF nf]
    by (simp add: apder_term_frontiers_def)
  let ?U = "rfrontier r \<union> apder_term_frontier_acc r RONE"
  have target: "strong_apder_acc r RONE =
      rsimpStrong_dlform_closure ?U"
    by (simp add: strong_apder_acc_def sigma)
  have "p = r \<or> p \<in> ?U"
    using p by (auto simp add: apder_rows_def front_eq)
  then show "x \<in> strong_apder_acc r RONE"
  proof
    assume pr: "p = r"
    have flat: "set (rflts [r]) \<subseteq> ?U"
      using rtail_nf_rflts_singleton_eq_rfrontier
        [OF apder_nf_imp_rtail_nf[OF nf]]
      by simp
    have "row_dlforms (rsimpStrong_raw r) \<subseteq>
        rsimpStrong_dlform_closure ?U"
      by (rule row_dlforms_rsimpStrong_raw_subset_dlform_closure_rflts_single
          [OF flat])
    then show ?thesis
      using xp pr target by blast
  next
    assume pU: "p \<in> ?U"
    have "row_dlforms (rsimpStrong_raw p) \<subseteq>
        rsimpStrong_dlform_closure ?U"
      by (rule row_dlforms_rsimpStrong_raw_self_closure[OF pU])
    then show ?thesis
      using xp target by blast
  qed
qed

end
