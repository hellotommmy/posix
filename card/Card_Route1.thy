theory Card_Route1
  imports "Posix_Cubic.DirectUniverseCubic"
begin

(* ===================================================================== *)
(* ROUTE-1 — formalize the validated singleton-cover linear row-count.    *)
(* Task + the two proof-level corrections: see ROUTE1.md (repo root).     *)
(* Build: scripts\codex-isabelle-build-posix.ps1 -Session Posix_Card_Route1 *)
(* NO sorry. Build green at all times. Fail-stop + report exact goal.     *)
(* ===================================================================== *)

subsection \<open>Helper definitions (pre-verified to build; reuse these)\<close>

definition D :: "rrexp \<Rightarrow> rrexp \<Rightarrow> nat" where
  "D r k = card (strong_apder_acc r k - strong_apder_acc RONE k)"

definition single_root :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_root q k =
     rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))"

definition single_term :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_term q k =
     rsimpStrong_dlform_closure (apder_term_frontier_acc q k)"

fun ralts_size_budget :: "rrexp list \<Rightarrow> nat" where
  "ralts_size_budget [] = 0"
| "ralts_size_budget (q # qs) = rsize q + ralts_size_budget qs"

(* ===================================================================== *)
(* LEMMA CHAIN TO LAND (bottom-up; cite green names from DEFINITIONS.txt) *)
(* See ROUTE1.md for each step + the green facts. Summary:                *)
(*                                                                        *)
(* 1. strong_apder_acc_RALTS_singleton_cover  (L1, via SAA-level cover,   *)
(*      NOT the false dl_le_pruned_altseq device)                         *)
(* 2. star_boundary_shift_le_one ; boundary_term_absorb (via S1) ;        *)
(*      seq_head_core_le_rsize (fill the RSEQ/RALTS-head sorry cases)     *)
(* 3. card_strong_apder_acc_singleton_RALTS_diff_base_le_rsize  (L2)      *)
(*      induction on q; RSEQ recurrence  D1(SEQ r1 r2)k <= rsize r1+D1 r2 k *)
(* 4. card_strong_apder_acc_RALTS_diff_base_le_size_budget  (RALTS step)  *)
(* 5. card_strong_apder_acc_diff_base_le_rsize  (global, induction on r   *)
(*      arbitrary k; + 2 new RSTAR sub-lemmas)                            *)
(* 6. card_apder_strong_dlfrontier_le  (the target)                       *)
(* 7. cubic_gate_unconditional  via actual_gate_from_direct_universe_rowlevel *)
(*                                                                        *)
(* Append the lemmas below this line.                                     *)
(* ===================================================================== *)

lemma strong_apder_acc_RALTS_terms_singleton_cover:
  "rsimpStrong_dlform_closure (apder_term_frontier_acc (RALTS rs) k) \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
  unfolding strong_apder_acc_def rsimpStrong_dlform_closure_def
  by auto

lemma strong_apder_acc_RALTS_root_singleton_cover_RZERO:
  "rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS rs) RZERO)) \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) RZERO)"
  by (simp add: rsimpStrong_dlform_closure_def)

lemma strong_apder_acc_RALTS_root_singleton_cover_RONE:
  "rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS rs) RONE)) \<subseteq>
    (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) RONE)"
  unfolding strong_apder_acc_def rsimpStrong_dlform_closure_def
  by (induction rs) auto

lemma finite_single_root [simp]:
  "finite (single_root q k)"
  by (simp add: single_root_def)

lemma finite_single_term [simp]:
  "finite (single_term q k)"
  by (simp add: single_term_def)

lemma strong_apder_acc_single_RALTS_decomp:
  "strong_apder_acc (RALTS [q]) k = single_root q k \<union> single_term q k"
  unfolding strong_apder_acc_def single_root_def single_term_def
    rsimpStrong_dlform_closure_def
  by auto

lemma strong_apder_acc_RONE_eq_closure_rfrontier:
  "strong_apder_acc RONE k = rsimpStrong_dlform_closure (rfrontier k)"
  by (simp add: strong_apder_acc_def)

lemma card_row_dlforms_rsimp7_SEQ_atom_RSTAR_le_one:
  "card (row_dlforms (rsimp7_SEQ_atom (RSTAR r) k)) \<le> 1"
  by (cases k) (auto simp add: rsimp7_SEQ_atom_def split: rrexp.splits)

lemma star_boundary_shift_le_one:
  assumes nfk: "apder_nf k"
  shows "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) \<le> 1"
proof (cases "rsimpStrong_raw r")
  case RZERO
  have sub: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) \<subseteq>
      strong_apder_acc RONE k"
    using RZERO row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF nfk]
    by (cases k) (auto simp add: strong_apder_acc_RONE_eq_closure_rfrontier
        rsimpStrong_dlform_closure_def)
  have empty: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k = {}"
    using sub by auto
  have card0: "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) = 0"
    using empty by simp
  show ?thesis
    using card0 by linarith
next
  case RONE
  have sub: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) \<subseteq>
      strong_apder_acc RONE k"
    using RONE row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF nfk]
    by (cases k) (auto simp add: strong_apder_acc_RONE_eq_closure_rfrontier
        rsimpStrong_dlform_closure_def)
  have empty: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k = {}"
    using sub by auto
  have card0: "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) = 0"
    using empty by simp
  show ?thesis
    using card0 by linarith
next
  case (RSTAR s)
  then have sub: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k \<subseteq>
      row_dlforms (rsimp7_SEQ_atom (RSTAR s) (rsimpStrong_raw k))"
    by (cases k) (auto simp add: strong_apder_acc_RONE_eq_closure_rfrontier
        rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def)
  have "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) \<le>
      card (row_dlforms (rsimp7_SEQ_atom (RSTAR s) (rsimpStrong_raw k)))"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> 1"
    by (rule card_row_dlforms_rsimp7_SEQ_atom_RSTAR_le_one)
  finally show ?thesis .
next
  case (RCHAR c)
  then have sub: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k \<subseteq>
      row_dlforms (rsimp7_SEQ_atom (RSTAR (RCHAR c)) (rsimpStrong_raw k))"
    by (cases k) (auto simp add: strong_apder_acc_RONE_eq_closure_rfrontier
        rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def)
  have "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) \<le>
      card (row_dlforms (rsimp7_SEQ_atom (RSTAR (RCHAR c)) (rsimpStrong_raw k)))"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> 1"
    by (rule card_row_dlforms_rsimp7_SEQ_atom_RSTAR_le_one)
  finally show ?thesis .
next
  case (RSEQ x1 x2)
  then have sub: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k \<subseteq>
      row_dlforms (rsimp7_SEQ_atom (RSTAR (RSEQ x1 x2)) (rsimpStrong_raw k))"
    by (cases k) (auto simp add: strong_apder_acc_RONE_eq_closure_rfrontier
        rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def)
  have "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) \<le>
      card (row_dlforms (rsimp7_SEQ_atom (RSTAR (RSEQ x1 x2)) (rsimpStrong_raw k)))"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> 1"
    by (rule card_row_dlforms_rsimp7_SEQ_atom_RSTAR_le_one)
  finally show ?thesis .
next
  case (RALTS xs)
  then have sub: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k \<subseteq>
      row_dlforms (rsimp7_SEQ_atom (RSTAR (RALTS xs)) (rsimpStrong_raw k))"
    by (cases k) (auto simp add: strong_apder_acc_RONE_eq_closure_rfrontier
        rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def)
  have "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) \<le>
      card (row_dlforms (rsimp7_SEQ_atom (RSTAR (RALTS xs)) (rsimpStrong_raw k)))"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> 1"
    by (rule card_row_dlforms_rsimp7_SEQ_atom_RSTAR_le_one)
  finally show ?thesis .
next
  case (RNTIMES x1 x2)
  then have sub: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k \<subseteq>
      row_dlforms (rsimp7_SEQ_atom (RSTAR (RNTIMES x1 x2)) (rsimpStrong_raw k))"
    by (cases k) (auto simp add: strong_apder_acc_RONE_eq_closure_rfrontier
        rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def)
  have "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) \<le>
      card (row_dlforms (rsimp7_SEQ_atom (RSTAR (RNTIMES x1 x2)) (rsimpStrong_raw k)))"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> 1"
    by (rule card_row_dlforms_rsimp7_SEQ_atom_RSTAR_le_one)
  finally show ?thesis .
next
  case (RBACKREF4 x1 x2 x3 x4 x5)
  then have sub: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k \<subseteq>
      row_dlforms (rsimp7_SEQ_atom (RSTAR (RBACKREF4 x1 x2 x3 x4 x5)) (rsimpStrong_raw k))"
    by (cases k) (auto simp add: strong_apder_acc_RONE_eq_closure_rfrontier
        rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def)
  have "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) \<le>
      card (row_dlforms (rsimp7_SEQ_atom (RSTAR (RBACKREF4 x1 x2 x3 x4 x5)) (rsimpStrong_raw k)))"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> 1"
    by (rule card_row_dlforms_rsimp7_SEQ_atom_RSTAR_le_one)
  finally show ?thesis .
next
  case (RHALF x1 x2 x3)
  then have sub: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k \<subseteq>
      row_dlforms (rsimp7_SEQ_atom (RSTAR (RHALF x1 x2 x3)) (rsimpStrong_raw k))"
    by (cases k) (auto simp add: strong_apder_acc_RONE_eq_closure_rfrontier
        rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def)
  have "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) \<le>
      card (row_dlforms (rsimp7_SEQ_atom (RSTAR (RHALF x1 x2 x3)) (rsimpStrong_raw k)))"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> 1"
    by (rule card_row_dlforms_rsimp7_SEQ_atom_RSTAR_le_one)
  finally show ?thesis .
next
  case (RRESIDUE x1 x2)
  then have sub: "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k \<subseteq>
      row_dlforms (rsimp7_SEQ_atom (RSTAR (RRESIDUE x1 x2)) (rsimpStrong_raw k))"
    by (cases k) (auto simp add: strong_apder_acc_RONE_eq_closure_rfrontier
        rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def)
  have "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) \<le>
      card (row_dlforms (rsimp7_SEQ_atom (RSTAR (RRESIDUE x1 x2)) (rsimpStrong_raw k)))"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> 1"
    by (rule card_row_dlforms_rsimp7_SEQ_atom_RSTAR_le_one)
  finally show ?thesis .
qed

lemma boundary_excess_le_single_root_RZERO:
  "card (strong_apder_acc RONE (rsimp4_SEQ_atom RZERO k) -
      strong_apder_acc RONE k) \<le>
    card (single_root RZERO k - strong_apder_acc RONE k)"
  by (simp add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def)

lemma boundary_excess_le_single_root_RONE:
  "card (strong_apder_acc RONE (rsimp4_SEQ_atom RONE k) -
      strong_apder_acc RONE k) \<le>
    card (single_root RONE k - strong_apder_acc RONE k)"
  by simp

lemma rsimpStrong_ALTs_raw_single_RCHAR [simp]:
  "rsimpStrong_ALTs_raw [RCHAR c] = RCHAR c"
  by (simp add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma rsimpStrong_ALTs_raw_single_nonzero_nonalt [simp]:
  assumes "q \<noteq> RZERO"
    and "nonalt q"
  shows "rsimpStrong_ALTs_raw [q] = q"
  using assms
  by (cases q) (simp_all add: rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma boundary_excess_le_single_root_RCHAR:
  "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RCHAR c) k) -
      strong_apder_acc RONE k) \<le>
    card (single_root (RCHAR c) k - strong_apder_acc RONE k)"
  unfolding single_root_def strong_apder_acc_def
    rsimpStrong_dlform_closure_def
  by (cases k) (auto simp add: rsimp7_SEQ_atom_def)

lemma boundary_excess_le_single_root_RNTIMES:
  "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RNTIMES r n) k) -
      strong_apder_acc RONE k) \<le>
    card (single_root (RNTIMES r n) k - strong_apder_acc RONE k)"
  unfolding single_root_def strong_apder_acc_def
    rsimpStrong_dlform_closure_def
  by (cases k) (auto simp add: rsimp7_SEQ_atom_def split: rrexp.splits)

lemma boundary_excess_le_single_root_RBACKREF4:
  "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RBACKREF4 r1 r2 r3 r4 cs) k) -
      strong_apder_acc RONE k) \<le>
    card (single_root (RBACKREF4 r1 r2 r3 r4 cs) k - strong_apder_acc RONE k)"
  unfolding single_root_def strong_apder_acc_def
    rsimpStrong_dlform_closure_def
  by (cases k) (auto simp add: rsimp7_SEQ_atom_def)

lemma boundary_excess_le_single_root_RHALF:
  "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RHALF r cs rep) k) -
      strong_apder_acc RONE k) \<le>
    card (single_root (RHALF r cs rep) k - strong_apder_acc RONE k)"
  unfolding single_root_def strong_apder_acc_def
    rsimpStrong_dlform_closure_def
  by (cases k) (auto simp add: rsimp7_SEQ_atom_def)

lemma boundary_excess_le_single_root_RRESIDUE:
  "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RRESIDUE cs rep) k) -
      strong_apder_acc RONE k) \<le>
    card (single_root (RRESIDUE cs rep) k - strong_apder_acc RONE k)"
  unfolding single_root_def strong_apder_acc_def
    rsimpStrong_dlform_closure_def
  by (cases k) (auto simp add: rsimp7_SEQ_atom_def)

lemma boundary_excess_le_single_root_RSTAR:
  "card (strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) -
      strong_apder_acc RONE k) \<le>
    card (single_root (RSTAR r) k - strong_apder_acc RONE k)"
  unfolding single_root_def strong_apder_acc_def
    rsimpStrong_dlform_closure_def
  by (cases "rsimpStrong_raw r"; cases k)
    (auto simp add: rsimp7_SEQ_atom_def)

lemma boundary_excess_le_single_root_nonseq_nonalt:
  assumes "rnonseq t"
    and "nonalt t"
  shows "card (strong_apder_acc RONE (rsimp4_SEQ_atom t k) -
      strong_apder_acc RONE k) \<le>
    card (single_root t k - strong_apder_acc RONE k)"
  using assms
proof (cases t)
  case RZERO
  then show ?thesis
    by (rule ssubst) (rule boundary_excess_le_single_root_RZERO)
next
  case RONE
  then show ?thesis
    by (rule ssubst) (rule boundary_excess_le_single_root_RONE)
next
  case (RCHAR c)
  then show ?thesis
    by (rule ssubst) (rule boundary_excess_le_single_root_RCHAR)
next
  case (RSEQ t1 t2)
  then show ?thesis
    using assms by simp
next
  case (RALTS rs)
  then show ?thesis
    using assms by simp
next
  case (RSTAR r)
  then show ?thesis
    by (rule ssubst) (rule boundary_excess_le_single_root_RSTAR)
next
  case (RNTIMES r n)
  then show ?thesis
    by (rule ssubst) (rule boundary_excess_le_single_root_RNTIMES)
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?thesis
    by (rule ssubst) (rule boundary_excess_le_single_root_RBACKREF4)
next
  case (RHALF r cs rep)
  then show ?thesis
    by (rule ssubst) (rule boundary_excess_le_single_root_RHALF)
next
  case (RRESIDUE cs rep)
  then show ?thesis
    by (rule ssubst) (rule boundary_excess_le_single_root_RRESIDUE)
qed

lemma ralts_size_budget_eq_rsizes:
  "ralts_size_budget rs = rsizes rs"
  by (induction rs) simp_all

lemma sum_rsize_set_le_ralts_size_budget:
  "(\<Sum>q \<in> set rs. rsize q) \<le> ralts_size_budget rs"
proof -
  have "(\<Sum>q \<in> set rs. rsize q) \<le> rsizes rs"
    by (rule sum_set_le_sum_list_nat)
  then show ?thesis
    by (simp add: ralts_size_budget_eq_rsizes)
qed

lemma strong_apder_acc_RONE_s4_RSTAR_eq_root_row:
  "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) =
    row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))"
  by (cases k) (simp_all add: strong_apder_acc_RONE_eq_closure_rfrontier
      rsimpStrong_dlform_closure_def)

lemma card_RSTAR_root_row_diff_base_le_one:
  assumes nfk: "apder_nf k"
  shows "card
      (row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k)) -
        strong_apder_acc RONE k) \<le> 1"
  using star_boundary_shift_le_one[OF nfk, of r]
    strong_apder_acc_RONE_s4_RSTAR_eq_root_row[of r k]
  by simp

lemma card_strong_apder_acc_singleton_RSEQ_rec_spine:
  assumes boundary_term_absorb:
    "\<And>t k. apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((strong_apder_acc RONE (rsimp4_SEQ_atom t k) -
          strong_apder_acc RONE k) \<union>
        (single_term t k - strong_apder_acc RONE k)) \<le>
      D (RALTS [t]) k"
    and seq_head_core_le_rsize:
    "\<And>h t k. apder_nf h \<Longrightarrow> apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ h t) k \<union>
          single_term h (rsimp4_SEQ_atom t k)) -
        (strong_apder_acc RONE k \<union>
          strong_apder_acc RONE (rsimp4_SEQ_atom t k))) \<le> rsize h"
    and nf1: "apder_nf r1"
    and nf2: "apder_nf r2"
    and nfk: "apder_nf k"
  shows "D (RALTS [RSEQ r1 r2]) k \<le>
    rsize r1 + D (RALTS [r2]) k"
proof -
  let ?c = "rsimp4_SEQ_atom r2 k"
  let ?A = "strong_apder_acc (RALTS [RSEQ r1 r2]) k"
  let ?B = "strong_apder_acc RONE k"
  let ?Bc = "strong_apder_acc RONE ?c"
  let ?Core =
    "(single_root (RSEQ r1 r2) k \<union> single_term r1 ?c) -
      (?B \<union> ?Bc)"
  let ?Tail = "(?Bc - ?B) \<union> (single_term r2 k - ?B)"
  have decomp: "?A =
      single_root (RSEQ r1 r2) k \<union> single_term r1 ?c \<union>
      single_term r2 k"
    unfolding strong_apder_acc_single_RALTS_decomp single_term_def
      rsimpStrong_dlform_closure_def
    by auto
  have cover: "?A - ?B \<subseteq> ?Core \<union> ?Tail"
    using decomp by auto
  have card_cover: "card (?A - ?B) \<le> card (?Core \<union> ?Tail)"
    by (rule card_mono) (use cover in auto)
  also have "... \<le> card ?Core + card ?Tail"
    by (rule card_Un_le)
  also have "... \<le> rsize r1 + D (RALTS [r2]) k"
  proof (rule add_mono)
    show "card ?Core \<le> rsize r1"
      by (rule seq_head_core_le_rsize[OF nf1 nf2 nfk])
    show "card ?Tail \<le> D (RALTS [r2]) k"
      by (rule boundary_term_absorb[OF nf2 nfk])
  qed
  finally show ?thesis
    by (simp add: D_def)
qed

lemma card_strong_apder_acc_RALTS_diff_base_le_size_budget_spine:
  assumes L1_cover:
    "\<And>rs k. strong_apder_acc (RALTS rs) k \<subseteq>
      (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    and branch_bound:
    "\<And>q. q \<in> set rs \<Longrightarrow>
      D (RALTS [q]) k \<le> rsize q"
  shows "D (RALTS rs) k \<le> ralts_size_budget rs"
proof -
  let ?B = "strong_apder_acc RONE k"
  let ?U = "(\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
  have cover_diff: "strong_apder_acc (RALTS rs) k - ?B \<subseteq> ?U - ?B"
    using L1_cover[of rs k] by auto
  have "D (RALTS rs) k \<le> card (?U - ?B)"
    unfolding D_def
    by (rule card_mono) (use cover_diff in auto)
  also have "... =
      card (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k - ?B)"
    by auto
  also have "... \<le>
      (\<Sum>q \<in> set rs. card (strong_apder_acc (RALTS [q]) k - ?B))"
    by (rule card_UN_le) auto
  also have "... \<le> (\<Sum>q \<in> set rs. rsize q)"
    by (rule sum_mono) (use branch_bound in \<open>auto simp add: D_def\<close>)
  also have "... \<le> ralts_size_budget rs"
    by (rule sum_rsize_set_le_ralts_size_budget)
  finally show ?thesis .
qed

end
