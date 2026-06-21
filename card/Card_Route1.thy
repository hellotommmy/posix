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

definition D1 :: "rrexp \<Rightarrow> rrexp \<Rightarrow> nat" where
  "D1 q k = D (RALTS [q]) k"

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

lemma single_root_RSTAR_eq_boundary:
  "single_root (RSTAR r) k =
    strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k)"
  unfolding single_root_def strong_apder_acc_RONE_eq_closure_rfrontier
  by (cases k; cases "rsimpStrong_raw r")
    (auto simp add: rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def)

lemma single_term_subset_singleton_RALTS:
  "single_term q k - strong_apder_acc RONE k \<subseteq>
    strong_apder_acc (RALTS [q]) k - strong_apder_acc RONE k"
  by (auto simp add: strong_apder_acc_single_RALTS_decomp)

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

lemma D1_RSEQ_step_spine:
  assumes boundary_term_absorb:
    "\<And>t k. apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((strong_apder_acc RONE (rsimp4_SEQ_atom t k) -
          strong_apder_acc RONE k) \<union>
        (single_term t k - strong_apder_acc RONE k)) \<le>
      D1 t k"
    and seq_head_core_le_rsize:
    "\<And>h t k. apder_nf h \<Longrightarrow> apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ h t) k \<union>
          single_term h (rsimp4_SEQ_atom t k)) -
        (strong_apder_acc RONE k \<union>
          strong_apder_acc RONE (rsimp4_SEQ_atom t k))) \<le> rsize h"
    and nf1: "apder_nf r1"
    and nf2: "apder_nf r2"
    and nfk: "apder_nf k"
  shows "D1 (RSEQ r1 r2) k \<le> rsize r1 + D1 r2 k"
proof -
  have bnd_D:
    "\<And>t k. apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((strong_apder_acc RONE (rsimp4_SEQ_atom t k) -
          strong_apder_acc RONE k) \<union>
        (single_term t k - strong_apder_acc RONE k)) \<le>
      D (RALTS [t]) k"
    using boundary_term_absorb by (simp add: D1_def)
  have "D (RALTS [RSEQ r1 r2]) k \<le>
      rsize r1 + D (RALTS [r2]) k"
    by (rule card_strong_apder_acc_singleton_RSEQ_rec_spine
        [OF bnd_D seq_head_core_le_rsize nf1 nf2 nfk])
  then show ?thesis
    by (simp add: D1_def)
qed

lemma D1_RSTAR_step_spine:
  assumes nfr: "apder_nf r"
    and nfk: "apder_nf k"
  shows "D1 (RSTAR r) k \<le>
    1 + D1 r (rsimp4_SEQ_atom (RSTAR r) k)"
proof -
  let ?c = "rsimp4_SEQ_atom (RSTAR r) k"
  let ?A = "strong_apder_acc (RALTS [RSTAR r]) k"
  let ?B = "strong_apder_acc RONE k"
  let ?Bc = "strong_apder_acc RONE ?c"
  let ?T = "single_term r ?c"
  have decomp: "?A = ?Bc \<union> ?T"
    unfolding strong_apder_acc_single_RALTS_decomp
      single_root_RSTAR_eq_boundary single_term_def
      rsimpStrong_dlform_closure_def
    by auto
  have cover: "?A - ?B \<subseteq> (?Bc - ?B) \<union> (?T - ?Bc)"
    using decomp by auto
  have card_cover: "card (?A - ?B) \<le>
      card ((?Bc - ?B) \<union> (?T - ?Bc))"
    by (rule card_mono) (use cover in auto)
  also have "... \<le> card (?Bc - ?B) + card (?T - ?Bc)"
    by (rule card_Un_le)
  also have "... \<le> 1 + D1 r ?c"
  proof (rule add_mono)
    show "card (?Bc - ?B) \<le> 1"
      by (rule star_boundary_shift_le_one[OF nfk])
    have term_sub: "?T - ?Bc \<subseteq>
        strong_apder_acc (RALTS [r]) ?c - ?Bc"
      using single_term_subset_singleton_RALTS[of r ?c] by auto
    have "card (?T - ?Bc) \<le>
        card (strong_apder_acc (RALTS [r]) ?c - ?Bc)"
      by (rule card_mono) (use term_sub in auto)
    then show "card (?T - ?Bc) \<le> D1 r ?c"
      by (simp add: D1_def D_def)
  qed
  finally show ?thesis
    by (simp add: D1_def D_def)
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

lemma card_strong_apder_acc_RALTS_diff_base_le_size_budget_from_D1_spine:
  assumes L1_cover:
    "\<And>rs k. strong_apder_acc (RALTS rs) k \<subseteq>
      (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    and singleton_bound:
    "\<And>q k. apder_nf q \<Longrightarrow> apder_nf k \<Longrightarrow>
      D1 q k \<le> rsize q"
    and nfrs: "apder_nf (RALTS rs)"
    and nfk: "apder_nf k"
  shows "D (RALTS rs) k \<le> ralts_size_budget rs"
proof (rule card_strong_apder_acc_RALTS_diff_base_le_size_budget_spine
    [OF L1_cover])
  fix q
  assume q: "q \<in> set rs"
  have nfq: "apder_nf q"
    using nfrs q by simp
  show "D (RALTS [q]) k \<le> rsize q"
    using singleton_bound[OF nfq nfk] by (simp add: D1_def)
qed

lemma card_strong_apder_acc_diff_base_le_rsize_spine:
  assumes ralts_diff:
    "\<And>rs k. apder_nf (RALTS rs) \<Longrightarrow> apder_nf k \<Longrightarrow>
      D (RALTS rs) k \<le> rsize (RALTS rs)"
    and clean: "apder_clean r"
    and nfk: "apder_nf k"
  shows "D r k \<le> rsize r"
  using clean nfk
proof (induction r arbitrary: k)
  case RZERO
  then show ?case
    by (simp add: D_def strong_apder_acc_def
        rsimpStrong_dlform_closure_def)
next
  case RONE
  then show ?case
    by (simp add: D_def strong_apder_acc_def
        rsimpStrong_dlform_closure_def)
next
  case (RCHAR c)
  show ?case
    using card_strong_apder_acc_RCHAR_diff_base_le[OF RCHAR.prems(2)]
    by (simp add: D_def)
next
  case (RSEQ r1 r2)
  let ?k1 = "rsimp4_SEQ_atom r2 k"
  let ?A1 = "strong_apder_acc r1 ?k1"
  let ?A2 = "strong_apder_acc r2 k"
  let ?B = "strong_apder_acc RONE k"
  let ?M = "strong_apder_acc RONE ?k1"
  have clean1: "apder_clean r1"
    using RSEQ.prems(1) by (rule apder_clean_RSEQ_left)
  have clean2: "apder_clean r2"
    using RSEQ.prems(1) by (rule apder_clean_RSEQ_right)
  have nf2: "apder_nf r2"
    using clean2 by (simp add: apder_clean_def)
  have nf_k1: "apder_nf ?k1"
    by (rule apder_nf_rsimp4_SEQ_atom[OF nf2 RSEQ.prems(2)])
  have IH1: "D r1 ?k1 \<le> rsize r1"
    by (rule RSEQ.IH(1)[OF clean1 nf_k1])
  have IH2: "D r2 k \<le> rsize r2"
    by (rule RSEQ.IH(2)[OF clean2 RSEQ.prems(2)])
  have acc_sub:
    "strong_apder_acc (RSEQ r1 r2) k \<subseteq> ?A1 \<union> ?A2"
    by (rule strong_apder_acc_RSEQ_subset)
  have diff_sub:
    "strong_apder_acc (RSEQ r1 r2) k - ?B \<subseteq> (?A1 \<union> ?A2) - ?B"
    using acc_sub by auto
  have mono:
    "D (RSEQ r1 r2) k \<le> card ((?A1 \<union> ?A2) - ?B)"
    unfolding D_def
    by (rule card_mono) (use diff_sub in auto)
  have mid: "?M \<subseteq> ?A2"
    by (rule strong_apder_acc_RONE_sigma_subset)
  have telescope:
    "card ((?A1 \<union> ?A2) - ?B) \<le>
      card (?A1 - ?M) + card (?A2 - ?B)"
    by (rule card_Un_Diff_telescope_le[OF _ _ mid]) simp_all
  have "D (RSEQ r1 r2) k \<le> D r1 ?k1 + D r2 k"
    using mono telescope by (simp add: D_def)
  also have "... \<le> rsize r1 + rsize r2"
    using IH1 IH2 by simp
  finally show ?case
    by simp
next
  case (RALTS rs)
  have nf_r: "apder_nf (RALTS rs)"
    using RALTS.prems(1) by (simp add: apder_clean_def)
  show ?case
    by (rule ralts_diff[OF nf_r RALTS.prems(2)])
next
  case (RSTAR r)
  let ?ks = "rsimp4_SEQ_atom (RSTAR r) k"
  let ?Root = "row_dlforms (rsimpStrong_raw ?ks)"
  let ?Ar = "strong_apder_acc r ?ks"
  let ?B = "strong_apder_acc RONE k"
  let ?Bs = "strong_apder_acc RONE ?ks"
  have clean_r: "apder_clean r"
    using RSTAR.prems(1) by (rule apder_clean_RSTAR_body)
  have nf_r: "apder_nf r"
    using clean_r by (simp add: apder_clean_def)
  have nf_ks: "apder_nf ?ks"
    by (rule apder_nf_rsimp4_SEQ_atom[OF _ RSTAR.prems(2)])
      (use nf_r in simp)
  have IH: "D r ?ks \<le> rsize r"
    by (rule RSTAR.IH[OF clean_r nf_ks])
  have root_eq: "?Bs = ?Root"
    using strong_apder_acc_RONE_s4_RSTAR_eq_root_row[of r k]
    by simp
  have root_bound: "card (?Root - ?B) \<le> 1"
    by (rule card_RSTAR_root_row_diff_base_le_one[OF RSTAR.prems(2)])
  have acc_sub:
    "strong_apder_acc (RSTAR r) k \<subseteq> ?Root \<union> ?Ar"
    by (rule strong_apder_acc_RSTAR_subset)
  have diff_sub:
    "strong_apder_acc (RSTAR r) k - ?B \<subseteq> (?Ar \<union> ?Root) - ?B"
    using acc_sub by auto
  have mono:
    "D (RSTAR r) k \<le> card ((?Ar \<union> ?Root) - ?B)"
    unfolding D_def
    by (rule card_mono) (use diff_sub in auto)
  have telescope:
    "card ((?Ar \<union> ?Root) - ?B) \<le>
      card (?Ar - ?Root) + card (?Root - ?B)"
    by (rule card_Un_Diff_telescope_le[of ?Ar ?Root ?Root ?B]) simp_all
  have "D (RSTAR r) k \<le> D r ?ks + 1"
    using mono telescope root_bound root_eq by (simp add: D_def)
  also have "... \<le> rsize r + 1"
    using IH by simp
  finally show ?case
    by simp
next
  case (RNTIMES r n)
  then show ?case
    by (simp add: apder_clean_def)
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case
    by (simp add: apder_clean_def)
next
  case (RHALF r cs rep)
  then show ?case
    by (simp add: apder_clean_def)
next
  case (RRESIDUE cs rep)
  then show ?case
    by (simp add: apder_clean_def)
qed

lemma card_apder_strong_dlfrontier_le_spine:
  assumes global:
    "\<And>r k. apder_clean r \<Longrightarrow> apder_nf k \<Longrightarrow> D r k \<le> rsize r"
    and clean: "apder_clean r"
  shows "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
proof -
  let ?U = "apder_strong_dlfrontier r"
  let ?A = "strong_apder_acc r RONE"
  have nfr: "apder_nf r"
    using clean by (simp add: apder_clean_def)
  have bridge: "?U \<subseteq> ?A"
    by (rule apder_strong_dlfrontier_subset_strong_apder_acc_RONE[OF nfr])
  have card_U_A: "card ?U \<le> card ?A"
    by (rule card_mono) (use bridge in auto)
  have lift: "card ?A \<le> Suc (card (?A - {RONE}))"
    by (rule card_le_Suc_card_Diff_singleton) simp
  have diff_bound: "card (?A - {RONE}) \<le> rsize r"
  proof -
    have "D r RONE \<le> rsize r"
      by (rule global[OF clean]) simp
    then show ?thesis
      by (simp add: D_def)
  qed
  show ?thesis
    using card_U_A lift diff_bound by linarith
qed

corollary cubic_gate_unconditional_spine:
  assumes global:
    "\<And>r k. apder_clean r \<Longrightarrow> apder_nf k \<Longrightarrow> D r k \<le> rsize r"
    and clean: "apder_clean r"
  shows "rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
    \<le> 2 * (rsize r + 3) ^ 3"
proof -
  have cardU: "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
    by (rule card_apder_strong_dlfrontier_le_spine[OF global clean])
  show ?thesis
    by (rule actual_gate_from_direct_universe_rowlevel[OF clean cardU])
qed

subsection \<open>Short integration route: reduce the spine to general-k RALTS diff\<close>

lemma card_strong_apder_acc_diff_base_le_rsize_from_RALTS_diff_spine:
  assumes RALTS_diff:
    "\<And>rs k. apder_nf (RALTS rs) \<Longrightarrow> apder_nf k \<Longrightarrow>
      card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
        \<le> rsize (RALTS rs)"
    and clean: "apder_clean r"
    and nfk: "apder_nf k"
  shows "D r k \<le> rsize r"
proof (rule card_strong_apder_acc_diff_base_le_rsize_spine[OF _ clean nfk])
  fix rs k
  assume nfrs: "apder_nf (RALTS rs)"
    and nfk': "apder_nf k"
  have "card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
      \<le> rsize (RALTS rs)"
    by (rule RALTS_diff[OF nfrs nfk'])
  then show "D (RALTS rs) k \<le> rsize (RALTS rs)"
    by (simp add: D_def)
qed

lemma card_apder_strong_dlfrontier_le_from_RALTS_diff_spine:
  assumes RALTS_diff:
    "\<And>rs k. apder_nf (RALTS rs) \<Longrightarrow> apder_nf k \<Longrightarrow>
      card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
        \<le> rsize (RALTS rs)"
    and clean: "apder_clean r"
  shows "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
proof (rule card_apder_strong_dlfrontier_le_spine[OF _ clean])
  fix r k
  assume clean': "apder_clean r"
    and nfk: "apder_nf k"
  show "D r k \<le> rsize r"
    by (rule card_strong_apder_acc_diff_base_le_rsize_from_RALTS_diff_spine
        [OF RALTS_diff clean' nfk])
qed

corollary cubic_gate_unconditional_from_RALTS_diff_spine:
  assumes RALTS_diff:
    "\<And>rs k. apder_nf (RALTS rs) \<Longrightarrow> apder_nf k \<Longrightarrow>
      card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
        \<le> rsize (RALTS rs)"
    and clean: "apder_clean r"
  shows "rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
    \<le> 2 * (rsize r + 3) ^ 3"
proof (rule cubic_gate_unconditional_spine[OF _ clean])
  fix r k
  assume clean': "apder_clean r"
    and nfk: "apder_nf k"
  show "D r k \<le> rsize r"
    by (rule card_strong_apder_acc_diff_base_le_rsize_from_RALTS_diff_spine
        [OF RALTS_diff clean' nfk])
qed

lemma card_strong_apder_acc_diff_base_le_rsize_from_L1_D1_spine:
  assumes L1_cover:
    "\<And>rs k. strong_apder_acc (RALTS rs) k \<subseteq>
      (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    and singleton_bound:
    "\<And>q k. apder_nf q \<Longrightarrow> apder_nf k \<Longrightarrow>
      D1 q k \<le> rsize q"
    and clean: "apder_clean r"
    and nfk: "apder_nf k"
  shows "D r k \<le> rsize r"
proof (rule card_strong_apder_acc_diff_base_le_rsize_spine
    [OF _ clean nfk])
  fix rs k
  assume nfrs: "apder_nf (RALTS rs)"
    and nfk': "apder_nf k"
  have "D (RALTS rs) k \<le> ralts_size_budget rs"
    by (rule card_strong_apder_acc_RALTS_diff_base_le_size_budget_from_D1_spine
        [OF L1_cover singleton_bound nfrs nfk'])
  then show "D (RALTS rs) k \<le> rsize (RALTS rs)"
    by (simp add: ralts_size_budget_eq_rsizes)
qed

lemma card_apder_strong_dlfrontier_le_from_L1_D1_spine:
  assumes L1_cover:
    "\<And>rs k. strong_apder_acc (RALTS rs) k \<subseteq>
      (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    and singleton_bound:
    "\<And>q k. apder_nf q \<Longrightarrow> apder_nf k \<Longrightarrow>
      D1 q k \<le> rsize q"
    and clean: "apder_clean r"
  shows "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
proof (rule card_apder_strong_dlfrontier_le_spine[OF _ clean])
  fix r k
  assume clean': "apder_clean r"
    and nfk: "apder_nf k"
  show "D r k \<le> rsize r"
    by (rule card_strong_apder_acc_diff_base_le_rsize_from_L1_D1_spine
        [OF L1_cover singleton_bound clean' nfk])
qed

corollary cubic_gate_unconditional_from_L1_D1_spine:
  assumes L1_cover:
    "\<And>rs k. strong_apder_acc (RALTS rs) k \<subseteq>
      (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
    and singleton_bound:
    "\<And>q k. apder_nf q \<Longrightarrow> apder_nf k \<Longrightarrow>
      D1 q k \<le> rsize q"
    and clean: "apder_clean r"
  shows "rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
    \<le> 2 * (rsize r + 3) ^ 3"
proof (rule cubic_gate_unconditional_spine[OF _ clean])
  fix r k
  assume clean': "apder_clean r"
    and nfk: "apder_nf k"
  show "D r k \<le> rsize r"
    by (rule card_strong_apder_acc_diff_base_le_rsize_from_L1_D1_spine
        [OF L1_cover singleton_bound clean' nfk])
qed

end
