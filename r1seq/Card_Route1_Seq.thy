theory Card_Route1_Seq
  imports "Posix_Cubic.DirectUniverseCubic"
begin

(* ===================================================================== *)
(* LANE SEQ-HEAD — prove seq_head_core_le_rsize.  See ROUTE_SEQ.md.       *)
(* Build with the private USER_HOME command from ROUTE_SEQ.md.             *)
(* NO sorry. Build green. Fail-stop + report.                            *)
(* ===================================================================== *)

abbreviation A :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "A r k \<equiv> strong_apder_acc r k"

abbreviation B :: "rrexp \<Rightarrow> rrexp set" where
  "B k \<equiv> A RONE k"

definition D1 :: "rrexp \<Rightarrow> rrexp \<Rightarrow> nat" where
  "D1 q k = card (A (RALTS [q]) k - B k)"

definition single_root :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_root q k =
     rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))"
definition single_term :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_term q k =
     rsimpStrong_dlform_closure (apder_term_frontier_acc q k)"

lemma finite_single_root [simp]: "finite (single_root q k)"
  by (simp add: single_root_def)

lemma finite_single_term [simp]: "finite (single_term q k)"
  by (simp add: single_term_def)

lemma A_single_decomp:
  "A (RALTS [q]) k = single_root q k \<union> single_term q k"
  by (simp add: strong_apder_acc_def single_root_def single_term_def
      rsimpStrong_dlform_closure_def)

lemma A_single_RZERO_eq [simp]:
  "A (RALTS [RZERO]) k = A RZERO k"
  unfolding strong_apder_acc_def
  by (cases k)
    (simp_all add: rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def
      rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma A_single_RCHAR_eq [simp]:
  "A (RALTS [RCHAR c]) k = A (RCHAR c) k"
  unfolding strong_apder_acc_def
  by (cases k) (auto simp add: rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def
      rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma B_alt:
  "B k = rsimpStrong_dlform_closure (rfrontier k)"
  by (simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

lemma apder_nf_s4:
  assumes "apder_nf r" "apder_nf k"
  shows "apder_nf (rsimp4_SEQ_atom r k)"
  using assms
proof (induction r arbitrary: k)
  case RZERO
  then show ?case by simp
next
  case RONE
  then show ?case by simp
next
  case (RCHAR c)
  then show ?case by (cases k) auto
next
  case (RSEQ r1 r2)
  then show ?case by simp
next
  case (RALTS rs)
  then show ?case by (cases k) auto
next
  case (RSTAR r)
  then show ?case by (cases k) auto
next
  case (RNTIMES r n)
  then show ?case by (cases k) auto
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?case by (cases k) auto
next
  case (RHALF r cs rep)
  then show ?case by (cases k) auto
next
  case (RRESIDUE cs rep)
  then show ?case by (cases k) auto
qed

lemma single_term_RZERO [simp]: "single_term RZERO k = {}"
  by (simp add: single_term_def rsimpStrong_dlform_closure_def)

lemma single_term_RONE [simp]: "single_term RONE k = {}"
  by (simp add: single_term_def rsimpStrong_dlform_closure_def)

lemma single_term_RCHAR [simp]: "single_term (RCHAR c) k = B k"
  by (simp add: single_term_def B_alt)

lemma single_term_RSEQ [simp]:
  "single_term (RSEQ r1 r2) k =
    single_term r1 (rsimp4_SEQ_atom r2 k) \<union> single_term r2 k"
  by (simp add: single_term_def rsimpStrong_dlform_closure_def)

lemma single_term_RSTAR [simp]:
  "single_term (RSTAR r) k =
    single_term r (rsimp4_SEQ_atom (RSTAR r) k)"
  by (simp add: single_term_def)

lemma single_term_RALTS [simp]:
  "single_term (RALTS rs) k =
    (\<Union>q \<in> set rs. single_term q k)"
  by (simp add: single_term_def rsimpStrong_dlform_closure_def)

lemma rsimpStrong_ALTs_raw_Nil [simp]:
  "rsimpStrong_ALTs_raw [] = RZERO"
  by (simp add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma rsimpStrong_raw_RALTS_single_RSEQ_RZERO [simp]:
  "rsimpStrong_raw (RALTS [RSEQ RZERO t]) = RZERO"
  by (simp add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def
      rsimp7_SEQ_atom_def)

lemma rsimpStrong_raw_RSEQ_RALTS_single_RSEQ_RZERO [simp]:
  "rsimpStrong_raw (RSEQ (RALTS [RSEQ RZERO t]) k) = RZERO"
  by (simp add: rsimp7_SEQ_atom_def)

lemma single_root_RSEQ_RZERO [simp]:
  "single_root (RSEQ RZERO t) k = {}"
  by (cases k)
    (simp_all add: single_root_def rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def)

lemma seq_head_core_RZERO_le_rsize:
  "card ((single_root (RSEQ RZERO t) k \<union>
           single_term RZERO (rsimp4_SEQ_atom t k))
          - (B k \<union> B (rsimp4_SEQ_atom t k)))
    \<le> rsize RZERO"
  by simp

lemma D1_RZERO_le_rsize:
  "D1 RZERO k \<le> rsize RZERO"
proof -
  have "D1 RZERO k = card (A RZERO k - B k)"
    by (simp add: D1_def)
  also have "... = 0"
    by (simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)
  finally show ?thesis by simp
qed

lemma card_row_dlforms_rsimp4_SEQ_atom_RCHAR_le_one [simp]:
  "card (row_dlforms (rsimp4_SEQ_atom (RCHAR c) k)) \<le> 1"
  by (cases k) auto

lemma card_row_dlforms_RSEQ_RCHAR_le_one [simp]:
  "card (row_dlforms (RSEQ (RCHAR c) k)) \<le> 1"
  by simp

lemma card_row_dlforms_rsimp4_SEQ_atom_RCHAR_s4_s4_le_one [simp]:
  "card (row_dlforms
      (rsimp4_SEQ_atom (RCHAR c) (rsimp4_SEQ_atom r (rsimp4_SEQ_atom s k)))) \<le> 1"
  by (rule card_row_dlforms_rsimp4_SEQ_atom_RCHAR_le_one)

lemma card_row_dlforms_rsimp4_SEQ_atom_RCHAR_s4_s4_le_Suc0:
  "card (row_dlforms
      (rsimp4_SEQ_atom (RCHAR c) (rsimp4_SEQ_atom r (rsimp4_SEQ_atom s k)))) \<le> Suc 0"
proof -
  have "card (row_dlforms
      (rsimp4_SEQ_atom (RCHAR c) (rsimp4_SEQ_atom r (rsimp4_SEQ_atom s k)))) \<le> 1"
    by (rule card_row_dlforms_rsimp4_SEQ_atom_RCHAR_s4_s4_le_one)
  then show ?thesis
    by simp
qed

lemma single_root_RSEQ_RCHAR_card_le_one:
  "card (single_root (RSEQ (RCHAR c) t) k) \<le> 1"
  unfolding single_root_def
  apply (cases k; cases "rsimpStrong_raw t"; cases "rsimpStrong_raw k")
  apply (auto simp add: rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def
      rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def
      rsimpStrong_prune_pair_raw_def Let_def)
  by (metis card_row_dlforms_rsimp4_SEQ_atom_RCHAR_s4_s4_le_Suc0)+

lemma seq_head_core_RCHAR_le_rsize:
  "card ((single_root (RSEQ (RCHAR c) t) k \<union>
           single_term (RCHAR c) (rsimp4_SEQ_atom t k))
          - (B k \<union> B (rsimp4_SEQ_atom t k)))
    \<le> rsize (RCHAR c)"
proof -
  have sub:
    "(single_root (RSEQ (RCHAR c) t) k \<union>
       single_term (RCHAR c) (rsimp4_SEQ_atom t k))
      - (B k \<union> B (rsimp4_SEQ_atom t k))
     \<subseteq> single_root (RSEQ (RCHAR c) t) k"
    by auto
  have "card ((single_root (RSEQ (RCHAR c) t) k \<union>
           single_term (RCHAR c) (rsimp4_SEQ_atom t k))
          - (B k \<union> B (rsimp4_SEQ_atom t k)))
    \<le> card (single_root (RSEQ (RCHAR c) t) k)"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> 1"
    by (rule single_root_RSEQ_RCHAR_card_le_one)
  finally show ?thesis
    by simp
qed

lemma D1_RCHAR_le_rsize:
  assumes "apder_nf k"
  shows "D1 (RCHAR c) k \<le> rsize (RCHAR c)"
  unfolding D1_def
  using card_strong_apder_acc_RCHAR_diff_base_le[OF assms, of c]
  by simp

lemma rsimpStrong_ALTs_raw_singleton_RONE [simp]:
  "rsimpStrong_ALTs_raw [RONE] = RONE"
  by (simp add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma rsimpStrong_ALTs_raw_singleton_RSTAR [simp]:
  "rsimpStrong_ALTs_raw [RSTAR r] = RSTAR r"
  by (simp add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma rsimpStrong_ALTs_raw_rflts_single_rsimpStrong_RSTAR [simp]:
  "rsimpStrong_ALTs_raw (rflts [rsimpStrong_raw (RSTAR r)]) =
    rsimpStrong_raw (RSTAR r)"
  by (cases "rsimpStrong_raw r") simp_all

lemmas rsimpStrong_ALTs_raw_rflts_single_rsimpStrong_RSTAR_simps [simp] =
  rsimpStrong_ALTs_raw_rflts_single_rsimpStrong_RSTAR[simplified]

lemma star_single_root_eq_B:
  "single_root (RSTAR r) k = B (rsimp4_SEQ_atom (RSTAR r) k)"
  unfolding single_root_def B_alt rsimpStrong_dlform_closure_def
  by (cases k) (auto simp add: rsimp7_SEQ_atom_def)

lemma card_subset_singleton_le_one:
  assumes "S \<subseteq> {x}"
  shows "card S \<le> 1"
proof -
  have "card S \<le> card {x}"
    by (rule card_mono) (use assms in auto)
  then show ?thesis by simp
qed

lemma card_row_dlforms_rsimpStrong_rsimp4_RSTAR_diff_le_one:
  "card (row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k)) -
      row_dlforms (rsimpStrong_raw k)) \<le> 1"
proof -
  have sub: "row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k)) -
      row_dlforms (rsimpStrong_raw k) \<subseteq>
      {rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k)}"
    by (cases k; cases "rsimpStrong_raw r"; cases "rsimpStrong_raw k")
      (auto simp add: rsimp7_SEQ_atom_def split: rrexp.splits if_splits)
  show ?thesis
    by (rule card_subset_singleton_le_one[OF sub])
qed

lemma B_rsimp4_RSTAR_eq_row_dlforms:
  "B (rsimp4_SEQ_atom (RSTAR r) k) =
    row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))"
  unfolding B_alt rsimpStrong_dlform_closure_def
  by (cases k) simp_all

lemma star_boundary_shift_le_one:
  assumes "apder_nf r" "apder_nf k"
  shows "card (B (rsimp4_SEQ_atom (RSTAR r) k) - B k) \<le> 1"
proof -
  have base: "row_dlforms (rsimpStrong_raw k) \<subseteq> B k"
    by (rule row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF assms(2)])
  have sub: "B (rsimp4_SEQ_atom (RSTAR r) k) - B k \<subseteq>
      row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k)) -
      row_dlforms (rsimpStrong_raw k)"
    using base by (auto simp add: B_rsimp4_RSTAR_eq_row_dlforms)
  have "card (B (rsimp4_SEQ_atom (RSTAR r) k) - B k) \<le>
      card (row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k)) -
        row_dlforms (rsimpStrong_raw k))"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> 1"
    by (rule card_row_dlforms_rsimpStrong_rsimp4_RSTAR_diff_le_one)
  finally show ?thesis .
qed

lemma D1_RSTAR_step:
  assumes "apder_nf r" "apder_nf k"
  shows "D1 (RSTAR r) k \<le> 1 + D1 r (rsimp4_SEQ_atom (RSTAR r) k)"
proof -
  let ?c = "rsimp4_SEQ_atom (RSTAR r) k"
  have root: "single_root (RSTAR r) k = B ?c"
    by (rule star_single_root_eq_B)
  have decomp:
    "A (RALTS [RSTAR r]) k = B ?c \<union> single_term r ?c"
    using A_single_decomp[of "RSTAR r" k] root by simp
  have telescope:
    "card ((single_term r ?c \<union> B ?c) - B k) \<le>
      card (single_term r ?c - B ?c) + card (B ?c - B k)"
    by (rule card_Un_Diff_telescope_le) auto
  have term_bound:
    "card (single_term r ?c - B ?c) \<le> D1 r ?c"
    unfolding D1_def
    by (rule card_mono) (auto simp add: A_single_decomp)
  have boundary: "card (B ?c - B k) \<le> 1"
    by (rule star_boundary_shift_le_one[OF assms])
  have "D1 (RSTAR r) k =
      card ((single_term r ?c \<union> B ?c) - B k)"
    by (simp add: D1_def decomp Un_commute)
  also have "... \<le> card (single_term r ?c - B ?c) + card (B ?c - B k)"
    by (rule telescope)
  also have "... \<le> D1 r ?c + 1"
    using term_bound boundary by simp
  finally show ?thesis
    by simp
qed

(* TARGET (prove below; statement + steer in ROUTE_SEQ.md):
   lemma seq_head_core_le_rsize:
     assumes "apder_nf h" "apder_nf t" "apder_nf k"
     shows
       "card ((single_root (RSEQ h t) k \<union> single_term h (rsimp4_SEQ_atom t k))
              - (strong_apder_acc RONE k \<union> strong_apder_acc RONE (rsimp4_SEQ_atom t k)))
        <= rsize h"
   Induction on h. The RALTS-head case may use the L1 singleton cover — assume it
   (state as an extra `assumes` and report that dependency); the Secretary supplies
   the green L1 from the Cover lane. *)

end
