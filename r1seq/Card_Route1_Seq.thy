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

lemma seq_head_core_RONE_le_rsize_from_root_subset:
  assumes root_sub:
    "single_root (RSEQ RONE t) k \<subseteq> B (rsimp4_SEQ_atom t k)"
  shows
    "card ((single_root (RSEQ RONE t) k \<union>
             single_term RONE (rsimp4_SEQ_atom t k))
            - (B k \<union> B (rsimp4_SEQ_atom t k)))
      \<le> rsize RONE"
proof -
  let ?c = "rsimp4_SEQ_atom t k"
  have root_empty:
    "single_root (RSEQ RONE t) k - (B k \<union> B ?c) = {}"
    using root_sub by auto
  show ?thesis
    by (simp add: root_empty)
qed

lemma seq_head_core_RONE_le_rsize_from_root_diff:
  assumes root_diff:
    "card (single_root (RSEQ RONE t) k -
      (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> 1"
  shows
    "card ((single_root (RSEQ RONE t) k \<union>
             single_term RONE (rsimp4_SEQ_atom t k))
            - (B k \<union> B (rsimp4_SEQ_atom t k)))
      \<le> rsize RONE"
  using root_diff by simp

lemma seq_head_core_RONE_counterexample:
  fixes a b :: char
  defines "t \<equiv> RSEQ (RALTS [RCHAR a, RCHAR b]) (RSTAR (RCHAR a))"
  defines "k \<equiv> RSTAR (RCHAR a)"
  assumes "a \<noteq> b"
  shows
    "apder_nf RONE"
    "apder_nf t"
    "apder_nf k"
    "card ((single_root (RSEQ RONE t) k \<union>
             single_term RONE (rsimp4_SEQ_atom t k))
            - (B k \<union> B (rsimp4_SEQ_atom t k))) = 2"
    "rsize RONE = 1"
  using assms
  by (simp_all add: t_def k_def single_root_def rsimpStrong_dlform_closure_def
      B_alt
      rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def
      rsimpStrong_prune_pair_raw_def rsimp7_SEQ_atom_def)

lemma seq_head_core_le_rsize_unrestricted_false:
  "\<exists>h t k. apder_nf h \<and> apder_nf t \<and> apder_nf k \<and>
    rsize h <
      card ((single_root (RSEQ h t) k \<union> single_term h (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k)))"
proof -
  let ?a = "CHR ''a''"
  let ?b = "CHR ''b''"
  let ?t = "RSEQ (RALTS [RCHAR ?a, RCHAR ?b]) (RSTAR (RCHAR ?a))"
  let ?k = "RSTAR (RCHAR ?a)"
  have neq: "?a \<noteq> ?b"
    by simp
  have nf_t: "apder_nf ?t"
    using seq_head_core_RONE_counterexample(2)[OF neq] by simp
  have nf_k: "apder_nf ?k"
    using seq_head_core_RONE_counterexample(3)[OF neq] by simp
  have core:
    "card ((single_root (RSEQ RONE ?t) ?k \<union>
             single_term RONE (rsimp4_SEQ_atom ?t ?k))
            - (B ?k \<union> B (rsimp4_SEQ_atom ?t ?k))) = 2"
    using seq_head_core_RONE_counterexample(4)[OF neq] by simp
  have nf_h: "apder_nf RONE"
    by simp
  have budget:
    "rsize RONE <
      card ((single_root (RSEQ RONE ?t) ?k \<union>
             single_term RONE (rsimp4_SEQ_atom ?t ?k))
            - (B ?k \<union> B (rsimp4_SEQ_atom ?t ?k)))"
    using core by simp
  show ?thesis
    using nf_h nf_t nf_k budget by blast
qed

lemma seq_head_core_RALTS_RONE_counterexample:
  fixes a b c :: char
  defines "h \<equiv> RALTS [RONE]"
  defines "t \<equiv> RSEQ (RALTS [RCHAR a, RCHAR b, RCHAR c]) (RSTAR (RCHAR a))"
  defines "k \<equiv> RSTAR (RCHAR a)"
  assumes "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
  shows
    "apder_nf h"
    "apder_nf t"
    "apder_nf (RSEQ h t)"
    "apder_nf k"
    "card ((single_root (RSEQ h t) k \<union>
             single_term h (rsimp4_SEQ_atom t k))
            - (B k \<union> B (rsimp4_SEQ_atom t k))) = 3"
    "rsize h = 2"
  using assms
  by (simp_all add: h_def t_def k_def single_root_def rsimpStrong_dlform_closure_def
      B_alt
      rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def
      rsimpStrong_prune_pair_raw_def rsimp7_SEQ_atom_def)

lemma seq_head_core_le_rsize_nf_seq_false:
  "\<exists>h t k. apder_nf (RSEQ h t) \<and> apder_nf k \<and>
    rsize h <
      card ((single_root (RSEQ h t) k \<union> single_term h (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k)))"
proof -
  let ?a = "CHR ''a''"
  let ?b = "CHR ''b''"
  let ?c = "CHR ''c''"
  let ?h = "RALTS [RONE]"
  let ?t = "RSEQ (RALTS [RCHAR ?a, RCHAR ?b, RCHAR ?c]) (RSTAR (RCHAR ?a))"
  let ?k = "RSTAR (RCHAR ?a)"
  have neq: "?a \<noteq> ?b" "?a \<noteq> ?c" "?b \<noteq> ?c"
    by simp_all
  have nf_seq: "apder_nf (RSEQ ?h ?t)"
    using seq_head_core_RALTS_RONE_counterexample(3)[OF neq] by simp
  have nf_k: "apder_nf ?k"
    using seq_head_core_RALTS_RONE_counterexample(4)[OF neq] by simp
  have core:
    "card ((single_root (RSEQ ?h ?t) ?k \<union>
             single_term ?h (rsimp4_SEQ_atom ?t ?k))
            - (B ?k \<union> B (rsimp4_SEQ_atom ?t ?k))) = 3"
    using seq_head_core_RALTS_RONE_counterexample(5)[OF neq] by simp
  have size: "rsize ?h = 2"
    using seq_head_core_RALTS_RONE_counterexample(6)[OF neq] by simp
  have budget:
    "rsize ?h <
      card ((single_root (RSEQ ?h ?t) ?k \<union>
             single_term ?h (rsimp4_SEQ_atom ?t ?k))
            - (B ?k \<union> B (rsimp4_SEQ_atom ?t ?k)))"
    using core size by simp
  show ?thesis
    apply (rule exI[of _ ?h])
    apply (rule exI[of _ ?t])
    apply (rule exI[of _ ?k])
    using nf_seq nf_k budget by simp
qed

lemma boundary_RALTS_singleton_branch_cover_false:
  fixes a :: char
  defines "q \<equiv> RSEQ (RCHAR a) (RSTAR (RCHAR a))"
  defines "k \<equiv> RSTAR (RCHAR a)"
  shows "\<not>
    ((B (rsimp4_SEQ_atom (RALTS [q]) k) - B k) \<union>
      (single_term (RALTS [q]) k - B k) \<subseteq>
     (B (rsimp4_SEQ_atom q k) - B k) \<union>
      (single_term q k - B k))"
  by (simp add: q_def k_def B_alt single_term_def
      rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def
      rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma D1_RZERO_le_rsize:
  "D1 RZERO k \<le> rsize RZERO"
proof -
  have "D1 RZERO k = card (A RZERO k - B k)"
    by (simp add: D1_def)
  also have "... = 0"
    by (simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)
  finally show ?thesis by simp
qed

lemma D1_RONE_le_rsize:
  assumes "apder_nf k"
  shows "D1 RONE k \<le> rsize RONE"
proof -
  have sub: "A (RALTS [RONE]) k \<subseteq> B k"
  proof (cases k)
    case RZERO
    then show ?thesis
      by (simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
          rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)
  next
    case RONE
    then show ?thesis
      by (simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
          rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)
  next
    case (RCHAR c)
    then show ?thesis
      using row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF assms]
      by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
          rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def rsimp7_SEQ_atom_def)
  next
    case (RSEQ k1 k2)
    then show ?thesis
      using row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF assms]
      by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
          rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def rsimp7_SEQ_atom_def)
  next
    case (RALTS ks)
    then show ?thesis
      using row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF assms]
      by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
          rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def rsimp7_SEQ_atom_def)
  next
    case (RSTAR k)
    then show ?thesis
      using row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF assms]
      by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
          rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def rsimp7_SEQ_atom_def)
  next
    case (RNTIMES k n)
    then show ?thesis
      using row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF assms]
      by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
          rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def rsimp7_SEQ_atom_def)
  next
    case (RBACKREF4 k1 k2 k3 k4 cs)
    then show ?thesis
      using row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF assms]
      by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
          rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def rsimp7_SEQ_atom_def)
  next
    case (RHALF k cs rep)
    then show ?thesis
      using row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF assms]
      by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
          rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def rsimp7_SEQ_atom_def)
  next
    case (RRESIDUE cs rep)
    then show ?thesis
      using row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF assms]
      by (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def
          rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def rsimp7_SEQ_atom_def)
  qed
  have empty: "A (RALTS [RONE]) k - B k = {}"
    using sub by auto
  have "D1 RONE k = 0"
    unfolding D1_def
    by (simp add: empty)
  then show ?thesis
    by simp
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

lemma combined_RSEQ_RCHAR_le_rsize_from_boundary_rsize:
  assumes boundary:
    "card ((B (rsimp4_SEQ_atom t k) - B k) \<union>
      (single_term t k - B k)) \<le> rsize t"
  shows
    "card ((single_root (RSEQ (RCHAR c) t) k \<union>
        single_term (RCHAR c) (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) +
      card ((B (rsimp4_SEQ_atom t k) - B k) \<union>
        (single_term t k - B k))
      \<le> rsize (RSEQ (RCHAR c) t)"
proof -
  have head:
    "card ((single_root (RSEQ (RCHAR c) t) k \<union>
        single_term (RCHAR c) (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> rsize (RCHAR c)"
    by (rule seq_head_core_RCHAR_le_rsize)
  show ?thesis
    using head boundary by simp
qed

lemma D1_RCHAR_le_rsize:
  assumes "apder_nf k"
  shows "D1 (RCHAR c) k \<le> rsize (RCHAR c)"
  unfolding D1_def
  using card_strong_apder_acc_RCHAR_diff_base_le[OF assms, of c]
  by simp

lemma boundary_RZERO_le_rsize:
  "card ((B (rsimp4_SEQ_atom RZERO k) - B k) \<union>
    (single_term RZERO k - B k)) \<le> rsize RZERO"
  by (simp add: B_alt rsimpStrong_dlform_closure_def)

lemma boundary_RONE_le_rsize:
  "card ((B (rsimp4_SEQ_atom RONE k) - B k) \<union>
    (single_term RONE k - B k)) \<le> rsize RONE"
  by simp

lemma boundary_RCHAR_le_rsize:
  assumes "apder_nf k"
  shows
    "card ((B (rsimp4_SEQ_atom (RCHAR c) k) - B k) \<union>
      (single_term (RCHAR c) k - B k)) \<le> rsize (RCHAR c)"
proof -
  have sub:
    "B (rsimp4_SEQ_atom (RCHAR c) k) \<subseteq> A (RALTS [RCHAR c]) k"
    by (cases k)
      (auto simp add: B_alt strong_apder_acc_def
        rsimpStrong_dlform_closure_def rsimp7_SEQ_atom_def
        rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)
  have "card (B (rsimp4_SEQ_atom (RCHAR c) k) - B k) \<le>
      card (A (RALTS [RCHAR c]) k - B k)"
    by (rule card_mono) (use sub in auto)
  also have "... = D1 (RCHAR c) k"
    by (simp add: D1_def)
  also have "... \<le> rsize (RCHAR c)"
    by (rule D1_RCHAR_le_rsize[OF assms])
  finally show ?thesis
    by simp
qed

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

lemma boundary_RSTAR_step:
  assumes "apder_nf r" "apder_nf k"
  shows
    "card ((B (rsimp4_SEQ_atom (RSTAR r) k) - B k) \<union>
      (single_term (RSTAR r) k - B k))
      \<le> 1 + D1 r (rsimp4_SEQ_atom (RSTAR r) k)"
proof -
  let ?c = "rsimp4_SEQ_atom (RSTAR r) k"
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
  have boundary_sub:
    "(B ?c - B k) \<union> (single_term (RSTAR r) k - B k) \<subseteq>
      (single_term r ?c \<union> B ?c) - B k"
    by auto
  have "card ((B ?c - B k) \<union> (single_term (RSTAR r) k - B k)) \<le>
      card ((single_term r ?c \<union> B ?c) - B k)"
    by (rule card_mono) (use boundary_sub in auto)
  also have "... \<le> card (single_term r ?c - B ?c) + card (B ?c - B k)"
    by (rule telescope)
  also have "... \<le> D1 r ?c + 1"
    using term_bound boundary by simp
  finally show ?thesis
    by simp
qed

lemma boundary_RSTAR_le_rsize_from_child:
  assumes "apder_nf r" "apder_nf k"
    and "D1 r (rsimp4_SEQ_atom (RSTAR r) k) \<le> rsize r"
  shows
    "card ((B (rsimp4_SEQ_atom (RSTAR r) k) - B k) \<union>
      (single_term (RSTAR r) k - B k)) \<le> rsize (RSTAR r)"
  using boundary_RSTAR_step[OF assms(1,2)] assms(3) by simp

lemma D1_RSTAR_le_rsize_from_child:
  assumes "apder_nf r" "apder_nf k"
    and "D1 r (rsimp4_SEQ_atom (RSTAR r) k) \<le> rsize r"
  shows "D1 (RSTAR r) k \<le> rsize (RSTAR r)"
  using D1_RSTAR_step[OF assms(1,2)] assms(3) by simp

lemma D1_RSEQ_step_from_seq_head_and_boundary:
  fixes r1 r2 k
  defines "c \<equiv> rsimp4_SEQ_atom r2 k"
  assumes seq_head:
    "card ((single_root (RSEQ r1 r2) k \<union> single_term r1 c) -
      (B k \<union> B c)) \<le> rsize r1"
    and boundary:
    "card ((B c - B k) \<union> (single_term r2 k - B k)) \<le> D1 r2 k"
  shows "D1 (RSEQ r1 r2) k \<le> rsize r1 + D1 r2 k"
proof -
  let ?Root = "single_root (RSEQ r1 r2) k"
  let ?T1 = "single_term r1 c"
  let ?T2 = "single_term r2 k"
  have decomp:
    "A (RALTS [RSEQ r1 r2]) k = ?Root \<union> ?T1 \<union> ?T2"
    by (auto simp add: A_single_decomp c_def)
  have incl:
    "A (RALTS [RSEQ r1 r2]) k - B k \<subseteq>
      ((?Root \<union> ?T1) - (B k \<union> B c)) \<union>
      ((B c - B k) \<union> (?T2 - B k))"
    using decomp by auto
  have "D1 (RSEQ r1 r2) k \<le>
      card (((?Root \<union> ?T1) - (B k \<union> B c)) \<union>
        ((B c - B k) \<union> (?T2 - B k)))"
    unfolding D1_def
    by (rule card_mono) (use incl in auto)
  also have "... \<le>
      card ((?Root \<union> ?T1) - (B k \<union> B c)) +
      card ((B c - B k) \<union> (?T2 - B k))"
    by (rule card_Un_le)
  also have "... \<le> rsize r1 + D1 r2 k"
    using seq_head boundary by simp
  finally show ?thesis .
qed

lemma D1_RSEQ_le_rsize_from_seq_head_boundary_child:
  fixes r1 r2 k
  assumes seq_head:
    "card ((single_root (RSEQ r1 r2) k \<union>
      single_term r1 (rsimp4_SEQ_atom r2 k)) -
      (B k \<union> B (rsimp4_SEQ_atom r2 k))) \<le> rsize r1"
    and boundary:
    "card ((B (rsimp4_SEQ_atom r2 k) - B k) \<union>
      (single_term r2 k - B k)) \<le> D1 r2 k"
    and child: "D1 r2 k \<le> rsize r2"
  shows "D1 (RSEQ r1 r2) k \<le> rsize (RSEQ r1 r2)"
proof -
  have "D1 (RSEQ r1 r2) k \<le> rsize r1 + D1 r2 k"
    by (rule D1_RSEQ_step_from_seq_head_and_boundary)
      (use seq_head boundary in simp_all)
  then show ?thesis
    using child by simp
qed

lemma D1_RSEQ_step_from_head_boundary_budgets:
  fixes r1 r2 k
  defines "c \<equiv> rsimp4_SEQ_atom r2 k"
  assumes seq_head:
    "card ((single_root (RSEQ r1 r2) k \<union> single_term r1 c) -
      (B k \<union> B c)) \<le> H"
    and boundary:
    "card ((B c - B k) \<union> (single_term r2 k - B k)) \<le> K"
  shows "D1 (RSEQ r1 r2) k \<le> H + K"
proof -
  let ?Root = "single_root (RSEQ r1 r2) k"
  let ?T1 = "single_term r1 c"
  let ?T2 = "single_term r2 k"
  have decomp:
    "A (RALTS [RSEQ r1 r2]) k = ?Root \<union> ?T1 \<union> ?T2"
    by (auto simp add: A_single_decomp c_def)
  have incl:
    "A (RALTS [RSEQ r1 r2]) k - B k \<subseteq>
      ((?Root \<union> ?T1) - (B k \<union> B c)) \<union>
      ((B c - B k) \<union> (?T2 - B k))"
    using decomp by auto
  have "D1 (RSEQ r1 r2) k \<le>
      card (((?Root \<union> ?T1) - (B k \<union> B c)) \<union>
        ((B c - B k) \<union> (?T2 - B k)))"
    unfolding D1_def
    by (rule card_mono) (use incl in auto)
  also have "... \<le>
      card ((?Root \<union> ?T1) - (B k \<union> B c)) +
      card ((B c - B k) \<union> (?T2 - B k))"
    by (rule card_Un_le)
  also have "... \<le> H + K"
    using seq_head boundary by simp
  finally show ?thesis .
qed

lemma D1_RSEQ_le_rsize_from_head_suc_boundary_child:
  fixes r1 r2 k
  assumes seq_head:
    "card ((single_root (RSEQ r1 r2) k \<union>
      single_term r1 (rsimp4_SEQ_atom r2 k)) -
      (B k \<union> B (rsimp4_SEQ_atom r2 k))) \<le> Suc (rsize r1)"
    and boundary:
    "card ((B (rsimp4_SEQ_atom r2 k) - B k) \<union>
      (single_term r2 k - B k)) \<le> D1 r2 k"
    and child: "D1 r2 k \<le> rsize r2"
  shows "D1 (RSEQ r1 r2) k \<le> rsize (RSEQ r1 r2)"
proof -
  have "D1 (RSEQ r1 r2) k \<le> Suc (rsize r1) + D1 r2 k"
    by (rule D1_RSEQ_step_from_head_boundary_budgets)
      (use seq_head boundary in simp_all)
  then show ?thesis
    using child by simp
qed

lemma boundary_RSEQ_step_from_boundary_children:
  fixes r1 r2 k
  defines "c \<equiv> rsimp4_SEQ_atom r2 k"
  assumes left:
    "card ((B (rsimp4_SEQ_atom r1 c) - B c) \<union>
      (single_term r1 c - B c)) \<le> H"
    and right:
    "card ((B c - B k) \<union> (single_term r2 k - B k)) \<le> K"
  shows
    "card ((B (rsimp4_SEQ_atom (RSEQ r1 r2) k) - B k) \<union>
      (single_term (RSEQ r1 r2) k - B k)) \<le> H + K"
proof -
  let ?A = "B (rsimp4_SEQ_atom r1 c) \<union> single_term r1 c"
  let ?B = "B c \<union> single_term r2 k"
  have target_sub:
    "(B (rsimp4_SEQ_atom (RSEQ r1 r2) k) - B k) \<union>
      (single_term (RSEQ r1 r2) k - B k) \<subseteq> (?A \<union> ?B) - B k"
    by (auto simp add: c_def)
  have telescope:
    "card ((?A \<union> ?B) - B k) \<le> card (?A - B c) + card (?B - B k)"
    by (rule card_Un_Diff_telescope_le) auto
  have A_eq:
    "?A - B c =
      (B (rsimp4_SEQ_atom r1 c) - B c) \<union> (single_term r1 c - B c)"
    by auto
  have B_eq:
    "?B - B k = (B c - B k) \<union> (single_term r2 k - B k)"
    by auto
  have "card ((B (rsimp4_SEQ_atom (RSEQ r1 r2) k) - B k) \<union>
      (single_term (RSEQ r1 r2) k - B k)) \<le> card ((?A \<union> ?B) - B k)"
    by (rule card_mono) (use target_sub in auto)
  also have "... \<le> card (?A - B c) + card (?B - B k)"
    by (rule telescope)
  also have "... \<le> H + K"
    using left right by (simp add: A_eq B_eq)
  finally show ?thesis .
qed

lemma boundary_RSEQ_le_rsize_from_children:
  fixes r1 r2 k
  assumes left:
    "card ((B (rsimp4_SEQ_atom r1 (rsimp4_SEQ_atom r2 k)) -
        B (rsimp4_SEQ_atom r2 k)) \<union>
      (single_term r1 (rsimp4_SEQ_atom r2 k) -
        B (rsimp4_SEQ_atom r2 k))) \<le> rsize r1"
    and right:
    "card ((B (rsimp4_SEQ_atom r2 k) - B k) \<union>
      (single_term r2 k - B k)) \<le> rsize r2"
  shows
    "card ((B (rsimp4_SEQ_atom (RSEQ r1 r2) k) - B k) \<union>
      (single_term (RSEQ r1 r2) k - B k)) \<le> rsize (RSEQ r1 r2)"
proof -
  have "card ((B (rsimp4_SEQ_atom (RSEQ r1 r2) k) - B k) \<union>
      (single_term (RSEQ r1 r2) k - B k)) \<le> rsize r1 + rsize r2"
    by (rule boundary_RSEQ_step_from_boundary_children)
      (use left right in simp_all)
  then show ?thesis
    by simp
qed

lemma boundary_le_rsize_from_D1_RALTS_clean:
  assumes d1:
    "\<And>q k. legacy_rrexp q \<Longrightarrow> rntimes_free q \<Longrightarrow>
      apder_nf q \<Longrightarrow> apder_nf k \<Longrightarrow> D1 q k \<le> rsize q"
    and ralts_boundary:
    "\<And>rs k. legacy_rrexp (RALTS rs) \<Longrightarrow> rntimes_free (RALTS rs) \<Longrightarrow>
      apder_nf (RALTS rs) \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((B (rsimp4_SEQ_atom (RALTS rs) k) - B k) \<union>
        (single_term (RALTS rs) k - B k)) \<le> rsize (RALTS rs)"
    and clean: "legacy_rrexp t" "rntimes_free t" "apder_nf t" "apder_nf k"
  shows
    "card ((B (rsimp4_SEQ_atom t k) - B k) \<union>
      (single_term t k - B k)) \<le> rsize t"
  using clean
proof (induction t arbitrary: k)
  case RZERO
  then show ?case
    using boundary_RZERO_le_rsize[of k] by simp
next
  case RONE
  then show ?case
    using boundary_RONE_le_rsize[of k] by simp
next
  case (RCHAR c)
  then show ?case
    using boundary_RCHAR_le_rsize[of k c] by simp
next
  case (RSEQ t1 t2)
  let ?c = "rsimp4_SEQ_atom t2 k"
  have nf_c: "apder_nf ?c"
    using RSEQ.prems by (intro apder_nf_s4) auto
  have left:
    "card ((B (rsimp4_SEQ_atom t1 ?c) - B ?c) \<union>
      (single_term t1 ?c - B ?c)) \<le> rsize t1"
    using RSEQ.IH(1)[OF _ _ _ nf_c] RSEQ.prems by auto
  have right:
    "card ((B (rsimp4_SEQ_atom t2 k) - B k) \<union>
      (single_term t2 k - B k)) \<le> rsize t2"
    using RSEQ.IH(2) RSEQ.prems by auto
  show ?case
    by (rule boundary_RSEQ_le_rsize_from_children[OF left right])
next
  case (RALTS rs)
  then show ?case
    by (intro ralts_boundary) auto
next
  case (RSTAR t)
  let ?c = "rsimp4_SEQ_atom (RSTAR t) k"
  have nf_c: "apder_nf ?c"
    using RSTAR.prems by (intro apder_nf_s4) auto
  have child: "D1 t ?c \<le> rsize t"
    using RSTAR.prems nf_c by (intro d1) auto
  show ?case
    by (rule boundary_RSTAR_le_rsize_from_child)
      (use RSTAR.prems child in auto)
next
  case (RNTIMES t n)
  then show ?case by simp
next
  case (RBACKREF4 t1 t2 t3 t4 cs)
  then show ?case by simp
next
  case (RHALF t cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma D1_RSEQ_le_rsize_from_combined_head_boundary:
  fixes r1 r2 k
  defines "c \<equiv> rsimp4_SEQ_atom r2 k"
  assumes combined:
    "card ((single_root (RSEQ r1 r2) k \<union> single_term r1 c) -
        (B k \<union> B c)) +
      card ((B c - B k) \<union> (single_term r2 k - B k))
      \<le> rsize (RSEQ r1 r2)"
  shows "D1 (RSEQ r1 r2) k \<le> rsize (RSEQ r1 r2)"
proof -
  let ?Root = "single_root (RSEQ r1 r2) k"
  let ?T1 = "single_term r1 c"
  let ?T2 = "single_term r2 k"
  have decomp:
    "A (RALTS [RSEQ r1 r2]) k = ?Root \<union> ?T1 \<union> ?T2"
    by (auto simp add: A_single_decomp c_def)
  have incl:
    "A (RALTS [RSEQ r1 r2]) k - B k \<subseteq>
      ((?Root \<union> ?T1) - (B k \<union> B c)) \<union>
      ((B c - B k) \<union> (?T2 - B k))"
    using decomp by auto
  have "D1 (RSEQ r1 r2) k \<le>
      card (((?Root \<union> ?T1) - (B k \<union> B c)) \<union>
        ((B c - B k) \<union> (?T2 - B k)))"
    unfolding D1_def
    by (rule card_mono) (use incl in auto)
  also have "... \<le>
      card ((?Root \<union> ?T1) - (B k \<union> B c)) +
      card ((B c - B k) \<union> (?T2 - B k))"
    by (rule card_Un_le)
  also have "... \<le> rsize (RSEQ r1 r2)"
    using combined by simp
  finally show ?thesis .
qed

lemma combined_RSEQ_le_rsize_from_head_suc_boundary_rsize:
  assumes seq_head:
    "card ((single_root (RSEQ r1 r2) k \<union>
      single_term r1 (rsimp4_SEQ_atom r2 k)) -
      (B k \<union> B (rsimp4_SEQ_atom r2 k))) \<le> Suc (rsize r1)"
    and boundary:
    "card ((B (rsimp4_SEQ_atom r2 k) - B k) \<union>
      (single_term r2 k - B k)) \<le> rsize r2"
  shows
    "card ((single_root (RSEQ r1 r2) k \<union>
        single_term r1 (rsimp4_SEQ_atom r2 k)) -
        (B k \<union> B (rsimp4_SEQ_atom r2 k))) +
      card ((B (rsimp4_SEQ_atom r2 k) - B k) \<union>
        (single_term r2 k - B k))
      \<le> rsize (RSEQ r1 r2)"
  using seq_head boundary by simp

lemma card_UN_list_Diff_le_sum_rsize:
  assumes "\<And>q. q \<in> set rs \<Longrightarrow> card (F q - C) \<le> rsize q"
  shows "card ((\<Union>q \<in> set rs. F q) - C) \<le> sum_list (map rsize rs)"
  using assms
proof (induction rs)
  case Nil
  then show ?case by simp
next
  case (Cons q qs)
  have split:
    "((\<Union>x \<in> set (q # qs). F x) - C) =
      (F q - C) \<union> ((\<Union>x \<in> set qs. F x) - C)"
    by auto
  have card_split: "card ((\<Union>x \<in> set (q # qs). F x) - C) \<le>
      card (F q - C) + card ((\<Union>x \<in> set qs. F x) - C)"
  proof -
    have "card ((\<Union>x \<in> set (q # qs). F x) - C) =
        card ((F q - C) \<union> ((\<Union>x \<in> set qs. F x) - C))"
      by (subst split) simp
    also have "... \<le> card (F q - C) +
        card ((\<Union>x \<in> set qs. F x) - C)"
      by (rule card_Un_le)
    finally show ?thesis .
  qed
  have q_bound: "card (F q - C) \<le> rsize q"
    using Cons.prems by simp
  have qs_bound:
    "card ((\<Union>x \<in> set qs. F x) - C) \<le> sum_list (map rsize qs)"
    using Cons.IH Cons.prems by auto
  show ?case
    using card_split q_bound qs_bound by simp
qed

lemma D1_RALTS_le_rsize_from_L1_and_branches:
  assumes cover:
    "A (RALTS [RALTS rs]) k \<subseteq> (\<Union>q \<in> set rs. A (RALTS [q]) k)"
    and branches:
    "\<And>q. q \<in> set rs \<Longrightarrow> D1 q k \<le> rsize q"
  shows "D1 (RALTS rs) k \<le> rsize (RALTS rs)"
proof -
  have diff_sub:
    "A (RALTS [RALTS rs]) k - B k \<subseteq>
      (\<Union>q \<in> set rs. A (RALTS [q]) k) - B k"
    using cover by auto
  have "D1 (RALTS rs) k \<le>
      card ((\<Union>q \<in> set rs. A (RALTS [q]) k) - B k)"
    unfolding D1_def
    by (rule card_mono) (use diff_sub in auto)
  also have "... \<le> sum_list (map rsize rs)"
    by (rule card_UN_list_Diff_le_sum_rsize)
      (use branches in \<open>simp add: D1_def\<close>)
  finally show ?thesis
    by simp
qed

lemma seq_head_core_RALTS_le_rsize_from_cover_and_branches:
  fixes rs t k
  defines "c \<equiv> rsimp4_SEQ_atom t k"
  assumes cover:
    "single_root (RSEQ (RALTS rs) t) k \<union> single_term (RALTS rs) c
      \<subseteq> (\<Union>q \<in> set rs.
        single_root (RSEQ q t) k \<union> single_term q c)"
    and branches:
    "\<And>q. q \<in> set rs \<Longrightarrow>
      card ((single_root (RSEQ q t) k \<union> single_term q c) -
        (B k \<union> B c)) \<le> rsize q"
  shows
    "card ((single_root (RSEQ (RALTS rs) t) k \<union>
             single_term (RALTS rs) (rsimp4_SEQ_atom t k)) -
            (B k \<union> B (rsimp4_SEQ_atom t k)))
      \<le> rsize (RALTS rs)"
proof -
  let ?Base = "B k \<union> B c"
  let ?F = "\<lambda>q. single_root (RSEQ q t) k \<union> single_term q c"
  have diff_sub:
    "(single_root (RSEQ (RALTS rs) t) k \<union> single_term (RALTS rs) c) -
       ?Base \<subseteq> (\<Union>q \<in> set rs. ?F q) - ?Base"
    using cover by auto
  have card_c: "card ((single_root (RSEQ (RALTS rs) t) k \<union>
             single_term (RALTS rs) c) - ?Base) \<le>
      card ((\<Union>q \<in> set rs. ?F q) - ?Base)"
    by (rule card_mono) (use diff_sub in auto)
  also have sum_bound: "... \<le> sum_list (map rsize rs)"
    by (rule card_UN_list_Diff_le_sum_rsize) (erule branches)
  finally have "card ((single_root (RSEQ (RALTS rs) t) k \<union>
             single_term (RALTS rs) c) - ?Base) \<le> sum_list (map rsize rs)" .
  then show ?thesis
    unfolding c_def by simp
qed

lemma required_seq_head_core_le_rsize_from_cases_clean:
  assumes rone_diff:
    "\<And>t k. apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card (single_root (RSEQ RONE t) k -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> 1"
    and rseq_case:
    "\<And>r1 r2 t k. legacy_rrexp (RSEQ r1 r2) \<Longrightarrow>
      rntimes_free (RSEQ r1 r2) \<Longrightarrow> apder_nf (RSEQ r1 r2) \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ (RSEQ r1 r2) t) k \<union>
        single_term (RSEQ r1 r2) (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> rsize (RSEQ r1 r2)"
    and rstar_case:
    "\<And>r t k. legacy_rrexp (RSTAR r) \<Longrightarrow>
      rntimes_free (RSTAR r) \<Longrightarrow> apder_nf (RSTAR r) \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ (RSTAR r) t) k \<union>
        single_term (RSTAR r) (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> rsize (RSTAR r)"
    and ralts_cover:
    "\<And>rs t k. single_root (RSEQ (RALTS rs) t) k \<union>
      single_term (RALTS rs) (rsimp4_SEQ_atom t k)
      \<subseteq> (\<Union>q \<in> set rs.
        single_root (RSEQ q t) k \<union>
        single_term q (rsimp4_SEQ_atom t k))"
    and clean:
    "legacy_rrexp h" "rntimes_free h" "apder_nf h"
    "h \<noteq> RZERO" "h \<noteq> RONE" "apder_nf t" "apder_nf k"
  shows
    "card ((single_root (RSEQ h t) k \<union>
             single_term h (rsimp4_SEQ_atom t k)) -
            (B k \<union> B (rsimp4_SEQ_atom t k)))
      \<le> rsize h"
  using clean
proof (cases h)
  case RZERO
  then show ?thesis using clean by simp
next
  case RONE
  then show ?thesis using clean by simp
next
  case (RCHAR c)
  then show ?thesis
    using seq_head_core_RCHAR_le_rsize[of c t k] by simp
next
  case (RSEQ r1 r2)
  then show ?thesis
    using rseq_case[of r1 r2 t k] clean by simp
next
  case (RALTS rs)
  let ?c = "rsimp4_SEQ_atom t k"
  have cover:
    "single_root (RSEQ (RALTS rs) t) k \<union> single_term (RALTS rs) ?c
      \<subseteq> (\<Union>q \<in> set rs.
        single_root (RSEQ q t) k \<union> single_term q ?c)"
    by (rule ralts_cover)
  have branches:
    "\<And>q. q \<in> set rs \<Longrightarrow>
      card ((single_root (RSEQ q t) k \<union> single_term q ?c) -
        (B k \<union> B ?c)) \<le> rsize q"
  proof -
    fix q
    assume q: "q \<in> set rs"
    have q_clean: "legacy_rrexp q" "rntimes_free q" "apder_nf q"
      using RALTS clean q by auto
    have q_nonalt: "nonalt q"
      using RALTS clean q by auto
    have q_nz: "q \<noteq> RZERO"
      using RALTS clean q by auto
    show "card ((single_root (RSEQ q t) k \<union> single_term q ?c) -
        (B k \<union> B ?c)) \<le> rsize q"
    proof (cases q)
      case RZERO
      then show ?thesis using q_nz by simp
    next
      case RONE
      have "card (single_root (RSEQ RONE t) k - (B k \<union> B ?c)) \<le> 1"
        by (rule rone_diff[OF clean(6,7)])
      then show ?thesis
        unfolding RONE by (rule seq_head_core_RONE_le_rsize_from_root_diff)
    next
      case (RCHAR c)
      then show ?thesis
        using seq_head_core_RCHAR_le_rsize[of c t k] by simp
    next
      case (RSEQ s1 s2)
      then show ?thesis
        using rseq_case[of s1 s2 t k] q_clean clean by simp
    next
      case (RALTS qs)
      then show ?thesis using q_nonalt by simp
    next
      case (RSTAR r)
      then show ?thesis
        using rstar_case[of r t k] q_clean clean by simp
    next
      case (RNTIMES r n)
      then show ?thesis using q_clean by simp
    next
      case (RBACKREF4 r1 r2 r3 r4 cs)
      then show ?thesis using q_clean by simp
    next
      case (RHALF r cs rep)
      then show ?thesis using q_clean by simp
    next
      case (RRESIDUE cs rep)
      then show ?thesis using q_clean by simp
    qed
  qed
  show ?thesis
    unfolding RALTS
    by (rule seq_head_core_RALTS_le_rsize_from_cover_and_branches[OF cover branches])
next
  case (RSTAR r)
  then show ?thesis
    using rstar_case[of r t k] clean by simp
next
  case (RNTIMES r n)
  then show ?thesis using clean by simp
next
  case (RBACKREF4 r1 r2 r3 r4 cs)
  then show ?thesis using clean by simp
next
  case (RHALF r cs rep)
  then show ?thesis using clean by simp
next
  case (RRESIDUE cs rep)
  then show ?thesis using clean by simp
qed

lemma required_seq_head_core_le_rsize_from_cases_nf_seq:
  assumes rone_diff:
    "\<And>t k. apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card (single_root (RSEQ RONE t) k -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> 1"
    and rseq_case:
    "\<And>r1 r2 t k. legacy_rrexp (RSEQ r1 r2) \<Longrightarrow>
      rntimes_free (RSEQ r1 r2) \<Longrightarrow> apder_nf (RSEQ r1 r2) \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ (RSEQ r1 r2) t) k \<union>
        single_term (RSEQ r1 r2) (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> rsize (RSEQ r1 r2)"
    and rstar_case:
    "\<And>r t k. legacy_rrexp (RSTAR r) \<Longrightarrow>
      rntimes_free (RSTAR r) \<Longrightarrow> apder_nf (RSTAR r) \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ (RSTAR r) t) k \<union>
        single_term (RSTAR r) (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> rsize (RSTAR r)"
    and ralts_cover:
    "\<And>rs t k. single_root (RSEQ (RALTS rs) t) k \<union>
      single_term (RALTS rs) (rsimp4_SEQ_atom t k)
      \<subseteq> (\<Union>q \<in> set rs.
        single_root (RSEQ q t) k \<union>
        single_term q (rsimp4_SEQ_atom t k))"
    and clean: "legacy_rrexp h" "rntimes_free h" "apder_nf (RSEQ h t)" "apder_nf k"
  shows
    "card ((single_root (RSEQ h t) k \<union>
             single_term h (rsimp4_SEQ_atom t k)) -
            (B k \<union> B (rsimp4_SEQ_atom t k)))
      \<le> rsize h"
proof -
  have h_nf: "apder_nf h" and t_nf: "apder_nf t"
    and h_nz: "h \<noteq> RZERO" and h_no: "h \<noteq> RONE"
    using clean by auto
  show ?thesis
    by (rule required_seq_head_core_le_rsize_from_cases_clean
        [OF rone_diff rseq_case rstar_case ralts_cover
          clean(1) clean(2) h_nf h_nz h_no t_nf clean(4)])
qed

lemma D1_singleton_le_rsize_from_seq_head_boundary_L1_clean:
  assumes L1:
    "\<And>rs k. A (RALTS [RALTS rs]) k \<subseteq>
      (\<Union>q \<in> set rs. A (RALTS [q]) k)"
    and seq_head:
    "\<And>h t k. legacy_rrexp h \<Longrightarrow> rntimes_free h \<Longrightarrow>
      apder_nf h \<Longrightarrow> apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ h t) k \<union>
        single_term h (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> rsize h"
    and boundary:
    "\<And>t k. legacy_rrexp t \<Longrightarrow> rntimes_free t \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((B (rsimp4_SEQ_atom t k) - B k) \<union>
        (single_term t k - B k)) \<le> D1 t k"
    and clean: "legacy_rrexp q" "rntimes_free q" "apder_nf q" "apder_nf k"
  shows "D1 q k \<le> rsize q"
  using clean
proof (induction q arbitrary: k)
  case RZERO
  then show ?case
    using D1_RZERO_le_rsize[of k] by simp
next
  case RONE
  then show ?case
    using D1_RONE_le_rsize[of k] by simp
next
  case (RCHAR c)
  then show ?case
    using D1_RCHAR_le_rsize[of k c] by simp
next
  case (RSEQ q1 q2)
  have sh:
    "card ((single_root (RSEQ q1 q2) k \<union>
      single_term q1 (rsimp4_SEQ_atom q2 k)) -
      (B k \<union> B (rsimp4_SEQ_atom q2 k))) \<le> rsize q1"
    using RSEQ.prems by (intro seq_head) auto
  have bnd:
    "card ((B (rsimp4_SEQ_atom q2 k) - B k) \<union>
      (single_term q2 k - B k)) \<le> D1 q2 k"
    using RSEQ.prems by (intro boundary) auto
  have child: "D1 q2 k \<le> rsize q2"
    using RSEQ.IH(2) RSEQ.prems by auto
  show ?case
    by (rule D1_RSEQ_le_rsize_from_seq_head_boundary_child[OF sh bnd child])
next
  case (RALTS rs)
  have branch: "\<And>q. q \<in> set rs \<Longrightarrow> D1 q k \<le> rsize q"
    using RALTS.IH RALTS.prems by auto
  show ?case
    by (rule D1_RALTS_le_rsize_from_L1_and_branches[OF L1 branch])
next
  case (RSTAR q)
  let ?c = "rsimp4_SEQ_atom (RSTAR q) k"
  have nf_c: "apder_nf ?c"
    using RSTAR.prems by (intro apder_nf_s4) auto
  have child: "D1 q ?c \<le> rsize q"
    using RSTAR.IH[OF _ _ _ nf_c] RSTAR.prems by auto
  show ?case
    using D1_RSTAR_le_rsize_from_child[of q k] RSTAR.prems child by auto
next
  case (RNTIMES q n)
  then show ?case by simp
next
  case (RBACKREF4 q1 q2 q3 q4 cs)
  then show ?case by simp
next
  case (RHALF q cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma D1_singleton_le_rsize_from_seq_head_suc_boundary_L1_clean:
  assumes L1:
    "\<And>rs k. A (RALTS [RALTS rs]) k \<subseteq>
      (\<Union>q \<in> set rs. A (RALTS [q]) k)"
    and seq_head:
    "\<And>h t k. legacy_rrexp h \<Longrightarrow> rntimes_free h \<Longrightarrow>
      apder_nf h \<Longrightarrow> apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ h t) k \<union>
        single_term h (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> Suc (rsize h)"
    and boundary:
    "\<And>t k. legacy_rrexp t \<Longrightarrow> rntimes_free t \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((B (rsimp4_SEQ_atom t k) - B k) \<union>
        (single_term t k - B k)) \<le> D1 t k"
    and clean: "legacy_rrexp q" "rntimes_free q" "apder_nf q" "apder_nf k"
  shows "D1 q k \<le> rsize q"
  using clean
proof (induction q arbitrary: k)
  case RZERO
  then show ?case
    using D1_RZERO_le_rsize[of k] by simp
next
  case RONE
  then show ?case
    using D1_RONE_le_rsize[of k] by simp
next
  case (RCHAR c)
  then show ?case
    using D1_RCHAR_le_rsize[of k c] by simp
next
  case (RSEQ q1 q2)
  have sh:
    "card ((single_root (RSEQ q1 q2) k \<union>
      single_term q1 (rsimp4_SEQ_atom q2 k)) -
      (B k \<union> B (rsimp4_SEQ_atom q2 k))) \<le> Suc (rsize q1)"
    using RSEQ.prems by (intro seq_head) auto
  have bnd:
    "card ((B (rsimp4_SEQ_atom q2 k) - B k) \<union>
      (single_term q2 k - B k)) \<le> D1 q2 k"
    using RSEQ.prems by (intro boundary) auto
  have child: "D1 q2 k \<le> rsize q2"
    using RSEQ.IH(2) RSEQ.prems by auto
  show ?case
    by (rule D1_RSEQ_le_rsize_from_head_suc_boundary_child[OF sh bnd child])
next
  case (RALTS rs)
  have branch: "\<And>q. q \<in> set rs \<Longrightarrow> D1 q k \<le> rsize q"
    using RALTS.IH RALTS.prems by auto
  show ?case
    by (rule D1_RALTS_le_rsize_from_L1_and_branches[OF L1 branch])
next
  case (RSTAR q)
  let ?c = "rsimp4_SEQ_atom (RSTAR q) k"
  have nf_c: "apder_nf ?c"
    using RSTAR.prems by (intro apder_nf_s4) auto
  have child: "D1 q ?c \<le> rsize q"
    using RSTAR.IH[OF _ _ _ nf_c] RSTAR.prems by auto
  show ?case
    using D1_RSTAR_le_rsize_from_child[of q k] RSTAR.prems child by auto
next
  case (RNTIMES q n)
  then show ?case by simp
next
  case (RBACKREF4 q1 q2 q3 q4 cs)
  then show ?case by simp
next
  case (RHALF q cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma D1_singleton_le_rsize_from_seq_head_suc_boundary_rsize_L1_clean:
  assumes L1:
    "\<And>rs k. A (RALTS [RALTS rs]) k \<subseteq>
      (\<Union>q \<in> set rs. A (RALTS [q]) k)"
    and seq_head:
    "\<And>h t k. legacy_rrexp h \<Longrightarrow> rntimes_free h \<Longrightarrow>
      apder_nf h \<Longrightarrow> apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ h t) k \<union>
        single_term h (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> Suc (rsize h)"
    and boundary:
    "\<And>t k. legacy_rrexp t \<Longrightarrow> rntimes_free t \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((B (rsimp4_SEQ_atom t k) - B k) \<union>
        (single_term t k - B k)) \<le> rsize t"
    and clean: "legacy_rrexp q" "rntimes_free q" "apder_nf q" "apder_nf k"
  shows "D1 q k \<le> rsize q"
  using clean
proof (induction q arbitrary: k)
  case RZERO
  then show ?case
    using D1_RZERO_le_rsize[of k] by simp
next
  case RONE
  then show ?case
    using D1_RONE_le_rsize[of k] by simp
next
  case (RCHAR c)
  then show ?case
    using D1_RCHAR_le_rsize[of k c] by simp
next
  case (RSEQ q1 q2)
  have sh:
    "card ((single_root (RSEQ q1 q2) k \<union>
      single_term q1 (rsimp4_SEQ_atom q2 k)) -
      (B k \<union> B (rsimp4_SEQ_atom q2 k))) \<le> Suc (rsize q1)"
    using RSEQ.prems by (intro seq_head) auto
  have bnd:
    "card ((B (rsimp4_SEQ_atom q2 k) - B k) \<union>
      (single_term q2 k - B k)) \<le> rsize q2"
    using RSEQ.prems by (intro boundary) auto
  have combined:
    "card ((single_root (RSEQ q1 q2) k \<union>
        single_term q1 (rsimp4_SEQ_atom q2 k)) -
        (B k \<union> B (rsimp4_SEQ_atom q2 k))) +
      card ((B (rsimp4_SEQ_atom q2 k) - B k) \<union>
        (single_term q2 k - B k))
      \<le> rsize (RSEQ q1 q2)"
    by (rule combined_RSEQ_le_rsize_from_head_suc_boundary_rsize[OF sh bnd])
  show ?case
    by (rule D1_RSEQ_le_rsize_from_combined_head_boundary)
      (use combined in simp)
next
  case (RALTS rs)
  have branch: "\<And>q. q \<in> set rs \<Longrightarrow> D1 q k \<le> rsize q"
    using RALTS.IH RALTS.prems by auto
  show ?case
    by (rule D1_RALTS_le_rsize_from_L1_and_branches[OF L1 branch])
next
  case (RSTAR q)
  let ?c = "rsimp4_SEQ_atom (RSTAR q) k"
  have nf_c: "apder_nf ?c"
    using RSTAR.prems by (intro apder_nf_s4) auto
  have child: "D1 q ?c \<le> rsize q"
    using RSTAR.IH[OF _ _ _ nf_c] RSTAR.prems by auto
  show ?case
    using D1_RSTAR_le_rsize_from_child[of q k] RSTAR.prems child by auto
next
  case (RNTIMES q n)
  then show ?case by simp
next
  case (RBACKREF4 q1 q2 q3 q4 cs)
  then show ?case by simp
next
  case (RHALF q cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma D1_singleton_le_rsize_from_required_seq_head_boundary_L1_clean:
  assumes L1:
    "\<And>rs k. A (RALTS [RALTS rs]) k \<subseteq>
      (\<Union>q \<in> set rs. A (RALTS [q]) k)"
    and seq_head:
    "\<And>h t k. legacy_rrexp h \<Longrightarrow> rntimes_free h \<Longrightarrow>
      apder_nf h \<Longrightarrow> h \<noteq> RZERO \<Longrightarrow> h \<noteq> RONE \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ h t) k \<union>
        single_term h (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> rsize h"
    and boundary:
    "\<And>t k. legacy_rrexp t \<Longrightarrow> rntimes_free t \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((B (rsimp4_SEQ_atom t k) - B k) \<union>
        (single_term t k - B k)) \<le> D1 t k"
    and clean: "legacy_rrexp q" "rntimes_free q" "apder_nf q" "apder_nf k"
  shows "D1 q k \<le> rsize q"
  using clean
proof (induction q arbitrary: k)
  case RZERO
  then show ?case
    using D1_RZERO_le_rsize[of k] by simp
next
  case RONE
  then show ?case
    using D1_RONE_le_rsize[of k] by simp
next
  case (RCHAR c)
  then show ?case
    using D1_RCHAR_le_rsize[of k c] by simp
next
  case (RSEQ q1 q2)
  have sh:
    "card ((single_root (RSEQ q1 q2) k \<union>
      single_term q1 (rsimp4_SEQ_atom q2 k)) -
      (B k \<union> B (rsimp4_SEQ_atom q2 k))) \<le> rsize q1"
    using RSEQ.prems by (intro seq_head) auto
  have bnd:
    "card ((B (rsimp4_SEQ_atom q2 k) - B k) \<union>
      (single_term q2 k - B k)) \<le> D1 q2 k"
    using RSEQ.prems by (intro boundary) auto
  have child: "D1 q2 k \<le> rsize q2"
    using RSEQ.IH(2) RSEQ.prems by auto
  show ?case
    by (rule D1_RSEQ_le_rsize_from_seq_head_boundary_child[OF sh bnd child])
next
  case (RALTS rs)
  have branch: "\<And>q. q \<in> set rs \<Longrightarrow> D1 q k \<le> rsize q"
    using RALTS.IH RALTS.prems by auto
  show ?case
    by (rule D1_RALTS_le_rsize_from_L1_and_branches[OF L1 branch])
next
  case (RSTAR q)
  let ?c = "rsimp4_SEQ_atom (RSTAR q) k"
  have nf_c: "apder_nf ?c"
    using RSTAR.prems by (intro apder_nf_s4) auto
  have child: "D1 q ?c \<le> rsize q"
    using RSTAR.IH[OF _ _ _ nf_c] RSTAR.prems by auto
  show ?case
    using D1_RSTAR_le_rsize_from_child[of q k] RSTAR.prems child by auto
next
  case (RNTIMES q n)
  then show ?case by simp
next
  case (RBACKREF4 q1 q2 q3 q4 cs)
  then show ?case by simp
next
  case (RHALF q cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
qed

lemma D1_singleton_le_rsize_from_seq_head_cases_boundary_L1_clean:
  assumes L1:
    "\<And>rs k. A (RALTS [RALTS rs]) k \<subseteq>
      (\<Union>q \<in> set rs. A (RALTS [q]) k)"
    and rone_diff:
    "\<And>t k. apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card (single_root (RSEQ RONE t) k -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> 1"
    and rseq_case:
    "\<And>r1 r2 t k. legacy_rrexp (RSEQ r1 r2) \<Longrightarrow>
      rntimes_free (RSEQ r1 r2) \<Longrightarrow> apder_nf (RSEQ r1 r2) \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ (RSEQ r1 r2) t) k \<union>
        single_term (RSEQ r1 r2) (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> rsize (RSEQ r1 r2)"
    and rstar_case:
    "\<And>r t k. legacy_rrexp (RSTAR r) \<Longrightarrow>
      rntimes_free (RSTAR r) \<Longrightarrow> apder_nf (RSTAR r) \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ (RSTAR r) t) k \<union>
        single_term (RSTAR r) (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> rsize (RSTAR r)"
    and ralts_cover:
    "\<And>rs t k. single_root (RSEQ (RALTS rs) t) k \<union>
      single_term (RALTS rs) (rsimp4_SEQ_atom t k)
      \<subseteq> (\<Union>q \<in> set rs.
        single_root (RSEQ q t) k \<union>
        single_term q (rsimp4_SEQ_atom t k))"
    and boundary:
    "\<And>t k. legacy_rrexp t \<Longrightarrow> rntimes_free t \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((B (rsimp4_SEQ_atom t k) - B k) \<union>
        (single_term t k - B k)) \<le> D1 t k"
    and clean: "legacy_rrexp q" "rntimes_free q" "apder_nf q" "apder_nf k"
  shows "D1 q k \<le> rsize q"
proof -
  have seq_head:
    "\<And>h t k. legacy_rrexp h \<Longrightarrow> rntimes_free h \<Longrightarrow>
      apder_nf h \<Longrightarrow> h \<noteq> RZERO \<Longrightarrow> h \<noteq> RONE \<Longrightarrow>
      apder_nf t \<Longrightarrow> apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ h t) k \<union>
        single_term h (rsimp4_SEQ_atom t k)) -
        (B k \<union> B (rsimp4_SEQ_atom t k))) \<le> rsize h"
    by (rule required_seq_head_core_le_rsize_from_cases_clean
        [OF rone_diff rseq_case rstar_case ralts_cover])
  show ?thesis
    by (rule D1_singleton_le_rsize_from_required_seq_head_boundary_L1_clean
        [OF L1 seq_head boundary clean])
qed

lemma D1_singleton_le_rsize_from_combined_RSEQ_L1_clean:
  assumes L1:
    "\<And>rs k. A (RALTS [RALTS rs]) k \<subseteq>
      (\<Union>q \<in> set rs. A (RALTS [q]) k)"
    and rseq_combined:
    "\<And>r1 r2 k. legacy_rrexp (RSEQ r1 r2) \<Longrightarrow>
      rntimes_free (RSEQ r1 r2) \<Longrightarrow> apder_nf (RSEQ r1 r2) \<Longrightarrow>
      apder_nf k \<Longrightarrow>
      card ((single_root (RSEQ r1 r2) k \<union>
          single_term r1 (rsimp4_SEQ_atom r2 k)) -
          (B k \<union> B (rsimp4_SEQ_atom r2 k))) +
        card ((B (rsimp4_SEQ_atom r2 k) - B k) \<union>
          (single_term r2 k - B k))
        \<le> rsize (RSEQ r1 r2)"
    and clean: "legacy_rrexp q" "rntimes_free q" "apder_nf q" "apder_nf k"
  shows "D1 q k \<le> rsize q"
  using clean
proof (induction q arbitrary: k)
  case RZERO
  then show ?case
    using D1_RZERO_le_rsize[of k] by simp
next
  case RONE
  then show ?case
    using D1_RONE_le_rsize[of k] by simp
next
  case (RCHAR c)
  then show ?case
    using D1_RCHAR_le_rsize[of k c] by simp
next
  case (RSEQ q1 q2)
  have combined:
    "card ((single_root (RSEQ q1 q2) k \<union>
        single_term q1 (rsimp4_SEQ_atom q2 k)) -
        (B k \<union> B (rsimp4_SEQ_atom q2 k))) +
      card ((B (rsimp4_SEQ_atom q2 k) - B k) \<union>
        (single_term q2 k - B k))
      \<le> rsize (RSEQ q1 q2)"
    using RSEQ.prems by (intro rseq_combined) auto
  show ?case
    by (rule D1_RSEQ_le_rsize_from_combined_head_boundary)
      (use combined in simp)
next
  case (RALTS rs)
  have branch: "\<And>q. q \<in> set rs \<Longrightarrow> D1 q k \<le> rsize q"
    using RALTS.IH RALTS.prems by auto
  show ?case
    by (rule D1_RALTS_le_rsize_from_L1_and_branches[OF L1 branch])
next
  case (RSTAR q)
  let ?c = "rsimp4_SEQ_atom (RSTAR q) k"
  have nf_c: "apder_nf ?c"
    using RSTAR.prems by (intro apder_nf_s4) auto
  have child: "D1 q ?c \<le> rsize q"
    using RSTAR.IH[OF _ _ _ nf_c] RSTAR.prems by auto
  show ?case
    using D1_RSTAR_le_rsize_from_child[of q k] RSTAR.prems child by auto
next
  case (RNTIMES q n)
  then show ?case by simp
next
  case (RBACKREF4 q1 q2 q3 q4 cs)
  then show ?case by simp
next
  case (RHALF q cs rep)
  then show ?case by simp
next
  case (RRESIDUE cs rep)
  then show ?case by simp
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
