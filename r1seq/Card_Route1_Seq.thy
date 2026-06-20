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

(* ===================================================================== *)
(* GENERAL-CONTINUATION D BOUND ROUTE.                                    *)
(*   card (strong_apder_acc r k - strong_apder_acc RONE k) <= rsize r     *)
(* via the GREEN per-constructor carrier subsets (reassoc-clean), giving  *)
(* the gate count lemma card (apder_strong_dlfrontier r) <= Suc (rsize r) *)
(* directly.  RALTS is the cross-prune-leaky case (cover lane); carried   *)
(* as an explicit hypothesis RALTS_diff below.                            *)
(* ===================================================================== *)

text \<open>row_dlforms of an RSTAR-headed / RSEQ(RSTAR ..)-headed row is a singleton.\<close>

lemma row_dlforms_RSTAR [simp]:
  "row_dlforms (RSTAR s) = {RSTAR s}"
  by simp

lemma row_dlforms_RSEQ_RSTAR [simp]:
  "row_dlforms (RSEQ (RSTAR s) X) = {RSEQ (RSTAR s) X}"
  by simp

lemma card_row_dlforms_rsimp7_RSTAR_le_one:
  "card (row_dlforms (rsimp7_SEQ_atom (RSTAR s) Y)) \<le> 1"
proof (cases Y)
  case (RSEQ y1 y2)
  then show ?thesis
    by (cases y1)
       (auto simp add: rsimp7_SEQ_atom_def)
qed (auto simp add: rsimp7_SEQ_atom_def)

lemma rsimpStrong_raw_RSTAR_cases:
  "rsimpStrong_raw (RSTAR r) = RONE \<or> (\<exists>s. rsimpStrong_raw (RSTAR r) = RSTAR s)"
  by (cases "rsimpStrong_raw r") auto

text \<open>The strong-opened star boundary either collapses into the continuation's
  own strong form (so it is absorbed by the base) or opens to a single row.\<close>

lemma star_root_collapse_or_singleton:
  "rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k) = rsimpStrong_raw k
   \<or> card (row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))) \<le> 1"
proof (cases "k = RZERO \<or> k = RONE")
  case True
  then show ?thesis
  proof
    assume "k = RZERO"
    then show ?thesis by simp
  next
    assume k1: "k = RONE"
    have "rsimp4_SEQ_atom (RSTAR r) k = RSTAR r" using k1 by simp
    then show ?thesis
      using rsimpStrong_raw_RSTAR_cases[of r] by auto
  qed
next
  case False
  then have s4eq: "rsimp4_SEQ_atom (RSTAR r) k = RSEQ (RSTAR r) k"
    by (cases k) auto
  have Seq: "rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k) =
      rsimp7_SEQ_atom (rsimpStrong_raw (RSTAR r)) (rsimpStrong_raw k)"
    by (simp add: s4eq)
  from rsimpStrong_raw_RSTAR_cases[of r] show ?thesis
  proof
    assume "rsimpStrong_raw (RSTAR r) = RONE"
    then have "rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k) = rsimpStrong_raw k"
      by (simp add: Seq rsimp7_SEQ_atom_def)
    then show ?thesis by blast
  next
    assume "\<exists>s. rsimpStrong_raw (RSTAR r) = RSTAR s"
    then obtain s where s: "rsimpStrong_raw (RSTAR r) = RSTAR s" by blast
    have "card (row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))) \<le> 1"
      using card_row_dlforms_rsimp7_RSTAR_le_one[of s "rsimpStrong_raw k"]
      by (simp only: Seq s)
    then show ?thesis by blast
  qed
qed

lemma star_root_diff_base_le_one:
  assumes nfk: "apder_nf k"
  shows "card (row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))
               - strong_apder_acc RONE k) \<le> 1"
proof (cases "rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k) = rsimpStrong_raw k")
  case True
  then have coll: "rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k) = rsimpStrong_raw k" .
  have subC: "row_dlforms (rsimpStrong_raw k) \<subseteq> strong_apder_acc RONE k"
    by (rule row_dlforms_rsimpStrong_raw_subset_strong_apder_acc_RONE[OF nfk])
  have e: "row_dlforms (rsimpStrong_raw k) - strong_apder_acc RONE k = {}"
    using subC by (simp add: Diff_eq_empty_iff)
  have z: "row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))
           - strong_apder_acc RONE k = {}"
    by (simp only: coll e)
  show ?thesis by (subst z) simp
next
  case False
  hence R: "card (row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))) \<le> 1"
    using star_root_collapse_or_singleton[of r k] by blast
  have "card (row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))
             - strong_apder_acc RONE k)
        \<le> card (row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k)))"
    by (rule card_mono) auto
  with R show ?thesis by linarith
qed

text \<open>The strong-opened star plug equals the strong closure of its own
  one-row frontier (the plug is never alternation-headed).\<close>

lemma star_plug_base_eq_root:
  "strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k) =
     row_dlforms (rsimpStrong_raw (rsimp4_SEQ_atom (RSTAR r) k))"
  by (cases k)
     (auto simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)

(* --------------------------------------------------------------------- *)
(* The GENERAL-CONTINUATION D BOUND, by induction on r over the clean     *)
(* fragment.  RSEQ/RSTAR use the GREEN per-constructor carrier subsets    *)
(* (which are reassociation-clean), the telescope combinator, the RONE    *)
(* base-shift, and the star boundary lemma above.  RALTS is the           *)
(* cross-prune-leaky constructor (the parallel COVER lane) and is carried *)
(* as the explicit hypothesis RALTS_diff.                                 *)
(* --------------------------------------------------------------------- *)

lemma card_strong_apder_acc_diff_base_le:
  assumes RALTS_diff:
    "\<And>rs k. apder_nf (RALTS rs) \<Longrightarrow> apder_nf k \<Longrightarrow>
       card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
         \<le> rsize (RALTS rs)"
  shows "apder_clean r \<Longrightarrow> apder_nf k \<Longrightarrow>
     card (strong_apder_acc r k - strong_apder_acc RONE k) \<le> rsize r"
proof (induction r arbitrary: k)
  case RZERO
  then show ?case
    by (simp add: strong_apder_acc_def rsimpStrong_dlform_closure_def)
next
  case RONE
  then show ?case by simp
next
  case (RCHAR c)
  show ?case
    by (rule card_strong_apder_acc_RCHAR_diff_base_le[OF RCHAR.prems(2)])
next
  case (RSEQ r1 r2)
  have cl1: "apder_clean r1" and cl2: "apder_clean r2"
    using RSEQ.prems(1) by (auto simp add: apder_clean_def)
  have nfk: "apder_nf k" using RSEQ.prems(2) .
  have nf2: "apder_nf r2" using cl2 by (simp add: apder_clean_def)
  let ?m = "rsimp4_SEQ_atom r2 k"
  have nfm: "apder_nf ?m" using apder_nf_s4[OF nf2 nfk] .
  have mid: "strong_apder_acc RONE ?m \<subseteq> strong_apder_acc r2 k"
    by (rule strong_apder_acc_RONE_sigma_subset)
  have ih1: "card (strong_apder_acc r1 ?m - strong_apder_acc RONE ?m) \<le> rsize r1"
    by (rule RSEQ.IH(1)[OF cl1 nfm])
  have ih2: "card (strong_apder_acc r2 k - strong_apder_acc RONE k) \<le> rsize r2"
    by (rule RSEQ.IH(2)[OF cl2 nfk])
  have "card (strong_apder_acc (RSEQ r1 r2) k - strong_apder_acc RONE k)
        \<le> card ((strong_apder_acc r1 ?m \<union> strong_apder_acc r2 k)
                  - strong_apder_acc RONE k)"
    by (rule card_mono) (use strong_apder_acc_RSEQ_subset[of r1 r2 k] in auto)
  also have "... \<le> card (strong_apder_acc r1 ?m - strong_apder_acc RONE ?m)
                  + card (strong_apder_acc r2 k - strong_apder_acc RONE k)"
    by (rule card_Un_Diff_telescope_le
        [OF finite_strong_apder_acc finite_strong_apder_acc mid])
  also have "... \<le> rsize r1 + rsize r2" using ih1 ih2 by linarith
  also have "... \<le> rsize (RSEQ r1 r2)" by simp
  finally show ?case .
next
  case (RALTS rs)
  have nf: "apder_nf (RALTS rs)" using RALTS.prems(1) by (simp add: apder_clean_def)
  show ?case by (rule RALTS_diff[OF nf RALTS.prems(2)])
next
  case (RSTAR r)
  have clr: "apder_clean r" using RSTAR.prems(1) by (simp add: apder_clean_def)
  have nfk: "apder_nf k" using RSTAR.prems(2) .
  have nfr: "apder_nf r" using clr by (simp add: apder_clean_def)
  have nfRSTAR: "apder_nf (RSTAR r)" using nfr by simp
  let ?mm = "rsimp4_SEQ_atom (RSTAR r) k"
  have nfmm: "apder_nf ?mm" using apder_nf_s4[OF nfRSTAR nfk] .
  have root_eq: "strong_apder_acc RONE ?mm
                 = row_dlforms (rsimpStrong_raw ?mm)"
    by (rule star_plug_base_eq_root)
  have sub: "strong_apder_acc (RSTAR r) k
             \<subseteq> strong_apder_acc RONE ?mm \<union> strong_apder_acc r ?mm"
    using strong_apder_acc_RSTAR_subset[of r k] by (simp only: root_eq)
  have ih: "card (strong_apder_acc r ?mm - strong_apder_acc RONE ?mm) \<le> rsize r"
    by (rule RSTAR.IH[OF clr nfmm])
  have sb: "card (strong_apder_acc RONE ?mm - strong_apder_acc RONE k) \<le> 1"
    using star_root_diff_base_le_one[OF nfk] by (simp only: root_eq)
  have "card (strong_apder_acc (RSTAR r) k - strong_apder_acc RONE k)
        \<le> card ((strong_apder_acc r ?mm \<union> strong_apder_acc RONE ?mm)
                  - strong_apder_acc RONE k)"
    by (rule card_mono) (use sub in auto)
  also have "... \<le> card (strong_apder_acc r ?mm - strong_apder_acc RONE ?mm)
                  + card (strong_apder_acc RONE ?mm - strong_apder_acc RONE k)"
    by (rule card_Un_Diff_telescope_le
        [OF finite_strong_apder_acc finite_strong_apder_acc subset_refl])
  also have "... \<le> rsize r + 1" using ih sb by linarith
  also have "... = rsize (RSTAR r)" by simp
  finally show ?case .
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

(* --------------------------------------------------------------------- *)
(* THE GATE COUNT LEMMA (the project's single remaining open lemma).       *)
(* Follows from the general-k D bound at k = RONE, via the GREEN bridge    *)
(*   apder_strong_dlfrontier r \<subseteq> strong_apder_acc r RONE  and       *)
(*   strong_apder_acc RONE RONE = {RONE}.  Carries the RALTS cover         *)
(* hypothesis RALTS_diff (the parallel COVER lane).                        *)
(* --------------------------------------------------------------------- *)

lemma card_apder_strong_dlfrontier_le:
  assumes RALTS_diff:
    "\<And>rs k. apder_nf (RALTS rs) \<Longrightarrow> apder_nf k \<Longrightarrow>
       card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
         \<le> rsize (RALTS rs)"
  assumes clean: "apder_clean r"
  shows "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
proof -
  have nf: "apder_nf r" using clean by (simp add: apder_clean_def)
  have d': "card (strong_apder_acc r RONE - {RONE}) \<le> rsize r"
    using card_strong_apder_acc_diff_base_le[OF RALTS_diff clean, of RONE] by simp
  have "card (strong_apder_acc r RONE)
        \<le> Suc (card (strong_apder_acc r RONE - {RONE}))"
    by (rule card_le_Suc_card_Diff_singleton) simp
  also have "... \<le> Suc (rsize r)" using d' by simp
  finally have c2: "card (strong_apder_acc r RONE) \<le> Suc (rsize r)" .
  have "card (apder_strong_dlfrontier r) \<le> card (strong_apder_acc r RONE)"
    by (rule card_mono)
       (use apder_strong_dlfrontier_subset_strong_apder_acc_RONE[OF nf] in auto)
  with c2 show ?thesis by linarith
qed

text \<open>And the full cubic gate closes through the GREEN row-level gate,
  modulo the same RALTS cover hypothesis.\<close>

lemma actual_gate_route1_seq:
  assumes RALTS_diff:
    "\<And>rs k. apder_nf (RALTS rs) \<Longrightarrow> apder_nf k \<Longrightarrow>
       card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
         \<le> rsize (RALTS rs)"
  assumes clean: "apder_clean r"
  shows "rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
           \<le> 2 * (rsize r + 3) ^ 3"
  by (rule actual_gate_from_direct_universe_rowlevel
        [OF clean card_apder_strong_dlfrontier_le[OF RALTS_diff clean]])

end
