theory Card_Route1_Bnd
  imports "Posix_Cubic.DirectUniverseCubic"
begin

(* ===================================================================== *)
(* LANE BOUNDARY — prove S1 + boundary_term_absorb.  See ROUTE_BND.md.    *)
(* Build: scripts\codex-isabelle-build-posix.ps1 -Session Posix_Card_Route1_Bnd *)
(* NO sorry. Build green. Fail-stop + report.                            *)
(* ===================================================================== *)

definition D :: "rrexp \<Rightarrow> rrexp \<Rightarrow> nat" where
  "D r k = card (strong_apder_acc r k - strong_apder_acc RONE k)"
definition single_root :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_root q k =
     rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))"
definition single_term :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_term q k =
     rsimpStrong_dlform_closure (apder_term_frontier_acc q k)"
definition boundary_excess :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "boundary_excess t k =
     strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k"
definition root_excess :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "root_excess t k = single_root t k - strong_apder_acc RONE k"
definition term_excess :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "term_excess t k = single_term t k - strong_apder_acc RONE k"

lemma card_le_if_missing_in_image:
  fixes X Y :: "'a set"
  assumes "finite X" "finite Y" "X - Y \<subseteq> f ` (Y - X)"
  shows "card X \<le> card Y"
proof -
  have finXY: "finite (X \<inter> Y)" "finite (X - Y)" "finite (Y - X)"
    using assms(1,2) by simp_all
  have X: "card X = card (X \<inter> Y) + card (X - Y)"
  proof -
    have "X = (X \<inter> Y) \<union> (X - Y)"
      by auto
    then have "card X = card ((X \<inter> Y) \<union> (X - Y))"
      by simp
    also have "... = card (X \<inter> Y) + card (X - Y)"
      using finXY by (intro card_Un_disjoint) auto
    finally show ?thesis .
  qed
  have Y: "card Y = card (X \<inter> Y) + card (Y - X)"
  proof -
    have "Y = (X \<inter> Y) \<union> (Y - X)"
      by auto
    then have "card Y = card ((X \<inter> Y) \<union> (Y - X))"
      by simp
    also have "... = card (X \<inter> Y) + card (Y - X)"
      using finXY by (intro card_Un_disjoint) auto
    finally show ?thesis .
  qed
  have "card (X - Y) \<le> card (f ` (Y - X))"
    by (rule card_mono) (use assms finXY in auto)
  also have "... \<le> card (Y - X)"
    by (rule card_image_le) (use finXY in auto)
  finally show ?thesis
    using X Y by simp
qed

lemma finite_single_root [simp]:
  "finite (single_root q k)"
  by (simp add: single_root_def)

lemma finite_single_term [simp]:
  "finite (single_term q k)"
  by (simp add: single_term_def)

lemma finite_boundary_excess [simp]:
  "finite (boundary_excess t k)"
  by (simp add: boundary_excess_def)

lemma finite_root_excess [simp]:
  "finite (root_excess t k)"
  by (simp add: root_excess_def)

lemma finite_term_excess [simp]:
  "finite (term_excess t k)"
  by (simp add: term_excess_def)

lemma boundary_excess_le_root_excess_if_missing:
  assumes "boundary_excess t k - root_excess t k
      \<subseteq> rsimpStrong_raw ` (root_excess t k - boundary_excess t k)"
  shows "card (boundary_excess t k) \<le> card (root_excess t k)"
  by (rule card_le_if_missing_in_image[OF finite_boundary_excess finite_root_excess assms])

lemma boundary_term_absorb_if_missing_with_term:
  assumes "(boundary_excess t k \<union> term_excess t k)
      - (root_excess t k \<union> term_excess t k)
      \<subseteq> rsimpStrong_raw `
        ((root_excess t k \<union> term_excess t k)
          - (boundary_excess t k \<union> term_excess t k))"
  shows "card (boundary_excess t k \<union> term_excess t k)
      \<le> card (root_excess t k \<union> term_excess t k)"
  by (rule card_le_if_missing_in_image) (use assms in auto)

lemma boundary_missing_from_subset:
  assumes "boundary_excess t k \<subseteq> root_excess t k"
  shows "boundary_excess t k - root_excess t k
      \<subseteq> rsimpStrong_raw ` (root_excess t k - boundary_excess t k)"
  using assms by auto

lemma strong_apder_acc_singleton_decomp:
  "strong_apder_acc (RALTS [q]) k = single_root q k \<union> single_term q k"
  by (simp add: strong_apder_acc_def single_root_def single_term_def
      rsimpStrong_dlform_closure_def)

lemmas boundary_excess_defs =
  boundary_excess_def root_excess_def strong_apder_acc_def single_root_def
  rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
  rsimpStrong_prune_rows_raw_def rsimpStrong_prune_pair_raw_def
  rsimp7_SEQ_atom_def Let_def

lemma boundary_excess_RZERO_subset:
  "boundary_excess RZERO k \<subseteq> root_excess RZERO k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RZERO:
  "boundary_excess RZERO k - root_excess RZERO k
      \<subseteq> rsimpStrong_raw ` (root_excess RZERO k - boundary_excess RZERO k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RZERO_subset])

lemma boundary_excess_RONE_subset:
  "boundary_excess RONE k \<subseteq> root_excess RONE k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RONE:
  "boundary_excess RONE k - root_excess RONE k
      \<subseteq> rsimpStrong_raw ` (root_excess RONE k - boundary_excess RONE k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RONE_subset])

lemma boundary_excess_RCHAR_subset:
  "boundary_excess (RCHAR c) k \<subseteq> root_excess (RCHAR c) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RCHAR:
  "boundary_excess (RCHAR c) k - root_excess (RCHAR c) k
      \<subseteq> rsimpStrong_raw ` (root_excess (RCHAR c) k - boundary_excess (RCHAR c) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RCHAR_subset])

lemma boundary_excess_RALTS_RZERO_subset:
  "boundary_excess (RALTS rs) RZERO \<subseteq> root_excess (RALTS rs) RZERO"
  by (simp add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RALTS_RZERO:
  "boundary_excess (RALTS rs) RZERO - root_excess (RALTS rs) RZERO
      \<subseteq> rsimpStrong_raw ` (root_excess (RALTS rs) RZERO - boundary_excess (RALTS rs) RZERO)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RALTS_RZERO_subset])

lemma boundary_excess_RALTS_RONE_subset:
  "boundary_excess (RALTS rs) RONE \<subseteq> root_excess (RALTS rs) RONE"
  by (simp add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RALTS_RONE:
  "boundary_excess (RALTS rs) RONE - root_excess (RALTS rs) RONE
      \<subseteq> rsimpStrong_raw ` (root_excess (RALTS rs) RONE - boundary_excess (RALTS rs) RONE)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RALTS_RONE_subset])

lemma rsimpStrong_raw_RALTS_single_RSTAR:
  "rsimpStrong_raw (RALTS [RSTAR r]) = rsimpStrong_raw (RSTAR r)"
  by (cases "rsimpStrong_raw r";
      simp_all add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma rsimpStrong_ALTs_raw_single_RSTAR:
  "rsimpStrong_ALTs_raw (rflts [rsimpStrong_raw (RSTAR r)]) =
     rsimpStrong_raw (RSTAR r)"
  by (cases "rsimpStrong_raw r";
      simp_all add: rsimpStrong_ALTs_raw_def rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RZERO_eq_boundary:
  "single_root (RSTAR r) RZERO =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) RZERO)"
  by (simp add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def)

lemma single_root_RSTAR_RONE_eq_boundary:
  "single_root (RSTAR r) RONE =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) RONE)"
  by (simp add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_raw_RALTS_single_RSTAR)

lemma single_root_RSTAR_RCHAR_eq_boundary:
  "single_root (RSTAR r) (RCHAR c) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RCHAR c))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RSEQ_eq_boundary:
  "single_root (RSTAR r) (RSEQ k1 k2) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RSEQ k1 k2))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RALTS_eq_boundary:
  "single_root (RSTAR r) (RALTS ks) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RALTS ks))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RSTAR_eq_boundary:
  "single_root (RSTAR r) (RSTAR s) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RSTAR s))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def rsimp7_SEQ_atom_def)

lemma single_root_RSTAR_RNTIMES_eq_boundary:
  "single_root (RSTAR r) (RNTIMES s n) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RNTIMES s n))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RBACKREF4_eq_boundary:
  "single_root (RSTAR r) (RBACKREF4 r1 r2 r3 r4 cs) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RBACKREF4 r1 r2 r3 r4 cs))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RHALF_eq_boundary:
  "single_root (RSTAR r) (RHALF s cs rep) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RHALF s cs rep))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_RRESIDUE_eq_boundary:
  "single_root (RSTAR r) (RRESIDUE cs rep) =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) (RRESIDUE cs rep))"
  by (cases "rsimpStrong_raw r";
      simp_all add: single_root_def strong_apder_acc_def
      rsimpStrong_dlform_closure_def rsimpStrong_ALTs_raw_def
      rsimpStrong_prune_rows_raw_def)

lemma single_root_RSTAR_eq_boundary:
  "single_root (RSTAR r) k =
     strong_apder_acc RONE (rsimp4_SEQ_atom (RSTAR r) k)"
  by (cases k)
     (simp_all add: single_root_RSTAR_RZERO_eq_boundary
        single_root_RSTAR_RONE_eq_boundary
        single_root_RSTAR_RCHAR_eq_boundary
        single_root_RSTAR_RSEQ_eq_boundary
        single_root_RSTAR_RALTS_eq_boundary
        single_root_RSTAR_RSTAR_eq_boundary
        single_root_RSTAR_RNTIMES_eq_boundary
        single_root_RSTAR_RBACKREF4_eq_boundary
        single_root_RSTAR_RHALF_eq_boundary
        single_root_RSTAR_RRESIDUE_eq_boundary)

lemma boundary_excess_RSTAR_subset:
  "boundary_excess (RSTAR r) k \<subseteq> root_excess (RSTAR r) k"
  by (simp add: boundary_excess_def root_excess_def single_root_RSTAR_eq_boundary)

lemma boundary_missing_RSTAR:
  "boundary_excess (RSTAR r) k - root_excess (RSTAR r) k
      \<subseteq> rsimpStrong_raw ` (root_excess (RSTAR r) k - boundary_excess (RSTAR r) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RSTAR_subset])

lemma boundary_excess_RBACKREF4_subset:
  "boundary_excess (RBACKREF4 r1 r2 r3 r4 cs) k
      \<subseteq> root_excess (RBACKREF4 r1 r2 r3 r4 cs) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RBACKREF4:
  "boundary_excess (RBACKREF4 r1 r2 r3 r4 cs) k
      - root_excess (RBACKREF4 r1 r2 r3 r4 cs) k
      \<subseteq> rsimpStrong_raw `
        (root_excess (RBACKREF4 r1 r2 r3 r4 cs) k
          - boundary_excess (RBACKREF4 r1 r2 r3 r4 cs) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RBACKREF4_subset])

lemma boundary_excess_RHALF_subset:
  "boundary_excess (RHALF r cs rep) k \<subseteq> root_excess (RHALF r cs rep) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RHALF:
  "boundary_excess (RHALF r cs rep) k - root_excess (RHALF r cs rep) k
      \<subseteq> rsimpStrong_raw `
        (root_excess (RHALF r cs rep) k - boundary_excess (RHALF r cs rep) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RHALF_subset])

lemma boundary_excess_RRESIDUE_subset:
  "boundary_excess (RRESIDUE cs rep) k \<subseteq> root_excess (RRESIDUE cs rep) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RRESIDUE:
  "boundary_excess (RRESIDUE cs rep) k - root_excess (RRESIDUE cs rep) k
      \<subseteq> rsimpStrong_raw `
        (root_excess (RRESIDUE cs rep) k - boundary_excess (RRESIDUE cs rep) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RRESIDUE_subset])

lemma boundary_excess_RNTIMES_subset:
  "boundary_excess (RNTIMES r n) k \<subseteq> root_excess (RNTIMES r n) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_missing_RNTIMES:
  "boundary_excess (RNTIMES r n) k - root_excess (RNTIMES r n) k
      \<subseteq> rsimpStrong_raw `
        (root_excess (RNTIMES r n) k - boundary_excess (RNTIMES r n) k)"
  by (rule boundary_missing_from_subset[OF boundary_excess_RNTIMES_subset])

(* TARGETS (prove below; statements + steer in ROUTE_BND.md):
   (S1)  card (strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
           <= card (single_root t k - strong_apder_acc RONE k)
   (boundary_term_absorb)
         card ((strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
               \<union> (single_term t k - strong_apder_acc RONE k))
           <= D (RALTS [t]) k
   Prove boundary_term_absorb VIA S1 (boundary-excess <= root-excess, collision-free),
   NOT via a raw injection. *)

end
