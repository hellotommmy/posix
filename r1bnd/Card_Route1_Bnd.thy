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

lemma boundary_excess_RONE_subset:
  "boundary_excess RONE k \<subseteq> root_excess RONE k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_excess_RCHAR_subset:
  "boundary_excess (RCHAR c) k \<subseteq> root_excess (RCHAR c) k"
  by (cases k; simp_all add: boundary_excess_defs split: rrexp.splits)

lemma boundary_excess_RALTS_RZERO_subset:
  "boundary_excess (RALTS rs) RZERO \<subseteq> root_excess (RALTS rs) RZERO"
  by (simp add: boundary_excess_defs split: rrexp.splits)

lemma boundary_excess_RALTS_RONE_subset:
  "boundary_excess (RALTS rs) RONE \<subseteq> root_excess (RALTS rs) RONE"
  by (simp add: boundary_excess_defs split: rrexp.splits)

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
