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

lemma finite_single_root [simp]:
  "finite (single_root q k)"
  by (simp add: single_root_def)

lemma finite_single_term [simp]:
  "finite (single_term q k)"
  by (simp add: single_term_def)

lemma strong_apder_acc_singleton_decomp:
  "strong_apder_acc (RALTS [q]) k = single_root q k \<union> single_term q k"
  by (simp add: strong_apder_acc_def single_root_def single_term_def
      rsimpStrong_dlform_closure_def)

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
