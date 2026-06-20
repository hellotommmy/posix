theory Card_Route1_Cover
  imports "Posix_Cubic.DirectUniverseCubic"
begin

(* ===================================================================== *)
(* LANE COVER — prove L1 (the SAA-level singleton cover).  See ROUTE_COVER.md. *)
(* Build: scripts\codex-isabelle-build-posix.ps1 -Session Posix_Card_Route1_Cover *)
(* NO sorry. Build green. Fail-stop + report.                            *)
(* ===================================================================== *)

(* shared defs (same names as the integration file) *)
definition single_root :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_root q k =
     rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))"
definition single_term :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_term q k =
     rsimpStrong_dlform_closure (apder_term_frontier_acc q k)"

(* TARGET (prove below; statement + steer in ROUTE_COVER.md):
   lemma strong_apder_acc_RALTS_singleton_cover:
     "strong_apder_acc (RALTS rs) k \<subseteq> (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
   Prove at the SAA level (fix-(a)); do NOT use the false dl_le_pruned_altseq route. *)

end
