theory Card_Route1_Seq
  imports "Posix_Cubic.DirectUniverseCubic"
begin

(* ===================================================================== *)
(* LANE SEQ-HEAD — prove seq_head_core_le_rsize.  See ROUTE_SEQ.md.       *)
(* Build: scripts\codex-isabelle-build-posix.ps1 -Session Posix_Card_Route1_Seq *)
(* NO sorry. Build green. Fail-stop + report.                            *)
(* ===================================================================== *)

definition single_root :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_root q k =
     rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))"
definition single_term :: "rrexp \<Rightarrow> rrexp \<Rightarrow> rrexp set" where
  "single_term q k =
     rsimpStrong_dlform_closure (apder_term_frontier_acc q k)"

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
