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

end
