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

(* TARGETS (prove below; statements + steer in ROUTE_BND.md):
   (S1)  card (strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
           <= card (single_root t k - strong_apder_acc RONE k)
   (boundary_term_absorb)
         card ((strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
               \<union> (single_term t k - strong_apder_acc RONE k))
           <= D (RALTS [t]) k
   Prove boundary_term_absorb VIA S1 (boundary-excess <= root-excess, collision-free),
   NOT via a raw injection. *)

(* ===================================================================== *)
(* GREEN REFORMULATION (no sorry).  rsimpStrong_dlform_closure distributes *)
(* over Un, so the carrier splits cleanly:                                 *)
(*   Aself(t,k) = B(s4 t k) u single_term t k        (decomp_self)         *)
(*   Aalt (t,k) = single_root t k u single_term t k  (decomp_alt)          *)
(* whence BOTH lane targets reduce to the single core inequality           *)
(*   card (Aself t k - B k) <= card (Aalt t k - B k).                       *)
(* (Aself = strong_apder_acc t k ; Aalt = strong_apder_acc (RALTS[t]) k ;  *)
(*  B = strong_apder_acc RONE.)                                            *)
(* ===================================================================== *)

lemma finite_single_root [simp]: "finite (single_root t k)"
  by (simp add: single_root_def)

lemma finite_single_term [simp]: "finite (single_term t k)"
  by (simp add: single_term_def)

(* rsimpStrong_dlform_closure is a per-element big-union, so it distributes
   over Un (row_dlforms stays opaque -- no recursive blow-up). *)
lemma rsimpStrong_dlform_closure_Un:
  "rsimpStrong_dlform_closure (U \<union> V)
     = rsimpStrong_dlform_closure U \<union> rsimpStrong_dlform_closure V"
  by (simp add: rsimpStrong_dlform_closure_def)

lemma strong_apder_acc_decomp_self:
  "strong_apder_acc t k
     = strong_apder_acc RONE (rsimp4_SEQ_atom t k) \<union> single_term t k"
  by (simp add: strong_apder_acc_def single_term_def
      rsimpStrong_dlform_closure_Un)

lemma strong_apder_acc_decomp_alt:
  "strong_apder_acc (RALTS [t]) k = single_root t k \<union> single_term t k"
  by (simp add: strong_apder_acc_def single_root_def single_term_def
      rsimpStrong_dlform_closure_Un)

(* The absorb LHS union is exactly  Aself(t,k) - B k.  (Instantiate the
   decomposition at the FIXED t,k first, so it cannot loop as a rewrite.) *)
lemma boundary_term_absorb_lhs_eq:
  "(strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
     \<union> (single_term t k - strong_apder_acc RONE k)
   = strong_apder_acc t k - strong_apder_acc RONE k"
proof -
  have "strong_apder_acc t k
      = strong_apder_acc RONE (rsimp4_SEQ_atom t k) \<union> single_term t k"
    by (rule strong_apder_acc_decomp_self)
  then show ?thesis by (simp add: Un_Diff)
qed

(* The absorb RHS (and the S1 RHS root-excess summand) is  Aalt(t,k) - B k. *)
lemma boundary_term_absorb_rhs_eq:
  "strong_apder_acc (RALTS [t]) k - strong_apder_acc RONE k
   = (single_root t k - strong_apder_acc RONE k)
     \<union> (single_term t k - strong_apder_acc RONE k)"
proof -
  have "strong_apder_acc (RALTS [t]) k = single_root t k \<union> single_term t k"
    by (rule strong_apder_acc_decomp_alt)
  then show ?thesis by (simp add: Un_Diff)
qed

end
