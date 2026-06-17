theory DirectUniverseCubic_L3
  imports "Posix_Antimirov.AntimirovFactoredTransition"
begin

(* Owner: WORKER-CODEX / L3 lane.  The crux lemma `member_opened_quadratic`.

   TARGET (the form the Phase-1 assembly in DirectUniverseCubic consumes):
     apder_nf r ==> q : apder_rows r
       ==> rsize_set (row_dlforms (rsimpStrong_raw q)) <= (rsize r + 2)^2

   (Equivalent under `apder_clean r` to the route-doc form quantified over
   `partial_derivative_live_row_universe r`, since
   `apder_rows r ⊆ partial_derivative_live_row_universe r`
   (apder_rows_subset_partial_derivative_live_row_universe_clean @35122) and the gate rows
   are contained in the smaller union over `apder_rows r`.)

   STATUS: BLOCKED on existing facts (genuine fail-stop, NO loose composition, NO sorry).
   The two available per-member facts compose only to a QUARTIC, not the target quadratic:

     (A) rsize_set_row_dlforms_rsimpStrong_raw_quadratic @22761 :
           rsize_set (row_dlforms (rsimpStrong_raw p)) <= Suc (rsize p) * rsize p
         -- quadratic in the MEMBER size rsize p.
     (B) apder_rows_member_size_quadratic @31364 :
           apder_nf r ==> x : apder_rows r ==> rsize x <= Suc ((rsize r + 2)^2)
         -- the member size is quadratic in the ROOT (and this is TIGHT: members are
            path-continuations built by stacked rsimp4_SEQ_atom tails, genuinely quadratic,
            cf. apder_terms_member_size_quadratic @2920).

   Composing (A) o (B):
       opened(q) <= Suc (rsize q) * rsize q
                 <= Suc (Suc ((rsize r+2)^2)) * Suc ((rsize r+2)^2)
                 ~ ((rsize r+2)^2)^2  = (rsize r+2)^4      (QUARTIC)
   The target is (rsize r+2)^2.  The gap is a full factor of (rsize r+2)^2; linarith /
   any monotone composition cannot bridge it.  This is the same size x multiplicity
   cancellation that walls the pot route, now at per-member granularity: the per-member
   bound (A) is quadratic-in-member precisely when the member's strong opening DUPLICATES a
   tail across many alternation heads (rsimp7_SEQ_atom distribution), and (B)'s member can
   itself be quadratic-in-root -- but the two extremes never co-occur (a quadratic-in-root
   member strong-collapses so its opening is small).  Capturing that requires a structural /
   amortized argument on the shape of q, NOT the two static facts above.

   Provenance note for the report: `row_dlforms (rsimpStrong_raw q) ⊆ strong_opened_live_row_universe r`
   DOES hold for q : apder_rows r (it is one member of the union defining
   apder_strong_dlfrontier r ⊆ strong_opened_live_row_universe r,
   apder_strong_dlfrontier_subset_strong_opened_live @35158), but bounding opened(q) by the
   WHOLE universe is circular -- the universe's rsize_set is exactly what the gate is trying
   to bound.

   Per WORKER_CODEX_PROMPT / DIRECT_UNIVERSE_CUBIC_ROUTE.md §6: do NOT fall back to the loose
   composition (it overshoots the downstream 2x budget in 26% of cases and here is quartic),
   do NOT add a sorry, do NOT drift to a dead target.  FAIL-STOP, file kept GREEN.

   The candidate statement is recorded (commented) below so the next attempt has the exact goal:

   lemma member_opened_quadratic:
     assumes "apder_nf r" and "q : apder_rows r"
     shows "rsize_set (row_dlforms (rsimpStrong_raw q)) <= (rsize r + 2)^2"
*)

end
