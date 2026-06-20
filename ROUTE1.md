# ROUTE-1 FORMALIZATION — your task in this worktree (Codex worker)

You are the Isabelle/HOL worker formalizing **route-1** (the singleton-cover linear row-count) of a cubic
size-bound proof for a POSIX regex lexer. A Secretary (a separate Claude session) supervises: it has VALIDATED this
design end-to-end (~70M+ Python cases, exhaustive to rsize 11) and CORRECTED two proof-level pitfalls for you. **Your
job is to FORMALIZE the validated design below — not to re-derive or re-search it.** Build green, no `sorry`, commit
small, and fail-stop + report the exact goal state when stuck. The human relays your reports to the Secretary.

## The goal (one lemma closes the Gate)
The whole cubic Gate is GREEN modulo ONE linear row-count lemma, and **ANY linear bound closes it**:
```isabelle
lemma card_apder_strong_dlfrontier_le:
  assumes "apder_clean r"
  shows   "card (apder_strong_dlfrontier r) <= Suc (rsize r)"   (* or <= C*rsize r + D for fixed C,D *)
```
Then `cubic_gate_unconditional` follows via the existing green
`actual_gate_from_direct_universe_rowlevel[OF clean <this>]` (in `cubic/DirectUniverseCubic.thy`). If your final
constant is `Suc(rsize r)` exactly, use it directly; if L2 only yields `<= rsize q + const`, prove the linear
`<= C*rsize r + D` and loosen the downstream `budget_suc_quad_le_cube` (DEFINITIONS notes any linear bound suffices).

## Read first (in this worktree)
- `pro_ask_round2/DEFINITIONS.txt` — every function + the GREEN lemmas you cite, VERBATIM (with the prune chain).
- `pro_ask_round2/DESIGN.md` — the singleton-cover design (L1 cover + L2 singleton-size -> D(r,k)<=rsize r -> card(U)<=rsize+1).
- `pro_ask_round2/verdict_G3.md` (the L2 proof + 3 helpers), `verdict_G2.md` (L1), `verdict_G4.md` (the assembly).
- The green base you build on (do NOT modify): `cubic/DirectUniverseCubic.thy`.
Do NOT read the 37k-line `active/AntimirovFactoredTransition.thy` whole — grep for the green facts you cite.

## ★ THE TWO PROOF-LEVEL CORRECTIONS (validated by the Secretary — follow these, do NOT use the verdicts' broken routes)
1. **L1 cover — prove it at the SAA level, NOT via `dl_le_pruned_altseq`.** verdict_G2's `dl_le_pruned_altseq` /
   `singleton_source_ok` route is FALSE (it tracks only the branch ROOT-row opening; the σ7 `a*·a*`-collapse residual,
   e.g. a bare `a*`, is an ORPHAN there — min CE rs=[((a+b)·a*),((a+1)·a*)]). Instead prove the plain set membership:
   ```isabelle
   lemma strong_apder_acc_RALTS_singleton_cover:
     "strong_apder_acc (RALTS rs) k <= (UN q:set rs. strong_apder_acc (RALTS [q]) k)"
   ```
   directly: every opened parent row lies in SOME branch's FULL carrier `strong_apder_acc (RALTS[q]) k` (the residual
   is covered by that branch's term-frontier / continuation part, not its root). The term part distributes per-branch
   trivially (`apder_term_frontier_acc (RALTS rs) k = (UN q. apder_term_frontier_acc q k)`); the root part is the work
   — show each surviving cross-pruned row of `S(RALTS rs)` opened under k is in some singleton's SAA. No single-origin
   tag is needed; a plain `UN` membership is enough, which is exactly what L2's telescoping consumes.
2. **L2 `boundary_term_absorb` — prove it via S1, NOT a raw injection.** The clean collision-free sufficient condition:
   ```isabelle
   (* S1 *)  card (strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
            <= card (single_root t k - strong_apder_acc RONE k)
   ```
   (boundary-excess never exceeds root-excess; validated 0/629,868, collision-free by construction). With S1 plus the
   disjointness of collapsed-boundary forms from genuine term rows, `boundary_term_absorb` follows without an ad-hoc map.

## The lemma chain to land (bottom-up; cite the green names verbatim from DEFINITIONS.txt §D)
Helper defs (add): `D r k = card (strong_apder_acc r k - strong_apder_acc RONE k)`,
`single_root q k = rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))`,
`single_term q k = rsimpStrong_dlform_closure (apder_term_frontier_acc q k)`,
`fun ralts_size_budget` (sum of rsize over the list).
1. **L1** `strong_apder_acc_RALTS_singleton_cover` — via correction (1) above.
2. **L2 helpers** (verdict_G3): `star_boundary_shift_le_one` (even holds as `card (B (s4 (RSTAR r) k)) <= 1` absolute —
   the plugged star is single-`dl`-headed, never RALTS); `boundary_term_absorb` (via S1, correction (2));
   `seq_head_core_le_rsize` (**fill the RSEQ-head and RALTS-head cases that verdict_G3 leaves `sorry`** — they rest on
   L1 + `card_UN_le`/`card_Un_Diff` bookkeeping; statement validated 48.5M+564k).
3. **L2** `card_strong_apder_acc_singleton_RALTS_diff_base_le_rsize` (= `D1 q k <= rsize q`): induction on q using the
   corrected RSEQ recurrence `D1 (RSEQ r1 r2) k <= rsize r1 + D1 r2 k` (the `1 + D1 r1 (s4 r2 k) + D1 r2 k` form is
   FALSE — CE `(1+a*)·c*` at `k=c*`) and the RSTAR step via `star_boundary_shift_le_one` + IH.
4. **RALTS budget step** `card_strong_apder_acc_RALTS_diff_base_le_size_budget`: from L1 + `card_UN_le` + the set
   identity `(UN_i X_i) - C = UN_i (X_i - C)` + per-branch L2 + `sum_mono` (needs `finite_strong_apder_acc`).
5. **global** `card_strong_apder_acc_diff_base_le_rsize` (`D r k <= rsize r`): induction on r arbitrary k; RCHAR via
   `card_strong_apder_acc_RCHAR_diff_base_le`; RSEQ via `strong_apder_acc_RSEQ_subset` + `strong_apder_acc_RONE_sigma_subset`
   + `card_Un_Diff_telescope_le`; RSTAR via `strong_apder_acc_RSTAR_subset` + the two new RSTAR sub-lemmas
   (`card_rho_RSTAR_diff_base_le_1` and the equality `strong_apder_acc RONE (s4 (RSTAR r) k) = row_dlforms (rsimpStrong_raw (s4 (RSTAR r) k))`,
   both validated 0/~2M — verdict_G4 gives only a sketch; write the real case-split on `s4 (RSTAR r) k ∈ {RZERO, RSTAR r, RSEQ (RSTAR r) k}`);
   RALTS via step 4.
6. **target** `card_apder_strong_dlfrontier_le`: bridge `apder_strong_dlfrontier r <= strong_apder_acc r RONE`
   (`apder_strong_dlfrontier_subset_strong_apder_acc_RONE`), `strong_apder_acc RONE RONE = {RONE}`
   (`strong_apder_acc_RONE_RONE`), `card_le_Suc_card_Diff_singleton`, and step 5 at k=RONE.
7. **corollary** `cubic_gate_unconditional` via `actual_gate_from_direct_universe_rowlevel`.
Mechanical side-lemmas you will also need (all validated true): `finite_strong_apder_acc`, `finite (row_dlforms _)`,
`apder_nf (rsimp4_SEQ_atom r k)` (0/2.2M), `(UN_i X_i) - C = UN_i (X_i - C)`, `ralts_size_budget` = `sum_list (map rsize)`.

## Discipline (hard)
- Write ALL your work in `card/Card_Route1.thy`. Do NOT modify `cubic/DirectUniverseCubic.thy` or anything in
  `pro_ask_round2/`, `active/`, `base/`. (Edit ROOT only — your `Posix_Card_Route1` session is already there.)
- **Build green at all times, 0 sorry/oops/admit.** Build this lane:
  `powershell -File scripts\codex-isabelle-build-posix.ps1 -Session Posix_Card_Route1` (it takes the per-session lock;
  the base heap is warm). Exit 0 = green. Never claim green without an exit-0 build. If a build fails with
  `Posix_Cubic FAILED ... "parent ... saved state does not match"` or a `127`/heap-mismatch, that is SHARED-HEAP
  contention from another worktree's build, NOT your error — just re-run the build (Base/Antimirov re-elaborate, ~1.5min)
  and it goes green. (The scaffold + the 4 helper defs are already verified green.)
- **Grep to confirm every green lemma name** before citing (they are listed in DEFINITIONS.txt §D and exist verbatim
  in `cubic/DirectUniverseCubic.thy` / `active/`). Do not invent names.
- If a step won't go through, **FAIL-STOP**: keep the file green (proved lemmas + the open goal as a comment, NO
  sorry), and report the EXACT remaining goal state + the smallest obstruction. Do NOT grind or weaken statements.
- If you suspect a step is actually FALSE (a new CE), STOP and report it with the minimal regex+k — the Secretary
  re-validates on the witness family before any change. (Three "0 violations" in this project turned out to be
  sampling artifacts; a hand-constructed CE beats a sweep.)
- Commit small on branch `card/route1-formalize` as each lemma lands; report status after each.

## Report protocol (to the Secretary, via the human)
After each build, report in plain math: which lemma is now green (state it as an inequality), what's next, and any
obstruction. When `cubic_gate_unconditional` builds green (0 sorry), STOP and report the full proof text + build result.
