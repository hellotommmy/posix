# AGENT BRIEF — read this FIRST (fresh start, 2026-06-17). Complete current context.

You are a fresh proof worker on the POSIX regex **cubic size-bound** Isabelle/HOL proof. You run in your
OWN git worktree (your working dir = your worktree; your own branch). You do NOT share a tree with other
agents — edit freely, you cannot clash.

## THE GOAL — ONE lemma closes everything
The entire clean-fragment cubic **Gate is GREEN** (0 sorry) modulo a single COUNT bound. Prove:
```isabelle
lemma card_apder_strong_dlfrontier_le:
  assumes "apder_clean r"                  (* or apder_nf r *)
  shows   "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
```
then discharge → the unconditional cubic Gate (this corollary is the finish line):
```isabelle
corollary cubic_gate_unconditional:
  assumes "apder_clean r"
  shows "rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))) \<le> 2*(rsize r+3)^3"
  by (rule actual_gate_from_direct_universe_rowlevel[OF assms card_apder_strong_dlfrontier_le[OF assms]])
```
Validated TRUE numerically: `card(apder_strong_dlfrontier r) \<le> rsize r + 1`, worst ratio 1.000, 0
fails / 6174 on the clean fragment. A looser linear bound `\<le> a*rsize r + b` also works (then loosen
`universe_le_cubic_rowlevel`'s CARD hypothesis + `budget_suc_quad_le_cube`).

## STATE — already GREEN in `cubic/DirectUniverseCubic.thy` (33 lemmas, 0 sorry). DO NOT reprove / delete.
- The **8-lemma green brick** reduces the Gate to the CARD bound via COUNT × PER-ROW-SIZE
  (`per_row_size_le_quadratic`, `universe_le_cubic_rowlevel`, `actual_gate_from_direct_universe_rowlevel`,
  `budget_suc_quad_le_cube`, `card_times_quadratic_le_cube`, …).
- **~25 GREEN card-scaffold lemmas already proven** toward CARD via the `strong_apder_acc` accumulator:
  `apder_strong_dlfrontier r \<subseteq> strong_apder_acc r RONE` (the bridge), per-constructor subset lemmas
  (`strong_apder_acc_{RSEQ,RSTAR,RCHAR,RALTS,RONE}_subset`), and card-telescoping lemmas
  (`card_le_rsize_set`, `card_Un_Diff_telescope_le`, `card_strong_apder_acc_{RCHAR,RSTAR}_root_diff_base_le`,
  `card_apder_strong_dlfrontier_RALTS_diff_RONE_le`, …). **BUILD ON THESE** — you are close.
- `apder_strong_dlfrontier r = (\<Union>q\<in>apder_rows r. row_dlforms (rsimpStrong_raw q))` (def @11400 in
  `active/AntimirovFactoredTransition.thy`; that file is HUGE — grep, never read whole).

## HOW to finish CARD (the count, three viable angles — diversity is intentional)
- **A · D-law transfer**: `D_law_clean` @37145, `apder_T_bound`/`apder_S_bound`/`T_and_S` @37058 bound the
  linear row count — bridge to `card(apder_strong_dlfrontier r)`.
- **B · card telescope (the scaffold's own line)**: finish the `strong_apder_acc` per-constructor
  telescoping already started (`card_Un_Diff_telescope_le` + the per-ctor diff lemmas) to a linear total.
- **C · structural induction** on `apder_strong_dlfrontier` / `strong_apder_acc` directly to `\<le> Suc(rsize r)`.
Pick your assigned angle; if it stalls, say so precisely and try another — do NOT thrash.

## DEAD — never work on (these are the walls we already bypassed)
`pot` / cube-shell / `strong_opened_live_acc_potential` / amortised Φ; the **per-member** opening bound
(`opened(q) \<le> (rsize r+2)^2` — composes to quartic, the size×multiplicity cancellation); the
DEEP-frontier linear card (FALSE for RNTIMES/general; `apder_strong_dlfrontier \<not>\<subseteq> apder_deep_frontier`);
`ctx_bound`/`child_ok`/`drain`. If your target mentions any of these as the thing to BOUND, STOP.

## DISCIPLINE (hard)
- **No `sorry`/`oops`/`admit`, ever.** Keep `cubic/DirectUniverseCubic.thy` GREEN; APPEND only; never
  delete/modify the existing 33 green lemmas.
- Build YOUR worktree: `powershell -File <this-worktree>\scripts\codex-isabelle-build-posix.ps1 -Session Posix_Cubic`
  (first build ~37s rebuilds the Antimirov heap, then ~10s). The `-Session Posix_Rewrite_Fallback` lane is
  the separate `→r'` route in `rewrite/RewriteFallback.thy` (D-lane only).
- When green WITH the card lemma + corollary: `git commit` to YOUR branch, then report. Do NOT push to
  `codex/backref-values` and do NOT merge — the human/Secretary integrates the winner.
- Fail-stop + report the exact blocked subgoal if you genuinely can't close it.

## Deeper context (optional): `FINISH_HERE.md`, `DIRECT_UNIVERSE_CUBIC_ROUTE.md` (route + numbers + the
`→r'` fallback §6), `STEER.md` (live board). `PROGRESS_BACKREF.md` tail = latest state.
