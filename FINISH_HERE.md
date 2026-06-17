# FINISH HERE — the whole cubic Gate is GREEN modulo ONE count lemma (2026-06-17)

Build: `powershell -File scripts\codex-isabelle-build-posix.ps1 -Session Posix_Cubic` (~10s leaf, EXIT 0, 0 sorry).
All work is in `cubic/DirectUniverseCubic.thy`, branch `codex/backref-values`, UNCOMMITTED.

## The ONE remaining lemma (everything else is proven)
```isabelle
lemma card_apder_strong_dlfrontier_le:
  assumes "apder_clean r"                       (* or apder_nf r *)
  shows   "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"
```
`apder_strong_dlfrontier r = (\<Union>q\<in>apder_rows r. row_dlforms (rsimpStrong_raw q))` (defs @11400, @11335).
It is a **linear ROW COUNT**. Validated TRUE: `#rows \<le> rsize r + 1`, worst ratio exactly 1.000,
0 fails / 6174 on the clean fragment (`scratch_direct_universe_cubic.py` + the row-level check).

If a looser linear bound `\<le> a*rsize r + b` is all that's provable, prove that and loosen
`universe_le_cubic_rowlevel`'s `CARD` hypothesis + `budget_suc_quad_le_cube` accordingly (the cube
`2*(rsize r+3)^3` has ample room for any linear x quadratic).

## Discharge it → DONE (the unconditional cubic Gate)
```isabelle
corollary cubic_gate_unconditional:
  assumes "apder_clean r"
  shows "rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))) \<le> 2*(rsize r+3)^3"
  by (rule actual_gate_from_direct_universe_rowlevel[OF assms
        card_apder_strong_dlfrontier_le[OF assms]])
```

## Already GREEN in cubic/DirectUniverseCubic.thy (don't redo)
- `per_row_size_le_quadratic` — each row `\<le> Suc((rsize r+2)^2)` (via `row_dlforms_member_size_le_rsize`
  @5902 + `rsize_rsimpStrong_raw_le` @3808 + `apder_rows_member_size_quadratic` @31364).
- `universe_le_cubic_rowlevel` — `rsize_set(apder_strong_dlfrontier r) \<le> 2*(rsize r+3)^3` assuming CARD,
  via `rsize_set_le_card_member_budgetI` @521 (the count x per-row-size lemma) + `budget_suc_quad_le_cube`.
- `actual_gate_from_direct_universe_rowlevel` — the Gate assuming CARD (via gate-rows inclusion @19490 +
  `rsize_set_mono` @403).
- (also the older PER-MEMBER brick `universe_le_cubic`/`actual_gate_from_direct_universe` — keep as backup.)

## How to prove CARD — pointers (the count was the tractable half)
- The linear ROW COUNT was already cracked here as the **D-law**: `D_law_clean` @37145,
  `apder_T_bound`/`apder_S_bound`/`T_and_S` @37058. Find whether it bounds `card(apder_strong_dlfrontier r)`
  or a dominating set, and bridge.
- Card machinery: `card (aseq_terms r) \<le> rsize r` @371; `card_row_dlforms_..._diff_le` family @5541+
  (bounds card of opened-row DIFFERENCES by rsize — may telescope over `apder_rows`); `card_apder_frontier_*`
  @3068; grep `card.*rsimpStrong_dlform_closure` / `card.*apder_strong_dlfrontier` for a near-miss.
- ⚠ Ruled out: the DEEP-frontier linear card is FALSE for RNTIMES/general input, and
  `apder_strong_dlfrontier \<not>\<subseteq> apder_deep_frontier` — so do NOT route through the deep frontier; the
  strong frontier needs its own count on the clean fragment (apder_clean, no RNTIMES).
- ⚠ Do NOT try to bound the SIZE per-member (the dead per-member L3): it hits the size x multiplicity
  cancellation (composes to quartic). The whole point of the row-level route is COUNT x per-row-SIZE.

## Context
`DIRECT_UNIVERSE_CUBIC_ROUTE.md` (full route + numbers), `STEER.md` top banner (status), memory
`posix-direct-universe-cubic-bypass`. The pot/cube-shell/Φ programme is OFF the critical path.
