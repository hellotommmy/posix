# CARD-LEMMA FRONTIER — the true current state (2026-06-19)

Authoritative status of the ONE open lemma that finishes the cubic Gate. This SUPERSEDES the 2026-06-17
framing in `FINISH_HERE.md` / `DIRECT_UNIVERSE_CUBIC_ROUTE.md` where they conflict (those predate the
2026-06-18/19 validation that refuted the naive count routes). Read this first.

## The Gate is GREEN modulo ONE count lemma
```isabelle
lemma card_apder_strong_dlfrontier_le:
  assumes "apder_clean r"
  shows   "card (apder_strong_dlfrontier r) \<le> Suc (rsize r)"     (* a LINEAR row COUNT *)
```
`apder_strong_dlfrontier r = (\<Union>q\<in>apder_rows r. row_dlforms (rsimpStrong_raw q))`
(= `rsimpStrong_dlform_closure (apder_rows r)`). Call it **U(r)** (the STRONG-opened universe).
Discharge it ⇒ unconditional Gate (wired, green): `cubic_gate_unconditional` via
`actual_gate_from_direct_universe_rowlevel[OF clean card_apder_strong_dlfrontier_le[OF clean]]`.
A looser **LINEAR** bound `\<le> a\<cdot>rsize r + b` also closes the Gate (loosen `budget_suc_quad_le_cube`).
A **quadratic** card bound does NOT (makes the Gate quartic). The bound is TRUE: 0 viol, |r| up to 62462,
worst ratio exactly 1.000.

## What is GREEN (cite; do NOT reprove) — in `cubic/DirectUniverseCubic.thy` unless noted
- Row-level assembly: `per_row_size_le_quadratic`, `universe_le_cubic_rowlevel`,
  `actual_gate_from_direct_universe_rowlevel`, `budget_suc_quad_le_cube`, `card_times_quadratic_le_cube`.
- `card_apder_rows_clean_le_rsize_plus_2` @active:37190 — `card (apder_rows r) \<le> rsize r + 2` (the linear ROOT count).
- `apder_strong_dlfrontier_RALTS_subset` @active:19053 — **CLEAN RALTS subset**: `U(RALTS rs) \<subseteq> (\<Union>q\<in>set rs. U q)`.
- `strong_apder_acc` diff-card machinery (cubic/, ~341–691): per-ctor SUBSET lemmas, `card_Un_Diff_telescope_le` @633,
  RCHAR diff base @598, RALTS diff step `card_apder_strong_dlfrontier_RALTS_diff_RONE_le` @671, the @389 bridge.
- `card_le_Suc_card_Diff_singleton` @cubic:307 (EXCESS→absolute lift), `card_le_rsize_set` @cubic:328.
- `card_opened_boundary_forms_le_apder_zw2` @cubic:194 — `card (opened_boundary_forms r k) \<le> apder_zw2 r` (full green induction).
- `apder_zw2_rntimes_free_le_rsize` @active:29914 — `rntimes_free r ==> apder_zw2 r \<le> rsize r`.
- Position/width: `card_apder_terms_le_awidth` @active:1870; `apder_awidth_le_rsize_rntimes_free` @active:23259.

## THE WALL — the lone blocked step (validated 2026-06-19)
`card(U r) \<le> |r|+1` is TRUE and the per-constructor card recurrences hold, BUT the clean-subset induction is
blocked at **RSEQ-strong**:
- RALTS clean subset: GREEN (@19053). RSTAR clean subset: found viable (0/200k) — needs committing.
- **RSEQ-strong has NO clean subset**: the cross-row `rsimpStrong_ALTs_raw` set-prune KEEPS uncollapsed
  `…\<cdot>(c*\<cdot>c*)` rows that per-row `S` collapses, so `U(SEQ a b) \<not>\<subseteq> {prepend-image U a} \<union> U b`
  (~0.02% leak). The inequality `card(U(SEQ a b)) \<le> card(U a) + card(U b)` holds ONLY by a **GLOBAL CANCELLATION**.
- This is the SAME `a*\<cdot>a*` cross-prune wall as verdict7/8/cand2-4/child_ok, now isolated to ONE inequality.

## DEAD — do NOT revisit (validated refuted)
- The whole **`pot` / cube-shell / affine-envelope / charge-cubic / amortized Φ** programme — it bounds a 21×-loose
  over-approximation of `‖U‖`; off the critical path entirely.
- **Per-member L3** (`opened(q) \<le> (|r|+2)²`) — composes to QUARTIC (cancellation per-member).
- **Deep-frontier** route — `apder_strong_dlfrontier \<not>\<subseteq> apder_deep_frontier` (RONE in one not the other); deep card is false for RNTIMES.
- **Naive diff-card telescope / D-law transfer / amortized Ψ** as the FINISH — they LEAK at the RSEQ-strong step
  (the "D_law_clean @37145 cracks it" claim is WRONG: `D_law_clean` bounds the FRONTIER-ROW count, not the strong
  dlform set). The machinery is reusable up to RSEQ; RSEQ is the open content.
- **The SUM carrier** `Σ_q card(dl(S q))` summed per-row — RALTS overshoot grows linearly in |r|.

## LIVE attacks on the wall (the 4 lanes)
1. **RSEQ-DIRECT** (slot T): complete the per-constructor card induction; the lone open step is the RSEQ-strong
   card bound `card(U(SEQ a b)) \<le> card(U a) + card(U b)` (RALTS/RSTAR clean). Prove it via a global-cancellation /
   ledger argument (account for the cross-pruned `…(c*c*)` rows that S collapses), NOT a clean subset.
2. **Uun-BRIDGE** (slot D): the RSEQ subset IS clean in the UNSIMPLIFIED universe `Uun` (σ4 prepend, 0 viol) ⇒
   `card(Uun r) \<le> |r|+1` provable cleanly; then the BRIDGE `card(U r) \<le> card(Uun r)` via a DEFINABLE INJECTION
   `U \<hookrightarrow> Uun` over the prune order (the hard gap). Also try transferring via `card_opened_boundary_forms_le_apder_zw2`
   if `opened_boundary_forms` relates to U.
3. **POSITIONS** (slot P): global position/Glushkov injection — `card(U r) \<le> apder_awidth r + 1` via ONE injection
   of the whole strong frontier into Antimirov positions (thesis Property 9 / AFP `Myhill-Nerode`), bypassing the
   per-constructor recurrence. (Strong frontier is NOT a subset of the deep frontier — needs its own position key.)
4. **REWRITE** (slot R): sidestep the count — the near-identity rewrite `\<leadsto>r'` transporting the controllable
   closed-form cubic bound on `rsimpStrong_raw (rders r s)` onto `rders_simpStrong r s` (thesis Ch5/6). See
   `rewrite/RewriteFallback.thy`.

## Discipline (all lanes)
No `sorry`/`oops`/`admit` — ever; fail-stop + report the exact remaining goal. Validate any NEW numeric sub-claim on
the witness family (`witness_gen.py` + `scratch_direct_universe_cubic.py` / `scratch_pro_amortized_validate.py`)
BEFORE grinding. One owner per worktree; keep your `.thy` green at all times. Build your lane's session (see PROMPT.md).
