# ✅ CARD via `card_UN_le` — the VALIDATED route that sidesteps the a*.a* wall (2026-06-17)

The dead `strong_apder_acc` route needed MEMBERSHIP (each opened row ∈ some child accumulator) → FALSE at
RALTS (the leaked row `a·(a*·a*)` belongs to no child, a*.a* wall). The NEW route needs only a COUNT
UPPER BOUND via `card_UN_le` — the leaked row is just counted in its OWN element's contribution; no
membership in children. **`count ≠ membership`, so a*.a* cannot bite it.** Validated 0 violations.

## The chain (target: `card (apder_strong_dlfrontier r) ≤ <linear>`)
```
card (apder_strong_dlfrontier r)
  = card (⋃ q∈apder_rows r. row_dlforms (rsimpStrong_raw q))     -- unfold (apder_strong_dlfrontier_def @11400,
                                                                    rsimpStrong_dlform_closure_def @11335)
  ≤ (∑ q∈apder_rows r. card (row_dlforms (rsimpStrong_raw q)))   -- card_UN_le  [TRIVIAL; apder_rows finite]
  ≤ <linear in rsize r>                                          -- the remaining crux: the SUM is linear
```
A LOOSER linear constant is FINE (e.g. `≤ 4*rsize r + 4`): just relax the `CARD` hypothesis in the green
`universe_le_cubic_rowlevel` + `budget_*` arithmetic — linear × quadratic-per-row = cubic with room under
`2*(rsize r+3)^3`. So aim for ANY clean linear bound, not necessarily `Suc (rsize r)`.

## Validation (0 violations; exhaustive small ≤rsize 10 + ~300k heavy a*.a*/RALTS adversarial)
- `card (apder_rows r) ≤ 2*rsize r + 2`  — **0 viol** (C1; worst 1.00·(n+1)).
- `(∑ q∈apder_rows r. card (row_dlforms (rsimpStrong_raw q))) ≤ 4*rsize r + 4` — **0 viol** (C3; worst 1.40·(n+1)).
- `card (apder_strong_dlfrontier r) ≤ rsize r + 1` — 0 viol (the bound; Antimirov).
- ❌ dead alternatives (do NOT retry): inject-into-`apder_terms` (330k viol), inject-into-`apder_rows`
  (68k viol), the `strong_apder_acc` per-child distribution (a*.a* wall, RALTS).
Reproduce: `posix-codex/scratch_card_terms_bridge.py`.

## How to prove the two pieces (build on EXISTING results — see AGENT_BRIEF LEARN-FIRST rule)
1. **`card_UN_le` step** (trivial): `card (⋃ i∈I. A i) ≤ (∑ i∈I. card (A i))` for finite I — Isabelle library
   lemma `card_UN_le`. Need `finite (apder_rows r)` (grep; apder_terms/rfrontier are finite).
2. **`card (apder_rows r) ≤ linear`**: `apder_rows r = {r} ∪ rfrontier r ∪ (⋃ t∈apder_terms r. rfrontier t)`
   (@1732/@1736). `card (apder_terms r) ≤ apder_awidth r` is PROVEN (`card_apder_terms_le_awidth` @1870, via
   `card_image_le` — NO distribution); `apder_awidth r ≤ rsize r`. Bound `card (rfrontier q)` by q's
   top-alternation branch count. Assemble linearly.
3. **`(∑ q∈apder_rows r. card (row_dlforms (rsimpStrong_raw q))) ≤ linear`** — the crux. This is an
   opened-row-COUNT sum; the **D-law** `D_law_clean` @37145 (+ `apder_T_bound`/`apder_S_bound` @37058)
   already bounds opened-row counts linearly, and the `card_row_dlforms_..._diff_le` family @5541+ bounds
   per-step opened-row card by rsize. Bridge the sum to these (or telescope per-element card via @5541).
   NOTE: a loose `card(apder_rows) · max-per-element` gives only QUADRATIC (per-element is linear, C2 worst
   0.667·(n+1)); you must bound the SUM directly (it IS linear, C3) — via the D-law / diff-card counts,
   NOT card×max.

This is a COUNT argument (card_UN_le + D-law), structurally disjoint from the a*.a* membership wall.
