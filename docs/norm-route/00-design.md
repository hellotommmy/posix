# 00 — N-route design summary (Route 2)

## End target (plain math)
Prove a **linear** cardinality bound for clean `r`:

    card( apder_strong_dlfrontier r )  ≤  C · rsize r + D          (any fixed C, D)

where `apder_strong_dlfrontier r = ⋃_{q ∈ apder_rows r} row_dlforms (rsimpStrong_raw q)`
= `U(r)`, the strong-opened Antimirov universe.

**Why ANY linear constant closes the cubic Gate.** The Gate's target is
`rsize_set(gate rows) ≤ cubic(rsize r)`. It already factors (all GREEN in
`cubic/DirectUniverseCubic.thy`) as

    rsize_set(U r)  ≤  card(U r) · max-row-size(U r)
                    ≤  card(U r) · Suc((rsize r + 2)²)        [per_row_size_le_quadratic, GREEN]

and `max-row-size` is already quadratic. So `card(U r)` linear ⇒ `rsize_set(U r)` cubic.
The currently-wired constant is `Suc(rsize r)` (C=1,D=1) via `budget_suc_quad_le_cube`,
but that lemma is pure `nat` arithmetic: replacing `Suc(rsize r)` by `C·rsize r + D`
re-derives a cubic RHS (loosen the constant), and `actual_gate_from_direct_universe_rowlevel`
consumes it unchanged. **A quadratic card bound does NOT suffice (Gate → quartic).**
So the entire remaining problem is: *U(r) has linearly-many rows.*

## Why the direct route is walled, and the N-route's bet
The clean-subset induction on `U` dies at **RSEQ-strong**: the cross-row prune
`rsimpStrong_ALTs_raw` KEEPS uncollapsed rows like `b*·(a*·a*)` that per-row `S`
collapses to `b*·a*`, so `U(SEQ a b) ⊄ {prepend U a} ∪ U b`. The inequality holds only
by a *global cancellation* no structural induction captures (same wall as
verdict7/8/cand2-4/child_ok).

**N-route bet:** redefine the normalizer so the wall disappears. Use a NEW normalizer
`N = nstrong` built on an **associative** append `α = nplug` (sequence-spine + unit/zero
laws + adjacent-identical-star fold) instead of σ7. Then `N` fully collapses `b*·(a*·a*)
→ b*·a*`, and the new opening `δ_N` and accumulator `A_N` get CLEAN per-constructor
subset recurrences (no `+1`). Bound `A_N` internally (linear, Wave 3). Then bridge the
OLD rows back via a **provenance-indexed** universe `A_N#`:

    U_old(r) ⊆ strong_apder_acc(r,1) ↪ A_N#(r,1),     |A_N#(r,1)| ≤ C·rsize r + D.

Old rows that collapse together under N get DISTINCT provenance tags (so the map is
injective), but the tag set is a small recursive debt indexed by constructor
occurrences, so the total stays linear. Feed the linear `card(U r)` to the existing
GREEN Gate.

## Wave plan & status (see 02-lemma-map.md for the lemma graph)
| Wave | content | key lemma | status |
|------|---------|-----------|--------|
| 0 | baseline model + adversarial list | — | **DONE** (this dir; `norm_model.py` green) |
| 1A | α/nplug + list lemmas | `nplug_assoc` | next; hand-proof done, 0/5.27M |
| 1B | N/nstrong + nalts | `nstrong_rsimp4_shadow` | hand-proof NATURAL, 0/80210 |
| 2A | δ_N/ndlforms | OPEN-SHADOW (S-form) | S-form 0 viol; raw FALSE (DNP-2) |
| 2B | A_N accumulator | 4 subset recurrences | pending |
| 3 | internal linear count | `card(A_N r k − base) ≤ C·rsize r` | pending |
| 4 | old→new shadow | `N(S r)=N r`, `old_acc_shadow` | `N∘S=N` 0/8021 (T7) |
| 5 | provenance injection | `nacc_excess_sharp` + inj, NO product | **the crux** (DNP-4/5) |
| 6 | integrate to Gate | `card_apder_strong_dlfrontier_linear_norm` | pending |

## Wave-0 acceptance (met)
- Faithful model reproduces OLD defs + named CEs. ✓
- `old exact containment into U_N fails`: `b*·(a*·a*) ∈ U(r)`, not N-normal. ✓ [T4]
- `normalized shadow membership holds`: S-form OPEN-SHADOW 0 violations. ✓ [T5_S]
- "do not prove" list written. ✓ [01-adversarial.md]

## The one thing that decides the route
Wave 5: can `U_old ↪ A_N#` be made injective with `|A_N#| ≤ linear` WITHOUT a product?
The family `r_n = (b_1*·a* + ⋯ + b_n*·a*)·a*` (each fiber `{b_i*·a*, b_i*·(a*·a*)}`
collapsing to `b_i*·a*`) is the make-or-break: tags must be `O(n)`, not `O(n²)`. The
Secretary hand-validates the tag-count linearity on this family BEFORE any agent grinds
Wave 5.
