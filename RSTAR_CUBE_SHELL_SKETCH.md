# RSTAR cube-shell — de-risked proof sketch (2026-06-16)

**Context.** Both per-step budgets (`ctx_bound`, `child_ok`/`drain_child_budget`) are FALSE in-regime (sampling
artifacts). The gate instead reduces — via GREEN lemmas already in `active/AntimirovFactoredTransition.thy` — to a
single **cube-shell invariant**, whose only open constructor step is RSTAR. This file is the de-risked plan for that
step. The cube-shell is machine-validated TRUE (0 / 90k+ depth≥5, incl. the exact `child_ok` killers).

## The reduction (ALL GREEN — no sorry)
```
gate (actual_gate_from_current_drain @36253, conditional)
  ⇐ actual_gate_bridge_from_strong_opened_live_potential @35221          [GREEN]
  ⇐ strong_opened_live_acc_potential r RONE ≤ 2·(rsize r+3)^3
  ⇐ rsize_set_strong_opened_live_row_universe_le_potential @35010        [GREEN]
  ⇐ CUBE-SHELL:  strong_opened_live_acc_potential r k ≤ (rsize r + rsize k)^3 − (rsize k)^3
       leaves RONE @33332, RCHAR @33860                                  [GREEN]
       RALTS @33665, RSEQ @33928 (compose children's shells)             [GREEN]
       RSTAR                                                             [OPEN — this file]
```
Assemble by `induct r` over the cube-shell; specialize `k := RONE` (so `(rsize r+1)^3−1 ≤ 2(rsize r+3)^3`).

## The RSTAR step
Potential def (@33045): `pot (RSTAR r) k = HEAD + BODY` where
```
HEAD = rsize_set (row_dlforms (S (rsimp4_SEQ_atom (RSTAR r) k)))
BODY = pot r (rsimp4_SEQ_atom (RSTAR r) k)          -- body opened against j := r*·k
```
Target shell, split as a difference of cubes (B = rsize r, K = rsize k):
```
(rsize(RSTAR r)+K)^3 − K^3  =  (1+B+K)^3 − K^3
                            =  [ (1+B+K)^3 − (B+K)^3 ]   +   [ (B+K)^3 − K^3 ]
                                 \___ HEAD layer ___/         \____ SAT ____/
```
**Validated decomposition (Secretary, 0 violations / 15059 S-fixed RSTAR roots, incl. nested stars + a*·a* trigger):**
- **HEAD** ≤ `(1+B+K)^3 − (B+K)^3`
- **SAT** : `BODY = pot r (rsimp4_SEQ_atom (RSTAR r) k) ≤ (B+K)^3 − K^3`
- SAT lhs/rhs ratio: min 0.073, median 0.254, max 0.806 (always < 1 — true with margin, but not loose).

### HEAD lemma — EASY (direct analogue of an existing GREEN lemma)
`strong_opened_live_acc_RALTS_root_shell_large` (@33427) proves exactly `1 + rsize_set(row_dlforms(S(rsimp4_SEQ_atom
(RALTS rs) k))) ≤ (n+1)^3 − n^3` from `rsize_set_row_dlforms_rsimpStrong_raw_quadratic` (@22761) +
`rsize_rsimp4_SEQ_atom_le` + cube arithmetic. The RSTAR HEAD has the same shape (`rsimp4_SEQ_atom (RSTAR r) k`,
`rsize ≤ 1 + rsize(RSTAR r) + rsize k = 2+B+K`); copy the @33427 proof with `n := B+K`. Low risk.

### SAT lemma — THE crux (true, well-isolated; the real remaining content)
`pot r (rsimp4_SEQ_atom (RSTAR r) k) ≤ (rsize r + rsize k)^3 − (rsize k)^3`, i.e. **opening the body `r` against its
OWN star continuation `r*·k` costs only the body's `k`-shell — the `r*` prefix is absorbed for free.** This is the
saturation that the naive cube-shell IH misses (the IH would charge the inflated `r*·k`-shell ≈ `(2B)^3 ≈ 7·B^3`, vs
the needed `(B+K)^3−K^3 ≈ 2·B^3`).

Ingredients on hand:
- `strong_opened_live_row_universe_acc_RSTAR_subset` (@33132): `SOLR_acc (RSTAR r) k ⊆ row_dlforms(S(r*·k)) ∪
  SOLR_acc r (r*·k)` — the body-against-`r*·k` rows live inside the STAR's own universe.
- static cubic facts: `card_apder_rows_clean_le_rsize_plus_2` (@37190, linear row count) +
  `apder_rows_member_size_quadratic` (@31364, quadratic row size) + `rsize_set_row_dlforms_rsimpStrong_raw_quadratic`
  (@22761, quadratic opening). Linear × quadratic ≈ cubic — the right order.
- `strong_opened_live_acc_potential_RSTAR_RONE_linear_split` (@33391, GREEN) already peels the root layer.

⚠ **HONEST CAVEAT / the genuine difficulty.** SAT is a statement about the recursive *potential* `pot`, which
OVER-approximates `rsize_set(SOLR_acc …)` (lemma @34905 is `rsize_set ≤ pot`, the wrong direction to just inherit the
set bound). So SAT does NOT fall out of the set-subset lemmas alone. The proof must show the potential's *unrolling of
the body against `r*·k`* itself saturates — i.e. as the induction peels `r` apart, the accumulated `r*` prefix in the
continuation collapses under `S` (the same `a*·a*→a*` absorption, here HELPING) so the summed head terms stay within
`(B+K)^3 − K^3` rather than growing. Plausible routes: (a) a strengthened induction proving SAT and the set-bound
simultaneously; (b) bounding `pot r (r*·k)` by the star-universe potential `pot (RSTAR r) k` minus HEAD via a
potential-monotonicity/idempotency lemma under the `r*` prefix; (c) a direct cube-shell-with-saturation IH that tracks
the collapsing prefix. This is the real open math — well-isolated and TRUE, but not a one-liner.

## Refinement (2026-06-16): the AFFINE structure splits the crux into two scalar lemmas
Empirically, **`pot(RSTAR r, k)` is EXACTLY affine in `rsize k`** (0 non-affine / 437 S-fixed `r*`, incl. the witness
chains; second differences identically 0):
```
pot(RSTAR r, k) = A(r) + B(r)·rsize k          (M := rsize(RSTAR r))
```
The star prefix `r*` in every recursive continuation **linearizes** the `k`-dependence — this *is* the saturation,
made precise (the quadratic `k`-interaction the naive IH feared never materialises). Validated scalar bounds (0
violations / 437):
```
ROOT :  A(r) ≤ M³            (intercept; the star's own opened universe is cubic)
SLOPE:  B(r) ≤ 3·M²          (continuation enters linearly, slope ≤ 3M²; observed max 0.52·M²)
```
These two close the RSTAR cube-shell by **pure cube arithmetic**, for ALL `k`:
```
pot(RSTAR r,k) = A(r)+B(r)·n ≤ M³ + 3M²·n ≤ (M+n)³ − n³        (since (M+n)³−n³ = M³+3M²n+3Mn² ≥ M³+3M²n),  n:=rsize k
```
So the RSTAR step reduces to two **scalar** obligations, much sharper than the original SAT:
- **SLOPE lemma** (new, the easy half): `pot(RSTAR r, k) ≤ pot(RSTAR r, RONE) + 3M²·(rsize k − 1)` — the continuation
  contributes at most `3M²` per unit size. Provable from the affine/tail structure (`k` sits behind the saturating
  `r*` prefix); this is what reduces general-`k` to the root.
- **ROOT lemma** (the remaining core): `pot(RSTAR r, RONE) ≤ M³` (equivalently, via `_RSTAR_RONE_linear_split` @33391,
  `pot r (r*) ≤ M³ − M`). Still a statement about the recursive potential, but now a SINGLE scalar at the fixed root
  continuation — no longer a family over `k`. This is the genuine remaining nut; route via the static star-universe
  facts (@37190 linear count, @31364 quadratic size) applied to the potential's body-against-`r*` unrolling.

## Recommended attack
The RSTAR cube-shell is now: HEAD (easy, @33427 analogue) + SLOPE (easy, affine/tail) + ROOT (the one scalar core)
+ cube arithmetic. ROOT (`pot(RSTAR r, RONE) ≤ M³`) is a good GPT Pro design target, or a WORKER-A attempt with this
sketch; everything else is routine. Probes (reproduce the validation): `/tmp/cube_shell_probe.py`,
`/tmp/cube_shell_sweep.py`, `/tmp/sat_focus.py`, `/tmp/pot_form.py` (affine), `/tmp/affine_bounds.py` (ROOT/SLOPE).
