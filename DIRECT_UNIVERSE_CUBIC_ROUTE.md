# THE DIRECT-UNIVERSE CUBIC ROUTE — validated bypass of the `pot` wall (2026-06-17)

**Status:** numerically validated, 0 violations / 10,092 distinct S-fixed regexes incl. ALL known
killers. This is the live route. The old `pot`-cubic anchor (`pot(r*,char c) ≤ M³+3M²`) is **no longer
on the critical path** — it was a bound on a 21×-too-loose over-approximation.

---

## 0. One-paragraph summary

The Gate's actual target is `‖U(r)‖ = rsize_set(strong_opened_live_row_universe r)`. The proved chain
already gives **gate-rows ⊆ U(r)** (monotonicity, GREEN) and **‖U(r)‖ ≤ pot(r,RONE)** (GREEN, @35010),
then tries to prove `pot ≤ 2(|r|+3)³` — and that is the wall (8+ Pro rounds, the size×multiplicity
cancellation). **But `pot` over-approximates `‖U(r)‖` by up to 21×.** The actual `‖U(r)‖` is trivially
cubic (worst 0.04× the cube `(|r|+3)³`) and decomposes cleanly over the **deduplicated** Antimirov
universe `D(r)` — linear count × quadratic per-member opening — **with no pot, no trace, no
multiplicity, no injection.** Bound `‖U(r)‖` directly; rewire the gate bridge to consume it; done.

---

## 1. The objects (all already defined in `active/AntimirovFactoredTransition.thy`)

- `partial_derivative_live_row_universe r` =: **D(r)** — the Antimirov partial-derivative universe
  `{0,1,r} ∪ paths(r) ∪ ∂r ∪ ⋃_{q∈paths} ∂q`. (Python: `drain_rowcount_check.partial_derivative_live_row_universe`.)
- `strong_opened_live_row_universe r` =: **U(r)** `= row_dlformss_set (rsimpStrong_raw ` D(r))`.
  (Python: `drain_rowcount_check.strong_opened_live`.)
- The Gate target: `rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))) ≤ 2(rsize r+3)³`.
- `‖U(r)‖ := rsize_set (U r)`.

## 2. The proved facts we stand on (do NOT reprove)

- **MONO**: gate-rows ⊆ U(r). (The bridge `actual_gate_bridge_from_strong_opened_live_potential`
  @35221 already routes the gate through U(r); its internals contain this inclusion.)
- **L2 (linear count)**: `card (D r) ≤ rsize r + 2`  — `card_apder_rows_clean_le_rsize_plus_2` @37190.
- **MEMQUAD (member size quadratic)**: every `q ∈ D r` has `rsize q ≤ (rsize r + 2)²`
  — `apder_rows_member_size_quadratic` @31364.
- **OPENQUAD (opening quadratic)**: `rsize_set (row_dlforms (rsimpStrong_raw q)) ≤ …quadratic…`
  — `rsize_set_row_dlforms_rsimpStrong_raw_quadratic` @22761. (Check the exact RHS — see L3 below.)
- **U≤pot** (no longer needed, but confirms the model): `rsize_set_strong_opened_live_row_universe_le_potential` @35010.

## 3. THE NEW CHAIN (what to prove)

```
‖U(r)‖ = rsize_set (⋃_{q∈D(r)} row_dlforms (rsimpStrong_raw q))
       ≤ Σ_{q∈D(r)} rsize_set (row_dlforms (rsimpStrong_raw q))     -- L1  (subadditivity)
       ≤ card(D r) · max_{q∈D(r)} rsize_set(row_dlforms(rsimpStrong_raw q))
       ≤ (rsize r + 2) · (rsize r + 2)²                              -- L2 (proved) · L3
       = (rsize r + 2)³  ≤  2(rsize r + 3)³                          -- cube arithmetic
```

### Lemmas to formalize
- **L1 — subadditivity (TRIVIAL, high confidence).**
  `rsize_set (⋃ x∈X. f x) ≤ (Σ x∈X. rsize_set (f x))` for finite `X`. Standard `sum`/`SUP` subadditivity
  of `rsize_set` over a finite union; likely a 1–5 line `sum_mono`/`card`-style lemma or already present.
  Specialise to `X = D r`, `f q = row_dlforms (rsimpStrong_raw q)`.
- **L3 — per-member opening ≤ quadratic-in-ROOT (THE crux, tractable, PROVENANCE-BASED).**
  `q ∈ D r ⟹ apder_clean r ⟹ rsize_set (row_dlforms (rsimpStrong_raw q)) ≤ (rsize r + 2)²`.
  VALIDATED worst **0.31×** (margin ~3×). This is a SINGLE-OBJECT bound (one member; no sum, no trace,
  no multiplicity) — far more tractable than the pot wall.
  - ⚠ **BUDGET ALERT — do NOT prove this via the loose linear composition.** The tempting route
    "opening is linear: `opened(q) ≤ c·rsize q` (validated c≈4.3) AND `rsize q ≤ (rsize r+2)²` (MEMQUAD)"
    gives `opened ≤ ~5·(rsize r+2)²`, and then `card(D)·5(rsize r+2)² > 2(rsize r+3)³` in **26%** of
    cases (numerically verified). The factor-5 linear constant blows the 2× budget. **DEAD sub-route.**
  - ✅ **Required shape:** opening of a *member of `D r`* is ≤ `(rsize r+2)²` directly — must USE that q
    is a partial-derivative member of r (its strong-opened rows live inside r's own finite universe),
    NOT just q's standalone (quadratic) size. Build on MEMQUAD @31364 + the *universe-level* opening
    facts, or relate `row_dlforms(rsimpStrong_raw q)` for `q ∈ D r` back to `U(r)` itself.
  - If even the tight per-member form resists, pivot to the FALLBACK rewrite route (§6) — do NOT
    grind the loose composition.
- **ASSEMBLE — `universe_le_cubic`.**
  `apder_clean r ⟹ rsize_set (strong_opened_live_row_universe r) ≤ 2*(rsize r + 3)^3`. From L1+L2+L3
  (or L1 + linear-opening + `rsize_set(D r) ≤ (rsize r+2)³`) + cube arithmetic `(n+2)³ ≤ 2(n+3)³`.
- **BRIDGE — `actual_gate_from_direct_universe`.**
  Restate `actual_gate_bridge_from_strong_opened_live_potential` @35221 to consume `universe_le_cubic`
  (i.e. `‖U(r)‖ ≤ 2(rsize r+3)³`) DIRECTLY instead of the pot bound. Internally it already has
  gate-rows ⊆ U(r); just feed the direct bound where it currently feeds `‖U‖ ≤ pot ≤ cubic`.

## 4. Validation (reproduce: `python scratch_direct_universe_cubic.py`)

10,092 distinct S-fixed regexes: exhaustive small (rsize ≤ 8), ronepair towers, thesis Fig-7.1 blow-up
`((a*+(aa)*+…)*)*`, witness-family p/k (the ctx_bound/child_ok killers), named CEs, random clean.

| check | result |
|---|---|
| `‖U(r)‖ ≤ 2(|r|+3)³` (HEADLINE) | **0 violations**, worst ratio 0.0406× cube |
| `card(D r) ≤ |r|+2` (L2) | 0 fails |
| member size ≤ `(|r|+2)²` (MEMQUAD) | 0 fails |
| `E_summem = Σ opened` is an UB of `‖U‖` and ≤ budget | 0 not-UB, 0 over-budget, worst 0.041× |
| `card(D)·max-opened` ≤ budget (assembly) | 0 over-budget, worst 0.125× |
| L3: per-member opened ≤ `(|r|+2)²` | worst 0.3625× |
| L3a: per-member opened ≤ `c·rsize(q)` | worst 4.26× (linear, c≈5) |
| `rsize_set(D r) ≤ (|r|+2)³` | worst 0.111× |
| **faithfulness** `‖U‖ ≤ pot` (proved .thy fact) | **0 fails — model OK** |
| pot/‖U‖ (how loose pot is) | up to **21.23×** |

The 21× gap is the whole reason the pot route is stuck: every failed round proved cubicity of a
21×-loose proxy that internally carries the cancellation. `‖U(r)‖` itself has no cancellation to fight.

## 5. Why this is also the thesis's own intended route

PhD thesis (Tan) Ch.7 §7.1.1 **Conjecture 3**: `f(r\_bsimpStrongs s) ⊆ PDER_Σ*(r)` and **Property 9**
(Antimirov, formalised by Wu et al., AFP `Myhill-Nerode`): `‖PDER_Σ*(r)‖ ≤ O(‖r‖³)`. I.e. embed the
strong-simplified derivative into the cubic-bounded partial-derivative universe. `D(r)`/`U(r)` here ARE
that universe; L2 is Property-9's linear count; L3 is the per-term size. The user's `→r'` near-identity
rewrite is the same bridge in rewrite-relation clothing (FALLBACK, §6).

## 6. FALLBACK — the user's `→r'` near-identity REWRITING-RELATION route (the PhD-thesis method)

Use this if the card-linear count (and the per-member L3) both resist. This is the user's own idea,
from the thesis's rewriting-relation method that proved blexer_simp correctness AND the size bound.

### The idea (user, verbatim intent)
Define a NEW rewriting relation `→r'` that does **almost no** simplification — it converts between two
**nearly identical** regexes (the cases where step-wise-strong sometimes MISSES a normalization and
sometimes ADDS an extra one). The two regexes are:
- `r1 = r \_bdersStrong s` — STEP-WISE strongest-simp-with-prune at every derivative step
  (`.thy`: `rders_simpStrong`, base/GeneralRegexBound.thy @18513; strong simp `rsimpStrong_raw` @18365).
- `r2 = bsimpCubic (r \_bders s)` — derive RAW, apply the strongest-simp-with-prune ONCE at the end
  (`.thy`: `rsimpStrong_raw (rders r s)`).
Both already rewrite-relate to the raw derivative `r\s` (the thesis Ch.5 result, proved). The NEW claim:
there is a STRICTER `r1 →r' r2` that changes size by **very little**, so `|rsize r1 − rsize r2| ≤ O(|r|³)`
(or directly transports r2's bound to r1). Likely needs: **`→r'` commutes with derivative AND with the
strongest-simp-with-prune.** Then r2 (once-simplified, controllable via the closed forms) hands its
cubic bound to r1 (the actual algorithm).

### Thesis method to mirror (PhD thesis, Tan, KCL 2023)
- **Ch.5 §5.3.3–5.3.5** — the atomic rewrite `⤳` (rrewrite), small-step, **size-non-increasing**; its
  closure `⤳*`; KEY props: `r ⤳* bsimp r`; **commutes with derivative `r₁ ⤳ r₂ ⟹ r₁\c ⤳* r₂\c`**
  (Lemma 5 / Theorem 4); `a\s ⤳* a\_bsimps s`.
- **Ch.6 §6.3–6.4** — list rewrites `⤳ₕ/⤳_scf/⤳_f/⤳_g`; **closed forms** (Thm 5/6/7) expressing
  `r\_rsimps s` as a single `rsimp(∑ deduped terms)`; then **bounding** the closed forms.
- **Ch.7 §7.1** — `bsimpStrong` = bsimp with `distinctBy`→`distinctWith` (recursive `prune`/CUBICRULE);
  `bdersStrong`; **Conjecture 1** `‖a\_bsimpStrongs s‖ = O(|a|³)`; **Conjecture 3** `f(r\_bsimpStrongs s)
  ⊆ PDER_Σ*(r)`; **Property 9** (Antimirov, AFP `Myhill-Nerode`) `‖PDER_Σ*(r)‖ ≤ O(|r|³)`. The whole
  current row-universe route IS a formalization of Conjecture 3 + Property 9.

### Existing `.thy` substrate to reuse (grep — line numbers may drift)
- `rrewrite`/`srewrite` (inductive `⤳`, size-non-increasing) — base/BlexerSimp.thy @1055.
- `rrewrites`/`srewrites` (closures `⤳*`) — @1076; `srewritescf` (`scf⤳*`) — base/ClosedForms.thy @1063.
- Commutation/preservation: `rder_rsimp_ALTs_commute` (BasicIdentities @504), `rewrites_preserves_bder`
  (BlexerSimp @1526), and the Ch.6 `r ⤳ₕ r' ⟹ r\ᵣc ⤳ₕ* r'\ᵣc` r-regex commutation.
- Closed forms + their size bounds — base/ClosedForms.thy, base/ClosedFormsBounds.thy, base/FBound.thy.
- `rders_simpStrong` (step-wise strong) @18513; `rsimpStrong_raw` (strong-simp-with-prune) @18365.

### Plan
1. Define `→r'` (a near-identity rewrite capturing the step-vs-once discrepancy) in a NEW small theory.
2. **VALIDATE FIRST** on the witness family (`witness_gen.py` + `scratch_direct_universe_cubic.py`): is
   `|rsize r1 − rsize r2|` actually small (≤ cubic with a tame constant)? does `→r'` commute with
   derivative + strong-simp-with-prune empirically? (Iron rule — confirm before formalizing.)
3. Prove `→r'` commutes with derivative and with `rsimpStrong_raw`; prove the size-change bound; transport
   r2's closed-form cubic bound to r1. r2 is the controllable side (closed forms, Ch.6).
This is heavier machinery (whole rewrite system + closed forms) than the row-level count — but it is the
genuinely DIFFERENT method and the thesis's proven template, so it is the right hedge if the count blocks.

## 7. Discipline (unchanged)

No `sorry`/`oops`/`admit` ever. Workers fail-stop + report exact goal state. Single owner per file.
Validate any NEW numeric sub-claim on the witness family (`witness_gen.py` + `scratch_direct_universe_cubic.py`)
BEFORE grinding. New lemmas live in NEW small theories (see lane assignment in STEER.md), not buried in
the 37k-line active file, until the final BRIDGE wiring.
