# 01 — Adversarial "DO NOT PROVE" list  (Wave 0, Route 2 / N-route)

This is the authoritative list of statements that are **FALSE** (or known-doomed) for
the N-route, each with the minimal counterexample that kills it. Every later wave's
`<lane>-adversarial.md` must re-confirm it has NOT silently re-introduced one of these.
Validation harness: `experiments/norm/norm_model.py` (faithful model of the OLD
Isabelle defs + the NEW α/N/δ_N). Re-run it before trusting any "0 violations".

Convention: `S` = `rsimpStrong_raw`, `σ4` = `rsimp4_SEQ_atom`, `σ7` = `rsimp7_SEQ_atom`,
`N` = `nstrong`, `α`/`nplug` = normalized append, `δ_N`/`ndlforms` = normalized opening,
`dl` = `row_dlforms`, `U(r)` = `apder_strong_dlfrontier r = ⋃_{q∈apder_rows r} dl(S q)`.

---

## DNP-1 — exact containment of old rows into the normalized universe
**DO NOT prove** `U_old(r) ⊆ U_N(r)` or `oldActualRows(r) ⊆ U_N(r)`.
**Killed by** the uncollapsed self-star row. For `r = (1 + b*·a*)·a*` (rsize 9, clean),
`U(r)` contains `x = b*·(a*·a*)` with `x ≠ N(x)` (`N(x) = b*·a*`). Old `S` keeps this
row uncollapsed (σ7 collapses ONLY a *leading* `a*·a*`; here the head is `b*`), so `x`
is NOT N-normal and lies in no set of N-normal forms. [T4 / named CEs CE1–CE4]
**Instead:** an INJECTION `U_old(r) ↪ A_N#(r)` with a provenance index (Wave 5). The
map on rows is the shadow `x ↦ (prov, N x)`, never set containment.

## DNP-2 — the RAW (un-S'd) opening shadow
**DO NOT prove** `x ∈ dl(q) ⟹ N x ∈ δ_N(N q)` (the Wave-2A statement as first written).
**FALSE — 112 / 14211 violations**, smallest `q = 1*·(a+b)` (clean, apder_nf):
`dl(q) = {q}` because the head `1*` is a STAR, not an ALTS, so old `dl`'s
distribution rule `dl(SEQ (ALTS ps) k)` does NOT fire — `q` stays a single unopened
frontier row. But `N(q) = (a+b)` (N unit-collapses the nullable head `1*`), and
`δ_N((a+b)) = {a, b}` (δ_N SPLITS the exposed alternation). So
`N(x) = (a+b) ∉ {a,b}`. A **granularity mismatch**: old `dl` leaves a unit-reducible
non-ALTS head whole; N collapses it and δ_N then splits.
**Instead — USE the S-form** (the carrier's actual form), which is **0 violations** [T5_S]:

> **OPEN-SHADOW (use this):**  `x ∈ dl(S q) ⟹ N x ∈ δ_N(N q)`.

Justification it is sufficient: `U(r) = ⋃_{q∈apder_rows r} dl(S q)` opens `S q`, never
raw `q`; and `N(S q) = N q` (the Wave-4 identity **T7**, 0/8021 exhaustive), so
`δ_N(N(S q)) = δ_N(N q)`. S pre-normalizes away exactly the degenerate `1*·…`/`0*·…`
heads that break the raw form. (This is the route2_verdict §6 fallback, now confirmed
necessary AND sufficient.)

## DNP-3 — a global "+1" at the RALTS / alternation step
**DO NOT** let `δ_N`/`A_N`/the excess set need an additive `+1` per alternation branch.
**Killed historically** by the SAA-RALTS `2n > n+1` trap at two branches sharing a star
tail. The N-route's whole point is that, on N-normalized branches, the RALTS opening is
a clean union with NO debt: `A_N(Σ rᵢ, k) ⊆ ⋃ᵢ A_N(rᵢ, k)`. If a `+1` reappears, the
internal count (Wave 3) goes super-linear — STOP and report.

## DNP-4 — counting the provenance universe via a product
**DO NOT** define `A_N#(r,k) = A_N(r,k) × Π(r)` or tag a row with the old row itself.
A product is **quadratic** (kills the Gate → quartic) and self-tagging is tautological /
uncountable. The tag must be a finite recursive **debt set** indexed by constructor
*occurrences* (each `nat` bound to a list index / occurrence), charged to `rsize r`,
so `|A_N#(r,k)| ≤ C·rsize r + D`. [kill-criteria §14.5–6]

## DNP-5 — Ω(n²) tags on the shared-tail alternation family
**DO NOT** let the provenance map produce `Ω(n²)` tags on
`q_i = b_i*·a*,  r_n = (q_1+⋯+q_n)·a*`. Each old fiber `{R_i = b_i*·a*, P_i = b_i*·(a*·a*)}`
collapses to `R_i` under N; the two pre-images must get DISTINCT tags `(π₁,R_i)`,`(π₂,R_i)`
with the **total** tag count `O(n)`, not `O(n²)`. This family is the Wave-5 gate. [§14.6]

## DNP-6 — opening the opaque lexer internals on the main line
**DO NOT** unfold `afactored1` / `rpder_strong_rows_raw`. They appear only in the GREEN
black-box `actual_gate_from_direct_universe_rowlevel`. If the main line needs them,
switch to the backup route (§12), do not grind. [§14.8]

---

## Kill-criterion #1 verdict (nstrong_rsimp4_shadow) — NATURAL, NOT killed
Target: `N(σ4(r,k)) = α(N r, N k)` (`nstrong_rsimp4_shadow`).
**Hand-proof (induction on the σ4 recursion / on r):**
- `r ∈ {0,1}`: `σ4(0,k)=0`, `α(0,·)=0` (0 absorbs); `σ4(1,k)=k`, `α(1,N k)=N k` for
  N-normal `N k` (units stripped by `norm_seq`). ✓
- `r` a leaf (CHAR/ALTS/STAR), `k∉{0,1}`: `σ4(r,k)=RSEQ r k`, so
  `N(σ4(r,k)) = N(RSEQ r k) = α(N r, N k)` **definitionally**. `k∈{0,1}` are the unit
  laws above. Note α does NOT distribute the ALTS head (it is a spine factor) — matching
  σ4, which also keeps `(ALTS rs)·k` whole. ✓  [the §5 third hand-value, T1]
- `r = RSEQ r₁ r₂`: `σ4` left-flattens, `σ4(RSEQ r₁ r₂, k) = σ4(r₁, σ4(r₂,k))`. By IH
  twice, `N(σ4(r,k)) = α(N r₁, α(N r₂, N k))`, while
  `α(N r, N k) = α(α(N r₁,N r₂), N k)`. Equal **iff α is associative** (`nplug_assoc`).
**The lone load-bearing sub-step is `nplug_assoc`** (the star-fold boundary). Prove it
FIRST at the list level (`norm_seq_append_assoc`, `norm_seq_idem`) — Wave 1A.
**Adversarial probes (all gave equality):** `a·(a*·a*)`, `a*·a*`, `(b*+c*)·a*` [T1];
`a*·(a*·b)`, `(a*·a*)·a*`, `0*·c`, and α-assoc stress `α(α(a*,1),a*)`, `α(α(a*,b),a*)`,
`[a*,a*,a*]` runs.
**Python confirmation (NOT a substitute):** `N(σ4(r,k))=α(N r,N k)` **0 / 80210**
exhaustive (clean r≤rsize7 × 10 curated k incl. `b*·b*`); `nplug_assoc` **0 / 5 268 024**
on N-normal triples; `N idem` 0/8021; `N∘S=N` 0/8021. [T2,T3,T6,T7]
**Verdict: GREEN to formalize** (Wave 1). The crux it leans on is α-associativity.

## ⚠ Standing methodology caveat for ALL later waves
Every "0 violations" above is **exhaustive only to rsize 7** (T2/T5) / N-normal rsize 5
(T3). These are NOT conclusive for the *witness families* (nested-SEQ chains opened at
`star*`, deep tails) that historically hid CEs at rate ~1e-6 under random sampling. Any
wave that FORMALIZES the shadow / the count MUST re-run the relevant check at larger
size AND on the named families (CE2/CE4/deep-tail) before grinding. A hand-proof is
required per `pro_ask_PREAMBLE.txt`; a green Python run alone is a RED FLAG.
