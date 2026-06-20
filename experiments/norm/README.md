# experiments/norm — Wave-0 faithful regression model (Route 2 / N-route)

`norm_model.py` is a **regression model, not a proof**. It implements the OLD Isabelle
definitions verbatim (`σ4`, `σ7`, `rsimpStrong_raw` incl. the cross-row prune,
`row_dlforms`, `apder_*`) and the NEW ones (`α`/`nplug`, `N`/`nstrong`, `δ_N`/`ndlforms`),
then runs the named counterexamples and small-size EXHAUSTIVE checks.

    python norm_model.py

Tests:
- **T1** three hand-computed `N` values (kill-criterion #1 anchors)
- **T2** `nstrong_rsimp4_shadow`: `N(σ4 r k) = α(N r, N k)`  (KILL-CRIT #1)
- **T3** `nplug_assoc` (α associativity — the lone fragile sub-step of T2)
- **T4** old `U(r)` carries uncollapsed `s*·s*` rows ⇒ exact containment FALSE (→ shadow)
- **T5** opening shadow: RAW form FALSE (DNP-2), **S-form** `x∈dl(S q)⟹N x∈δ_N(N q)` holds
- **T6** `N` idempotent
- **T7** `N(S r) = N r` (Wave-4 identity; connects S-form shadow to the target)

Current result (rsize ≤ 7, alphabet {a,b}): T1,T2,T3,T4,T6,T7 PASS; T5_S PASS; T5_raw
FAIL (expected — see `docs/norm-route/01-adversarial.md` DNP-2).

**⚠ These "0 violations" are exhaustive only to small size.** Before any wave FORMALIZES
the shadow or the count, re-run the relevant check at larger size AND on the witness
families (CE2/CE4/deep-tail). A green run alone is a RED FLAG, never a green light
(`pro_ask_PREAMBLE.txt`).
