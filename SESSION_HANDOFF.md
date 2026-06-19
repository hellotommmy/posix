# Session handoff — POSIX cubic-bound proof (Secretary)

**Date:** 2026-06-16. **Branch:** `codex/backref-values`. **HEAD:** `8096f22`. **`active/AntimirovFactoredTransition.thy`: 0 sorry.**
**Read first:** `posix-codex/PROOF_STATE.pdf` (the full, self-contained math state — every symbol defined recursively).

## Your role
Secretary / scavenger coordinating an Isabelle/HOL **cubic size-bound** proof for a POSIX regex lexer. You relay GPT-Pro
design verdicts to workers, but **VALIDATE every design before any worker grinds it** — sample-check at depth≥5 on the
**WITNESS family (NOT random)**, including small M, using the faithful Python model. No `sorry`/`oops`/`admit` ever lands;
workers fail-stop + report; single-owner `.thy` editing; commit small. You do not edit the `.thy` yourself.

## Where the proof stands — formalised modulo the affine envelope
The clean-fragment cubic chain is formalised (no sorry) **modulo ONE hypothesis**: the **affine envelope**
> **`env`: pot(RSTAR r) k ≤ M³ + 3·M²·rsize k**  (all clean star sub-terms, all k; M = rsize(RSTAR r) = 1+rsize r),

carried explicitly by the gate lemma `actual_gate_from_cube_shell` @37552 (comment: "GREEN modulo the single RSTAR affine
envelope"). A **proved-but-UNUSED** certificate `RSTAR_affine_envelope_from_certificate` @37824 (never referenced again in
the file) shows `env ⟸ slope(Σ aB ≤ 3M²) ∧ affine(per-event) ∧ intercept`. The **slope and single-tail affine are
machine-validated but NOT formalised** — no concrete `aB`, no slope lemma, the certificate is never instantiated. Under the
single fixed tail the intercept collapses to the scalar **anchor / charge-cubic**:
> **`(⋆)  pot(RSTAR r)(RCHAR c) ≤ M³ + 3·M²`**  (= env at rsize k = 1, its hardest instance).

(⋆) is **machine-validated TRUE** — 0 violations, *exhaustive* to rsize 9 (≈8.7×10⁵ cases), worst ratio 0.95 at M=2. So
closing the Gate needs: formalise slope + single-tail affine (validated) **and** prove (⋆); the certificate then consumes
them. The genuinely-GREEN parts (conditional on `env`): the cube-shell reduction + non-RSTAR constructor shells + root_cubic
+ gate bridge @35010/@35221/@36275, the trace substrate + `rstar_atrace_sound` @37788, `length_atrace_le_4_rsize` @37884,
and the certificate lemma itself. Full corrected top-down state is in **`PROOF_STATE.pdf`** (read it; ~6 pages, all notation
defined; colour key: [proved] / [validated, not yet formalised] / [OPEN]).

## The wall (why the last lemma resists)
A **global size×multiplicity cancellation**: trace events that open *many* rows have *small* per-row cost; events with
*few* rows have *large* cost (anti-correlated). The true sum is ≈0.5× the budget, but **every structural per-event/
per-node/per-row invariant overshoots 1.2–7×** because it must charge the worst case at every event at once. So **no
rsize/count structural-induction invariant can prove it.** Source: the guarded collapse `a*·a* → a*` (via `S`/`σ₇`),
which lives only in the final strong step. (`PROOF_STATE.pdf` §5 has the data table.)

## DEAD routes — do NOT revisit
- **Per-step budgets are FALSE** (were sampling artifacts): `rsize_set(strong_child_drain) ≤ ctx_bound` (CE 47>46) AND
  `≤ drain_child_budget` / `child_ok` (CE 99>96). The whole `drain`/`ctx_bound`/`child_ok`/`master_cover`/weak-carrier
  family is dead. (Memory: `posix-ctx-bound-target-false-pivot-to-childok`, `childok-baseline-FALSE-checkerA`.)
- **All structural invariants for the charge-cubic overshoot** (cube-shell loose ~7M³ at RSTAR; `R³+3R²K` is *not* an
  envelope — fails small r; affine-in-cont not inductive; per-event-max over-counts; deduped-injection killed by
  multiplicity-18).
- **Pro's "anchored trace / boundary absorption"** (verdict_saturation) is **inert** — the `apush` boundary rule is dead
  code; it re-expresses the anchor without cracking it.

## The promising (untried) direction
An **amortized / potential** argument — the **size analogue of the `T+S` strict-credit invariant that already cracked the
sibling row-COUNT** (the "D law"): GREEN `apder_T_bound` + `apder_S_bound` + `T_and_S` (@37058) ⇒ `D_law_clean` (@37145).
`PROOF_STATE.pdf` §6 states the target: a potential Φ on (root r*, sub-term q, boundary) + a strict size-credit, paying
the per-event size by Φ's drop, telescoping to ≤ M³+3M². **No concrete Φ has been found.** (The Pro round on this,
`pro_ask_potential/verdict_potential.md`, re-converged to the inert anchored trace + an *uninstantiated* Φ template — NOT
a solution.) So the genuine next move is one of:
1. **Build a concrete Φ** (the one untried thing — design + validate on the witness family). Long shot but the right shape.
2. **Definitional rethink** of `pot`/opening so the cancellation becomes a *local* invariant (a structural induction
   would then suffice). May be the honest answer.
3. **Accept (⋆) as a validated lemma** (exhaustive 0/868k) and state the Gate conditional on it.

## File map
- `posix-codex/PROOF_STATE.tex` / `.pdf` — **the math (read first)**; self-contained, every symbol defined recursively.
- `posix-codex/STEER.md` — live orders board; the **tail** has the latest directive (charge-cubic wall, loop stopped).
- `posix-codex/active/AntimirovFactoredTransition.thy` — the proof (HEAD 8096f22). Key green lemmas: cube-shell driver
  @37449; `affine_envelope_imp_cube_shell` @37366; certificate `RSTAR_affine_envelope_from_certificate` @37824; trace
  substrate (aplug/aevt/aevt_cost/atrace/rstar_atrace) @37683–37712; `length_atrace_le_4_rsize` (BRICK1); gate bridge
  @35221; per-row bound `rsize_set_..._le_potential` @35010. D-law T+S precedent @37058/@37145. Static facts:
  `card_apder_rows_clean_le_rsize_plus_2` @37190, `apder_rows_member_size_quadratic` @31364,
  `rsize_set_row_dlforms_rsimpStrong_raw_quadratic` @22761. Build: `powershell -File scripts\codex-isabelle-build-posix.ps1`.
- **Validation model** (reuse VERBATIM): `agent_hunt_pipeline/scripts/{scratch_rowcount_check,drain_rowcount_check}.py`,
  `posix-codex/witness_gen.py`, `posix-codex/scratch_cubeshell_*.py`. Always validate on the witness family + small M.
- Pro rounds: `pro_ask_potential/` (amortized; verdict came back inert), `pro_ask_saturation/`, `pro_ask_A1_intercept/`,
  `pro_ask_RSTAR_body/`. Convention: each Pro ask is a fresh self-contained `pro_ask_<name>/` folder (paste PROMPT.txt +
  attach the listed files; save reply as `verdict_<name>.md`).
- Auto-memory (loads on session start): `posix-cube-shell-bypass-rstar-open`, `posix-ctx-bound-target-false-pivot-to-childok`,
  `childok-baseline-FALSE-checkerA`, `childok-drainbudget-strengthened-inv-refuted`, `verdict8-key-faithfulness-refuted`, …

## Autonomy note (tested this session)
The loop (Workflow fan-outs + background `Agent` workers + Pro-relay) runs **disciplined and safe** — no sorry ever, the
**validation gate catches false greens** (it caught the design panel's confident-but-false bound), bricks get banked,
the problem gets isolated precisely. But it **cannot crack this research-level wall**; that needs a human idea (the Φ) or
a definitional change. Don't expect auto-grinding to close it. (Cross-session `send_message` + transcript-search MCP tools
are blocked in bypass mode; spawn your own subagents via the `Agent` tool for autonomous work.)

## State right now
Nothing running. WORKER-A is HOLDING. Loop STOPPED (structural space exhausted). PROOF_STATE just finished + made fully
self-contained. Awaiting the user's decision on the next move (Φ / definitional / accept).
