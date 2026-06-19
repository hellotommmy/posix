# STEER — live orders board (read this BEFORE every proof step)

This file is the single current directive for each agent. It is SHORT on
purpose so you can re-read it every turn. The Secretary edits it in place; it
always reflects the latest orders. If a directive here conflicts with your
current plan, **this file wins** — switch immediately. Rationale and history
live in `PROGRESS_BACKREF.md`; this file is only "what to do right now."

Self-sync protocol (every agent, every turn):
1. `git pull --rebase --autostash` in `posix-codex`.
2. Re-read THIS file (and the PROGRESS tail if you need context).
3. Obey the order for your lane below. Claim the lemma you take in PROGRESS
   before editing so lanes don't collide. Stage ONLY your own hunks; commit small,
   push immediately. No `sorry`/`oops`/`admit`.

---

# 🔴🔴 CONCURRENCY NOTICE (2026-06-17) — YOU ARE ONE OF 4 PARALLEL AGENTS. READ BEFORE EDITING.

**Four agents run CONCURRENTLY right now. You are one of them.**
- **A / B / C** (3 agents) all prove the SAME single remaining lemma
  `card_apder_strong_dlfrontier_le` : `card (apder_strong_dlfrontier r) ≤ Suc (rsize r)`, each from a
  DIFFERENT angle (A = D-law transfer @37145/@37058; B = diff-card telescope @5541+; C = structural
  induction on the frontier). Three of you targeting one lemma is DELIBERATE — first GREEN proof wins.
- **D** — the `→r'` rewriting-relation route (independent fallback; see `DIRECT_UNIVERSE_CUBIC_ROUTE.md` §6).

**ANTI-COLLISION (mandatory):**
1. **The green brick ALREADY EXISTS** in `cubic/DirectUniverseCubic.thy` — the Gate is proven modulo
   EXACTLY this one card lemma (8 lemmas, 0 sorry: `universe_le_cubic_rowlevel`,
   `actual_gate_from_direct_universe_rowlevel`, `per_row_size_le_quadratic`, `budget_suc_quad_le_cube`,
   `card_times_quadratic_le_cube`, …). **DO NOT reprove ANY of it.** Only APPEND the card lemma + the
   `cubic_gate_unconditional` corollary (see `FINISH_HERE.md`).
2. **Stay on YOUR OWN branch.** Do NOT all push to `codex/backref-values`. Open a separate PR / report
   your proof-text. The human + Secretary integrate the winner — you do NOT merge into the shared branch.
3. Never touch another lemma; never add `sorry`/`oops`/`admit`. Once your build is green WITH the card
   lemma, STOP and report — do not keep grinding alternatives.
4. **If your checkout lacks `cubic/DirectUniverseCubic.thy` or `FINISH_HERE.md`, you are on a STALE base.**
   `origin/codex/backref-values` now carries the green brick + `cubic/` + `ROOT` (session `Posix_Cubic`)
   + the route docs. Rebase onto it before working. Build your lane: `-Session Posix_Cubic`.
5. **⚠ SHARED WORKING TREE — this is happening RIGHT NOW.** Several of you are editing the SAME physical
   `cubic/DirectUniverseCubic.thy` in ONE tree and clobbering each other ("the lemma changed under me /
   was weakened to a more natural form" = another agent overwrote you). Git branches do NOT isolate you
   when the working directory is shared. HARD RULE from now on:
   - **The 8 green-brick lemmas are LOCKED and CONFIRMED INTACT** (`cube_plus2_le_two_cube_plus3`,
     `card_times_quadratic_le_cube`, `universe_le_cubic`, `actual_gate_from_direct_universe`,
     `budget_suc_quad_le_cube`, `per_row_size_le_quadratic`, `universe_le_cubic_rowlevel`,
     `actual_gate_from_direct_universe_rowlevel`). NEVER delete or modify them. APPEND ONLY.
   - **Only ONE agent (the CARD-lane owner) may edit `cubic/DirectUniverseCubic.thy`.** Every OTHER
     card-angle agent: prove your attempt in YOUR OWN new file `cubic/CardAttempt_<B|C>.thy` (own
     `theory`, own `Posix_CardX` session in ROOT) — or just REPORT your proof-text and STOP touching the
     shared file. The D-lane is already correctly isolated in `rewrite/RewriteFallback.thy`.
   - Target remains ONLY: `card_apder_strong_dlfrontier_le` (`card (apder_strong_dlfrontier r) ≤ Suc
     (rsize r)`) + `cubic_gate_unconditional` (the discharge in `FINISH_HERE.md`).

---

# ⭐⭐ CURRENT ROUTE (2026-06-17) — DIRECT-UNIVERSE CUBIC. This banner SUPERSEDES every dated section below.

**READ THIS FIRST, EVERY TURN. If you just came out of a compaction/summary: your objective is in THIS
banner, not in any older section, memory, or half-remembered problem. The whole `pot` programme is
PAUSED.**

**The pivot (validated 0 violations / 10,092 regexes incl. all known killers — see
`DIRECT_UNIVERSE_CUBIC_ROUTE.md`):** the Gate's real target is `‖U(r)‖ =
rsize_set(strong_opened_live_row_universe r)`. It is DIRECTLY cubic (worst 0.04× the cube). `pot`
over-approximates it by **up to 21×** — that 21× is the entire reason the old anchor resisted. So we
bound `‖U(r)‖` directly via the Antimirov decomposition and rewire the bridge. NO pot, NO trace, NO
multiplicity, NO injection.

**STATUS (2026-06-17 night):** GREEN BRICK landed — `cubic/DirectUniverseCubic.thy` proves the GATE
`actual_gate_from_direct_universe` modulo ONE hypothesis, building over the deduped Antimirov rows
`apder_strong_dlfrontier r = (⋃ q∈apder_rows r. row_dlforms (rsimpStrong_raw q))` (card `apder_rows`
linear @37190; gate-rows inclusion @19490; L1 = `rsize_set_UN_le` @537). The **PER-MEMBER** L3
(`opened(q) ≤ (|r|+2)²` for q∈apder_rows) is BLOCKED — composes to quartic (same cancellation, per-member).

**UPDATE (2026-06-17, Secretary landed directly — subagents were hitting transient API 500s):** the
row-level assembly is GREEN in `cubic/DirectUniverseCubic.thy` — `per_row_size_le_quadratic`,
`universe_le_cubic_rowlevel`, `actual_gate_from_direct_universe_rowlevel` (+ `budget_suc_quad_le_cube`)
all build (0 sorry). **The ENTIRE GATE is now proven modulo ONE count bound:**
`card (apder_strong_dlfrontier r) ≤ Suc (rsize r)`. That is the ONLY remaining open lemma. Discharge it
→ `actual_gate_from_direct_universe_rowlevel[OF clean <card>]` is the unconditional cubic Gate.

**LIVE ROUTE = ROW-LEVEL (avoids the cancellation; validated 0/6174):** bound `rsize_set` by
**COUNT × PER-ROW-SIZE**, each separately bounded:
`rsize_set(apder_strong_dlfrontier r) = Σ_{x} rsize x ≤ card(apder_strong_dlfrontier r)·(|r|+2)²
≤ (|r|+1)·(|r|+2)² ≤ 2(|r|+3)³`, via
(i) **PER-ROW** `x∈apder_strong_dlfrontier r ⟹ rsize x ≤ (|r|+2)²` — EASY: `row_dlforms_member_size_le_rsize`
@5902 + `apder_rows_member_size_quadratic` @31364; and
(ii) **CARD-LINEAR** `card(apder_strong_dlfrontier r) ≤ |r|+1` — the crux, but it is a COUNT, and the
linear ROW COUNT was already cracked (D-law `D_law_clean` @37145, `apder_T_bound`/`apder_S_bound` @37058).
This makes `universe_le_cubic` UNCONDITIONAL → the Gate closes with NO open lemma.

**⛔ DEAD — DO NOT WORK ON ANY OF THESE (they are the old fixation traps):** `pot(r*,char c) ≤ M³+3M²`
(the charge-cubic anchor); the affine envelope / cube-shell / RSTAR cube-shell; the amortised potential
Φ / `aA1` intercept; `ctx_bound`; `child_ok`; `drain_child_budget`; `master_cover`; the weak carrier.
If the lemma you are about to touch is in this list, or mentions `pot`/`potential`/`cube_shell`/`aevt`/
`atrace` as the THING TO BOUND, **STOP** — you have drifted to a dead target.

**LANES (fast leaf session `Posix_Cubic` in `cubic/`, ~10s rebuilds, loads the Antimirov heap; build a
lane with `scripts\codex-isabelle-build-posix.ps1 -Session Posix_Cubic`. Both theories share this
session — KEEP YOUR FILE GREEN AT ALL TIMES or you break the other lane's build):**
- **WORKER-CODEX** owns `cubic/DirectUniverseCubic_L3.thy` — ONLY lemma **L3** `member_opened_quadratic`
  (per-member opening ≤ `(rsize r+2)^2`, TIGHT/provenance — see budget trap). Prompt:
  `WORKER_CODEX_PROMPT.md`. Claim L3 in PROGRESS.
- **WORKER-OPUS** owns `cubic/DirectUniverseCubic.thy` — **L1** (subadditivity) + **ASSEMBLE**
  `universe_le_cubic` (carry L3 as `assumes`) + **BRIDGE** `actual_gate_from_direct_universe`. Bridge is
  EASY: monotonicity @35179 + `rsize_set_mono` @403 + `finite_strong_opened_live_row_universe` @33059
  (simp). Prompt: `WORKER_OPUS_PROMPT.md`. Land L1 + the conditional assembly + bridge first (green with
  L3 as hypothesis), discharge once Codex lands L3.
- **SECRETARY** validates every NEW numeric sub-claim on the witness family before you grind it; ask.

**SELF-CHECK before any edit (anti-drift):** post one line in PROGRESS answering: (1) my lane's CURRENT
objective per this banner; (2) the exact lemma name I will edit; (3) confirm it is NOT in the DEAD list.
If you cannot, re-read this banner. No `sorry`/`oops`/`admit` ever. Fail-stop + report exact goal state.

---

## ✅ RESUME (2026-06-14) — build modularization LANDED & GREEN (~104s → ~28-40s)
RESUME your lanes below. ONE-TIME setup, each agent:
1. `git pull --rebase --autostash` (you'll receive the file moves).
2. The active file MOVED (identical content): now `active/AntimirovFactoredTransition.thy`
   and `active/AntimirovNormalFrontier.thy`. The 11 frozen theories are now in `base/`.
3. **Build the SAME command** — `scripts\codex-isabelle-build-posix.ps1` (no args) now
   targets the fast `Posix_Antimirov` leaf, loading the frozen base from its heap image:
   **~28-40s instead of ~104s.** (jEdit/PIDE: open the new `active/…` path, session
   `Posix_Antimirov` — auto-loads the `Posix_Base` heap.) You do NOT rebuild the base; if
   ever needed: `scripts\codex-isabelle-build-posix.ps1 -Session Posix_Base` (rare).
A: continue `master_cover_RALTS`. RSEQ is GREEN (Codex) and RSTAR is GREEN (B). Then the
`master_cover` driver + `strong_child_drain_potential` corollary + §7. Resume now.

---

### 🟢 BYPASS FOUND (2026-06-16) — gate reduces (ALL GREEN, no sorry) to the CUBE-SHELL invariant. One open step: RSTAR. child_ok/drain ABANDONED.
**The whole per-step budget detour (ctx_bound, child_ok, drain) was unnecessary.** The gate already has a SECOND,
green route in the file: `actual_gate_bridge_from_strong_opened_live_potential` (@35221) + the per-row bound
`rsize_set_strong_opened_live_row_universe_le_potential` (@35010, proven) reduce the gate to ONE inequality
`strong_opened_live_acc_potential r RONE ≤ 2·(rsize r+3)³`, which reduces to the **cube-shell invariant**
`strong_opened_live_acc_potential r k ≤ (rsize r + rsize k)³ − (rsize k)³`. Leaves (RONE @33332, RCHAR @33860) GREEN;
RALTS (@33665) + RSEQ (@33928) cube-shell steps GREEN (telescoping difference-of-cubes — composes additively, unlike
the dead quadratic budget). **Cube-shell is TRUE: Secretary-validated 0 violations / 90k+ depth≥5 incl. the EXACT
child_ok killers (pot 431 ≤ shell 13816 on the rsize-22 CE where strong 99 > dcb 96) AND worst-case RSTAR star-re-entry
inflation.** THE ONE OPEN PIECE: the **unconditional RSTAR cube-shell step** + the assembling induction driver. The
team's existing RSTAR escapes (`_RSTAR_root_cubic_if_body_plus_root` @33409, `_if_child_drain`) route through the
now-FALSE child_ok — DEAD. The real RSTAR obligation: `potential r (RSTAR r) ≤ ~2·(rsize(RSTAR r)+3)³` (star body
opened against its OWN star). Naive cube-shell IH is too loose (~7m³ vs needed ~2m³) because the re-entry continuation
doubles the body contribution; needs a DIRECT saturation argument (the body-against-its-own-star opening is bounded by
the star's own universe, not the IH product). **DE-RISKED (Secretary, see `RSTAR_CUBE_SHELL_SKETCH.md`):** RSTAR
cube-shell decomposes (0-viol/15059) into HEAD (≤ top shell layer — EASY, direct analogue of GREEN
`strong_opened_live_acc_RALTS_root_shell_large` @33427) + **SAT** `pot r (r*·k) ≤ (rsize r+rsize k)³−(rsize k)³` (the
saturation; TRUE 0/15k, ratio max 0.806). **SHARPENED (2026-06-16, secretary): `pot(RSTAR r, k)` is EXACTLY AFFINE
in `rsize k`** (0 non-affine/437 incl. witness chains; the `r*` prefix linearizes the continuation — that IS the
saturation), so `pot(RSTAR r,k)=A(r)+B(r)·rsize k` and the RSTAR cube-shell splits into TWO SCALAR bounds +
cube-arithmetic: **ROOT** `A(r) ≤ M³` and **SLOPE** `B(r) ≤ 3M²` (M=rsize(RSTAR r); both 0-viol/437, slope margin
0.52). Then `A+B·n ≤ M³+3M²n ≤ (M+n)³−n³` closes it for ALL k. SLOPE is the easy half (continuation enters linearly);
**ROOT** `pot(RSTAR r, RONE) ≤ M³` (≡ `pot r (r*) ≤ M³−M` via `_RSTAR_RONE_linear_split` @33391) is the lone scalar
core — route via the static star-universe facts (@37190 linear count, @31364 quadratic size). Full plan +
refinement in `RSTAR_CUBE_SHELL_SKETCH.md`. **GO (2026-06-16): GPT Pro returned `gpt_pro_bundle/verdict_root.md`; the
Secretary VALIDATED it** — trace soundness 0/949, affine envelope `pot(RSTAR r)k ≤ M³+3M²·rsize k` 0-viol, scalar
bounds A≤M³ & B≤3M² 0/437. Pro's strategy = a tagged `pot_trace` mirroring the potential + the affine envelope +
two scalar lemmas (`trace_A≤M³` via static facts, `trace_B≤3M²` via k-at-tail) → RSTAR cube-shell. **⚠ CAVEAT
(validation): Pro's unrestricted self-star absorption lemma is FALSE (483/508); it holds ONLY for r*-prefixed k, and
the body never contains the anchor r* anyway — so use k-at-TAIL linearity (slope) + static star-universe finiteness
(intercept), NOT r*·r* absorption.** **WORKER-A: GO — formalize per `WORKER_A_RSTAR_PROMPT.md` (land the safe
skeleton first: pot_trace+soundness → envelope→cube-shell arithmetic + driver wiring + HEAD; THEN the two scalar
lemmas = the crux). Claim lemmas in PROGRESS. Ask Secretary to validate any new numeric sub-claim on the witness
family before grinding it. Do NOT touch child_ok/drain or the unrestricted absorption.**
**⛔ SINGLE OWNER — the active `.thy` RSTAR/cube-shell work belongs to WORKER-A ONLY. If you are the earlier overnight
GATE-ASSEMBLY lane (`master_cover_RALTS` / `child_ok` / the `master_cover` driver / the `strong_child_drain_potential`
corollary / §7): ⛔ STOP NOW. Your target is FALSE — `child_ok` was refuted (CE 99>96, commit 4d8ca75), so that whole
chain CANNOT close and Isabelle will never prove it. Do NOT edit `active/AntimirovFactoredTransition.thy` (you will
collide with WORKER-A). Post one line in PROGRESS and halt; await re-tasking.**

### 📐 SECRETARY → WORKER-A: validation answers to your fail-stop asks (2026-06-16). Skeleton GREEN — excellent. Crux = the envelope.
You correctly caught the small-M gap. Validated on the witness family across **ALL M (incl 2,3,4)**:
- ✅ **USE — Q3 HEAD brick (kills the K²):** `opn(rsimp4_SEQ_atom (RSTAR r) k) ≤ 2·M + 2·M·rsize k` (0-viol all M; M=rsize(RSTAR r)). Linear in rsize k, explicit constants — land it.
- ✅ **USE — all-M-safe anchor:** `pot (RSTAR r) RONE ≤ M³ + 3·M²` (0-viol all M). Use THIS, not `M³` or `M³−M`.
- ✅ The envelope `pot(RSTAR r) k ≤ M³ + 3·M²·rsize k` holds 0-viol ALL M (target is solid).
- ❌ **DO NOT use (all FAIL at M=2):** `pot r (RSTAR r) ≤ M³−M` (9>6); the additive HEAD-complement split `BODY ≤ M³−2M+(3M²−2M)·rsize k` (15>12); old SAT `pot r (r*·k) ≤ (rsize r+rsize k)³−(rsize k)³` (9>7). The per-piece additive split does NOT partition cleanly at small M (HEAD sits below its bound there, so BODY exceeds its complement).
- ❌ SLOPE-relative-to-`pot ... RONE` FAILS: `pot(RSTAR r) k` depends on k's **structure**, not just rsize k (same-size RONE→11 vs C('a')→19), so RONE is the min-pot anchor and the relative-slope overflows.
- **Remaining crux = BODY `pot r (rsimp4_SEQ_atom (RSTAR r) k)`** (the saturation). Needs a UNIFIED argument (not additive split) OR explicit small-M (M≤4) base cases + the large-M engine (k-at-tail linearity + static star-universe cubic). **This BODY lemma is going to GPT Pro as a focused micro-ask in parallel** (`gpt_pro_bundle/0_PROMPT_FOR_GPT_PRO_BODY.txt`). MEANWHILE: land the HEAD brick + the ROOT-at-RONE anchor (both validated), keep the skeleton green; do not grind the additive split (it's false at small M).

### ✅ GO (2026-06-16): Pro `verdict_body` VALIDATED VIABLE — WORKER-A formalize the size-1-anchored affine certificate
GPT Pro returned the BODY strategy (`pro_ask_RSTAR_body/verdict_body.md`); the Secretary VALIDATED it (workflow + own
re-run). It AVOIDS the dead routes: a **size-1-anchored affine trace certificate** `pot(RSTAR r)k ≤ A1(r)+B(r)·(rsize k−1)`
with `A1(r) ≤ M³+3M²`, `B(r) ≤ 3M²` (a hole-aware A1 = symbolic upper bound over ALL size-1 tails, so the RONE-vs-RCHAR
structure dependence can't break it; B counts the right-hole occurrence weight, no k² since the body never re-creates the
root anchor). Numeric necessary conditions hold with **0 violations, EXHAUSTIVELY at small M** (every S-fixed star, body
rsize≤8 = 50,583 roots; ENV 0/3.45M): A1*(r)=max over size-1 tails ≤ M³+3M² all M; ENV holds; tight-anchor CORE holds too.
- ⚠ **ONE FORMALIZATION CAVEAT (knife-edge):** the binding case is `r=a*` at **M=2**: `A1*=19 ≤ M³+3M²=20`, slack EXACTLY 1.
  **Use the LOOSE intercept `A1(r)=M³+3M²` (and `B=3M²`) in the lemma statement**, NOT the concrete `A1*` — then the M=2
  margin is automatic from `1 ≤ rsize k` and you avoid the slack-1 arithmetic. (M=3 is structurally VACUOUS — spectrum
  jumps 2→4 — so NO small-M base cases are needed.)
- **WORKER-A: GO.** Formalize per `verdict_body.md` §"实施顺序" — the 8 patches: `aplug` → `aevt/aevt_cost/atrace/rstar_atrace`
  → `rstar_atrace_sound` (specialise the GREEN `pot_trace_sound`) → `aevt_tail_affine_size1` (hole-aware tail-linearity,
  the K²-killer) → `rstar_atrace_A1_bound` (≤ M³+3M², charge trace events to the static star universe via @37190/@31364/
  @22761 — tagged/list, NOT the wrong-direction set≤pot @34905) → `rstar_atrace_B_bound` (≤ 3M², the slope) →
  `strong_opened_live_acc_potential_RSTAR_affine_envelope`. Then reuse the GREEN `…_RSTAR_cube_shell`/driver/root/bridge —
  **gate closes.** Claim lemmas in PROGRESS; ask Secretary to validate any NEW numeric sub-claim (esp. the tail-affine
  constants) on the witness family before grinding. The two real lemmas are A1_bound (intercept) and B_bound (slope).

---

### 🛑 (superseded by the BYPASS above) BOTH per-step budgets FALSE (2026-06-16) — ctx_bound AND child_ok refuted.
**The "one numeric bound" we ground on for 9 routes — `rsize_set(strong_child_drain p k) ≤ ctx_bound(drain_ctxs p) k`
— is FALSE in-regime.** CE2 (Secretary-reproduced, S-fixed, nf, depth≥5): `p = 1+((1+((1+a)·a)+((c+1)·(c+1)))·c*)`,
`k = c*` → `rsize_set(strong)=47 > ctx_bound=46`. CE1: `p=(((((a+1)·b)+1)·((1+a)·(c·b*)))+c)`, `k=b*` → `64 > 60`.
The "machine-validated TRUE, 0-viol >10^5" was a **SAMPLING ARTIFACT**: real violation rate ~1/1.2M, so every
20k–40k gate missed it. **All 9 prior refutations were proving a FALSE lemma — that is why every one died.**
- ⭐ ctx_bound is NOT NEEDED. The gate wrapper `actual_gate_from_current_drain` (@36253) needs only
  `rsize_set(strong_opened_live_row_universes …) ≤ 2(rsize r+3)³`, scaffolded by **`child_ok`** (@32389):
  `∀k∈regime. rsize_set(strong_child_drain p k) ≤ drain_child_budget p k` — the **LOOSER** bound, which is what
  feeds cubicity (`drain_child_budget_root_cubic` @32651). `ctx_bound` was only a believed-tighter stepping stone
  (prove `≤ ctx_bound`, chain `ctx_bound_le_drain_child_budget` @32663 to `child_ok`). The stepping stone is false;
  **drop it.** There is no `strong_child_drain_ctx_bound` lemma — nothing consumes the tight bound.
- ⭐ `child_ok` is TRUE (holds on both CEs with slack 47≤60, 64≤74; 0/1.2M). Its proof = **master_cover** (set cover,
  RZERO/RONE/RCHAR/RSEQ/RSTAR GREEN, only **RALTS** open) **+ drain_child_budget superadditivity** (RSEQ GREEN:
  `strong_child_drain_RSEQ_budget_sum_le` @32882). The RALTS cover gap (parent re-exposes `b·(a*·a*)` no child
  strong has) is FIXED by verdict8's `plug_drain` companion (impl-B: `parent_strong ⊆ ⋃ child (strong∪plug)`,
  0-fail/13511). The looser `drain_child_budget` has the slack (≈13 on CE2) that `ctx_bound` lacked.
RE-VALIDATION RESULT (2026-06-16): **`child_ok` is ALSO FALSE.** `rsize_set(strong_child_drain p k) ≤
drain_child_budget p k` fails in-regime. Secretary-verified CE (S-fixed, nf, depth 6):
`p = (((((a+1)·b)+1)·((((a+1)·b)+1)·(a·b*)))+c)`, `k = b*` → `rsize_set(strong)=99 > drain_child_budget=96`. The
"0/1.2M" that supported child_ok was the SAME sampling artifact that hid the ctx_bound CE: `rand_clean` never builds
the killer structure — nested `SEQ(ALTS[pre,1], … SEQ(atom, star*))` opened at `k=star*`, which re-doubles
`star*→star*·star*` each frame, stacking uncollapsed S-shadow rows multiplicatively. A witness-biased generator finds
it at 2.7–9.5%. drain_child_budget (= drain_pot + drain_w·(1+rsize k)) is only ~QUADRATIC; the overshoot grows
QUADRATICALLY with chain depth, so NO constant / fixed multiplier / minimal companion / cubic-safe correction closes
it (all tested, all fail). **BUT** `rsize_set(strong_child_drain) ≤ (rsize p+3)³` holds directly with huge slack
(99 ≪ 15625) — strong IS cubic; the per-step BUDGET is the broken link.
- ⛔ Both ctx_bound (tight) and drain_child_budget (loose) per-step budgets are refuted. This is an ARCHITECTURE
  decision, escalated to the user. **A + ALL agents: HOLD. Do NOT start any Isabelle proof of `child_ok` or any
  per-step budget bound. Do NOT fire Pro until the architect picks the new frame.**
- ⚠ METHODOLOGY FIX (mandatory): every future validation gate MUST include the witness-family generator
  (`witness_family()` in `scratch_childok_drainbudget_A.py`) targeting the nested-SEQ-chain-opened-at-star* structure,
  NOT just `rand_clean`. Two "validated TRUE" claims were sampling artifacts of this exact blind spot.
  ✅ NOW ENFORCED IN CODE (2026-06-16, secretary): canonical shared guard `witness_gen.py`
  (re-exports the witness family + the 3 named CEs + `mixed_samples`/`gate_report` + a
  `confirm_named_ces()` regression check). The `cand3` G2 gate is rewired to it as a FALSITY
  DETECTOR (must find violations; 0 ⇒ sampler blind ⇒ abort) and no longer prints "all gates
  GREEN" off a `rand_clean` blind spot. Named-CE repro: `python scratch_ctxbound_target_FALSE_repro.py`
  (CE2 47>46, CE1 64>60, CHILDOK 99>96). New gates: `from witness_gen import gate_report, mixed_samples`.

---

## THE route — verdict5 weak-carrier (`GPT_PRO_GATE_BRIDGE_VERDICT4.md`, VALIDATED — implement it)

#3/#4 are UN-GATED. GPT Pro verdict5 gives the proof skeleton: a proof-only WEAK
carrier + an INJECTIVE indexed-slot charge, proven by MUTUAL induction over P (strong
cover) and Q (weak cover). Each parent drain row gets its own PAID slot — no boxed
`1+root` split. Sample-validated at depth≥5 (~660k checks, 0 in-fragment violations;
both CEs covered). Go straight to Isabelle; re-sample only if you change a statement.

### ⚠ TWO CAVEATS (validation-found — get these right or it breaks)
1. The WEAK acc must be S-FREE and use the non-collapsing `rsimp4` plug:
   `weak_child_drain p k = (⋃ (h,_)∈drain_ctxs p. row_dlforms (rsimp4_SEQ_atom h k)) − row_dlforms k`.
   Do NOT apply `rsimpStrong_raw` (S) inside the weak opening — S collapses `a*·a*→a*`
   and the duplicate row breaks the injective slot charge (measured: 4 in-fragment CEs).
   (§4's W3 inclusion keeps S on its LHS wrapped-root — that's the strong side and is
   fine; only the weak DEFINITION's acc must be S-free.)
2. Guards must include `S p = p` and `S k = k` (strong-normal fixpoint), NOT just
   `rtail_nf`/`nf` — `nf` accepts nested stars on which the inclusions fail. Keep
   verdict5's `norm`/`norm_k`. Also keep W3's LHS subtraction `strong_opened_live (S k)`
   (bigger set) — do not weaken it to `row_dlforms k`.

### Progress so far (GREEN — do not redo) — 2026-06-14, A's actual structure
- Weak carrier infra + `weak_child_drain` (S-FREE) + `weak_child_drain_ctx_bound` — GREEN.
- **A found #3/#4/#5 are ONE mutual induction (★).** It is being proved as per-constructor
  SET-INCLUSION lemmas named `master_cover_<CTOR>`:
    `strong_opened_live_row_universe_acc (CTOR …) k ⊆ [opened rows of CTOR] ∪ strong_opened_live_row_universe k`
  **GREEN: `master_cover_RZERO`, `master_cover_RONE`, `master_cover_RCHAR`,
  `master_cover_RSEQ`, `master_cover_RSTAR`** (RCHAR is the leaf pattern;
  RSEQ telescopes by `rsimp4_SEQ_atom`; RSTAR uses the explicit body IH).
- OPEN cases: `master_cover_RALTS`. The old
  additive acc-split (line 34844) is BOXED — do NOT use it.

### Lanes (post-unification) — RALTS + ASSEMBLY are A-EXCLUSIVE
- **WORKER-A (being re-engaged)** — owns the WHOLE remaining chain EXCLUSIVELY:
  `master_cover_RALTS` (the hard case) → the top-level `master_cover` induction driver →
  the `strong_child_drain_potential` corollary → §7 `actual_gate_from_current_drain` bound.
  A claims `master_cover_RALTS` in PROGRESS the moment it resumes.
- **WORKER-B / WORKER-Codex** — DONE (RSTAR / RSEQ). ⛔ Do NOT take `master_cover_RALTS`,
  the driver, the corollary, or the §7 bound — those are A's, even while A is idle. If you
  have self-synced and have nothing in your lane: HOLD (post one line in PROGRESS and stop).
  The remaining chain is SEQUENTIAL (RALTS→driver→corollary→§7) and single-owner, so a
  second agent on it would only collide.
- **WATCHDOG-C** (`/loop`) — MONITOR only. Take over A's lane ONLY if A is genuinely stalled
  >30 min mid-RALTS (a live worker, no commit) — and if so, FIRST claim `master_cover_RALTS`
  in PROGRESS so it doesn't collide with A re-engaging.

### Dependencies — BLOCKED ≠ STALLED (watchdog: do not misfire)
- WORKER-A (`master_cover_RALTS` + the whole assembly) is the SOLE remaining critical path.
- No other agent works RALTS or the assembly (collision). assembly is BLOCKED until
  `master_cover_RALTS` is green; everything else is DONE.

## What counts as progress (everything else does NOT)
A GREEN `master_cover_RALTS`, the assembled `master_cover`
induction, the `strong_child_drain_potential` corollary, or §7. **The corollary green =
the §4 blocker is CLOSED.** The boxed acc-split (line 34844), the refuted per-child subset,
or a child_ok-conditional wrapper do NOT count.

### 📍 A1 INTERCEPT is the LONE open lemma (2026-06-16). substrate/assembly/SLOPE GREEN. → Pro micro-ask out.
WORKER-A landed (GREEN, no sorry): the size-1 trace substrate (aplug/aevt/atrace/rstar_atrace + soundness),
driver/root/gate→apder_clean env, the envelope assembly `RSTAR_affine_envelope_from_certificate` (@37824), AND the
SLOPE half `aB` (count = #rows+#frontier, Σ≤3M², per-event valid). The ONLY thing left to close the WHOLE gate:
construct `aA1 :: aevt→nat` with (i) per-event `aevt_cost r k e ≤ aA1 e + aB e·(rsize k−1)` AND (ii) `Σ aA1 ≤ M³+3M²`
(relaxed (M+1)³−1 also suffices). Genuine cancellation nut: FOUR routes refuted (cost-at-RONE breaks (i); per-event
max over-counts (ii); Pro's deduped-apder_rows injection — multiplicity 14×; Secretary's per-row mult·size≤quad — 13/728
at large M). Secretary prepared `pro_ask_A1_intercept/` (self-contained Pro micro-ask). **WORKER-A: HOLD on A1 pending
verdict_a1 (Secretary validates first); substrate/assembly/slope are already GREEN — keep them so, do NOT grind a
refuted A1 route.** Loop: monitor only.

### ✅ A1 RESOLVED at design level (2026-06-16) — single-tail anchor; multiplicity nut DISSOLVED. Secretary autonomous worker owns A1 tonight; WORKER-A HOLD.
Pro's verdict_a1 no-go does NOT apply: it rested on a Secretary prompt error ("per-event max over-counts past M^3+3M^2").
Secretary RE-VALIDATED: Σ(per-event size-1 max) ≤ M^3+3M^2 (0/724, ratio 0.535) — within budget. So the GREEN per-event
assembly `RSTAR_affine_envelope_from_certificate` (@37824) STANDS; do NOT restructure to a sum-level interface.
**Corrected A1 design (full certificate validated 0/575, ALL M incl small):** set `aA1 e = aevt_cost r (RCHAR c) e`
for a FIXED char c (a single size-1 tail — it DOMINATES all size-1 tails per event, 442/442). Then:
- (i) per-event affine holds (size-1: RCHAR dominates → `aevt_cost r k e ≤ aA1 e`; |k|>1: A's slope aB covers it). 0-viol.
- (ii) `Σ aA1 = pot(RSTAR r)(RCHAR c)` BY `rstar_atrace_sound` (sum of one tail's cost over the trace = pot at that tail —
  NO multiplicity, NO ledger), then `pot(RSTAR r)(RCHAR c) ≤ M^3+3M^2` (0/442) — a SINGLE-ANCHOR cubic bound, like the
  validated RONE anchor; route via static star-universe facts (@37190 lin count, @31364 quad size, @22761 quad opening).
- (iii) `Σ aB ≤ 3M^2` — A's already-solved slope.
Plug (i)(ii)(iii) into @37824 → envelope → cube_shell → root → bridge → **GATE CLOSES.** Two real obligations remain:
the RCHAR-dominates-size-1 tail-monotonicity, and the single anchor `pot(RSTAR r)(RCHAR c) ≤ M^3+3M^2`.
**WORKER-A: HOLD A1 tonight (do not edit the .thy) — the Secretary is running a bounded autonomous worker on it to test
the overnight loop. If that worker stalls, A resumes in the morning with this design.**

### ⚠ DESIGN-PANEL false green CAUGHT (2026-06-16). Saturation STILL uncracked. Autonomous loop bounded-STOPPED.
The in-house invariant design panel "converged" on f(r,cont)=R^3+3R^2K (R=rsize r,K=rsize cont) claiming E=0 envelope.
**Secretary re-verification REFUTED it: 14245 envelope violations + 19993/38857 SAT violations** — f's R^3 intercept is
too small at SMALL r (a char has pot~6 > f=4); the panel agents likely tested only star-bodies, not all subterms.
f DOES telescope RSEQ (0/4804) and is tight at RSTAR, but it is NOT a true envelope, so it's dead. The real bracket
stands: intercept big enough for the small-r envelope vs small enough for RSTAR tightness — no rsize-only f is both
AND inductive (the cont-inflation sigma(RSTAR r)cont / sigma r2 cont defeats every tight rsize-only envelope; the
saturation is a SEPARATE induction on pot, not an f-step). The body-against-its-own-star SATURATION remains uncracked
by 8+ Pro verdicts + the autoworker + the design panel. **Autonomous loop STOPPED (bounded: 2 iterations). Next = a
sharp external Pro round on the saturation, or human insight — NOT more auto-grinding. WORKER-A: continue HOLD; the
gate stays GREEN-modulo the RSTAR saturation.** Substrate/assembly/slope + single-tail aA1 (multiplicity dissolved)
all stand; the lone wall is obligation B's body term.

### ✅ verdict_saturation VALIDATED VIABLE (2026-06-16) — anchored-trace; boundary absorption is DEAD CODE. Worker mobilized.
Secretary validated Pro's anchored-trace (workflow whalug4yw + cross-impl + EXHAUSTIVE enum to rsize 9, 868k cases):
V1 push-sound=0, V2=0, V3=0. TWO de-risking findings: (1) **V2 is an EQUALITY** pot(RSTAR r)(RCHAR c) =
sum_list(map (acost r (RCHAR c)) (rstar_atraceS r)) — trace soundness is a STRUCTURAL IDENTITY (each pot clause ↔
atraceS clause). (2) the apush BOUNDARY rule (S x = RSTAR r → AHere) is **provably DEAD CODE**: atraceS only pushes
SUBTERMS of the body, so rsize(S x) ≤ rsize(x) < rsize(RSTAR r); the branch never fires. Discharge it as UNREACHABLE via
a subterm-size lemma — NOT the false global self-star absorption (that was verdict_root's refuted trap; here the local
rule is provably inert). So the astack machinery is inert and the REAL remaining content = the CHARGE-CUBIC
`sum_list(map (acost r (RCHAR c)) (rstar_atraceS r)) ≤ M³+3M²` (validated 0/868k), proved by charging the (linear-many)
trace events to the cubic static star-universe (apder_rows(RSTAR r): @37190 linear count × @31364 quad size × @22761
quad opening). **Secretary autonomous worker mobilized to formalize. WORKER-A: continue HOLD.** Likely path: land V2
(identity) + boundary-unreachable + scaffold green, then the charge-cubic is the lone Isabelle lemma — clean if
#events×quadratic ≤ cubic works, else fail-stop on the exact charge-cubic goal (the multiplicity-aware tagged charge).

### 🧱 charge-cubic = the IRREDUCIBLE wall (2026-06-16). Structural-induction space EXHAUSTED. Autonomous loop STOPPED.
Formalize-worker fail-stopped (commit 332d66d): build GREEN, no sorry. BANKED **BRICK1** `length_atrace_le_4_rsize`
(length(atrace q xs) ≤ 4·rsize q — the LINEAR event-count factor, telescopes, tight). CORRECTION: Pro's
verdict_saturation `astack/apush/atraceS` machinery was NEVER committed (grep of all history finds none); the EXISTING
`aplug`/`atrace` substrate already IS the anchored trace and has NO boundary branch — so Pro's "boundary absorption"
added nothing (it was inert, as validated). The lone open goal is still `pot(RSTAR r)(RCHAR c) ≤ M³+3M²`
(= `sum_list(map (aevt_cost r (RCHAR c)) (rstar_atrace r)) ≤ M³+3M²`). The worker probed it with 15 scripts: anchor TRUE
(ratio ~0.5) but **EVERY structural charge OVERSHOOTS** — crude product 1.5×, saturated per-event cap × 4·rsize ~4M³,
tight body invariant doesn't ALTS-telescope, deduped-union cubic but multiplicity-18 kills the injection, generic quad
7×. Diagnosis (sharpest yet): a **GLOBAL CANCELLATION** (events with many rows have small cost; events with few rows
have large cost) that **NO rsize/count structural-induction invariant captures**. This wall has now defeated 8+ Pro
verdicts + 3 worker attempts + the design panel. **Autonomous loop STOPPED — structural induction is exhausted; the next
move needs a NEW PROOF TECHNIQUE (an amortized/POTENTIAL argument for the size cancellation — analogous to how the
D-law's telescoping invariant cracked the row-COUNT — or a rethink of the pot/opening DEFINITIONS), NOT more
auto-grinding.** WORKER-A: HOLD. Gate stays GREEN-modulo this one anchor; all bricks (substrate/assembly/slope/single-
tail/BRICK1) stand.
