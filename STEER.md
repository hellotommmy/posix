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
