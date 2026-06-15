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

### 🛑 GATE ASSEMBLY — the whole CARRIER CLASS is refuted (impossibility proven). A: HOLD. Pro V2 sharpened.
The §1 gate reduces (GREEN wrapper) to ONE numeric bound
`rsize_set(strong_child_drain p k) ≤ ctx_bound(drain_ctxs p) k` — machine-validated TRUE (0-viol, >10^5
depth≥5 cases). But EIGHT structural proof routes are now depth≥5-REFUTED, all on the guarded `a*·a*→a*`
collapse: per-child set-containment (master_cover, doesn't compose); recursive `scover`; injective
slot-origin via `collapses_to` (97/40849) + the two-route variant (24/52851, Hall collision); total-size
`strong≤weak` (strong CAN exceed weak, 36>29); non-injective aggregate (COVER fails 4/128541); pure
numeric induction (RALTS step 94/13837); S-rownorm the opening (UNSOUND — gate needs the un-normed drain).
- ⭐ IMPOSSIBILITY SQUARE (proven, 43707 cases): NO slot-derived carrier can sit between the strong total
  and ctx_bound. **The entire carrier / opened-row-membership / cover CLASS is dead — stop searching there.**
- ⭐ DIAGNOSIS: `strong_child_drain` mixes S-collapsed short rows + uncollapsed long rows; no injective
  row→slot charge exists (total budget covers, but slots are overloaded/underused).
THE ONE REMAINING SEED (Pro V2, now sharpened): charge each S-collapsed row to the **SOURCE STAR SLOT**
that produced the `a*·a*`, relating `rsimpStrong`'s collapse to a slot-cost **DECREASE** — NOT opened-row
membership. ACTION: fire GPT Pro V2 (`gpt_pro_bundle/0_PROMPT_FOR_GPT_PRO_ASSEMBLY_V2.txt`, updated with all
8 refutations + the impossibility square + this seed). **A + all agents: HOLD the §4 assembly — do NOT
invent another carrier/cover/charge. You MAY land the validated-safe bricks (absorbed-B1, guard-decomps,
L-SEQ/L-STAR lifts, ctx ledger).** Refutations in memory: `posix-scover-cover-refuted`,
`verdict6-tworoute-refuted`, `posix-cand3-numeric-induction-ralts-refuted`.

### ⏳ verdict7 — node→cost-token "budgeted collapse trace" (validating, 2026-06-15)
GPT Pro verdict7 (`gpt_pro_bundle/verdict7.md`): charge at the SYNTAX-NODE → COST-TOKEN level (not rows→slots),
so the collapsed row + its uncollapsed predecessor consume DISJOINT atoms (ordinary slot + source-star/collapse
slot) — dissolving the Hall collision. First idea of the right SHAPE (total-budget, divisible). Secretary is
validating it as a max-flow feasibility (does the divisible node→atom charge saturate at depth≥5, esp RALTS/CE-Hall).
**HOLD until validated.** If VIABLE → executor implements it; if the flow is infeasible → a Pro micro-ask. See
worked CEs in `FAILED_ROUTES_WORKED.pdf`.

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
