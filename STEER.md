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
  **GREEN: `master_cover_RZERO`, `master_cover_RONE`, `master_cover_RCHAR`** (line ~35873-35922;
  RCHAR is the pattern to mirror — `assumes rsimpStrong_raw k = k`, opens via
  `rsimp4_SEQ_atom`, absorbs the RONE boundary into SOL k).
- OPEN cases: `master_cover_RALTS`, `master_cover_RSEQ`, `master_cover_RSTAR`. The old
  additive acc-split (line 34844) is BOXED — do NOT use it.

### Lanes (post-unification)
- **WORKER-A** — owns `master_cover_RALTS` (its current claim — the hard case) +
  `master_cover_RSEQ` + the top-level `master_cover` induction driver that combines the
  cases + the final `strong_child_drain_potential` corollary.
- **WORKER-B** — owns **`master_cover_RSTAR`** (the RSTAR case; B's #4 area, now framed as
  the RSTAR case of the unified cover). Mirror `master_cover_RCHAR` (line 35905): state it
  in the same `…acc (RSTAR p) k ⊆ … ∪ strong_opened_live_row_universe k` shape, with an
  EXPLICIT induction-hypothesis assumption for the body `p` (the case is inductive, not a
  base case — see verdict5 §6: the star ENTRY slot + the recursive body under
  `nseq (RSTAR p) k`). Keep the `rsimpStrong_raw k = k` guard (caveat 2). This is
  INDEPENDENT of A's RALTS/RSEQ (it recurses on the body via the IH), so B can START NOW.
  CLAIM `master_cover_RSTAR` in PROGRESS before editing.
- **WATCHDOG-C** (`/loop`) — when `master_cover_RALTS/RSEQ/RSTAR` are all green: ensure the
  top-level `master_cover` induction + `strong_child_drain_potential` corollary are assembled
  (if A hasn't), then §7 `actual_gate_from_current_drain`. Until then: MONITOR + watchdog A.

### Dependencies — BLOCKED ≠ STALLED (watchdog: do not misfire)
- WORKER-A (`master_cover_RALTS`/RSEQ + driver) is the CRITICAL PATH and ACTIVE.
- WORKER-B (`master_cover_RSTAR`) is now UN-BLOCKED and independent of A's cases — start it.
  It is its OWN lemma; claim it so A doesn't also take RSTAR.
- C must NOT take over a case a live worker is committing; assembly (#6/§7) is BLOCKED until
  all three open cases are green.

## What counts as progress (everything else does NOT)
A GREEN `master_cover_<CTOR>` case (RALTS/RSEQ/RSTAR), the assembled `master_cover`
induction, the `strong_child_drain_potential` corollary, or §7. **The corollary green =
the §4 blocker is CLOSED.** The boxed acc-split (line 34844), the refuted per-child subset,
or a child_ok-conditional wrapper do NOT count.
