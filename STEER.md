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
   before editing so the two lanes don't collide.

---

## THE route — verdict4 context-cover (VALIDATED, implement it)

GPT Pro's verdict4 (`GPT_PRO_GATE_BRIDGE_VERDICT3.md`) replaces the refuted
set-MEMBERSHIP step with a size **cost-cover**: a linear context-slot ledger
`drain_ctxs p` (one slot per `drain_w` unit) whose **declared** cost survives the
`a*·a*→a*` collapse. Keeps `drain_pot`, `drain_w`, and the green §5 arithmetic.

**Secretary has sample-validated ALL of it at depth≥5 — zero violations across
~580k cases, and BOTH old CEs (C-DRAIN-1, C-DRAIN-2) are now covered.** You may go
STRAIGHT to Isabelle; only re-sample if you CHANGE a statement. ⚠ The master cover
is TIGHT on C-DRAIN-2 (slack 0) — the RSTAR/RSEQ arithmetic must be exact, no
rounding-away of constants.

### The 6-lemma stack to implement (verdict4 §5)

Infra (defs): `drain_ctx = rrexp×nat`, `ctx_base`, `ctx_count`,
`ctx_bound Cs k = ctx_base Cs + ctx_count Cs * (1 + rsize k)`,
`raw_plug h k = rsimp7_SEQ_atom h k`,
`ctx_extend q hc = (raw_plug (fst hc) q, snd hc + (1 + rsize q))`  ← DECLARED cost,
NOT `rsize (raw_plug …)`, and `drain_ctxs` (the structural recursion, §1).

1. `drain_ctxs_count_le_w`  : `ctx_count (drain_ctxs p) ≤ drain_w p`     (structural)
2. `drain_ctxs_base_le_pot` : `ctx_base  (drain_ctxs p) ≤ drain_pot p`   (structural)
3. `strong_child_drain_RALTS_ctx_bound`  — the RALTS cost cover           (NEW, crux)
4. `strong_child_drain_RSTAR_ctx_step`   — the RSTAR cost step            (NEW, crux)
5. `strong_child_drain_ctx_bound`  : `rsize_set (strong_child_drain p k) ≤ ctx_bound (drain_ctxs p) k`
   — the master induction on `rsize p` (continuation may grow), dispatching all ctors
6. `strong_child_drain_potential`  : the original target, as a COROLLARY of 1+2+5.
   **Lemma 6 green = the §4 blocker is CLOSED; then §7 `actual_gate_from_current_drain`.**

### Lanes (2026-06-14, post-validation)

- **opus** — own the INFRA defs + the two NEW semantic covers (#3 RALTS, #4 RSTAR).
  Commit the infra defs (`drain_ctxs`, `ctx_*`, `ctx_extend`, `raw_plug`) FIRST so
  Codex can build on them. These two covers are the only genuinely-new design
  content; everything else reuses existing facts.
- **Codex** — own the two STATIC lemmas (#1, #2 — pure structural induction; they
  need only the infra defs, not the covers, so start as soon as opus commits defs),
  the **RSEQ + RCHAR** ctx cases (reuse your green SEQ containment + verdict4 §4's
  exact RSEQ arithmetic), then the master assembly (#5, blocks on opus's #3/#4) and
  the corollary (#6).

## What counts as progress (everything else does NOT)

A GREEN (checked, no sorry) lemma from the 6-stack above, or §7. Lemma 6 green is
the win. A refuted boundary variant, a child_ok-conditional wrapper, or more
arithmetic outside this stack does NOT count.
