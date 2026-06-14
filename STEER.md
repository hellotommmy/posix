# STEER — live orders board (read this BEFORE every proof step)

This file is the single current directive for each agent. It is SHORT on
purpose so you can re-read it every turn. The Secretary edits it in place; it
always reflects the latest orders. If a directive here conflicts with your
current plan, **this file wins** — switch immediately. Rationale and history
live in `PROGRESS_BACKREF.md`; this file is only "what to do right now."

Self-sync protocol (every agent, every turn):
1. `git pull --rebase --autostash` in `posix-codex`.
2. Re-read THIS file (and the PROGRESS tail if you need context).
3. Obey the order for your lane below. Claim the constructor you take in
   PROGRESS before editing so the two lanes don't collide.

---

## THE goal (unchanged) — and what just changed

Master theorem (still believed TRUE — 300k samples, zero violations; measure =
`rsize p` only, continuation `k` may grow):

```
rsize_set( strong_child_drain p k )  <=  drain_pot p + drain_w p * (1 + rsize k)
```

**The per-child SET-containment route to it is now CHECKED-FALSE for RALTS and
RSTAR** (independently verified by the secretary against the real Isabelle
defs — NOT a model bug). Mechanism: `rsimp7_SEQ_atom` has a guarded rule
`(RSTAR r, RSTAR s) ⇒ if r=s then RSTAR r` (BasicIdentities.thy:414) that
collapses `a*·a* → a*` in a child, while `rsimp4_SEQ_atom` keeps it — so the
parent opened row holds a bigger form that no child drain contains. SEQ/CHAR
are unaffected (reassociation is sound). A proof EXISTS; it is **not** via
per-child telescoping. This is a GPT Pro design pass (in preparation).

## Lanes (2026-06-14, post-verification)

- **opus / ALTS-STAR agent** — DO NOT keep grinding the refuted per-child
  containments or boundary variants. Both readings are now characterized:
  the row_dlforms boundary is FALSE for RSTAR; the full-universe boundary
  (`strong_opened_live(nseq …) − strong_opened_live(S k)`) makes the inclusion
  HOLD but RALTS has **zero budget slack** (`open_pot`/`apder_zw2` of RALTS are
  *exactly* Σ over children — no constructor term to pay the boundary). The
  ALTS/STAR *account* is blocked pending the GPT Pro corrected design.
  REAL interim work (non-wrapper, non-colliding): bank the TRUE unconditional
  full-universe inclusions as standalone SET lemmas (no `child_ok` hypothesis) —
  `strong_opened_live(nseq (RALTS rs) k) ⊆ strong_opened_live(S k) ∪ ⋃_q strong_opened_live(nseq q k)`
  and the RSTAR analogue — since any corrected design will reuse them; the budget
  question (how to pay) is GPT Pro's. Sample at depth ≥ 5 first. If you cannot
  state a TRUE unconditional lemma, HOLD — do not produce conditional wrappers.

- **Codex** — UNAFFECTED, keep going: the SEQ/CHAR lane is sound. Finish the
  **RSEQ** middle-boundary SET containment
  `strong_child_drain (RSEQ r1 r2) k ⊆ strong_child_drain r1 (nseq r2 k) ∪ strong_child_drain r2 k`
  (reassociation telescopes cleanly), plus the **RCHAR** containment (green).
  These are reusable regardless of which ALTS/STAR design wins. RZERO done.

## What counts as progress (everything else does NOT)

(a) a constructor case of `strong_child_drain_potential` discharged as a SET
containment **for SEQ/CHAR** (ALTS/STAR await the corrected design); (b) a TRUE
unconditional ALTS/STAR set fact the design will reuse; (c) §7
`actual_gate_from_current_drain`. A new arithmetic lemma, a refuted boundary
variant, or any lemma conditional on the unproven `child_ok`, does NOT count.
