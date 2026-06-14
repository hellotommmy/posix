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

## THE blocker (the only thing that closes the gate)

State and DRIVE the master theorem by induction, measure = `rsize p` only
(continuation `k` may grow):

```
rsize_set( strong_child_drain p k )  <=  drain_pot p + drain_w p * (1 + rsize k)
```

It currently has **0 refs** — nobody has written it. This is the SET-level
opened-set telescoping containment (analog of the proved D-law boundary
`#(acc(r,k) - ∂k) <= w(r)`), NOT arithmetic.

## Lanes (2026-06-14)

- **opus / verdict2-§5 agent** — §5 arithmetic is DONE and GREEN; do NOT mine
  for more arithmetic (that is wrapper polish). Take the SET-level discharges
  for **RALTS** and **RSTAR**, then assemble the master induction. RSTAR
  recurses on the smaller body `p` under the larger continuation
  `nseq (RSTAR p) k`; the measure still decreases.

- **Codex** — finish the **RSEQ** middle-boundary SET carrier containment
  `strong_child_drain (RSEQ r1 r2) k  ⊆  strong_child_drain r1 (nseq r2 k) ∪ strong_child_drain r2 k`
  (the telescoping step), plus the **RCHAR** set containment you already
  budgeted. RZERO done.

## What counts as progress (everything else does NOT)

(a) a constructor case of `strong_child_drain_potential` discharged as a SET
containment; (b) the master induction assembled; (c) §7
`actual_gate_from_current_drain`. A new arithmetic lemma, or any lemma
conditional on the unproven `child_ok`, does NOT count.
