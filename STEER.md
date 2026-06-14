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
   before editing so lanes don't collide. Stage ONLY your own hunks (never
   `git add -A`); commit small; push immediately. No `sorry`/`oops`/`admit`.

---

## THE route — verdict4 context-cover (`GPT_PRO_GATE_BRIDGE_VERDICT3.md`, VALIDATED)

Bound the parent drain SIZE by a linear context-slot ledger `drain_ctxs p`, NOT by
set membership. Whole design sample-validated at depth≥5 (zero violations, ~580k
cases; both old CEs covered). Go straight to Isabelle; re-sample only if you CHANGE
a statement.

### Progress (DONE = green, do not redo)
- Infra defs `drain_ctxs` / `ctx_bound` / `ctx_extend` (+ `ctx_*_append`,
  `ctx_*_concat_map`, `ctx_bound_drain_ctxs_RALTS`) — GREEN.
- **#1** `drain_ctxs_count_le_w`, **#2** `drain_ctxs_base_le_pot` — GREEN.
- RCHAR / RSEQ / RZERO / RONE ctx cases — GREEN.

### THE bottleneck (the only remaining content) — lanes
- **WORKER-A → #3 `strong_child_drain_RALTS_ctx_bound`** (the crux; multi-lemma,
  needs sustained context — do NOT attempt cold-then-abandon). The subset pattern is
  a DEAD END (RALTS has no clean child subset — that's the CE `b·c*·c*`). Use the
  pinned reduction: `rsize_set_strong_opened_live_row_universe_acc_RALTS_le`
  (~line 34844) splits the parent into `1 + WRAPPED-ROOT
  row_dlforms(rsimpStrong_raw(rsimp4_SEQ_atom (RALTS rs) k)) + Σ_q children`. The ONE
  new lemma: charge the WRAPPED-ROOT rows to the child ctx ledger (this is where
  `b·c*·c*` is paid by a child CONTEXT, not a child set), bridge acc↔non-acc for the
  nseq-wrapped form, then apply the master IH to the children.
- **WORKER-B → #4 `strong_child_drain_RSTAR_ctx_step`** (independent of #3). Verdict4
  §3: direct star-context step — the escaped re-entry row is charged to a body context
  from `drain_ctxs p` extended by the declared `RSTAR p` suffix
  (`map (ctx_extend (RSTAR p)) (drain_ctxs p)`), plus the one entry slot. Use the size
  fact `rsize(nseq (RSTAR p) k) ≤ rsize p + rsize k + 2`. ⚠ the master cover is TIGHT
  on C-DRAIN-2 (slack 0) — keep the arithmetic exact.
- **ASSEMBLER/WATCHDOG-C** (`/loop`) → when #3 AND #4 are green: **#5**
  `strong_child_drain_ctx_bound` (induction on `rsize p`, dispatch the now-green ctor
  cases) + **#6** `strong_child_drain_potential` (corollary via #1+#2+#5, `nlinarith`),
  then begin §7 `actual_gate_from_current_drain`. Until then: monitor A & B; if either
  stalls >30min (no commit, clean tree), TAKE OVER its lane. Do not attempt #3/#4
  cold as a backup tick — only as a sustained primary.

## What counts as progress (everything else does NOT)
A GREEN lemma from {#3, #4, #5, #6} or §7. **#6 green = the §4 blocker is CLOSED.**
A child_ok-conditional wrapper, the refuted subset pattern, or arithmetic outside
this stack does NOT count.
