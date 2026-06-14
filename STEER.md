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

### Progress so far (GREEN — do not redo)
Infra `drain_ctxs`/`ctx_bound`/`ctx_extend`; static #1 `drain_ctxs_count_le_w`, #2
`drain_ctxs_base_le_pot`; RCHAR/RSEQ/RZERO/RONE ctx cases. The old additive acc-split
(line 34844) is BOXED — do NOT use it for #3.

### Lanes
- **WORKER-A** — the weak carrier + #3. Commit FIRST (so B can build): the infra
  (`wseq`, `weak_child_drain` [S-FREE acc per caveat 1], `slot_cost`, `ctx_bound_as_slots`,
  `alt_off`/`alt_slot`/`alt_slot_lt`/`nth_alt_slot`), then the CORE
  `weak_child_drain_charge` (injective slot charge, induction on `rsize p`, all ctor
  cases incl. the RALTS/RSEQ/RSTAR decomps in verdict5 §3) and its corollary
  `weak_child_drain_ctx_bound`. Then #3: `strong_child_drain_RALTS_to_weak_children`,
  `RALTS_wrapped_root_into_weak_slots`, `strong_child_drain_RALTS_ctx_bound` (verdict5 §4-5).
- **WORKER-B** — #4 RSTAR (verdict5 §6-7), after A commits the weak infra + `weak_child_drain_ctx_bound`:
  `star_entry_drain` def, `strong_child_drain_RSTAR_to_entry_weak_body`,
  `star_entry_drain_cost` (singleton/linear — NOT the generic quadratic row bound),
  `strong_child_drain_RSTAR_ctx_step`. ⚠ master cover is TIGHT on C-DRAIN-2 (slack 0).
- **WATCHDOG-C** (`/loop`) — when #3 AND #4 are green: **#5** `strong_child_drain_ctx_bound`
  as the MUTUAL P/Q induction (verdict5 §8: `P p ≡ ∀k. strong … ≤ ctx_bound`,
  `Q p ≡ ∀k. weak … ≤ ctx_bound`; #3 uses Q on RALTS children, #4 uses Q on the RSTAR
  body), then **#6** `strong_child_drain_potential` (corollary via #1+#2+#5), then §7
  `actual_gate_from_current_drain`. Until then: MONITOR + watchdog the critical path (A).

### Dependencies — BLOCKED ≠ STALLED (watchdog: do not misfire)
- WORKER-A (weak carrier + #3) is the CRITICAL PATH and is ACTIVE. Only A's lane is
  takeover-eligible, and only if A goes silent >30 min (no commit, clean tree, no live
  worker) mid-lemma.
- WORKER-B (#4) is **BLOCKED on A committing the weak infra + `weak_child_drain_ctx_bound`**,
  by design — it is NOT stalled. WATCHDOG-C must NOT take over #4 while it is blocked.
  Once A commits the weak infra, B becomes active/eligible.
- #5/#6/§7 are **BLOCKED on #3 AND #4** — not workable yet. Do not attempt early.

## What counts as progress (everything else does NOT)
A GREEN lemma from the verdict5 stack (weak charge / weak ctx_bound / #3 / #4 / #5 / #6)
or §7. **#6 green = the §4 blocker is CLOSED.** The boxed acc-split, the refuted subset,
or a child_ok-conditional wrapper do NOT count.
