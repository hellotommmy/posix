# Restart Handoff Prompts (paste one per fresh agent)

All agents share ONE worktree `C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`
on branch `codex/backref-values`, and coordinate through the `PROGRESS_BACKREF.md`
tail. Paste the matching block into each fresh CLI. Keep them short on purpose —
the charter does the heavy lifting.

For THIS cycle use the THREE prompts in the next section (verdict4 context-cover,
implementation phase). Everything below that is SUPERSEDED but kept for reference.

---

## CURRENT-CYCLE PROMPTS (2026-06-14, verdict4 context-cover — IMPLEMENTATION)

State: the verdict4 context-cover route is VALIDATED (depth≥5, zero violations).
Infra defs + static lemmas #1/#2 + RCHAR/RSEQ/RZERO/RONE ctx cases are GREEN. The
ONLY remaining content is **#3 RALTS cover** + **#4 RSTAR cover** (the two crux
semantic lemmas), then the mechanical **#5 master** + **#6 corollary** + **§7 gate**.

Pipeline: 3 agents, ALL in `C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`
on branch `codex/backref-values`, shared `AntimirovFactoredTransition.thy`, coordinating
via `STEER.md` self-sync + `PROGRESS_BACKREF.md` claims. Recommend all three be
Claude Code / Opus 4.8 (Codex GPT-5.5 stalled repeatedly last cycle). Common entry
chain (every agent, first thing): `STEER.md` → `MAINLINE.md` §1-2 →
`GPT_PRO_GATE_BRIDGE_VERDICT3.md` (the design; §2=RALTS, §3=RSTAR, §5=the 6-lemma
stack) → last ~150 lines of `PROGRESS_BACKREF.md` →
`agent_hunt_pipeline/projects/posix-backref/CLAUDE.md` (binding rules). Never
bulk-read history; trust git timestamps. No `sorry`/`oops`/`admit`; stage ONLY your
own hunks; `git pull --rebase --autostash` before every push; commit small, push
immediately. The design is pre-validated — go straight to Isabelle; re-sample
(reuse `scratch_drain_ctxs_master_check.py`) ONLY if you change a statement.

### PROMPT A — WORKER-A (#3 RALTS cover) — GATED on the GPT Pro micro-ask

⚠ DO NOT START until the GPT Pro cover-proof skeleton lands (see PROGRESS / STEER).
The two obvious reductions are both DEAD: (1) per-child SUBSET (RALTS has no clean
child subset — CE `b·c*·c*`); (2) the additive acc-split via
`rsize_set_strong_opened_live_row_universe_acc_RALTS_le` (line 34844) is BOXED —
measured 0/60000 close, deficit always `1+root` (subadditive on top of full child
ledgers). When the skeleton lands, this prompt will carry it. The RIGHT shape:
inject each parent drain ROW into a child CONTEXT SLOT and bound its `rsize` by the
slot's declared cost (`b·c*·c*` rsize 7 ≤ slot `(b·c*,4)` extended = `4+(1+2)=7`),
NOT a bulk `rsize_set` split. Deliverable: `strong_child_drain_RALTS_ctx_bound`
GREEN, no `sorry`; claim in PROGRESS before editing.

### PROMPT B — WORKER-B (#4 RSTAR cover) — ALSO GATED on the GPT Pro micro-ask

⚠ DO NOT START until the skeleton lands. #4's analog split lemma (line 34825) is the
SAME subadditive shape as #3's boxed one, so #4 is at the same risk — the micro-ask
covers BOTH RALTS and RSTAR cover proofs. When the skeleton lands, this prompt will
carry it. Deliverable: prove `strong_child_drain_RSTAR_ctx_step` (verdict4 §3 / stack
item #4) GREEN, no `sorry`; claim in PROGRESS before editing. Independent of #3. Route (verdict4 §3): the
direct star-context step — the escaped re-entry row is charged to a body context from
`drain_ctxs p` extended by the declared `RSTAR p` suffix
(`map (ctx_extend (RSTAR p)) (drain_ctxs p)`), plus the single entry slot
`(RSTAR p, rsize (RSTAR p))`. Target:
`rsize_set(strong_child_drain (RSTAR p) k) ≤ rsize(RSTAR p) + (1+rsize k) +
ctx_bound(drain_ctxs p)(nseq (RSTAR p) k)`, using the size fact
`rsize(nseq (RSTAR p) k) ≤ rsize p + rsize k + 2`. ⚠ the master cover is TIGHT on
C-DRAIN-2 (slack 0) — keep the arithmetic exact, do not round away constants. When
green, record it in PROGRESS and update STEER.

### PROMPT C — ASSEMBLER + WATCHDOG (`/loop`, e.g. every 20-30 min)

You are the assembler/watchdog on the POSIX cubic-bound project. Repo + entry chain:
see above. Run on `/loop`. EACH tick: `git pull --rebase --autostash`, read STEER +
PROGRESS tail, check whether `strong_child_drain_RALTS_ctx_bound` (#3) and
`strong_child_drain_RSTAR_ctx_step` (#4) are both GREEN.
- If BOTH green: prove **#5** `strong_child_drain_ctx_bound` (induction on `rsize p`,
  dispatching the now-green per-constructor ctx cases) and **#6**
  `strong_child_drain_potential` (corollary via #1 `drain_ctxs_count_le_w` + #2
  `drain_ctxs_base_le_pot` + #5; `nlinarith` after unfolding `ctx_bound`). #6 green =
  the §4 blocker is CLOSED — then begin §7 `actual_gate_from_current_drain`.
- If NOT both green: check WORKER-A and WORKER-B for stalls. If a lane has had NO
  commit for >30 min with a clean tree, TAKE OVER that lane (claim it in PROGRESS,
  using A's or B's route above). Do NOT attempt #3/#4 as a quick backup tick if a
  worker is actively committing — only take over a genuinely stalled lane.
Build to verify green: `scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300`.

---

## SUPERSEDED — CURRENT-CYCLE PROMPT (2026-06-14 12:00): execute verdict #2 — the drain potential

The D law and the cubic static front are PROVEN. Both original-root carriers
(opened-boundary + liveness) are checked-FALSE. GPT Pro's corrected design is
`GPT_PRO_GATE_BRIDGE_VERDICT2.md` — the continuation-parametric drain potential
over the CURRENT normalized rows. Two agents work it (lane split below): a NEW
agent on the core (PROMPT V3), the EXISTING Codex on the wrappers/bridge.

### PROMPT V3 — NEW agent (verdict2 core: defs + child invariant + arithmetic)

You are joining the POSIX cubic-bound project as a proof worker. Repo:
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, branch
`codex/backref-values`. ABSORB FIRST: `MAINLINE.md` §1-2, then
`GPT_PRO_GATE_BRIDGE_VERDICT2.md` (the design you execute — read it fully), then
the last 120 lines of `PROGRESS_BACKREF.md` (the 2026-06-14 verdict #2 broadcast
+ the other agent's claims — do NOT duplicate its lemmas). Symbol defs:
`STATUS_MATH.pdf`. Never bulk-read history. Trust git timestamps, not PROGRESS
labels. The D law is PROVEN — do not touch it. Both original-root carriers are
CHECKED-FALSE — do not re-attempt them.

GOAL: land verdict2 SECTIONS 1-5 — the continuation-parametric child invariant
that closes the gate. Carrier over the CURRENT normalized rows
(`S = rsimpStrong_raw`); measure = `rsize p` only; continuation `k` may grow
(incl. the star re-entry `nseq (RSTAR p) k`). The singleton-ALT CE is harmless
because the induction root is `S p`.

EXECUTION ORDER:
0. SAMPLE-CHECK FIRST at depth>=5 (extend `scratch_rowcount_check.py`): the child
   invariant `rsize_set(strong_child_drain p k) <= drain_pot p + drain_w p*(1+rsize k)`
   and the cubic `drain_pot r <= rsize r*(rsize r+2)^2`. Tune constants if needed
   (verdict shows positive slack everywhere, so it should sample clean). A deep CE
   => record in SUPER_LINEAR_PATTERNS.md + flag the admin. Do NOT skip this.
1. CLAIM in the PROGRESS tail, then DEFINE (verdict §1-2): `nseq`,
   `strong_child_drain`, `drain_pot`, `drain_child_budget`, `child_ok`. These are
   the shared interface the other agent's wrappers consume — define them first.
2. `rsize_nseq_le` and `rsize_nseq_star_le` (verdict §3 — syntactic size
   non-increase; NOT rowwise S-monotonicity, which is checked-false).
3. The recursive `strong_child_drain_potential` (verdict §4): constructor
   discharges RZERO/RONE (=∅), RCHAR (+1 slack), RALTS (additive child budget,
   subadditivity), RSEQ (+Wp slack, middle-boundary cancellation), RSTAR (+W+2
   slack, body under `nseq (RSTAR p) k`). Measure on `rsize p` only.
4. The cubic arithmetic (verdict §5): `drain_pot_le_cubic_core`,
   `drain_child_budget_root_cubic`.

DISCIPLINE: ONE build at a time (`scripts\codex-proof-workers.ps1 -Action Check`
first; lock shared). Red build = read the first failing goal, change ONE named
lemma, never relaunch on an unchanged goal; fail twice the same way -> switch
sub-target. NEVER force/weaken/sorry; run the four guards before pushing; stage
ONLY your own files (NEVER `git add -A` — the other agent has in-flight edits in
the same file). Commit small + push immediately; `pull --rebase --autostash`.
Report each CHECKED result as a math inequality + a <=10-word plain gloss. Claim
each def/lemma in PROGRESS before editing it. Do NOT touch the wrapper/bridge
lemmas (verdict §6-7) — those are the existing Codex agent's lane.

(The existing Codex agent: keep working your wrappers, but adapt them to consume
`child_ok` per verdict §6 and wire `actual_gate_from_current_drain` §7 once the
new agent's defs/child theorem land. Claim your lemmas in PROGRESS.)

---

## SUPERSEDED — overnight opened-boundary PROMPT N (carrier route checked-false 2026-06-14)

The opened-boundary carrier route below is machine-checked false (both original-root
carriers). Use PROMPT V3 above (the drain potential, verdict #2). Kept for reference.

### (old) overnight PROMPT N — opened-boundary route
The 2026-06-13 ASSEMBLY prompts (A3/B3) are superseded by this gap.

### PROMPT N — overnight lead (execute the opened-boundary design)

You are running OVERNIGHT, unattended, on the POSIX cubic-bound project. Repo:
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, branch
`codex/backref-values`. ABSORB FIRST: `MAINLINE.md` §1-2, then
`GPT_PRO_GATE_BRIDGE_VERDICT.md` (the design to execute), then
`GATE_BRIDGE_GAP.md` (the precise gap) and the last 100 lines of
`PROGRESS_BACKREF.md`. Symbol definitions: `STATUS_MATH.pdf`. Never bulk-read
history. Trust git timestamps, not PROGRESS labels. The D law is already PROVEN
(`D_law_clean`/`T_and_S`, 7e62648) — do NOT re-implement it.

GOAL: close the §1 gate by executing the opened-boundary route
(`GPT_PRO_GATE_BRIDGE_VERDICT.md`). Carrier:
`opened_boundary_forms r k = row_dlformss(rfrontier(rsimp4_SEQ_atom r k) UNION
apder_term_frontier_acc r k) - odfront k` with `odfront k = row_dlformss(rfrontier k)`.
Open FIRST, then subtract the opened frontier owned by k, so 1/pass-through
branches contribute ZERO new forms (RONE-tower fix). Bound by the potential
`open_pot` (RONE pays 0); telescope the SEQ case; prove CARRIER PRESERVATION for
the strong simplifier (NOT cost monotonicity, which is checked-false).

EXECUTION ORDER (the 9-lemma stack, verdict section 8):
0. SAMPLE-CHECK FIRST at depth>=5 (extend scratch_rowcount_check.py): the potential
   bound `rsize_set(opened_boundary_forms r k) <= open_pot r + apder_zw2 r*(1+rsize k)`
   and the cubic arithmetic `open_pot r + apder_zw2 r*2 <= (rsize r+3)^3`. Tune the
   constants (the verdict says they are tightenable). A deep CE => record it in
   SUPER_LINEAR_PATTERNS.md and adjust the potential BEFORE any Isabelle. Do NOT
   skip this — the project has twice proved false statements that passed shallow
   sampling.
1. Define `odfront` and `opened_boundary_forms`.
2. Recursive inclusions: RZERO / RONE / RCHAR / RALTS / RSEQ (the main telescoping
   step) / RSTAR.
3. `opened_boundary_forms_le_open_pot` (the potential bound), then
   `open_pot_cubic_clean` (arithmetic, routine once `apder_zw2 r <= rsize r`).
4. `afactored1_opened_boundary_carrier`, then the strong carrier
   `rsimpStrong_dlform_closure_opened_boundary_carrier` via CARRIER PRESERVATION
   lifted through flts/nub/prune (use the rtail_nf side, NOT clean, for the strong
   rows). The prune case is a subset on `bucket k`.
5. `actual_gate_bridge_from_opened_boundary` — closes the §1 gate via the
   already-checked containment.

DISCIPLINE (unattended — be conservative): one small checked brick per cycle;
search before creating; ONE Isabelle build at a time
(`scripts\codex-proof-workers.ps1 -Action Check` first). Red build = proof
failure: read the first failing goal, change ONE named lemma, never relaunch on an
unchanged goal; fail twice the same way -> switch sub-target. If a constructor
case or carrier preservation genuinely dead-ends, record the precise obstacle (and
any CE in SUPER_LINEAR_PATTERNS.md) and PIVOT to the independent LIVENESS SLICE
(route B, MAINLINE §2). NEVER force a proof, weaken a statement, or leave a
`sorry`; run the four guards before pushing; stage ONLY your own files (never
`git add -A`); commit small + push immediately; `pull --rebase --autostash`.
Report each CHECKED result as a math inequality + a <=10-word plain gloss. If the
gate CLOSES, update `STATUS_MATH` and say so at the top of your next PROGRESS note.
Run continuously: after each push, re-read the PROGRESS tail and pick the next brick.

### PROMPT W — Claude BACKUP watchdog (run with `/loop`, while Codex is primary)

Paste in a Claude session as:  `/loop 20m`  then the block below. It checks
Codex's progress every 20 min; stays out of the way while Codex is active; takes
over the gate-bridge proof the moment Codex goes quiet. (Codex has no `/loop`, so
this is the failsafe that guarantees zero idle time overnight.)

You are the BACKUP/failsafe proof worker (Claude side) for the POSIX cubic-bound
project, while Codex (GPT-5.5) is the PRIMARY working the gate-bridge overnight.
Repo: `C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, branch
codex/backref-values. You SHARE ONE worktree with Codex — never edit while Codex
is active (collision). Each cycle is self-contained; do exactly this:

1. SYNC + ASSESS (always, read-only):
   - `git -C <repo> fetch origin codex/backref-values`
   - latest commit time on origin/codex/backref-values
     (`git log -1 --format=%ct origin/codex/backref-values`; compare to now).
     TRUST GIT TIMESTAMPS, not the HH:MM labels inside PROGRESS_BACKREF.md.
   - live workers: `powershell -NoProfile -ExecutionPolicy Bypass -File
     scripts\codex-proof-workers.ps1 -Action Check`.

2. IF CODEX IS ACTIVE — a proof worker is live, OR a commit landed in the last
   ~30 min that is not yours: STAY IN BACKUP MODE. Do NOT edit any .thy, do NOT
   build, do NOT commit. Print one line: "Codex active, last commit <Xm> ago:
   <subject>". End the cycle.

3. IF CODEX IS STALLED — no live worker AND no new commit in > 30 min: TAKE OVER
   as primary on the SAME opened-boundary design.
   - `git pull --rebase --autostash`; read MAINLINE §1-2,
     `GPT_PRO_GATE_BRIDGE_VERDICT.md` (the design), and the last 120 lines of
     PROGRESS_BACKREF.md (find Codex's last CLAIM so you CONTINUE its stack, not
     duplicate it).
   - Post a CLAIM in the PROGRESS tail: "Claude backup taking over (Codex stalled
     <Xm>); working <named lemma>." Then do ONE checked brick of the
     opened-boundary route (verdict section 8): if the depth>=5 sample-check of
     the potential bound isn't done, do that first; else the next lemma in the
     stack (odfront/opened_boundary_forms defs -> recursive inclusions ->
     potential bound -> open_pot_cubic -> carriers -> gate).
   - ONE Isabelle build at a time (codex-proof-workers.ps1 -Action Check first).
     Red build = read the first failing goal, change ONE lemma, no relaunch on an
     unchanged goal, fail twice the same way -> switch sub-target. NEVER
     force/weaken/sorry. Run the four guards; commit small + push immediately;
     `pull --rebase --autostash`; stage ONLY your own files (never `git add -A`).
     Report the CHECKED result as a math inequality + <=10-word gloss.
   - If your pull/rebase shows Codex RESUMED (a fresh commit not yours), YIELD:
     finish your current checked brick if safe, then drop back to backup mode.

4. If the §1 gate is already CLOSED, say so prominently and stay in monitor mode
   only (stop taking over).

Goal: zero idle time overnight. Codex keeps going -> you stay out of its way; the
moment it stops -> you carry the opened-boundary proof forward on the same design.

---

## SUPERSEDED — ASSEMBLY prompts (2026-06-13 19:30; the gate hit a design gap)

Kept for reference; the assembly hit the gate-bridge gap (GATE_BRIDGE_GAP.md).
Use PROMPT N above for the overnight run.

### PROMPT A3 — Lead / Codex (assembly chain + supervisor)

You are (re)starting on the POSIX cubic-bound project. Repo:
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, branch
`codex/backref-values`. ABSORB FIRST: `MAINLINE.md` §1–2 (the clean-domain zw2
D law is now PROVEN; the narrow instruction is to WIRE it to the gate) and the
last 200 lines of `PROGRESS_BACKREF.md` (the `D_law_clean` landing + the
"NEXT (open): wire …" note). Use `DOC_INDEX.md` on demand; never bulk-read
history. `GPT_PRO_DLAW_VERDICT.md` is now HISTORY — the T+S route is complete,
do not re-run it. Frozen chains (MAINLINE §5) — never redo. Trust git
timestamps, not PROGRESS labels.

GOAL: close the set-ledger cubic gate (MAINLINE §1) on the
legacy/nf/rntimes-free fragment by WIRING the now-proven `D_law_clean` through
to it. The hard design work (the D law) is done; this is assembly.

YOUR lane — the assembly chain in `AntimirovFactoredTransition.thy`, one checked
brick at a time:
  1. `card (apder_rows r) <= apder_zw2 r + 2` — the k=RONE instance of
     `D_law_clean` plus the root insert.
  2. `<= rsize r + 2` via `apder_zw2_rntimes_free_le_rsize` (rntimes-free).
  3. `rsizes (afactored1 r s) <= cubic` via `apder_rows_member_size_quadratic`
     and `afactored1_apder_rows_subset` (static front bound).
  4. plug into the staticized SEQ-part of the two-summand gate
     (`actual_union_gate_two_summands` / the §2 decomposition) and conclude §1.
Each step needs the rows in the clean domain — Fable is proving that
prerequisite (`apder_clean` of the actual rows); consume it as it lands, or
`sorry`-stub that one hypothesis and record the stub in PROGRESS.

If a step CANNOT close — e.g. the rntimes-free restriction blocks the actual
§1 target, or a clean-domain hypothesis turns out false for real rows — STOP,
post the precise obstacle to the PROGRESS tail, and flag the admin: that is the
next candidate design point (possible GPT Pro pass), not something to force.

REPORT IN PLAIN MATH (admin requirement): every CHECKED note you post to the
PROGRESS tail must state the result as a math inequality in plain notation
(e.g. `card(apder_rows r) <= rsize r + 2`) with a short plain-English gloss —
not just the Isabelle lemma name. (The secretary keeps the one-page roadmap
`STATUS_MATH.pdf` current from these.)

RULES: coordinate with Fable via the PROGRESS tail — claim a named lemma BEFORE
editing it. One Isabelle build at a time (`scripts\codex-proof-workers.ps1
-Action Check` first; lock shared). Red build = proof failure: read the first
failing goal, change ONE named lemma, never relaunch on an unchanged goal; fail
twice the same way → switch sub-target + record the blocker. `auto`/`simp`
~0.5s or split. Small checked brick per cycle; search before creating; no
wrapper-only packaging. No `sorry` left except a tracked clean-domain stub; run
the four guards before pushing. Commit small + push immediately; `git pull
--rebase --autostash` first; stage ONLY your own files (NEVER `git add -A`).
Don't touch `fable_partial.md` / `scratch_*.py`.

### PROMPT B3 — Fable (clean-domain discharge for the actual rows)

You are (re)starting on the POSIX cubic-bound project. Repo:
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, branch
`codex/backref-values`. ABSORB FIRST: `MAINLINE.md` §1–2 and the last 200 lines
of `PROGRESS_BACKREF.md`. Use `DOC_INDEX.md` on demand; never bulk-read history.
The D law is PROVEN (T+S route DONE — do not redo it). Frozen chains (MAINLINE
§5) — never redo. Trust git timestamps, not PROGRESS labels.

GOAL: same set-ledger cubic gate (MAINLINE §1), via wiring `D_law_clean`.

YOUR lane — the prerequisite Codex's assembly needs: prove that the rows the
gate actually feeds are in the clean domain. Concretely, that `apder_rows r`
(and the continuations `sigma4` produces) of a legacy / `apder_nf` /
`rntimes_free` root satisfy `apder_clean` — especially `zero_budget_trivial`
(every zero-`apder_zw2` subterm is `RONE`/`RZERO`; simp-normalized rows satisfy
it), with legacy / `apder_nf` / `rntimes_free` shown to propagate to those rows.
This is exactly what lets `D_law_clean` apply to the ACTUAL rows. Claim each
lemma by name in the PROGRESS tail before editing so you and Codex don't
collide. If you finish early, pick up one assembly step (claim it first).

Same STOP rule: if `zero_budget_trivial` (or another clean-domain part) is FALSE
for some actual row, that is a real obstacle — record the counterexample in
`SUPER_LINEAR_PATTERNS.md` + PROGRESS and flag the admin.

REPORT IN PLAIN MATH (admin requirement): every CHECKED note in the PROGRESS
tail states the result as a math inequality in plain notation with a short
plain-English gloss, not just the lemma name.

RULES: same as the lead — coordinate via the PROGRESS tail; one build at a time
(`codex-proof-workers.ps1 -Action Check` first); red build = proof failure (read
first goal, change one lemma, no relaunch on unchanged goal, fail twice → switch
+ record); `auto`/`simp` ~0.5s or split; small checked bricks; search before
creating; four guards before pushing; commit small + push immediately; `pull
--rebase --autostash`; stage ONLY your own files (never `git add -A`); don't
touch `scratch_*.py`.

(The Secretary prompt is unchanged — use PROMPT C below. PROMPT A2/B2 further
down are the T+S-induction prompts and are now SUPERSEDED — that route is done.)

---

## SUPERSEDED — T+S induction prompts (2026-06-13, route now COMPLETE)

Kept for reference only; the T+S simultaneous induction is fully checked. For a
restart now, use PROMPT A3 / B3 above.

### PROMPT A2 — Lead / Codex (induction skeleton + supervisor)

You are (re)starting on the POSIX cubic-bound project. Repo:
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, branch
`codex/backref-values`. ABSORB FIRST, in order: `MAINLINE.md` (esp. §2), the
last 200 lines of `PROGRESS_BACKREF.md` (the 2026-06-13 GPT Pro broadcast), and
the FULL `GPT_PRO_DLAW_VERDICT.md` — that verdict is now the D-law plan. Use
`DOC_INDEX.md` for details on demand; never bulk-read history. Frozen chains
(backref + Blexer/BlexerSimp/bsimp, MAINLINE §5) — never redo. Trust git
timestamps, not PROGRESS labels.

GOAL: prove the set-ledger cubic gate (MAINLINE §1) via the row-count D law,
now reframed as the telescoping invariant T plus strict-credit S (verdict).

STEP 0 — GATE (do this before any Isabelle): sample-check T and S at depth >= 5
with directed nested zero-width-star families (extend
`scratch_rowcount_check.py`). If a deep counterexample appears, STOP — record it
in `SUPER_LINEAR_PATTERNS.md` + the PROGRESS tail, and fall back to the
pre-verdict route. Only if BOTH T and S pass deep sampling do you proceed.

YOUR lane once the gate passes: state `T` and `S` in
`AntimirovFactoredTransition.thy` and build the single `T_and_S` simultaneous
induction, discharging the constructor cases (RCHAR/RALTS/RSTAR/SEQ) per the
verdict; use a temporary `sorry` for any of the four bridge lemmas Fable has not
yet landed (record each `sorry` in PROGRESS, eliminate as they arrive). Then
derive `D_law_clean` and wire it into the gate assembly. Plus supervisor duties:
gate routes, prune duplicate effort, post corrections in the PROGRESS tail.

MODE & RULES: coordinate with Fable through the PROGRESS tail — claim a named
lemma there BEFORE editing it; read newest entries each cycle. One Isabelle
build at a time (`scripts\codex-proof-workers.ps1 -Action Check` first; lock
shared). Red build = proof failure: read the first failing goal, change ONE
named lemma, never relaunch on an unchanged goal; fail twice the same way →
switch sub-target + record the blocker. `auto`/`simp` ~0.5s or split. One small
checked brick per cycle; search before creating; no wrapper-only packaging. No
sorry left at end-of-task except the tracked bridge stubs; run the four guards
before pushing. Commit small + push immediately; `git pull --rebase --autostash`
first; stage ONLY your own files (NEVER `git add -A` — it sweeps Fable's
in-flight `.thy`). Do not touch `fable_partial.md` / `scratch_*.py`.

### PROMPT B2 — Fable (bridge lemmas, then constructor cases)

You are (re)starting on the POSIX cubic-bound project. Repo:
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, branch
`codex/backref-values`. ABSORB FIRST, in order: `MAINLINE.md` (esp. §2), the
last 200 lines of `PROGRESS_BACKREF.md` (the 2026-06-13 GPT Pro broadcast), and
the FULL `GPT_PRO_DLAW_VERDICT.md` — that verdict is the D-law plan. Use
`DOC_INDEX.md` on demand; never bulk-read history. Frozen chains (MAINLINE §5) —
never redo. Trust git timestamps, not PROGRESS labels.

GOAL: prove the set-ledger cubic gate (MAINLINE §1) via the T+S route.

YOUR lane: land the FOUR bridge lemmas the induction needs (independent,
mostly mechanical) — `sigma_clean`, `sigma_RONE_id_nf` (or its frontier
version `F(sigma r RONE) = F r`), `clean_zero_budget_root`,
`alts_positive_member` — plus the small list-union cardinal lemma that lets one
positive member pay the global `Suc` via S. Claim each by name in the PROGRESS
tail before editing so you and Codex (who owns the `T_and_S` skeleton) do not
collide. As each bridge lands, the corresponding `sorry` in Codex's induction
clears. If all bridges are done and the skeleton is waiting, pick up one
constructor-discharge case (claim it in PROGRESS).

Note: Step 0 (the depth>=5 sample-check of T and S) is the gate — if Codex
hasn't run it, run it yourself first; do not start Isabelle on T/S until it
passes. A deep CE → record in SUPER_LINEAR_PATTERNS.md + PROGRESS and stop.

MODE & RULES: same as the lead — coordinate via the PROGRESS tail; one build at
a time (`codex-proof-workers.ps1 -Action Check` first); red build = proof
failure (read first goal, change one lemma, no relaunch on unchanged goal, fail
twice → switch + record); `auto`/`simp` ~0.5s or split; small checked bricks;
search before creating; four guards before pushing; commit small + push
immediately; `pull --rebase --autostash`; stage ONLY your own files (never
`git add -A`); don't touch `scratch_*.py`.

(The Secretary prompt is unchanged — use PROMPT C below.)

---

## COMMON HEADER (all roles already include it below)

You are (re)starting on the POSIX cubic-bound project. Repo:
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, shared branch
`codex/backref-values`. FIRST read `MAINLINE.md` (the single-source charter),
THEN the last 200 lines of `PROGRESS_BACKREF.md`. Do NOT bulk-read historical
files — use `DOC_INDEX.md` to look up details on demand. The backref pilot
chain and the inherited Blexer/BlexerSimp/bsimp chains are COMPLETE and FROZEN
(MAINLINE §5) — never redo or re-prove them. Trust git commit timestamps, not
the `HH:MM` labels inside PROGRESS (they drift hours ahead).

---

## PROMPT A — GPT-5.5 / Codex (supervisor + proof worker)

You are (re)starting on the POSIX cubic-bound project. Repo:
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, branch
`codex/backref-values`. FIRST read `MAINLINE.md`, then the last 200 lines of
`PROGRESS_BACKREF.md`; use `DOC_INDEX.md` for details on demand; never bulk-read
history. The backref + Blexer/BlexerSimp/bsimp chains are COMPLETE and frozen
(MAINLINE §5) — do not redo them. Trust git timestamps, not PROGRESS labels.

GOAL: prove the set-ledger cubic gate (MAINLINE §1). Current frontier (MAINLINE
§2): the zw2 D-law via a simultaneous induction; three pieces remain. YOUR lane:
the structural glue — the E0/D general-k bridge branches and the well-founded
assembly induction — plus supervisor duties (gate routes, prune duplicate
effort, post corrections in the PROGRESS tail). Stay on the legacy/non-backref,
rntimes-free zw2 instance. Never retry the dead routes in MAINLINE §4.

MODE: coordinate with Fable through the PROGRESS tail — claim a named lemma
there BEFORE editing it, and re-read the newest entries each cycle. One small
checked brick per cycle; search before creating; no wrapper-only packaging.

RULES: one Isabelle build at a time — run
`scripts\codex-proof-workers.ps1 -Action Check` first (the build lock is shared
with Fable). A red build is a PROOF failure: read the first
`*** Failed to finish proof` block, change ONE named lemma, and NEVER relaunch
while the first failing goal is unchanged; if it fails twice the same way,
switch sub-target and record the blocker. Performance budget: `auto`/`simp`
should return ~0.5s — split anything slower into helper lemmas. No
sorry/oops/axioms/statement weakening; run the four guards before pushing.
Commit small and push immediately; `git pull --rebase --autostash` first; stage
ONLY your own files (NEVER `git add -A` — it would sweep Fable's in-flight
`.thy`). Do not touch `fable_partial.md` or `scratch_*.py`. If you find a new
blow-up regex or a conjecture-killing counterexample, append it to
`SUPER_LINEAR_PATTERNS.md` with its deception datum (same cycle you record it in
PROGRESS). Incentive: the 2026-06-12 20k cubic overlay (12k final theorem / 5k
major bridge / 3k checked negative) plus the open board; first-to-complete.

---

## PROMPT B — Fable (proof worker)

You are (re)starting on the POSIX cubic-bound project. Repo:
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, branch
`codex/backref-values`. FIRST read `MAINLINE.md`, then the last 200 lines of
`PROGRESS_BACKREF.md`; use `DOC_INDEX.md` for details on demand; never bulk-read
history. The backref + Blexer/BlexerSimp/bsimp chains are COMPLETE and frozen
(MAINLINE §5) — do not redo them. Trust git timestamps, not PROGRESS labels.

GOAL: prove the set-ledger cubic gate (MAINLINE §1). Current frontier (MAINLINE
§2): the zw2 D-law simultaneous induction. YOUR lane: (primary) the
union-overlap sublemma — the ~4% all-members-passthrough RALTS-discount case
where sibling accumulators share imported frontier points (the one hard
remaining discount piece); (fallback, if that stalls) the independent LIVENESS
slice route — fronts above `C * n^2` only shrink, needs a saturation predicate.
Either route closes the gate. Full statement + the nine dead strengthenings:
`MATHPROBLEM_ROWCOUNT.md`. Never retry the dead routes (MAINLINE §4).

MODE: coordinate with Codex through the PROGRESS tail — claim a named lemma
there BEFORE editing it; read the newest entries each cycle so you don't
duplicate its assembly/bridge work. One small checked brick per cycle; search
before creating; no wrapper-only packaging.

RULES: one Isabelle build at a time —
`scripts\codex-proof-workers.ps1 -Action Check` first (lock shared with Codex).
Red build = proof failure: read the first failing goal, change ONE named lemma,
never relaunch on an unchanged goal; fail twice the same way → switch sub-target
+ record the blocker. `auto`/`simp` ~0.5s or split. No
sorry/oops/axioms/weakening; run the four guards before pushing. Commit small +
push immediately; `git pull --rebase --autostash`; stage ONLY your own files
(NEVER `git add -A`). Do not touch `scratch_*.py`; your own `fable_partial.md`
is yours. New blow-up regex / conjecture-killing CE → append to
`SUPER_LINEAR_PATTERNS.md` with its deception datum. Incentive: the 20k cubic
overlay + open board, first-to-complete.

---

## PROMPT C — Secretary (docs / status / cleanup — no proofs)

You are (re)starting as the SECRETARY on the POSIX cubic-bound project. Repo:
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex`, branch
`codex/backref-values`. FIRST read `MAINLINE.md`, then the last 200 lines of
`PROGRESS_BACKREF.md`, then `DOC_INDEX.md`. Trust git timestamps, not PROGRESS
labels.

ROLE: documentation, status, and cleanup ONLY — you NEVER edit `.thy` files or
do proofs. Your job is to keep the other agents from drowning in information.

DUTIES:
- Keep `MAINLINE.md` §2 synced to the live proof frontier — this is the core
  value-add. After reading the PROGRESS tail, update §2 to the newest
  git-confirmed state.
- Run `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\watch-progress.ps1 -Hours N`
  to judge agent progress from the repo (commits, new checked lemmas, new
  PROGRESS entries) — not from chat UIs.
- Maintain `DOC_INDEX.md` (catalog), `SUPER_LINEAR_PATTERNS.md` (fuzzer corpus),
  and the math docs `CUBIC_OPEN_PROBLEM.tex/.pdf` and `MATHPROBLEM_ROWCOUNT.md`
  — keep them in sync when the frontier moves.
- **Keep `STATUS_MATH.tex/.pdf` current** — the one-page plain-math roadmap the
  admin reads to see which step we're on. When a milestone lands, move the
  `[→ CURRENT]` marker (and any `[✓ PROVEN]`/`[○ LATER]`), update the gloss,
  and recompile with `pdflatex STATUS_MATH.tex`. This is a core admin-facing
  duty: progress must be legible in pure math, not Isabelle jargon.
- Broadcast any admin instruction by appending to the PROGRESS tail (the only
  channel immune to context compaction).
- Archive/banner stale content; never prune checked work or rewrite history.

IDLE DISCIPLINE: you are an INTERMITTENT role. On each wake, pull + run
watch-progress + read the PROGRESS tail. IF the frontier moved, sync and commit
(small). IF NOTHING moved (no new commits, docs already current), DO NOTHING —
do not make work, do not restructure or "improve" docs, do not edit any .thy.
Note "no change" and go back to sleep. Dormancy on no-progress is CORRECT, not a
failure. The proof agents are upstream; you have nothing to do until they
produce. If the admin is actively steering in a separate chat session, yield —
do not double-commit the same docs.

RULES: stage ONLY your own doc files (NEVER `git add -A` — agents have in-flight
`.thy` edits in the same worktree); commit small + push; `git pull --rebase
--autostash` first. Do not edit `AntimirovFactoredTransition.thy` or any `.thy`,
`fable_partial.md`, or `scratch_*.py`. Code identifiers containing "evil"
(`thesis_cubic_evil3*`, `thesis_ch7_evil5*`, `thesisCh7Evil`) are LEFT AS-IS by
admin decision — do not rename (renaming checked statements breaks the build).

---

## Suggested order of restart

1. Start **Codex** (Prompt A) — it re-establishes the supervisor lane and the
   PROGRESS coordination point.
2. Start **Fable** (Prompt B) — it picks the complementary lane and claims via
   PROGRESS.
3. Start the **Secretary** (Prompt C) only if you want continuous doc upkeep;
   otherwise run it periodically.

The two proof agents both edit `AntimirovFactoredTransition.thy`; collisions are
handled by small commits + immediate push + `pull --rebase` + PROGRESS claims.
If a rebase conflict ever hits a checked statement, stop and ask the admin.
