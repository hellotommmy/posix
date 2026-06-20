# MAINLINE — Single-Source Charter for the POSIX Cubic Bound

Status: LIVE. Maintained by the secretary/cleanup session at the admin's
request. Created 2026-06-12. If this file and an older document disagree,
this file wins; if this file and the tail of `PROGRESS_BACKREF.md` disagree,
the newer PROGRESS entry wins and this file should be updated.

Read THIS file first in every fresh or compacted session. Read other
documents only on demand, via `DOC_INDEX.md`. Do not re-read large
historical files to "restore context"; that is how sessions drown.

## 0. The three standing questions (answer ALL THREE at every status check)

The admin's standing check. Whenever anyone — admin, secretary, monitor, or the
`posix-cubic-watch` routine — assesses this project, answer all three, from GIT
(not from the drifting `HH:MM` labels inside `PROGRESS_BACKREF.md`):

1. **进展如何 — Progress?** What checked results landed since the last look,
   stated as math inequalities + a ≤10-word plain gloss? How many commits, and
   the time of the latest one?
2. **卡住了吗 — Stuck?** Is a proof worker live / did a commit land recently
   (HEALTHY), or is it no-commit-in->30-min + no-worker (STALLED)? Is the current
   "live edge" a real WALL (a recorded blocker / a route dead-end / a checked
   counterexample) or just GRINDING a known/anticipated case?
3. **需要给 Pro 什么吗 — Need a design pass (GPT Pro)?** Only if a case genuinely
   DEAD-ENDS — a degree gap or counterexample the current design cannot absorb.
   Mechanical grinding and anticipated sub-issues (e.g. the RONE pass-through
   fix) do NOT warrant a GPT Pro pass; let the agents execute. If one IS needed,
   frame the precise obstacle (a minimal failing example) into the relevant gap
   file before escalating.

## 1. The One Open Problem

Everything in this repository now converges on one theorem, the
**set-ledger cubic gate**, to be proved in `AntimirovFactoredTransition.thy`
on branch `codex/backref-values`:

```text
rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
  <= 2 * (rsize r + 3)^3
```

Plain words: take the one-step rows produced after strong
simplification/pruning (`rpder_strong_rows_raw c (afactored1 r s)`, the
"actual rows"), open every row into linear forms, remove duplicates across
the whole union (`row_dlformss`), and sum the sizes of the distinct opened
rows (`rsize_set`). That total must be cubic in the original regex size.

Vocabulary (fixed, do not rename):

- `row_dlforms q` — open one row, deduplicate within the row.
- `row_dlformss rows` — open all rows, deduplicate across the union.
- `row_dlforms_list_size` / `afactored1_strong_dlform_list_cost` — the
  duplicated LIST quantities. These are the BAD quantities (see §4).
- `rsize_set U` — sum of `rsize` over distinct members of `U`.

## 2. Where the Proof Stands (as of 2026-06-14 — D law PROVEN; §5 drain ARITHMETIC done/green; context-cover infra + static lemmas + RCHAR/RSEQ ctx cases green; the #3/#4 cover PROOFS go via GPT Pro verdict5 WEAK-CARRIER skeleton (`GPT_PRO_GATE_BRIDGE_VERDICT4.md`) — a proof-only `weak_child_drain` (non-collapsing rsimp4 plug) + injective indexed-slot charge, mutual P/Q induction — VALIDATED at depth≥5 (~660k checks, 0 in-fragment violations, both CEs covered). #3/#4 UN-GATED, implementing. Two caveats: weak acc must be S-FREE; guards must be `S p=p`. Lemma `strong_child_drain_potential` green = §4 blocker CLOSED, then §7.)

> **⛔ SUPERSEDED (2026-06-16) — the per-step drain-budget route below is DEAD; the live
> route is the CUBE-SHELL potential bound (see STEER.md).** Adversarial re-validation with a
> *structured* witness family (not `rand_clean`) reproduced two independent in-regime
> counterexamples that refute BOTH per-step budget targets at depth≥5:
> - TIGHT: `rsize_set(strong_child_drain p k) ≤ ctx_bound(drain_ctxs p) k` is FALSE.
>   CE2 (rsize19): `p = 1+((1+((1+a)·a)+((c+1)·(c+1)))·c*)`, `k=c*` → 47 > 46.
>   CE1 (rsize18): `p=(((((a+1)·b)+1)·((1+a)·(c·b*)))+c)`, `k=b*` → 64 > 60.
> - LOOSE / `child_ok`: `rsize_set(strong_child_drain p k) ≤ drain_child_budget p k` is ALSO
>   FALSE. CHILDOK (rsize22): `p=(((((a+1)·b)+1)·((((a+1)·b)+1)·(a·b*)))+c)`, `k=b*` → 99 > 96.
> - **`drain_child_budget` is NOT "proven".** `child_okD` (@32981) only *unfolds the
>   assumption* `child_ok p`; nothing discharges `child_ok` unconditionally, and it is false
>   in-regime. So neither (a) "switch the target to `drain_child_budget`" nor (b) "add a
>   per-slot capacity fix to the ctx_bound ledger" rescues the route — the overshoot exceeds
>   even the looser quadratic budget and grows with chain depth.
> - The "0-violation > 10⁵ samples" that made both bounds look TRUE was a SAMPLING ARTIFACT:
>   `rand_clean` essentially never builds the killer (nested `SEQ(ALTS[pre,1], … SEQ(atom,
>   star*))` opened at `k=star*`, which re-doubles `star*→star*·star*` each frame). The
>   witness family finds CEs at ~11% (ctx_bound) / ~4.7% (drain_child_budget) on every seed.
> - Reproduce: `python scratch_ctxbound_target_FALSE_repro.py` (named CEs) and
>   `python witness_gen.py` (witness family + regression anchors). Every future drain-budget
>   gate MUST import `witness_gen`; a `rand_clean`-only gate is no longer acceptable.
> - The rest of §2 (verdict4 ledger / verdict5 weak-carrier / `master_cover` / child_ok) is
>   KEPT FOR HISTORY ONLY. Do not implement it. See §4 entry 11 and STEER.md for the live route.

- **CARD half: done, one-degree.** `card_row_dlformss_le_rsizes` and
  `card_row_dlformss_rpder_strong_rows_raw_le_generated` — distinct opened
  rows of the actual output are at most the generated total size.
- **Gate instance fully discharged (legacy fragment).**
  `actual_union_pair_budget_gate_instance` (908542b) with
  `H = Suc (2 * rsize r)` (`actual_union_seq_head_size_linear`) and
  `M = Suc H + rsizes(generated)` (one degree).
- **Pair-budget summand is ZERO (cfe3636).** The dlform universe has no
  keyed member (`afactored1_strong_dlform_universe_no_keyed_member`), so the
  active-suffix key set is empty and
  `pair_budget_afactored1_strong_dlform_universe_zero` holds; the gate has
  exactly two summands (`actual_union_gate_two_summands`). Note: the
  active-suffix machinery is DEGENERATE on the dlform universe (designed for
  row sets); do not spend effort instantiating it there.
- **SIZE half: ONE remaining obligation.** Of the two summands:
  1. `rsize_set (rnonseq_members (union))` — DONE cubic
     (`rsize_set_rnonseq_members_row_dlformss_rpder_strong_rows_raw_afactored1_cubic`).
  2. The SEQ part — OPEN. Exact decomposition on record:
     `card(SEQ members) * (linear heads) + sum over tails t of
     bucket(t) * rsize t`. The two load-bearing numbers:
     `card(union)` (empirically linear; best checked bound one degree in the
     generated total) and `bucket(t)` (empirically linear; best checked
     bound cubic). No self-reference remains in this decomposition.
- **Late-night refinement (22:25–23:45, commits 5865745..5f41633).** The
  SEQ-part obligation was staticized: dynamic front rows live in the static
  `apder_rows` carrier (`afactored1_apder_rows_subset`), whose member sizes
  are now CHECKED quadratic (`apder_rows_member_size_quadratic`, nf
  fragment). The whole gate (nf fragment) now closes by assembly once
  EITHER of two named frontiers lands:
  1. **The D law (row-count linear) — LANDED 2026-06-13 13:48 (7e62648).**
     The clean-domain zw2 instance is now PROVEN: `D_law_clean`
     (`apder_clean r ==> apder_clean k ==> card (apder_term_frontier_acc r k -
     rfrontier k) <= apder_zw2 r`), immediate from the `T_and_S` telescoping
     induction (GPT Pro T+S route, see below). What remains for the cubic gate
     is the downstream WIRING, not the D law. History — CORRECTED 2026-06-13
     00:13 and narrowed 04:00:
     `apder_nf r ==> apder_nf k ==> card (apder_term_frontier_acc r k -
     rfrontier k) <= apder_zw2 r` (zw2: star = Suc, not max-1) was the
     first repair. The old zwidth weight and the first J* joint invariant
     were BOTH falsified by depth-5 CEs after passing 200k/95k shallow
     samples. The unrestricted raw zw2 law is also checked false when
     zero counted repetitions are allowed:
     `apder_zw2_D_law_rntimes_zero_alt_false` has
     `RSEQ (RCHAR c) (RALTS [RNTIMES (RCHAR a) 0, RNTIMES (RCHAR b) 0])`
     with row count 2 and budget 1. The current proof-useful target is the
     legacy/non-backref, rntimes-free instance of the zw2 D law, matching the
     checked payoff `apder_zw2_rntimes_free_le_rsize` (commit 8a7a370),
     unless the admin explicitly reopens a zero-count-aware NTIMES
     weight/premise. Full statement, dead-ends and attacks:
     `MATHPROBLEM_ROWCOUNT.md` (repo root).
  2. **The liveness slice:** fronts above `C * n^2` only shrink (zero
     violations empirically; needs a saturation predicate).
- **Morning progress (06-13 ~03:40–09:18, git-authoritative; PROGRESS labels
  drift ahead — trust git).** The zw2 D law is now being proved by a
  **simultaneous induction**, not a one-shot bound. Structure landing:
  - A revived discount, the **clean-domain passthrough discount** (the old
    D+ idea, restricted to a "clean domain": `sigma4(r1,t) ∉ acc(r1,t) ⇒
    card(acc(r1,t) − F t) ≤ zw2 r1 − 1`), is now a named induction
    obligation — 240,256 deep samples, zero violations. STAR branch checked
    (`discount_RSTAR_if_body_D`); RCHAR checked (`discount_RCHAR`); the 96%
    member-discount RALTS case now CHECKED (`discount_RALTS_if_member_discount`,
    commit 581d9d6 11:48).
  - The **E00-RONE branch map is COMPLETE** (RCHAR, RALTS, RSTAR cond., SEQ
    cond.: `E00_RONE_RSEQ_if` etc.); the **E0 general-k bridge series** is in
    progress (RCHAR done).
  - **Three pieces remain** for row-count-linear: (a) the **union-overlap
    sublemma** — the 4% all-members-passthrough RALTS-discount case where
    sibling accumulators share imported frontier points; the 96% member-discount
    case is now CHECKED (`discount_RALTS_if_member_discount`, 581d9d6), so only
    this 4% slice is left; (b) the E0/D general-k branches (RCHAR done via
    `E0_RCHAR`; the RALTS bridge checked, `E0_RALTS_if_members`, e0b899b); (c)
    the **well-founded assembly induction** that ties the branches together.
- **GPT Pro steer (2026-06-13, `GPT_PRO_DLAW_VERDICT.md`): switch to the T+S
  telescoping invariant.** Instead of grinding the union-overlap sublemma (a)
  or J* directly, prove the boundary invariant
  `T(r,k): clean r ⟹ clean k ⟹ card((F(σ r k) ∪ A r k) − F k) ≤ W r`
  plus a strict-credit auxiliary
  `S(r,k): clean r ⟹ clean k ⟹ 0 < W r ⟹ Suc(card(A r k − F k)) ≤ W r`.
  D and J* both follow; the SEQ overlap DISAPPEARS (F(σ r2 k) is a boundary,
  subtracted left and paid once right — no inclusion-exclusion). It also found
  a real gap: **E0 must be the EXACT merged-frontier T law, not the `+1` form**
  (the +1 leaks a unit at the singleton-continuation SEQ case r1=a,r2=b,k=c;
  S supplies the spare). **All four bridges now CHECKED:** `sigma_clean`
  (9f8cff0), `sigma_RONE_id_nf` (95aa064), `clean_zero_budget_root` (95776a2),
  `alts_positive_member` (44206f2). The T/S invariants are now STATED in
  Isabelle (`apder_T_bound`, `apder_S_bound`, d70f0df) with the load-bearing
  implications checked (`apder_T_bound_imp_D` = T⟹D,
  `apder_S_bound_imp_discount` = S⟹discount). **The T+S route is COMPLETE
  (2026-06-13 13:48, 7e62648):** the `T_and_S` simultaneous induction is proven
  (`induct r arbitrary: k`, dispatching all four constructor cases
  `T_and_S_RCHAR` 10d4c79 / `T_and_S_RSEQ` b21524d / `T_and_S_RSTAR` d72d32c /
  `T_and_S_RALTS` 2c7401e; RZERO/RONE empty-set, NTIMES/backref vacuous by
  `apder_clean`), and the clean-domain zw2 D law `D_law_clean` follows
  immediately. Build GREEN, no `sorry`.
- **WIRING IN PROGRESS (2026-06-13 19:43–20:09).** Connecting `D_law_clean`
  to the cubic gate. Landed: `card_apder_rows_le_apder_zw2_plus_2`
  (card(apder_rows r) ≤ zw2 r + 2 — the D-law payoff) and
  `card_apder_rows_clean_le_rsize_plus_2`; the **static FRONT cubic bound**
  `rsizes_afactored1_clean_static_cubic`
  (`apder_clean r ⟹ rsizes (afactored1 r s) ≤ (rsize r + 3)^3`, uniform in s,
  b918254); and clean-domain propagation to the ACTUAL rows
  (`apder_clean_apder_rows`, `apder_clean_afactored1`, AntimirovNormalFrontier.thy)
  so `D_law_clean` applies per actual front row.
- **THE ONE REMAINING GAP — the dedup gate-bridge (OPEN; opened-boundary route
  stalled at a CHECKED-FALSE strong-carrier bridge → pivoted to the liveness
  slice, see below).** The D law and the
  cubic static front are proven, but the §1 gate
  `rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))) <=
  2*(rsize r+3)^3` is NOT yet closed, and the naive assembly does **not** work:
  the per-row **square-sum is QUINTIC** (linearly-many rows × quadratic member
  size — 2 degrees too weak) and the **non-deduplicated list is EXPONENTIAL**
  (RONE-pair tower, `afactored1_strong_dlform_list_cost_cubic_false`). The cubic
  bound must come from **deduplication / suffix-sharing** across the opened
  union — the analogue, for the `dlform` closure, of the telescoping invariant
  that cracked the D law. Sufficient to prove EITHER (i) the square-sum
  `<= 2*(rsize r+3)^3`, or (ii)
  `rsize_set (rsimpStrong_dlform_closure (set (afactored1 r (s@[c])))) <=
  2*(rsize r+3)^3`. Note: the strong-frontier rows are only `rtail_nf`, not
  fully `apder_clean`. The 8 checked facts to reuse and the dead routes are in
  `GATE_BRIDGE_GAP.md`.
- **OPENED-BOUNDARY ROUTE — executed, but its strong-carrier bridge is
  CHECKED-FALSE (2026-06-14).** The full opened-boundary stack landed at the
  `apder_clean`/`afactored1` level: carrier (`row_dlformss_set`, `odfront`), all
  base inclusions (RZERO/RONE/RCHAR/RALTS/SEQ-telescope/RSTAR), the `open_pot`
  potential + its cubic arithmetic, and the afactored1 carrier
  (9b110c4..783b403). BUT the bridge from there to the STRONG gate object is
  **false**: `rsimpStrong_dlform_closure(set(afactored1 r u)) <= odfront RONE ∪
  opened_boundary_forms r RONE` fails on the clean fragment — CE
  `r = RSTAR (RALTS [RCHAR a])`, `bad = RSTAR (RCHAR a)`
  (`rsimpStrong_dlform_closure_opened_boundary_carrier_false`, ae98002): strong
  simplification collapses a singleton ALT under STAR after the carrier was
  computed for the unsimplified root. So the opened-boundary carrier does NOT
  reach the strong-pruned gate as stated. (Verdict + full stack:
  `GPT_PRO_GATE_BRIDGE_VERDICT.md`; CE in `SUPER_LINEAR_PATTERNS.md`.)
- **PIVOT — the liveness slice (named frontier 2): adapters CHECKED, verbatim
  subset target FALSE.** If the deduped opened ledger lands inside the live
  universe, cubic follows — `rsize_set_subset_live_path_universe_cubic` /
  `rsize_set_subset_live_row_universe_cubic` (c54d09b):
  `U <= partial_derivative_live_{path,row}_universe r ==> rsize_set U <=
  2*(rsize r+3)^3`. BUT the obvious subset
  `row_dlformss (rpder_strong_rows_raw c (afactored1 r s)) <=
  partial_derivative_live_row_universe r` is **checked-false against the ORIGINAL
  root** — same CE family,
  `row_dlformss_actual_not_subset_live_row_universe_original_false` (3c7633a,
  `r = RSTAR (RALTS [RCHAR a])`). Using `rsimpStrong_raw r` as the root fixes the
  singleton-ALT case but is still false for an opened continuation
  (`([1|a].([1|a].c))` opens to `(a.c)`, absent from the normalized live-row
  universe), and the opened normalized universe has deeper prefix-sampled CEs.
- **Partial result (exact decomposition, conservative).** The SEQ-part splits
  into a generated-linear head summand plus a conservative tail term
  `front-card * G^2` (`actual_union_generated_square_decomposition`, 6370b8d) —
  but that term is likely **too weak** for cubic (under test); closing it would
  need a sharper opened-boundary / normalized-tail carrier.
- **Drain carrier (`strong_opened_live`) over the current normalized rows — §5
  arithmetic DONE/green; §4 per-child containment SPLIT.** §5: `drain_pot_le_cubic_core`
  (`rntimes_free r ⟹ drain_pot r ≤ rsize r*(rsize r+2)^2`) and
  `drain_child_budget_root_cubic` are PROVEN (green, no sorry). §4 per-child SET
  containment: **PROVEN for RCHAR (green) and RSEQ (Codex; reassociation telescopes
  soundly).**
- **CHECKED-FALSE (2026-06-14, secretary-verified): the per-child SET-containment
  route for RALTS and RSTAR.** The telescoping inclusion `parent drain ⊆ ⋃ child
  drains` is false because `rsimp7_SEQ_atom` has a guarded rule
  `(RSTAR r, RSTAR s) ⇒ if r=s then RSTAR r` (BasicIdentities.thy:414) collapsing
  `a*·a*→a*` in a child while `rsimp4_SEQ_atom` keeps it. CEs: **C-DRAIN-1** RALTS
  `(b·a* + 1)`, `k=a*` (parent keeps `b·a*·a*`, no child does); **C-DRAIN-2** RSTAR
  `(1+a)·c`, `k=1` (star re-entry form escapes). The corrected full-universe boundary
  makes the inclusion HOLD but **RALTS has zero budget slack** (`open_pot`/`apder_zw2`
  of RALTS are exactly Σ over children — nothing to pay the boundary). The master
  bound itself is still believed TRUE (300k). See `SUPER_LINEAR_PATTERNS.md` C-DRAIN,
  `GATE_BRIDGE_GAP.md` UPDATE 3.
- **CORRECTED ROUTE — verdict4 context-cover ledger (the bound) + verdict5 weak-carrier
  (the PROOF).** verdict4 (`GPT_PRO_GATE_BRIDGE_VERDICT3.md`) bounds the parent drain SIZE
  by the linear context-slot ledger `drain_ctxs p` (validated). Its #3/#4 cover PROOFS were
  deferred; the obvious additive acc-split was measured BOXED (line 34844). verdict5
  (`GPT_PRO_GATE_BRIDGE_VERDICT4.md`) gives the proof: a proof-only **`weak_child_drain`**
  carrier (S-FREE, non-collapsing `rsimp4` plug) + an **injective indexed-slot charge**, so
  each parent drain row gets its own paid slot (no `1+root` split). The strong cover #5 is a
  **mutual P/Q induction** (P=strong, Q=weak). VALIDATED depth≥5 (~660k checks, 0 in-fragment
  violations; W1 weak cover, W2/W3 RALTS bridge, W4/W5 RSTAR bridge; both CEs covered).
  ⚠ two caveats: weak acc S-FREE; guards `S p=p` (not just nf). Stack + lanes: STEER.md.
- **Current narrow instruction (2026-06-16):** the per-step drain-budget route (verdict4
  ledger + verdict5 weak-carrier + `child_ok`) is REFUTED (see the SUPERSEDED banner at the
  top of §2 and §4 entry 11). The live route is the **cube-shell potential bound** in STEER.md:
  the gate already reduces (all-green, no `sorry`) via `actual_gate_bridge_from_strong_opened_live_potential`
  (@35221) + `rsize_set_strong_opened_live_row_universe_le_potential` (@35010) to the cube-shell
  invariant `strong_opened_live_acc_potential r k ≤ (rsize r+rsize k)³ − (rsize k)³`. Leaves +
  RALTS + RSEQ cube-shell steps are GREEN; the ONE open piece is the **RSTAR cube-shell step**
  (the SAT saturation crux — `RSTAR_CUBE_SHELL_SKETCH.md`). All agents currently HOLD on the
  Isabelle side pending the user's design decision on SAT. Do NOT start any `child_ok` /
  ctx_bound / per-step-budget proof. ⛔ HISTORICAL (do not implement): the verdict5 stack —
  weak carrier + `weak_child_drain_charge`/`_ctx_bound`, #3 RALTS, #4 RSTAR, mutual-induction
  #5 + corollary #6. Do NOT use the BOXED additive acc-split (line 34844), nor the
  dead per-child membership. Do NOT re-attempt: the verbatim
  subset target, the opened-boundary/liveness original-root carriers, the square-sum
  or list-cost routes, the falsified unary/potential strengthenings, the old zwidth
  law, the first J* invariant, raw zw2, or `*_list_cost_alt_nodes`/generated-ledger
  wrappers (all dead). Stay on the legacy/non-backref, rntimes-free zw2 instance.
  Full dead-ends: `MATHPROBLEM_ROWCOUNT.md` + `GATE_BRIDGE_GAP.md`; full designs:
  `GPT_PRO_DLAW_VERDICT.md` (D law), `GPT_PRO_GATE_BRIDGE_VERDICT.md` /
  `GPT_PRO_GATE_BRIDGE_VERDICT2.md` (opened-boundary / drain — per-child ALTS/STAR
  now falsified).

## 3. Checked Facts to Reuse (never re-prove, search before adding)

| Fact | Plain meaning |
| --- | --- |
| `afactored1_strong_dlform_list_cost_cubic_false` | duplicated opened-LIST cost is NOT polynomial (RONE-pair tower witness, exponential) |
| `card_row_dlforms_le_rsize` | per row, distinct opened rows ≤ `rsize q` (linear, unconditional) |
| `rsize_set_row_dlforms_le_rsize_sq` | per row, opened set total size ≤ `(rsize q)^2` (quadratic, unconditional) |
| `rsize_set_row_dlformss_le_sum_rsize_sq` | union set ledger ≤ sum of per-row squares |
| `rsize_set_row_dlformss_rpder_strong_rows_raw_afactored1_le_sum_rsize_sq` | same, instantiated to the actual one-step output |
| `card_row_dlformss_le_rsizes` | union card ≤ total row size (one degree) |
| `card_row_dlformss_rpder_strong_rows_raw_le_generated` | actual-output union card ≤ generated total size |
| `rsizes_rpder_strong_rows_raw_le`, `rpder_strong_rows_raw_generated_budget` | one-pass rsizes deleter chain (GeneralRegexBound.thy) — do NOT re-derive |
| `rsizes_afactored1_rntimes_free_rsize_cubic` | NTIMES-free fragment: front total is cubic |
| `strong_derivative_front_terms_member_size_linear` | front member size is linear (`Suc (2 * rsize ...)`-shaped) |
| `rsize_set_split_rseq_tails_..._front_open_weighted_plus_active_alt_nodesI` and `..._front_weighted_plus_active_alt_nodesI` | weighted front/tail split interfaces |
| `raw_shared_prune_active_suffix_weighted_rseq_tails_..._le_pair_budget_list_cost` | active-suffix weighted tails paid by pair budget |
| `..._front_sum_plus_active_pair_budget_key_boundI` | newest pair-budget gate (see §2) |

(Exact long names live in `AntimirovFactoredTransition.thy` /
`GeneralRegexBound.thy`; grep before citing.)

## 4. Refuted or Dead — never spend effort here

1. **Duplicated opened-list cost** (`afactored1_strong_dlform_list_cost`,
   `row_dlforms_list_size`) as a polynomial target — REFUTED, exponential
   RONE-pair tower CE. Any route that needs a polynomial list cost is dead.
2. **Deep-frontier linear card** — `apder_deep_frontier_linear_card_false`:
   the premise `card (apder_deep_frontier r) <= apder_awidth r + rsize r + 3`
   is false in general (NTIMES multiplies alternation branches without paying
   into the budget). Only the NTIMES-free fragment version survives.
3. **Front-linear card** — checked counterexample (2026-06-12); do not try
   to discharge the front-linear premise universally.
4. **Generic owner-closure counting** — abstract owner exponential CE
   (2026-06-12); do not count owner closures generically.
5. **Subterm-deep carrier containment** — checked false (2026-06-12).
6. **Naive square-sum wrappers** — `sum q^2 <= rsizes rows * rsizes rows`
   and `length * max^3`-style products are true but lose a degree (quartic).
   Wrappers that do not exploit strong scan/prune sharing do not count.
7. **`bsimpCubic` emitted-tree route** — historical negative evidence: worse
   than thesis Chapter 7 baseline, and destructive sequence reassociation
   `(x.y).z -> x.(y.z)` breaks POSIX values. Do not optimize or revive.
8. **`rsimp9`** — historical only, not a payout artifact.
9. **`bsimpStrong` as a direct POSIX value candidate** — fails nested-star
   value CE (`STAR (STAR (CH a))` on `a`); it is a recognition gate only.
10. **`row_dlforms ⊆ apder_frontier`** — inclusion false; linear forms split
    `(a+b)c` while the whole-residual frontier stores `(a+b)c` and `c`.
11. **Per-step drain budgets — BOTH refuted in-regime (2026-06-16).** Neither
    `rsize_set(strong_child_drain p k) ≤ ctx_bound(drain_ctxs p) k` (TIGHT) nor
    `… ≤ drain_child_budget p k` (LOOSE / `child_ok`) holds at depth≥5. Named CEs: CE2
    (47>46), CE1 (64>60) break ctx_bound; CHILDOK rsize22 (99>96) breaks drain_child_budget
    too. `child_okD` @32981 only assumes `child_ok` — it is not a proof; nothing discharges
    `child_ok`, which is false. The overshoot grows ~quadratically with chain depth, so no
    constant / fixed multiplier / per-slot capacity fix to the ledger closes it. The whole
    verdict4-ledger + verdict5-weak-carrier + `master_cover` + `child_ok` family is dead. The
    deception datum (rand_clean 0/>10⁵ vs witness-family ~11%/~4.7%) is the reason this
    survived 9 refuted routes. Use the cube-shell potential bound instead (STEER.md). Repro:
    `scratch_ctxbound_target_FALSE_repro.py`, `witness_gen.py`. CE families in
    `SUPER_LINEAR_PATTERNS.md`.

If a plan needs one of these, stop and write the blocker in
`PROGRESS_BACKREF.md` instead of working around it silently.

**Companion-deliverable rule (admin, 2026-06-13).** Every entry in this §4,
and every counterexample that kills a conjecture/inequality/strengthening, is
ALSO a fuzzer-corpus deliverable. When you refute something, append the
concrete regex family (rrexp notation + parameterization + any fixed input),
what it killed, and the DECEPTION datum (how many samples / what depth it
passed before being caught) to `SUPER_LINEAR_PATTERNS.md` at the repo root — in
the same cycle you record it here. Never prune a CE because its conjecture is
dead; the deader the conjecture, the better the fuzzer input. This is additive
bookkeeping and must not slow the cubic proof. See the 2026-06-13 admin
directive in the PROGRESS tail.

## 5. Settled and Frozen (cite freely, do not re-derive, do not extend)

- **Backreference pilot chain — COMPLETE.** `BackRefLang.thy`
  (`xnullable_correctness`, `xder_correctness`, `xders_correctness`),
  `BackRefValues.thy` (`BL_flat_BPrf`, `blexer_correctness` with named
  None/Some/defined parts, POSIX lemmas), `BackRefBlexer.thy`,
  `BackRefGBlexer.thy`, `BackRefBitcodedSummary.thy`,
  `BackRefBoundedBlueprint.thy`. The bitcoded backref lexer EXISTS and is
  checked. Any instruction telling you to "create BackRefBlexer.thy" or
  "define the bitcoded backref lexer" is stale — ignore it.
- **Inherited Posix chain** (`Lexer.thy`, `Blexer.thy`, `BlexerSimp.thy`
  correctness incl. `blexer_correctness`, bsimp equivalence) — trusted
  completely; build on it, never re-prove.
- Statement freeze and the four guard scripts still apply (see §6).

## 6. Work Rules (the ones that actually keep output flowing)

Full text: `agent_hunt_pipeline/projects/posix-backref/CLAUDE.md`. The
high-yield core:

★. **Adversarial hand-proof BEFORE Python, before formalizing (admin rule,
   2026-06-20).** After decomposing a goal into hypothesis steps, for EACH
   step FIRST: (a) attempt the proof BY HAND — walk the actual induction /
   set-algebra, noting where it gets *unnatural*, which definition SHAPE it
   leans on, which case is fragile; (b) deliberately try to BREAK it — build a
   purpose-made MINIMAL counterexample driven by the definition shapes (σ7
   collapses ONLY a leading `a*·a*`; `rsimpStrong_ALTs_raw` prunes at the SET
   level; the `a*·a*` boundary; two branches sharing one star tail; a nullable
   head exposing the continuation). Only steps that pass BOTH (a *natural*
   hand-proof AND survival of a deliberate adversarial construction) are worth
   Python-confirming at scale and worth formalizing — if the best case isn't
   "every step goes through naturally," the plan isn't ready to execute.
   **Python CONFIRMS the hand-analysis (catches what you missed) + enforces
   the witness-family discipline; it NEVER substitutes for understanding — a
   "0 violations" with no hand-proof is a RED FLAG, not a green light.** Every
   refuted hypothesis here (ctx_bound 47>46, child_ok 99>96, the SAA-RALTS
   "+1" 2n>n+1, the per-branch `D(ALTS[q])≤D(q)+1` on `(1+a*)·b*`) had a SIMPLE
   shape-driven CE that hand-analysis kills in minutes; Python-only sampling
   burned whole sessions returning false `0/10⁵`. Bake this into every
   `pro_ask` prompt and worker instruction. (Memory: `feedback-adversarial-handproof-first`.)
0. **Report in plain math, not jargon (admin requirement, 2026-06-13).**
   Every `CHECKED` note in the PROGRESS tail must state the result as a math
   inequality/identity in plain notation (e.g. `card(apder_rows r) <= rsize r
   + 2`), with a ≤10-word plain-English gloss — NOT just the Isabelle lemma
   name. The single-page plain-math roadmap is `STATUS_MATH.tex/.pdf` (repo
   root); the secretary keeps it current so the admin can see which step
   we're on at a glance. When a milestone lands, update `STATUS_MATH` (move
   the `[→ CURRENT]` marker) and recompile.
1. **One small checked brick at a time.** Build after every meaningful
   change; commit only checked work; push promptly (within ~5 minutes when
   multiple agents are active).
2. **Search before creating.** Grep for existing lemmas/definitions first.
   Wrapper-only packaging is not progress and not bounty work.
3. **No idle waiting.** Do not wait for the other agent unless
   `scripts\codex-proof-workers.ps1 -Action Check` shows a live worker or
   `git status --short` shows tracked edits in your target region.
4. **One Isabelle build at a time (serial), or PRIVATE HEAPS (parallel).**
   For a SINGLE build use `scripts\codex-isabelle-build-posix.ps1
   -TimeoutSeconds 300` (per-session mutex). **For PARALLEL lanes (multiple
   worktrees/Codex building concurrently) EACH lane MUST set its OWN
   `ISABELLE_HOME_USER=<worktree>\.isa_home`** — concurrent builds against the
   SHARED heap store corrupt each other's PARENT heaps (`Posix_Cubic FAILED ...
   "parent ... saved state does not match"`, `SQLITE_CONSTRAINT_PRIMARYKEY`,
   "Duplicate export", rc127). The `.ps1` mutex keys on session NAME so it does
   NOT serialize different leaf sessions — they each rebuild the shared parent
   and clobber it. Private-home fix VALIDATED (a lane built green in its private
   store while another built on the shared store). First private build ~2min
   (rebuilds the chain); then isolated + fast. gitignore `.isa_home/`. Bake the
   private-home build command into every parallel-lane brief. (Memory:
   `posix-parallel-build-private-heaps`.) `SQLITE_CONSTRAINT_PRIMARYKEY` is a
   build-database collision, not a false theorem.
5. **Red background shell = proof failure, not shell failure.** Read the
   first `*** Failed to finish proof` block, change ONE small named lemma,
   rebuild. Never queue a second build while the first failing goal is
   unchanged.
6. **Proof performance budget.** `auto`/`simp`/broad search should return in
   ~0.5 s; 1–2 s on a line is debt; 30 s means narrow it; 200 s means the
   structure is wrong. Split into named helper lemmas instead of raising
   timeouts.
7. **Preserve proof shape before automation.** Case-split on the relevant
   constructor first; broad `auto` on an undigested goal destroys the state.
8. **Never throw away useful work.** No `git reset --hard`, no reverts
   without salvage, justify any file shrink in the commit message
   (`git diff --stat HEAD~1`).
9. **No `sorry`/`oops`/axioms/statement weakening.** Statement freeze is
   enforced by `backref_statement_guard.py`; run all four guards before
   pushing (`backref_bounty_guard.py`, `backref_no_cheat_guard.py`,
   `backref_role_guard.py`, `backref_statement_guard.py`).
10. **Update the PROGRESS tail after every meaningful step** — branch,
    commit, build result, theorem status, next smallest step, blockers. The
    PROGRESS tail is also the inter-agent coordination channel: claims,
    corrections, and route gates are posted there.
11. **If a statement seems false, stop and refute or record** — do not force
    a proof. Checked counterexamples (like the RONE-pair tower) are paid,
    first-class results.
12. **Smoke before proof** for any NEW simplifier/algorithm candidate:
    `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1` (exact POSIX values
    mandatory). The current set-ledger route needs no new smoke unless the
    algorithm itself changes.

## 7. Roles and No-Touch Zones (current run)

- **Fable (Claude code session)** — proof worker on the set-ledger gate.
- **GPT-5.5 (Codex CLI)** — supervisor: route gating, duplicate-effort
  pruning, corrections, handoffs.
- **Secretary session (this one)** — documentation, status, cleanup; does
  not edit `.thy` files.
- ACTIVE no-touch zones (per the 2026-06-12 orientation note in PROGRESS):
  tail half of `AntimirovFactoredTransition.thy`, tail of
  `PROGRESS_BACKREF.md`, `BACKREF_BOUNTIES.md` balances/overlay,
  `scratch_dlform_cost_model.py`, `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`.
- Shared branch `codex/backref-values`; sync with
  `git pull --rebase --autostash origin codex/backref-values`.

## 8. Session Start Checklist (fresh chat or after compaction)

1. Read this file (only this file).
2. `git pull --rebase --autostash origin codex/backref-values`, then
   `git status --short --branch` and the last ~10 commits.
3. `powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check`
4. Read the LAST ~200 lines of `PROGRESS_BACKREF.md` (never the whole file).
5. Continue the narrowest open instruction (currently §2's pair-budget
   premise) or the newest supervisor instruction in the PROGRESS tail.
6. Look up details only when needed, through `DOC_INDEX.md`.

Token discipline: do NOT load `DESIGN_LOG.md`, the pre-06-11 PROGRESS
archive, old handoffs, or `agent_hunt_pipeline/projects/posix-backref/archive/`
into context unless you are answering a specific historical question.
