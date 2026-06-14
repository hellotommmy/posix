# Gate-bridge gap: the final degree-collapse (OPEN, 2026-06-13)

The D law (row-count linearity) and the cubic STATIC FRONT are proven. The §1
set-ledger cubic gate is NOT yet closed: there is one genuine missing bridge — a
DESIGN point, not assembly (recorded by Codex, commit 3e8f5e5). This file states
it precisely for a fresh design pass. Notation + all symbol definitions:
`STATUS_MATH.pdf`. Full pipeline + the refuted list-cost route: `CUBIC_OPEN_PROBLEM.pdf`.

## The goal (the §1 gate)

```
rsize_set( row_dlformss( rpder_strong_rows_raw c (afactored1 r s) ) )  <=  2*(rsize r + 3)^3
```
In words: take the normalized front after reading `s` (`afactored1 r s`), apply
ONE strong simplify+prune step on the next letter `c` (`rpder_strong_rows_raw`),
open every resulting row into linear forms and DEDUPLICATE across the whole union
(`row_dlformss`), and sum the sizes of the distinct opened rows (`rsize_set`).
That total must be cubic in `rsize r`, uniformly in `s`.

## What is already PROVEN (checked, clean fragment)

1. Cubic static front (uniform in s):
   `apder_clean r ==> rsizes (afactored1 r s) <= (rsize r + 3)^3`.
2. Strong step does not grow size:
   `rsizes (rpder_strong_rows_raw c rows) <= rsizes (concat (map (rpder_norm_list c) rows))`.
3. Opened SQUARE ledger:
   `rsize_set (row_dlformss raw) <= sum_list (map (%q. rsize q * rsize q) raw)`.
4. Opened CARD:  `card (row_dlformss raw) <= rsizes (generated)`.
5. Containment into the dlform-closure carrier:
   `row_dlformss (rpder_strong_rows_raw c (afactored1 r s))
      <= rsimpStrong_dlform_closure (set (afactored1 r (s @ [c])))`.
6. Closure opening (per-row sum):
   `rsize_set (rsimpStrong_dlform_closure U)
      <= (SUM p in U. rsize_set (row_dlforms (rsimpStrong_raw p)))`.
7. A nonincreasing-closure lemma exists for `rsimpStrong_FRONTIER_closure`,
   but NOT for the `dlform` closure that the gate actually needs.
8. Each row is small: `card (apder_rows r) <= rsize r + 2` (linearly many rows)
   and each member has `rsize <= (rsize r + 2)^2` (quadratic).

## The GAP (proving EITHER one closes the gate)

```
(i)   sum_list (map (%q. rsize q * rsize q) (rpder_strong_rows_raw c (afactored1 r s)))
        <= 2*(rsize r + 3)^3
(ii)  rsize_set (rsimpStrong_dlform_closure (set (afactored1 r (s @ [c]))))
        <= 2*(rsize r + 3)^3
```

## Why the obvious routes FAIL (this is the crux)

- **Square-sum is too lossy.** By (8), rows number ~linear and each has size
  ~quadratic, so `sum (rsize q)^2 ~ linear * quartic = QUINTIC`, while the front
  TOTAL `sum (rsize q)` is only cubic (1). The square ledger (3) throws away the
  deduplication and is a genuine 2 degrees too weak.
- **The LIST (non-deduplicated) opening genuinely blows up.** Opening without
  the cross-row union is EXPONENTIAL — the RONE-pair tower, checked refutation
  `afactored1_strong_dlform_list_cost_cubic_false` (see `SUPER_LINEAR_PATTERNS.md`
  A1: list length `3*2^n - 2` against linear regex size). Only the SET/deduped
  union survives, because shared suffix-tails MERGE.
- So the missing bridge **must exploit deduplication / suffix-sharing**: the
  deduped opened union is cubic even though the per-row square-sum is quintic and
  the list is exponential. The degree must come from sharing, not from per-row
  accounting.

## The ASK

Design the degree-collapsing bridge — a checkable statement and proof sketch
that the DEDUPED opened union
`rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))` is cubic,
OR equivalently that the `dlform` closure has the cubic/nonincreasing property
the `frontier` closure already has. The D law was cracked by finding the right
invariant (a telescoping boundary); this needs the analogous SHARING invariant
for the opened ledger. Concretely:

1. What shared structure across the opened linear forms (e.g. common
   suffix-tails / a bounded set of distinct tails, each appearing under boundedly
   many heads) makes the deduplicated union cubic while the multiset is not?
2. State it as a checkable Isabelle bound (the carrier, the invariant, the
   per-constructor or per-step discharge), reusing the checked facts (1)-(8)
   where possible.
3. Flag any place the clean-fragment / rtail-nf distinction matters (the
   strong-frontier rows are only `rtail_nf`, not fully clean).

Respect the refutations in `CUBIC_OPEN_PROBLEM.pdf` §6 and
`SUPER_LINEAR_PATTERNS.md` (the list-cost / square-sum routes are dead as stated;
any bound must be on the deduplicated set).

---

## UPDATE 2026-06-14: the verdict's carrier-preservation step is FALSE as stated (checked CE)

Executing the opened-boundary verdict, the agent hit a genuine, machine-checked
obstacle. The verdict's section-5/7 "carrier preservation" — that strong rows
stay inside the clean opened-boundary carrier — is FALSE as literally stated.

Checked lemma `rsimpStrong_dlform_closure_opened_boundary_carrier_false`:
```
r   = RSTAR (RALTS [RCHAR a])     -- clean (apder_clean r holds)
bad = RSTAR (RCHAR a)
odfront RONE UNION opened_boundary_forms r RONE  =  {RONE, r}
bad : rsimpStrong_dlform_closure (set (afactored1 r []))     -- in the strong closure
bad NOTIN {RONE, r}                                          -- but NOT in the carrier
```
MECHANISM: the strong simplifier collapses the singleton alternation
`RALTS [RCHAR a] -> RCHAR a`, so `rsimpStrong_raw r = RSTAR (RCHAR a)`. That
strong-normalized row is not SYNTACTICALLY in the carrier, which only holds the
unsimplified `r`. The strong rows live in a DIFFERENT normal form (rtail_nf /
strong-normalized) than the clean carrier. The verdict gestured at this in
section 7 ("compare tails in the same normalized representation") but did not make
it precise; this CE pins it down.

THE DESIGN QUESTION FOR THE NEXT PASS:
Revise the carrier so the strong rows ARE contained, without losing the cubic
bound. Candidate directions (need a holistic check):
- Build the carrier over the STRONG-NORMALIZED root `rsimpStrong_raw r` (or close
  the carrier under the strong rewrites: singleton-ALT collapse, rflts, rdistinct,
  the prune). Since `rsimpStrong_raw` is root-size-non-increasing, a cubic bound in
  `rsize (rsimpStrong_raw r)` would transfer to `rsize r`.
- OR strengthen the root normal-form assumption to exclude singleton/degenerate
  alternations that the strong simplifier would collapse (a stronger normal form
  than `apder_clean`), IF the actual gate roots already satisfy it.
- Watch the interaction with the checked `rsimpStrong_raw_row_dlforms_cost_not_monotone`
  (the strong simplifier can INCREASE the opened SET ledger of a single row), so a
  per-row size-monotonicity argument will NOT work; the bound must be on the
  normalized carrier as a whole.
Constraint: still set-native, deduped, clean/rntimes-free fragment; respect all
refutations in CUBIC_OPEN_PROBLEM.pdf §6 and SUPER_LINEAR_PATTERNS.md.
---

## UPDATE 2 (2026-06-14 11:20): liveness is ALSO false; the viable carrier is the drain carrier over NORMALIZED rows

Both "original-root" routes are now checked-false by the SAME mechanism:
- opened-boundary carrier over the original root: `rsimpStrong_dlform_closure_opened_boundary_carrier_false`.
- liveness live-row-universe over the original root: `row_dlformss_actual_not_subset_live_row_universe_original_false`
  (same `RSTAR (RALTS [RCHAR a])`), and even over `rsimpStrong_raw r` it is false for an opened continuation
  (`([1|a].([1|a].c))` opens to `(a.c)`, absent from the normalized live-row universe).

Root cause (common to both): the strong simplifier NORMALIZES rows (singleton-ALT
collapse, flatten, dedup, prune), so the strong rows live in a representation that
no carrier/universe computed over the ORIGINAL root contains.

VIABLE ROUTE (already largely built by the agent): the **drain carrier over the
CURRENT normalized `afactored1 r s` rows** (`strong_opened_live`), into which the
actual gate rows are CHECKED to fall. Per-constructor containments
(RCHAR/RSEQ/RALTS/RSTAR/RONE) and root-potential base cubics are checked.

THE REMAINING DESIGN QUESTION (this is the real ask): design the **STAR-compatible
recursive CHILD invariant / potential** for the drain root-potential. The generic
drain induction is too coarse — a coarse child `2*(rsize+3)^3` sum leaves NO root
budget for the RALTS / RSTAR parent. Need a child-level invariant (an `open_pot`-
style potential charged so that RALTS sums and the RSTAR re-entry leave the parent
enough budget) that closes the conditional RALTS/RSEQ/RSTAR root-cubic wrappers
already in place. Sample at depth>=5 before Isabelle; constants are tunable.

---

## UPDATE 3 (2026-06-14): the per-child SET-containment route is CHECKED-FALSE for RALTS/RSTAR (secretary-verified)

Executing UPDATE 2's drain carrier (verdict2/§4), the §5 drain ARITHMETIC is
DONE/green (`drain_pot_le_cubic_core`, `drain_child_budget_root_cubic`) and the §4
per-child SET-containment is PROVEN for SEQ/CHAR (Codex; RCHAR green). But the
per-child telescoping INCLUSION `parent drain ⊆ ⋃ child drains` is machine/sample
checked-FALSE for RALTS and RSTAR, and the secretary independently verified the
MECHANISM against the real Isabelle definitions (not a sampling/model artifact):

- `rsimp7_SEQ_atom` (BasicIdentities.thy:414-421) has a deliberate guarded rule
  `(RSTAR r, RSTAR s) ⇒ if r=s then RSTAR r` (and prefix variant
  `(RSTAR r, RSEQ (RSTAR s) k) ⇒ if r=s then RSEQ (RSTAR r) k`) that collapses
  `a*·a* → a*`. `rsimp4_SEQ_atom` (BasicIdentities.thy:287-300) does NOT collapse
  it (`RSTAR r, r2 ⇒ RSEQ (RSTAR r) r2`). The parent row glues each child to the
  SAME continuation via `rsimp7_SEQ_atom`, so which pairings trigger the `r=s`
  guard differs between the child-normalized term and the parent row term.
- **C-DRAIN-1 (RALTS)**: parent `(b·a* + 1)`, `k = a*`.
  `strong_child_drain (RALTS [b·a*, 1]) a*` contains `b·(a*·a*)` (rsize 7); no
  child drain does — the child `nseq (b·a*) a*` reassociates and `a*·a*→a*`
  collapses it to `b·a*` (rsize 4).
- **C-DRAIN-2 (RSTAR)**: body `p = (1+a)·c`, `k = 1` (+ nested-star variants).
  `strong_child_drain (RSTAR p) k` keeps a star re-entry form
  `c·(((1+a)·c)*·…)` that escapes `star_entry p k ∪ child drain`.

WHY THE OBVIOUS PATCHES FAIL (both characterized):
- **row_dlforms boundary** (single parent opened row added): still FALSE for RSTAR.
- **full-universe boundary** (`strong_opened_live(nseq …) − strong_opened_live(S k)`):
  the inclusion HOLDS for both RALTS and RSTAR (0/40000), BUT cannot be PAID:
  `apder_zw2 (RALTS rs) = Σ apder_zw2` and `open_pot (RALTS rs) = Σ open_pot`
  EXACTLY (AntimirovFactoredTransition.thy:29673, 29702) — RALTS has **zero
  constructor slack**, so the extra boundary row's `rsize` has nowhere to be paid.
  (RSEQ/RSTAR DO carry slack — `apder_zw2 r1*(rsize r2+2)`, `Suc(zw2)*(rsize+2)` —
  RALTS alone does not.)

KEY POINT: the master bound `strong_child_drain_potential` is still believed TRUE
(300k samples, zero violations) — a proof EXISTS, just not via per-child ALTS/STAR
containment. The algebra `(a+b)·k = a·k + b·k` holds, but the strong-normaliser
does NOT distribute `·` over `+` (it wraps `RSEQ (ALTS …) k`) and DOES collapse
`a*·a*→a*`; per-child telescoping assumes left-distribution commutes with
star-idempotence, which is false.

THE CORRECTED ASK (GPT Pro pass): design a **non-telescoping ALTS/STAR account** —
bound the parent drain `rsize_set` DIRECTLY within `drain_pot p + drain_w p*(1+rsize k)`,
without requiring each parent opened row to land in a child drain. RALTS is the
hard case (zero slack): the account must absorb the un-collapsed `a*·a*`-type
parent rows into the children's *budget* even though they are not in the children's
*drain sets*. Reuse the PROVEN SEQ/CHAR containment and the GREEN §5 arithmetic;
the TRUE full-universe inclusion (above) is available as a building block.

---

## UPDATE 4 (2026-06-14): GPT Pro verdict4 — the context-cover ledger — ANSWERS it (validated)

GPT Pro returned the corrected design (`GPT_PRO_GATE_BRIDGE_VERDICT3.md`). It is
exactly the tail-incidence answer the UPDATE 3 ask asked for: bound the parent drain
SIZE, not its membership.

THE DESIGN: a linear ledger of one-hole right contexts
  `drain_ctxs p :: (rrexp × nat) list`  — one slot per `drain_w` unit (one per char,
  one per star re-entry), with each slot carrying a DECLARED cost
  `ctx_extend q hc = (rsimp7_SEQ_atom (fst hc) q, snd hc + (1 + rsize q))`.
The declared cost (NOT `rsize (raw_plug …)`) is the whole trick: when `rsimp7`
collapses `a*·a*→a*` in a child, the slot still charges for the consumed suffix. So
a parent opened row is SIZE-COVERED by a child context slot even though it is not a
MEMBER of any child drain. RALTS needs no new credit because `drain_ctxs (RALTS rs)`
is just `concat` of the children's ledgers — additive exactly like `drain_pot` and
`apder_zw2`. RSTAR adds one entry slot + extends every body slot by the declared
`RSTAR p` suffix (`W+2` slack, as the prior memo's star arithmetic).

  rsize_set (strong_child_drain p k)  ≤  ctx_bound (drain_ctxs p) k
                                      ≤  drain_pot p + drain_w p * (1 + rsize k)

(the second `≤` from `ctx_count ≤ drain_w` and `ctx_base ≤ drain_pot`).

WHY THE CEs ARE PAID:
- C-DRAIN-1: `b·(a*·a*)` (rsize 7) is charged to the slot of head `b·a*` (base 4)
  plus continuation `1 + rsize k = 3` → `4+3 = 7` exactly.
- C-DRAIN-2: the escaped star re-entry row is charged to a body slot extended by the
  declared `RSTAR p` suffix (`map (ctx_extend (RSTAR p)) (drain_ctxs p)`).

VALIDATION (secretary, depth≥5, 2026-06-14): three independent harnesses over the
faithful model (each passing the RCHAR-sanity gate + a transcription self-test),
ZERO violations across ~580k cases — the two static lemmas, the RALTS cover, the
RSTAR step/cover, the master `strong_child_drain_ctx_bound`, and the corollary all
hold; both C-DRAIN cases now PASS (C-DRAIN-2 tight, slack 0). 6-lemma implementation
stack in verdict4 §5; lane split in STEER.md. This is the route being implemented.

---

## UPDATE 5 (2026-06-14): the #3/#4 cover PROOFS — verdict5 weak-carrier + injective slot charge (validated)

verdict4 gave the context-cover BOUND (validated) but deferred the #3/#4 cover PROOFS.
The obvious additive acc-split via `rsize_set_strong_opened_live_row_universe_acc_RALTS_le`
(line 34844) was measured BOXED: it bounds the parent SUBADDITIVELY (`1 + wrapped-root +
Σ children`) on top of the already-full child ledgers (`Σ child ctx_bound == ctxR`), so the
`1 + root` term has nothing to charge against (0/60000 close; deficit always `1+root`).

GPT Pro verdict5 (`GPT_PRO_GATE_BRIDGE_VERDICT4.md`) is the corrected PROOF. The move:
insert a proof-only **weak carrier**
  `weak_child_drain p k = (⋃ (h,_)∈drain_ctxs p. row_dlforms (rsimp4_SEQ_atom h k)) − row_dlforms k`
(the NON-collapsing `rsimp4` plug — NOT `rsimpStrong`), and prove an **injective indexed-slot
charge** `weak_child_drain_charge` mapping each weak row to a distinct paid slot with
`rsize x ≤ slot_cost p k (ch x)`. Then `weak_child_drain_ctx_bound` uses subadditivity ONLY
AFTER every row has a slot (no free-standing `1+root`). #3 = `strong_child_drain (RALTS rs) k
⊆ ⋃_q weak_child_drain q k` then the slot bound; #4 = the analogous `star_entry_drain ∪
weak body`. The strong cover #5 is a **mutual P/Q induction** (P=strong, Q=weak); the old
route used P on children and lost the uncollapsed parent row — Q's root clause is exactly the
`rsimp4` plug the parent opener exposes. The CE `b·c*·c*` is charged to the child slot
`(b·c*,4)` extended by k = `4+(1+2)=7` via the weak plug (where the strong child collapsed it).

VALIDATION (secretary, depth≥5, 2026-06-14): 3 harnesses over the faithful model, ~660k
checks, 0 in-fragment violations — W1 weak cover (138852), W2/W3 RALTS bridge (359932),
W4/W5 RSTAR bridge + entry cost (164866); both CEs covered (C-DRAIN-2 tight, slack 0).

TWO IMPLEMENTATION CAVEATS (validation-found): (1) the weak acc must be S-FREE — applying
`rsimpStrong_raw` inside the weak opening collapses `a*·a*` and the duplicate row breaks the
injective charge (measured: 4 in-fragment CEs). (2) Guards must be `S p = p` / `S k = k`, not
just `rtail_nf`/`nf` (nf accepts nested stars on which the inclusions fail). The implementation
stack + lane split is in STEER.md; this is the route being implemented.