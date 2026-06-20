# 05 — Wave-5 (provenance injection) FEASIBILITY verdict

**Status: VIABLE, via a much simpler device than planned — but the linchpin needs a
rigorous hand-proof before formalizing.** Harness: `experiments/norm/wave5_probe.py`
(faithful `strong_apder_acc` + `apder_term_frontier_acc` + the new `nacc`/`nterm_acc`).

## The surprise: the provenance is a SINGLE BIT, not the §10 datatype
route2_verdict §10 plans an elaborate `prov` datatype (`PSeqL/PSeqR/POpenAlt/PPrune/…`).
The probe says that is unnecessary. The injection that works is

> **`x  ↦  (N x = x,  N x)`  :  strong_apder_acc r k − strong_apder_acc RONE k  →  {Root,Debt} × nacc(r, N k)`**

i.e. tag each old row with a single bit: *is it already N-normal?* This is injective and
has linear-card image, **provided** the linchpin below holds.

## What the probe established (all 0 violations unless noted)
1. **Clean nacc recurrences** (Wave 2B) — `nacc(RSEQ r1 r2)k ⊆ nacc r1 (α(N r2,k)) ∪ nacc r2 k`,
   `nacc(RALTS rs)k ⊆ ⋃ nacc q k` (**NO `+1`** — the historical killer), `nacc(RSTAR …)`.
   0 / 56 217. NATURAL: α collapses the very `a*·a*` rows σ7 left uncollapsed, so the new
   universe has no cross-prune residual to leak.
2. **Old→new shadow** (Wave 4) — `x ∈ strong_apder_acc r k ⟹ N x ∈ nacc r (N k)`. 0 / 149 556.
3. **≤ 1 non-normal old row per N-fiber** (the injectivity linchpin) — EXHAUSTIVE over
   337 383 (r,k) pairs (clean r ≤ rsize 8 × continuations incl. `a*·a*`, `a*·a*·a*`, `b*·b*`),
   all hand-built "double-uncollapse" candidates, AND the **witness family that made
   `child_ok` 99>96** (nested frames over `a·b*`) to depth 10. Max = **1**, never 2.
4. **Structural reason for (3)** — every non-normal old row has **exactly one** adjacent-equal-
   star duplication, of run length **exactly 2** (max sites = 1, max run = 2 over 2 745 rows).
   So a non-normal `x` is `C[s*·s*]` with `N x = C[s*]`; it is pinned by `N x` + the (forced)
   site.
5. **Linear, k-independent card** — `card(diff) = #normal-excess + #debt`; worst
   `normal-excess/rsize = 1.00`, `debt/rsize = 0.25`; both grow linearly on the witness family
   (each `= 2d+1`, rsize `= 8d+6`). normal-excess injects by identity into `nacc(r,Nk)`;
   debt is the bit's 2nd slot. ⇒ `card(strong_apder_acc r k − strong_apder_acc RONE k) ≤ C·rsize r`.

## Why this ESCAPES the wall that killed verdict7/8/cand2/childok
Those routes tried to assign a key/slot to the OLD cross-prune survivors — impossible, the
survivor has no local owner (the prune is global/order-dependent). The N-route never keys
them: N **collapses** the survivor (`b*·(a*·a*) ↦ b*·a*`) and a single bit recovers the lost
copy, because the lost multiplicity is provably **≤ 2** (≤1 normal + ≤1 non-normal per fiber).
The debt is computed from `N r_i` **locally**, never from the cross-prune.

## ⚠ The linchpin = Claim L — robust, but the easy proof is REFUTED (it is the new crux)
**Claim L:** for clean r,k, `strong_apder_acc r k` holds ≤ 1 non-normal row per N-value.
Equivalently: `N` restricted to the non-normal rows of the carrier is injective. If L holds,
the non-normal rows inject (via `N`) into the clean linear universe `nacc`, so **#debt is
linear** (the otherwise-hard count) and the linear card bound follows.

**Deep hunt (extended):** L holds on **2.8M+ checks** — exhaustive clean r ≤ rsize 9 × RICH
multi-star continuations (2 707 350), random r ≤ rsize 14 (120 000), AND nullable-**telescope**
constructions built specifically to realise two junctions for one `v`. Max non-normal-per-fiber
= **1** everywhere.

**Model verified faithful:** the surprising leading-dup row `a*·a*·b*` (∈ carrier of
`((1+a)·a*+b)·(a*·b*)`) is CORRECT per the verbatim defs — a RALTS-headed factor makes σ7 fall
through to the WEAK σ4 plug, which builds `a*·a*` uncollapsed deep in the row_dlforms recursion,
and the nullable `1` branch exposes it leading. So the data is trustworthy.

**The clean structural proof is DEAD.** I conjectured the dup is always trailing (⇒ `x = N(x)`
with last star doubled ⇒ L). **Refuted:** dups occur at varying spine positions — 30 723 are
NON-trailing (incl. leading; headlen ∈ {0,1,2}). So `v` alone does NOT fix the dup position;
L holds only because the *carrier* realises a single doubling per `v` — a derivative-path
property, not a syntactic one.

**Honest status:** L is the most robust card-bound lead this project has had (every prior route
was refuted; L survives every adversarial probe), BUT it is **UNPROVEN** and the obvious proof
failed. A real proof likely needs the **Antimirov partial-derivative position** structure (each
non-normal row ↔ a unique active star-junction; thesis Ch7 / AFP). Treat as RED: do not
formalize the bit-injection until L (or a bounded-multiplicity weakening) is hand-proved or sent
to Pro as a focused micro-ask. Re-hunt at rsize ≥ 16 opportunistically.

## If L holds, the Wave plan SIMPLIFIES dramatically
- Drop the `prov` datatype; Wave 5 = prove Claim L + the bit-injection card bound.
- Still need: Wave 1B (`nstrong`/`nalts`), Wave 2B (`nacc` defs + the 3 clean recurrences —
  validated), Wave 3 (`card(nacc r 1 − nbase 1) ≤ C·rsize r`, ratio bounded/decreasing),
  Wave 4 (the shadow — validated). Then Wave 5 (Claim L + injection) closes the linear bound.
