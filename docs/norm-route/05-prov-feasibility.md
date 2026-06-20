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

## ⚠ The linchpin that MUST get a rigorous hand-proof (do NOT formalize before this)
**Claim L:** for clean r,k, `strong_apder_acc r k` holds ≤ 1 non-normal row per N-value.
Plausible argument: (i) S/σ7 collapses every *leading* adjacent-equal-star pair; (ii) the only
surviving pair in an opened row is the single boundary where a non-collapsible head protects a
continuation whose leading star equals the source's trailing star — one σ4 boundary, one pair;
(iii) hence one duplication site, position fixed by the head; (iv) two non-normal rows with the
same N-value would need the same head-protected boundary ⇒ equal. **Step (iv) is not yet
rigorous** — "0 violations exhaustive to rsize 8" is exactly the kind of result this project has
been burned by (ctx_bound, child_ok). Treat as RED until the hand-proof closes (iv), and re-run
the hunt at rsize ≥ 11 and on more witness variants.

## If L holds, the Wave plan SIMPLIFIES dramatically
- Drop the `prov` datatype; Wave 5 = prove Claim L + the bit-injection card bound.
- Still need: Wave 1B (`nstrong`/`nalts`), Wave 2B (`nacc` defs + the 3 clean recurrences —
  validated), Wave 3 (`card(nacc r 1 − nbase 1) ≤ C·rsize r`, ratio bounded/decreasing),
  Wave 4 (the shadow — validated). Then Wave 5 (Claim L + injection) closes the linear bound.
