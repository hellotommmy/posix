# GPT Pro micro-ask — verdict7 node→cost-token flow is REFUTED by ONE CE (closest route yet)

**Date:** 2026-06-15. **Status:** verdict7 (budgeted collapse trace, node→cost-token
charge with a source-star slot) was validated as a divisible max-flow feasibility problem
(`scratch_verdict7_flow_feasibility_check.py`) and **REFUTED at depth≥5 by a single CE**.
This is the closest any route has come (9 routes now dead), so the ask is narrow: patch the
ONE residual overload, not redesign.

## The target (unchanged, still TRUE)

`rsize_set(strong_child_drain p k) ≤ ctx_bound(drain_ctxs p) k`, for `S p = p`, `S k = k`,
in-regime, depth≥5. **G2 sanity gate GREEN: 0 violations / 20000.** The TOTAL budget always
covers; the obstruction is always *how to distribute* it injectively/feasibly.

## What verdict7 proposed (and what the validator implemented faithfully)

Charge at the SYNTAX-NODE → COST-TOKEN level, not rows→slots. Sources = deduped strong rows
`x` (supply `rsize(x)`); sinks = `drain_ctxs` slots `i` (capacity `slot_cost = snd(dc[i]) +
(1+rsize k)`). Edges:
- **base two-route:** `x→i` if `x ∈ weak_slot_rows(p,k,i)` (uncollapsed `x=y`) OR `x ∈
  row_dlforms(S y)` for some `y` in slot `i` (`x` is the collapse of `y`).
- **verdict7 source-star addition:** when `y→x` is an `a*·a*→a*` absorption with freed star
  `sa`, also add `x→j` for every slot `j` whose head **is** `sa` or **is** `SEQ(sa,_)`
  (the source-star slot). Applied to BOTH the short collapsed row (sc1) and the long
  uncollapsed predecessor that still carries `a*·a*` (sc2).

The hope: the short collapsed row + its long predecessor draw DISJOINT atoms (ordinary slot
+ source-star slot), dissolving the row→slot Hall collision (the CE `p=a+b*·a*, k=a*` that
killed the two-route injection).

## Validation result — VIABLE in 40851/40852, REFUTED by 1

```
[NO   source-star] tested=40852  feasible=40827  INFEASIBLE=25   (Hall bites, as expected)
[WITH source-star] tested=40852  feasible=40851  INFEASIBLE= 1   <-- ONE residual CE
```

The source-star edge fixes 24 of the 25 base failures. The surviving CE (k = `b*`):

```
p = ((((a*·((c·(b·b))+1+(b·b)*+(b·c)))
      +((a+1+b)*·(((1+c)·a)+1+(a·b*)))
      +a)·((1+(a·b))·b*))
    +((1+b*+c+a)·(1+((1+((b+1)·(1+b)))·(b+1)))))
k = b*
flow = 251 / 295   (INFEASIBLE)
```

**Violated Hall cut** (supply 110 > capacity 98), 4 rows reaching only slots {0,10,16,21,23}:

```
T = { (a+1+b)*·( body1 ·((1+(a·b))·(b*·b*)) ),     <- long  (uncollapsed b*·b*)
      a*    ·( body2 ·((1+(a·b))·(b*·b*)) ),        <- long
      (a+1+b)*·( body1 ·((1+(a·b))·b*) ),           <- short (collapsed b*·b*→b*)
      a*    ·( body2 ·((1+(a·b))·b*) ) }            <- short
   body1 = ((1+c)·a)+1+(a·b*)        body2 = (c·(b·b))+1+(b·b)*+(b·c)
```

## Sharp diagnosis (the SAME failure mode, pushed one level down)

The collapse here is `b*·b* → b*`, and `k = b*`. There are TWO parallel star-children
(`a*` and `(a+1+b)*`) that EACH produce a `b*·b*` tail through the shared continuation
`·((1+(a·b))·b*)`. Both the long (`·b*·b*`) and short (`·b*`) variants of BOTH children
charge to the **same single source-star slot for `b*`** (the only slot whose head is `b*`
or `SEQ(b*,_)`). That one slot's capacity (plus the few ordinary slots reachable) totals 98,
but the 4 rows supply 110. **The row→slot Hall collision verdict7 dissolved has reappeared as
a node→source-star-slot collision: parallel children collapsing via the *same* star all pile
onto the one source-star slot for that star.** The atom-level disjointness only separates a
row from *its own* predecessor; it does not separate *sibling* rows that share a freed star.

## The micro-ask

The total budget is sufficient (G2 green) — so feasibility must be recoverable with a better
edge/capacity rule. Pick ONE, or tell us none works and why:

1. **Per-occurrence source-star slots.** Is the source-star slot genuinely unique per star
   `sa`, or can the charge be split across the *distinct syntactic occurrences* of `sa·sa`
   (one collapse event per child)? If `drain_ctxs` exposes a separate slot per occurrence of
   the doubled star, the 4 rows split 2+2 across two source-star slots and the cut relaxes.
   Does the faithful `drain_ctxs`/`slot_cost` already provide enough such slots, or does the
   charge need to target the *child's own* entry slot rather than the global `b*` slot?

2. **Capacity top-up from the freed-factor budget.** The `+(1+rsize k)` term in `slot_cost`
   is a per-slot constant. With `k=b*`, the collapse frees a `b*` whose `rsize` (≈ `1+rsize k`)
   is exactly the disjoint atom verdict7 wants. Should the source-star slot's capacity be
   `snd(dc[j]) + (#collapse events routed to j)·(1+rsize k)` rather than a flat `+ (1+rsize k)`?
   i.e. is the per-event freed-star budget being undercounted when one slot absorbs many events?

3. **Different atom accounting.** If neither holds, the divisible flow shape itself is wrong
   for shared-star parallel children, and we need a non-flow argument (a direct size-decrease
   ledger keyed on collapse events, summed over children) — please sketch it.

**Constraints:** answer must survive the CE above (k=b*, two parallel star-children sharing
the `b*·b*` tail) AND the prior killer (`p=a+b*·a*, k=a*`). Faithful model + this CE are in
`scratch_verdict7_flow_feasibility_check.py`; reuse its `drain_ctxs`/`slot_cost`/`weak_slot_rows`.
Do NOT propose any injective row→slot charge or strong⊆cover set-containment — 9 such routes
are refuted (see PROGRESS_BACKREF.md / STEER.md).
