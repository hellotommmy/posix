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
