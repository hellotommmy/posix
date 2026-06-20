## Verdict

I found **no counterexample** to L1, L2, STEP, GLOBAL, or TARGET in the completed search spaces. The strongest adversarial family I hit still behaved exactly as the design predicts: the old `+1` RALTS shortcut fails, but the singleton-cover plus singleton-size budget survives.

I did **not** complete exhaustive search to rsize 12–14. The completed spaces below are the ones I actually finished and can report. I included the harness and a JSON result summary:

* [Python harness](sandbox:/mnt/data/regex_redteam_harness.py)
* [Results JSON](sandbox:/mnt/data/regex_redteam_results.json)

The task asked for a faithful Python model of `rsize`, `s4`, `s7`, the strong-prune chain, `S`, `row_dlforms`, `apder_terms`, `strong_apder_acc`, `apder_strong_dlfrontier`, `apder_nf`, and `apder_clean`, then to hammer L1/L2/STEP/GLOBAL/TARGET.  I modeled the clean-fragment constructors and included `RALTS []` as `apder_nf`-valid; `apder_clean` then filters out zero-budget degenerates according to the uploaded definitions. 

## Sanity checks

The known bad shortcuts reproduced correctly:

`q = RSEQ (RALTS [RONE, RSTAR (RCHAR 'a')]) (RSTAR (RCHAR 'b'))`, `k = RSTAR (RCHAR 'b')`

* `D(q,k) = 1`
* `D(RALTS[q],k) = 3`
* `rsize(q) = 7`

This matches the design’s warning that `D(ALTS[q],k) <= D(q,k)+1` is false for `(1+a*).b*` under `b*`. 

Shared-tail family `rs = [x_i*.a*]`, `k = a*`:

* For `n=2`: parent `D = 4`, child-sum-plus-one `= 3`; old `+1` step fails.
* For `n=30`: parent `D = 60`, singleton-size budget `= 150`, child-sum-plus-one `= 31`; L1 and STEP still pass.

This directly targets the design’s known `n>=2` failure mode for the old RALTS step. 

## Exhaustive / targeted coverage completed

Generated normal-form counts:

* Alphabet `{a,b}`, `apder_nf` exact rsize 1–8:
  `[5, 8, 31, 153, 798, 4483, 26407, 160548]`
* Alphabet `{a,b}`, `apder_clean`, rsize ≤ 8: `106856`
* Alphabet `{a,b,c}`, `apder_nf` exact rsize 1–7:
  `[6, 10, 48, 266, 1602, 10472, 71566]`
* Alphabet `{a,b,c}`, `apder_clean`, rsize ≤ 7: `58087`

The carrier tested was exactly the design’s `A(r,k) = strong_apder_acc r k`, where `strong_apder_acc` is the strong closure of `rfrontier (s4 r k) ∪ apder_term_frontier_acc r k`.  The model also followed the uploaded `rsimpStrong_raw` / alternation-prune definitions, including the set-level alternation prune and dedup path.

### L2 — singleton-size

Claim tested:

`apder_nf q ∧ apder_nf k ⟹ D(RALTS[q], k) <= rsize q`

The design marks this as the crux lemma. 

Completed checks:

* `0 / 241032` violations: alphabet `{a,b}`, `q` rsize ≤ 6, `k` rsize ≤ 3.
* `0 / 449196` violations: alphabet `{a,b}`, `q` rsize ≤ 6, star-heavy continuations over `{a,b}`.
* `0 / 123648` violations: alphabet `{a,b,c}`, `q` rsize ≤ 5, `k` rsize ≤ 3.
* `0 / 448786` violations for nontrivial `q` only, alphabet `{a,b}`, `q` rsize ≤ 6, star-heavy continuations.

Best ratios found:

* Overall best ratio was the trivial tight case: `q = RCHAR 'a'`, `k = RONE`, `D = 1`, `rsize q = 1`.
* Best nontrivial ratio:
  `q = RSEQ (RCHAR 'a') (RCHAR 'b')`, `k = RONE`, `D = 2`, `rsize q = 3`, ratio `2/3`.
* Largest nontrivial `D` seen in this L2 sweep:
  `D = 3` at `q = RALTS [RSTAR (RCHAR 'b'), RCHAR 'a', RCHAR 'b']`, `k = RONE`, `rsize q = 5`.

### L1 — singleton cover

Claim tested:

`A(RALTS rs,k) ⊆ ⋃q∈set rs. A(RALTS[q],k)`

This is exactly the branch-origin cover in the design: pruning deletes covered branches but should not invent a row without a singleton branch origin. 

Completed checks:

* `0 / 794640` violations: alphabet `{a,b}`, all generated `RALTS` lists rsize ≤ 7, `k` rsize ≤ 3.
* `0 / 469952` violations: alphabet `{a,b,c}`, all generated `RALTS` lists rsize ≤ 6, `k` rsize ≤ 3.
* `0 / 29` violations: shared-tail family `rs=[x_i*.a*]`, `k=a*`, `n=2..30`.

No missing-origin rows were found.

### STEP — RALTS budget

Claim tested:

`D(RALTS rs,k) <= sum(rsize q for q in set rs)`

This is the RALTS step derived from L1 + L2 in the design. 

Completed checks were the same L1/STEP sweeps above:

* `0 / 794640` violations: alphabet `{a,b}`, all generated `RALTS` lists rsize ≤ 7, `k` rsize ≤ 3.
* `0 / 469952` violations: alphabet `{a,b,c}`, all generated `RALTS` lists rsize ≤ 6, `k` rsize ≤ 3.
* `0 / 29` violations: shared-tail family up to `n=30`.

Largest STEP stress result:

`rs = [RCHAR 'a', RSTAR (RCHAR 'b'), RSTAR (RCHAR 'a'), RCHAR 'b']`, `k = RONE`

* `D = 4`
* budget `= 6`
* no violation.

### GLOBAL

Claim tested:

`apder_clean r ∧ apder_nf k ⟹ D(r,k) <= rsize r`

The design’s global induction uses RCHAR/RSEQ/RSTAR green splits and the new RALTS step.

Completed checks:

* `0 / 106856` for `D(r,RONE) <= rsize r`, alphabet `{a,b}`, clean rsize ≤ 8.
* `0 / 734766` reachable induction pairs from those `{a,b}` clean rsize ≤ 8 terms.
* `0 / 835296` arbitrary product pairs for alphabet `{a,b}`, clean rsize ≤ 7, `k` rsize ≤ 3.
* `0 / 58087` for `D(r,RONE) <= rsize r`, alphabet `{a,b,c}`, clean rsize ≤ 7.
* `0 / 352478` reachable induction pairs from those `{a,b,c}` clean rsize ≤ 7 terms.
* `0 / 576256` arbitrary product pairs for alphabet `{a,b,c}`, clean rsize ≤ 6, `k` rsize ≤ 3.

Largest `D(r,RONE)` seen:

* Alphabet `{a,b}`, clean ≤ 8:
  `D = 4` at
  `r = RSEQ (RCHAR 'b') (RALTS [RSEQ (RCHAR 'b') (RCHAR 'b'), RCHAR 'a'])`,
  `rsize = 7`.

* Alphabet `{a,b,c}`, clean ≤ 7:
  `D = 4` at
  `r = RALTS [RCHAR 'c', RCHAR 'b', RSTAR (RCHAR 'a'), RCHAR 'a']`,
  `rsize = 6`.

### TARGET

Claim tested:

`card(apder_strong_dlfrontier r) <= rsize r + 1`

The target is the uploaded `card_apder_strong_dlfrontier_le`; the final gate consumes exactly this cardinality bound.  The model used `apder_strong_dlfrontier r = rsimpStrong_dlform_closure (apder_rows r)`, following the definitions.

Completed checks:

* `0 / 106856` violations: alphabet `{a,b}`, clean rsize ≤ 8.
* `0 / 58087` violations: alphabet `{a,b,c}`, clean rsize ≤ 7.
* The arbitrary-product GLOBAL sweeps above also rechecked TARGET for the same clean roots.

Largest `card(U)` seen:

* Alphabet `{a,b}`, clean ≤ 8:
  `card(U) = 5`, bound `= 8`, same `r` as the max `D` case above.
* Alphabet `{a,b,c}`, clean ≤ 7:
  `card(U) = 5`, bound `= 7`, at
  `RALTS [RCHAR 'c', RCHAR 'b', RSTAR (RCHAR 'a'), RCHAR 'a']`.

## Bottom line

No CE found. The red-team evidence supports the singleton-cover + singleton-size design, including the adversarial shared-tail family that kills the old `+1` shortcut. I would still treat L2 as the formal crux: the computational search did not break it, but it also did not reach the requested rsize 12–14 exhaustive bound.
