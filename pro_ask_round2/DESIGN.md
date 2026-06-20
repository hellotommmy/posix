# The validated design — singleton-cover + singleton-size (2026-06-20)

This is the live design for the ONE open lemma of the cubic Gate. It came from a GPT-5.5 round and has been
**independently re-validated** by us (faithful Python model, adversarial witness-biased sweep). All Isabelle
functions are defined verbatim in `DEFINITIONS.txt` (attached). Notation here: `S = rsimpStrong_raw`,
`s4 = rsimp4_SEQ_atom`, `s7 = rsimp7_SEQ_atom`, `dl = row_dlforms`, `C(X) = (UN p in X. dl(S p)) = rsimpStrong_dlform_closure X`,
`A(r,k) = strong_apder_acc r k`, `B(k) = A(RONE,k)`, `U(r) = apder_strong_dlfrontier r`,
`D(r,k) = card(A(r,k) - A(RONE,k))`.

## The target (unchanged)
`card (apder_strong_dlfrontier r) <= Suc (rsize r)` for `apder_clean r`. Any linear bound closes the Gate.

## What was REFUTED first (do not revisit)
- the "+1" RALTS step `D(ALTS rs, k) <= (SUM q. D(q,k)) + 1` is FALSE (n>=2 branches `x_i*.a*` under `k=a*`: parent
  has `2n` rows, child-sum+1 = `n+1`).
- the per-branch `D(ALTS[q],k) <= D(q,k) + 1` is ALSO FALSE (CE `q=(1+a*).b*, k=b*`: `D(q,k)=1` but `D(ALTS[q],k)=3`).
  The child `D(q,k)` collapses too hard under the continuation, hiding the slack.

## THE DESIGN (validated): branch-origin singleton cover + singleton-size budget
Replace the broken per-step bound by a looser-but-telescoping one that charges each branch its OWN SIZE, via the
**singleton-alternation carrier** `A(ALTS[q], k)`:

- **L1 (singleton cover).**  `A(ALTS rs, k)  SUBSET  (UN q in set rs. A(ALTS[q], k))`.
  Rationale: the SET-level prune inside `S(ALTS ..)` only DELETES head-branches already covered by an earlier row
  (`rflts` flattens/drops 0, `rdistinct` dedups, the pairwise prune removes covered branches) — it never invents a row
  with no source branch. So every opened parent row has a branch origin, hence lies in that branch's singleton carrier.
  This replaces the FALSE `A(ALTS rs,k) SUBSET (UN q. A(q,k))` (the child-carrier cover that leaks).

- **L2 (singleton-size).**  `apder_nf q ==> apder_nf k ==> D(ALTS[q], k) <= rsize q`.
  The singleton alternation opens branch `q` under `k` (with the tail-doubling `(x*.a*).a* -> x*.(a*.a*)`), but its
  non-base row count is bounded by the BRANCH's own syntactic size `rsize q` — the branch has enough internal slack to
  pay for its own uncollapsed `s*.s*` residuals. This is the NEW crux lemma.

From L1 + L2, the RALTS step telescopes with NO `+1` miracle:
```
D(ALTS rs, k) <= card( (UN q. A(ALTS[q],k)) - B(k) )
             <= SUM_{q in set rs} card( A(ALTS[q],k) - B(k) )   (card_UN_le)
             <= SUM_{q in set rs} rsize q                       (L2)
             <= SUM_{q in rs} rsize q  <  rsize (ALTS rs).
```

## The global induction (gives c=1, d=0)
`D(r,k) <= rsize r` for clean/nf (r,k), by induction on r:
- RCHAR: `D(c,k) <= 1 = rsize c`  — existing green `card_strong_apder_acc_RCHAR_diff_base_le`.
- RSEQ : `D(r1.r2,k) <= D(r1, s4 r2 k) + D(r2,k) <= rsize r1 + rsize r2 < rsize(r1.r2)`
         — existing green `strong_apder_acc_RSEQ_subset`, `strong_apder_acc_RONE_sigma_subset`, `card_Un_Diff_telescope_le`.
- RSTAR: `D(r*,k) <= 1 + D(r, s4 r* k) <= 1 + rsize r = rsize(r*)`
         — existing green `strong_apder_acc_RSTAR_subset` + a root-row-<=-1 lemma.
- RALTS: `D(ALTS rs,k) <= SUM_q rsize q < rsize(ALTS rs)` — the NEW L1+L2 step.
Then via the green bridge `U(r) SUBSET A(r,RONE)`, `A(RONE,RONE) = {RONE}` (green), and
`card A <= Suc(card(A - {x}))`:  `card(U r) <= Suc(D(r,RONE)) <= Suc(rsize r)`.  Gate closes.

## New recursive defs introduced (small)
```isabelle
fun ralts_size_budget :: "rrexp list => nat" where
  "ralts_size_budget [] = 0"
| "ralts_size_budget (q # qs) = rsize q + ralts_size_budget qs"
definition D :: "rrexp => rrexp => nat" where
  "D r k = card (strong_apder_acc r k - strong_apder_acc RONE k)"
```
(`A(ALTS[q],k)` is just `strong_apder_acc (RALTS [q]) k` — no new function.)

## Lemma chain to formalize (the deliverable)
```isabelle
lemma strong_apder_acc_RALTS_singleton_cover:                          (* L1 *)
  "strong_apder_acc (RALTS rs) k <= (UN q:set rs. strong_apder_acc (RALTS [q]) k)"
lemma card_strong_apder_acc_singleton_RALTS_diff_base_le_rsize:        (* L2 -- the crux *)
  assumes "apder_nf q" "apder_nf k"
  shows "card (strong_apder_acc (RALTS [q]) k - strong_apder_acc RONE k) <= rsize q"
lemma card_strong_apder_acc_RALTS_diff_base_le_size_budget:            (* RALTS step, from L1+L2 *)
  assumes "list_all apder_nf rs" "apder_nf k"
  shows "card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k) <= ralts_size_budget rs"
lemma card_strong_apder_acc_diff_base_le_rsize:                        (* global induction *)
  assumes "apder_clean r" "apder_nf k"
  shows "card (strong_apder_acc r k - strong_apder_acc RONE k) <= rsize r"
lemma card_apder_strong_dlfrontier_le:                                 (* THE TARGET *)
  assumes "apder_clean r"
  shows "card (apder_strong_dlfrontier r) <= Suc (rsize r)"
```

## Validation status (independently re-run by us — faithful model of DEFINITIONS.txt)
Adversarial witness-biased sweep (stars, seq-ending-in-star, multi-branch alts, rsize <= 20; ~4000 terms, ~2600
nonalt branches, ~150 continuations incl. star continuations):
- **L2 singleton-size `D(ALTS[q],k) <= rsize q` : 75000 tested, 0 violations.**
- **L1 cover `A(ALTS rs,k) SUBSET UN_q A(ALTS[q],k)` : 4999 tested, 0 violations.**
- global `D(r,RONE) <= rsize r` : 0 violations;  `|U(r)| <= rsize+1` : 0 violations.
- all named killers pass (the +1 CE, Pro's `(1+a*).b*`, collapsing-tail, awidth).
GPT-5.5 also reported 0 violations over exhaustive clean nf to size 8 ({a,b}/{a,b,c}) + random 10000.

## What remains = formalize L1 and L2 (L2 is the crux). That is what round-2 asks GPT to nail down.
