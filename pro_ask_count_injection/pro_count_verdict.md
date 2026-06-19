I found a hard stop: the proposed **SAA RALTS +1** step is **not true** under the definitions in `DEFINITIONS.txt`. So no injection/charge into that RHS can exist, because the target cardinality is too small.

The issue is not just a missing clever ledger. It is a genuine cardinal counterexample to the requested goal step:

```isabelle
card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
  <= (SUM q in set rs. card (strong_apder_acc q k - strong_apder_acc RONE k)) + 1
```

This is the exact step requested in `PROMPT.txt`.  The model used the given `rsimp7_SEQ_atom`, `rsimpStrong_raw`, `row_dlforms`, `rsimpStrong_dlform_closure`, `apder_term_frontier_acc`, and `strong_apder_acc` equations.    The broader gate target remains the linear `card_apder_strong_dlfrontier_le`, which is still the important open count lemma.    

## Counterexample

Take distinct characters `a`, `b`, `c`, and define

```isabelle
q_b = RSEQ (RSTAR (RCHAR b)) (RSTAR (RCHAR a))
q_c = RSEQ (RSTAR (RCHAR c)) (RSTAR (RCHAR a))
rs  = [q_b, q_c]
k   = RSTAR (RCHAR a)
r   = RALTS rs
```

This is clean:

```isabelle
apder_clean r
apder_nf k
rsize r = 11
rsize k = 2
```

The base is

```isabelle
strong_apder_acc RONE k = { RSTAR (RCHAR a) }
```

Each child contributes only one non-base row:

```isabelle
strong_apder_acc q_b k - strong_apder_acc RONE k
  = { RSEQ (RSTAR (RCHAR b)) (RSTAR (RCHAR a)) }

strong_apder_acc q_c k - strong_apder_acc RONE k
  = { RSEQ (RSTAR (RCHAR c)) (RSTAR (RCHAR a)) }
```

So the requested RHS is

```isabelle
1 + 1 + 1 = 3
```

But the parent has four non-base rows:

```isabelle
strong_apder_acc (RALTS [q_b, q_c]) k - strong_apder_acc RONE k
 =
{ RSEQ (RSTAR (RCHAR b)) (RSTAR (RCHAR a)),
  RSEQ (RSTAR (RCHAR c)) (RSTAR (RCHAR a)),
  RSEQ (RSTAR (RCHAR b)) (RSEQ (RSTAR (RCHAR a)) (RSTAR (RCHAR a))),
  RSEQ (RSTAR (RCHAR c)) (RSEQ (RSTAR (RCHAR a)) (RSTAR (RCHAR a))) }
```

Thus

```isabelle
card LHS = 4
card RHS = 3
```

So the proposed RALTS step fails.

## Why this happens

For each branch

```isabelle
q_x = RSEQ (RSTAR (RCHAR x)) (RSTAR (RCHAR a))
```

the child-side strong closure collapses the repeated `a* · a*` tail and gives only

```isabelle
x* · a*
```

But the parent root row first strong-simplifies the branch to

```isabelle
x* · a*
```

and then opens the alternation under continuation `a*`. Since `row_dlforms` calls `rsimp7_SEQ_atom` on the whole branch `p` and the continuation, and `p` is a top-level `RSEQ`, not a top-level `RSTAR`, `sigma7` falls back to `sigma4` and keeps the nested tail:

```isabelle
(x* · a*) · a*  ↦  x* · (a* · a*)
```

So every such branch contributes two parent rows:

```isabelle
x* · a*
x* · (a* · a*)
```

but only one child-side RHS slot:

```isabelle
x* · a*
```

The singleton `+1` repairs this for one branch, which is why the known `ALTS[ONE, b*·a*]` killer survives. It does **not** repair two independent branches.

More generally, for

```isabelle
rs_n = [ RSEQ (RSTAR (RCHAR b_i)) (RSTAR (RCHAR a)) . i < n ]
k    = RSTAR (RCHAR a)
```

with distinct `b_i ≠ a`, the parent side has `2n` non-base rows, while the child sum has `n`, so the requested `+1` bound fails for every `n ≥ 2`:

```isabelle
2n <= n + 1    false for n >= 2
```

This proves that no definable injection into the proposed RHS plus one slack point can exist.

## It is also reachable

This is not just an unreachable-continuation artifact. The same `k = RSTAR (RCHAR a)` is reached by the ordinary RSEQ continuation update from the clean regex

```isabelle
RSEQ (RALTS [q_b, q_c]) (RSTAR (RCHAR a))
```

At the left child, the induction continuation is

```isabelle
rsimp4_SEQ_atom (RSTAR (RCHAR a)) RONE = RSTAR (RCHAR a)
```

So a continuation invariant `P(k)` that holds for all actually reached continuations cannot exclude this counterexample unless it also excludes a genuine clean RSEQ descent.

## What a correct proof must track

The SAA RALTS proof cannot have a single global slack. It must carry **per-branch tail-collapse debt**, or abandon this SAA RALTS route.

The minimum extra structure is a provenance-indexed ledger, not an untagged set count. The ledger must distinguish:

```isabelle
origin branch q_x,
parent-root row      x* · (a* · a*),
child-collapsed row  x* · a*,
parent-term row      x* · a*
```

In the failed `+1` proof, the parent-root row and parent-term row both want to charge to the same child slot `x* · a*`. This collision happens independently for each branch `q_x`. Therefore the debt is linear in the number of such branches, not globally bounded by one.

A corrected SAA-style statement would need a term like:

```isabelle
card (strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k)
  <= (SUM q in set rs. card (strong_apder_acc q k - strong_apder_acc RONE k))
     + ralts_tail_debt rs k
```

where `ralts_tail_debt rs k` counts the branch-origin collisions caused by opening an already-strong branch under a matching star continuation. Such a debt is linear in `rs`, so it might still be compatible with a linear global bound, but it is not the requested `+1`.

A minimal family of definitions to add as regression/provenance scaffolding is:

```isabelle
definition bad_branch :: "char => char => rrexp" where
  "bad_branch x a = RSEQ (RSTAR (RCHAR x)) (RSTAR (RCHAR a))"

fun bad_branches :: "char list => char => rrexp list" where
  "bad_branches [] a = []"
| "bad_branches (x # xs) a = bad_branch x a # bad_branches xs a"

definition bad_ralts :: "char list => char => rrexp" where
  "bad_ralts xs a = RALTS (bad_branches xs a)"

definition bad_k :: "char => rrexp" where
  "bad_k a = RSTAR (RCHAR a)"
```

And the useful provenance skeleton is:

```isabelle
datatype origin =
    ORoot rrexp
  | OTerm rrexp

fun tagged_term_frontier_acc :: "rrexp => rrexp => (origin * rrexp) set" where
  "tagged_term_frontier_acc RZERO k = {}"
| "tagged_term_frontier_acc RONE k = {}"
| "tagged_term_frontier_acc (RCHAR c) k =
     ((%p. (OTerm (RCHAR c), p)) ` rfrontier k)"
| "tagged_term_frontier_acc (RALTS rs) k =
     (UN q:set rs. tagged_term_frontier_acc q k)"
| "tagged_term_frontier_acc (RSEQ r1 r2) k =
     tagged_term_frontier_acc r1 (rsimp4_SEQ_atom r2 k)
     Un tagged_term_frontier_acc r2 k"
| "tagged_term_frontier_acc (RSTAR r) k =
     tagged_term_frontier_acc r (rsimp4_SEQ_atom (RSTAR r) k)"
```

For the alternation root, the corresponding tagged prune must mirror `rsimpStrong_ALTs_raw`, but preserve the source branch through `rflts`, pruning, and `rdistinct`:

```isabelle
fun tagged_rflts :: "(rrexp * rrexp) list => (rrexp * rrexp) list" where
  "tagged_rflts [] = []"
| "tagged_rflts ((RZERO, q) # xs) = tagged_rflts xs"
| "tagged_rflts ((RALTS rs, q) # xs) =
     map (%p. (p, q)) rs @ tagged_rflts xs"
| "tagged_rflts ((p, q) # xs) = (p, q) # tagged_rflts xs"

fun tagged_prune_rows_acc :: "rrexp list => (rrexp * rrexp) list => (rrexp * rrexp) list" where
  "tagged_prune_rows_acc seen [] = []"
| "tagged_prune_rows_acc seen ((p, q) # xs) =
     (let p' = rsimpStrong_prune_against_rows_raw seen p
      in (p', q) # tagged_prune_rows_acc (p' # seen) xs)"

definition tagged_prune_rows :: "(rrexp * rrexp) list => (rrexp * rrexp) list" where
  "tagged_prune_rows xs = tagged_prune_rows_acc [] xs"

fun tagged_rdistinct :: "(rrexp * rrexp) list => rrexp set => (rrexp * rrexp) list" where
  "tagged_rdistinct [] acc = []"
| "tagged_rdistinct ((p, q) # xs) acc =
     (if p : acc
      then tagged_rdistinct xs acc
      else (p, q) # tagged_rdistinct xs ({p} Un acc))"

definition tagged_strong_alts_rows :: "rrexp list => (rrexp * rrexp) list" where
  "tagged_strong_alts_rows rs =
     tagged_rdistinct
       (tagged_rflts
         (tagged_prune_rows
           (tagged_rflts (map (%q. (rsimpStrong_raw q, q)) rs))))
       {}"
```

That tagged structure is exactly what exposes the failure: two different origins `q_b` and `q_c` each generate an independent collision. Any correct SAA proof must either budget these collisions or move to the direct `U` proof lane. The current frontier document already identifies the direct `U` RSEQ inequality as the cleaner live lane: `U` is RALTS-clean, and the remaining wall is the RSEQ global-cancellation argument.  

## Python evidence

The faithful Python model sanity-checked the main `U` bound over all clean regexes over `{a,b}` through size `≤ 7`:

```text
U_bound_exhaustive_size<=7 total 18984 violations 0 tight 2
```

It also reproduced the named regressions I could encode from the prompt:

```text
named SAA leak:
  r = ALTS[ONE, SEQ(STAR b, STAR a)], k = STAR a
  lhs/rhs = 2 / 2
  rows = { b*·a*, b*·(a*·a*) }

collapsing-tail CE size 12:
  U_card = 4
  contains a*·a*       = True
  contains a·(a*·a*)   = True

awidth CE:
  U_card = 3
  awidth + 1 = 2
```

The new RALTS-step counterexample output was:

```text
counterexample r (((b)*.(a)*)+((c)*.(a)*)) rsize 11 k (a)* ksize 2 clean True k_nf True
lhs_card 4
lhs [
  '((b)*.((a)*.(a)*))',
  '((b)*.(a)*)',
  '((c)*.((a)*.(a)*))',
  '((c)*.(a)*)'
]
rhs_card 3
childs [
  ('((b)*.(a)*)', 1, ['((b)*.(a)*)']),
  ('((c)*.(a)*)', 1, ['((c)*.(a)*)'])
]
```

The exact check harness was:

```python
q1 = SEQ(STAR(CHAR("b")), STAR(CHAR("a")))
q2 = SEQ(STAR(CHAR("c")), STAR(CHAR("a")))
r  = ALTS((q1, q2))
k  = STAR(CHAR("a"))

lhs = strong_apder_acc(r, k) - strong_apder_acc(ONE, k)
rhs = sum(
    len(strong_apder_acc(q, k) - strong_apder_acc(ONE, k))
    for q in set((q1, q2))
) + 1

print(apder_clean(r), apder_nf(k), rsize(r), rsize(k))
print(len(lhs), sorted(map(repr, lhs)))
print(rhs, [(repr(q), strong_apder_acc(q, k) - strong_apder_acc(ONE, k))
            for q in set((q1, q2))])
assert len(lhs) == 4
assert rhs == 3
assert len(lhs) > rhs
```

I did not find a way to repair the requested `+1` SAA RALTS step, because this is a cardinal counterexample, not an injectivity-choice failure. The next viable move is either to add a linear per-origin debt to the SAA induction, or to return to the direct `U` RSEQ global-cancellation lane.
