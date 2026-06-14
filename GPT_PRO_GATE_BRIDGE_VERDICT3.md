<!--
SECRETARY HEADER (2026-06-14). This is GPT Pro's verdict #4 (the corrected design
after the §4 per-child ALTS/STAR containment was CHECKED-FALSE — see
GATE_BRIDGE_GAP.md UPDATE 3). The route: replace the refuted set-MEMBERSHIP
(`parent drain ⊆ ⋃ child drains`) with a size COST-COVER via a linear context-slot
ledger `drain_ctxs` (one slot per `drain_w` unit; the *declared* cost survives the
`a*·a*→a*` collapse). Keeps `drain_pot`, `drain_w`, and the green §5 arithmetic.

STATUS: VALIDATED at depth>=5 (2026-06-14) — three independent harnesses, ZERO
violations across ~580k cases, and BOTH old CEs (C-DRAIN-1, C-DRAIN-2) are now
covered (each harness passed the RCHAR-sanity gate first + a transcription
self-test). The arithmetic spine (the two static lemmas `ctx_count ≤ drain_w`,
`ctx_base ≤ drain_pot`, and every per-constructor reconciliation) is hand-checked
sound; the two NEW semantic claims (RALTS/RSTAR cost covers, §2/§3) are the only
genuinely-new design points. NOTE: the master cover is TIGHT on C-DRAIN-2 (slack
0) — RSTAR/RSEQ arithmetic must be exact. The live work order + lane split is in
STEER.md. THIS IS THE ROUTE — implement the 6-lemma stack in §5.
-->

## Corrected design: replace child-drain **membership** by a continuation-context **cost cover**

The broken step was not the potential. It was the proof method. Keep `drain_pot`, `drain_w = apder_zw2`, and the green §5 arithmetic. Replace the RALTS/RSTAR child-set telescoping by a small *incidence ledger* of one-hole right contexts. The ledger pays for “a head waiting for the current continuation” rather than for membership in the child drain set.

This directly targets the verified obstruction: RALTS and RSTAR fail because `rsimp7_SEQ_atom` collapses equal adjacent stars in a child-normalized term while the parent opened row can keep the larger uncollapsed sequencing form; the recorded counterexamples are exactly the `b·(a*·a*)` RALTS case and the star re-entry `c·(((1+a)·c)*·…)` case.  The failed proof also cannot be repaired by adding a boundary row, because RALTS has no constructor slack: both `apder_zw2` and `open_pot` are exact sums over alternatives. 

The new invariant still proves the same target:

```isabelle
rsize_set (strong_child_drain p k)
  ≤ drain_pot p + drain_w p * (1 + rsize k)
```

but it proves it through an intermediate context cover, not through

```isabelle
strong_child_drain parent k ⊆ ⋃ child_drains
```

The drain carrier remains the current normalized-row carrier:

```isabelle
strong_child_drain p k =
  strong_opened_live (nseq p k) - strong_opened_live (S k)
```

where `S = rsimpStrong_raw` and `nseq p k = S (rsimp7_SEQ_atom (S p) (S k))`; that was the right carrier choice and should stay. 

---

## 1. New auxiliary ledger

Introduce a finite list of **drain contexts**. A context is represented by a syntactic head plus a declared base cost. The head is useful for local coverage lemmas; the declared cost is what prevents star-collapse from underpaying a parent row.

```isabelle
type_synonym drain_ctx = "rrexp × nat"

definition ctx_base where
  "ctx_base Cs = sum_list (map snd Cs)"

definition ctx_count where
  "ctx_count Cs = length Cs"

definition ctx_bound where
  "ctx_bound Cs k = ctx_base Cs + ctx_count Cs * (1 + rsize k)"

definition raw_plug where
  "raw_plug h k = rsimp7_SEQ_atom h k"

definition ctx_extend where
  "ctx_extend q hc =
     (raw_plug (fst hc) q, snd hc + (1 + rsize q))"
```

The important choice is `snd hc + (1 + rsize q)`, not `rsize (raw_plug (fst hc) q)`. If `raw_plug` collapses `a*·a*` to `a*`, the declared cost still remembers that a suffix slot was consumed. This is the difference between a robust budget and the refuted syntactic membership proof.

Define the contexts structurally:

```isabelle
fun drain_ctxs where
  "drain_ctxs RZERO = []"
| "drain_ctxs RONE  = []"
| "drain_ctxs (RCHAR c) = [(RCHAR c, rsize (RCHAR c))]"

| "drain_ctxs (RALTS rs) =
     concat (map drain_ctxs rs)"

| "drain_ctxs (RSEQ p q) =
     map (ctx_extend q) (drain_ctxs p) @ drain_ctxs q"

| "drain_ctxs (RSTAR p) =
     (RSTAR p, rsize (RSTAR p))
       # map (ctx_extend (RSTAR p)) (drain_ctxs p)"
```

`drain_ctxs` is a linear incidence list, not the exploded row-opening list. It has one slot per `drain_w` unit: one for each character contribution and one for each star re-entry. It therefore does not touch the refuted non-deduplicated opener/list-cost route, which is explicitly dead because the non-deduplicated opening can be exponential while the set union survives through suffix sharing. 

Prove these two static lemmas by straightforward structural induction:

```isabelle
lemma drain_ctxs_count_le_w:
  "ctx_count (drain_ctxs p) ≤ drain_w p"

lemma drain_ctxs_base_le_pot:
  "ctx_base (drain_ctxs p) ≤ drain_pot p"
```

Then the strengthened child theorem is:

```isabelle
lemma strong_child_drain_ctx_bound:
  assumes nf_p:     "rtail_nf p"
      and nf_k:     "rtail_nf k"
      and norm_p:   "S p = p"
      and norm_k:   "S k = k"
      and free_p:   "rntimes_free p"
      and free_k:   "rntimes_free k"
      and legacy_p: "legacy_rrexp p"
      and legacy_k: "legacy_rrexp k"
  shows
    "rsize_set (strong_child_drain p k)
       ≤ ctx_bound (drain_ctxs p) k"
```

The old theorem becomes a corollary:

```isabelle
corollary strong_child_drain_potential:
  assumes same_guards
  shows
    "rsize_set (strong_child_drain p k)
       ≤ drain_pot p + drain_w p * (1 + rsize k)"
  using strong_child_drain_ctx_bound
        drain_ctxs_base_le_pot
        drain_ctxs_count_le_w
  unfolding ctx_bound_def ctx_base_def ctx_count_def
  by nlinarith
```

This keeps the prior continuation-parametric theorem and measure: induction is on `rsize p`; the continuation may grow, including the `RSTAR p` re-entry continuation. 

---

## 2. RALTS corrected invariant

Do **not** prove

```isabelle
strong_child_drain (RALTS rs) k
  ⊆ ⋃q∈set rs. strong_child_drain q k
```

That is the checked-false step.

Instead prove the direct cost cover:

```isabelle
lemma strong_child_drain_RALTS_ctx_bound:
  assumes nf:      "rtail_nf (RALTS rs)"
      and nf_k:    "rtail_nf k"
      and norm:    "S (RALTS rs) = RALTS rs"
      and norm_k:  "S k = k"
      and free:    "rntimes_free (RALTS rs)"
      and free_k:  "rntimes_free k"
      and legacy:  "legacy_rrexp (RALTS rs)"
      and legacy_k:"legacy_rrexp k"
  shows
    "rsize_set (strong_child_drain (RALTS rs) k)
       ≤ sum_list
           (map (λq. ctx_bound (drain_ctxs q) k) rs)"
```

Then rewrite the right side:

```isabelle
sum_list (map (λq. ctx_bound (drain_ctxs q) k) rs)
= ctx_bound (concat (map drain_ctxs rs)) k
= ctx_bound (drain_ctxs (RALTS rs)) k
```

and discharge with `ctx_base ≤ drain_pot` and `ctx_count ≤ drain_w`:

```isabelle
ctx_bound (drain_ctxs (RALTS rs)) k
≤ drain_pot (RALTS rs) + drain_w (RALTS rs) * (1 + rsize k)
```

### Why this pays C-DRAIN-1

For

```isabelle
p = RALTS [RSEQ b (RSTAR a), RONE]
k = RSTAR a
```

the bad parent row is the uncollapsed form

```isabelle
b · (a* · a*)        -- size 7
```

It need not be a member of any child drain set. It is charged to the context already present in

```isabelle
drain_ctxs (RSEQ b (RSTAR a))
```

namely the context whose declared base is the head

```isabelle
b · a*               -- base cost 4
```

Applying the outer continuation costs one sequence node plus `rsize k = 2`, so the slot pays

```isabelle
4 + (1 + 2) = 7
```

exactly. RALTS needs no new constructor credit because its context list is just the concatenation of child context lists. The row is absorbed into the child **budget**, not the child **set**.

This is the tail-incidence answer to the zero-slack problem: each alternative contributes its own continuation slots, and the parent’s non-distributed opened row uses one of those slots.

---

## 3. RSTAR corrected invariant

Do **not** prove

```isabelle
strong_child_drain (RSTAR p) k
  ⊆ star_entry p k ∪ strong_child_drain p (nseq (RSTAR p) k)
```

That is exactly what C-DRAIN-2 refutes.

Instead prove the direct star-context cover:

```isabelle
lemma strong_child_drain_RSTAR_ctx_bound:
  assumes nf:      "rtail_nf (RSTAR p)"
      and nf_k:    "rtail_nf k"
      and norm:    "S (RSTAR p) = RSTAR p"
      and norm_k:  "S k = k"
      and free:    "rntimes_free (RSTAR p)"
      and free_k:  "rntimes_free k"
      and legacy:  "legacy_rrexp (RSTAR p)"
      and legacy_k:"legacy_rrexp k"
      and IH_body:
        "⋀j. rtail_nf j ⟹ S j = j ⟹ rntimes_free j ⟹ legacy_rrexp j ⟹
              rsize_set (strong_child_drain p j)
                ≤ ctx_bound (drain_ctxs p) j"
  shows
    "rsize_set (strong_child_drain (RSTAR p) k)
       ≤ ctx_bound (drain_ctxs (RSTAR p)) k"
```

A more useful internal form is:

```isabelle
lemma strong_child_drain_RSTAR_ctx_step:
  "rsize_set (strong_child_drain (RSTAR p) k)
     ≤ (rsize (RSTAR p) + (1 + rsize k))
       + ctx_bound (drain_ctxs p) (nseq (RSTAR p) k)"
```

Then use

```isabelle
rsize (nseq (RSTAR p) k) ≤ rsize p + rsize k + 2
```

which was already identified as the star-specialized size fact needed for the previous design. 

### Why this pays C-DRAIN-2

The escaped row

```isabelle
c · (((1+a)·c)* · ...)
```

is not required to be in the body child drain set. It is charged to a body context from `drain_ctxs p`, extended by the declared suffix `RSTAR p`. That is exactly the line

```isabelle
map (ctx_extend (RSTAR p)) (drain_ctxs p)
```

in `drain_ctxs (RSTAR p)`.

So the star case no longer says “the escaped row is in the child drain.” It says “the escaped row has the size of a body context plus the declared star-reentry suffix plus the outer continuation.” The `+1` in `drain_w (RSTAR p)` pays the separate star-entry context; the `(drain_w p + 1) * (rsize (RSTAR p) + 2)` part of `drain_pot (RSTAR p)` pays the re-entry suffix carried by every body context. That is the same potential as before, but now used as a context ledger rather than a set-containment ledger.

---

## 4. Per-constructor discharge

The induction is still on `rsize p`, with a list induction inside RALTS. Continuation size is not part of the measure.

### RZERO / RONE

```isabelle
drain_ctxs RZERO = []
drain_ctxs RONE  = []
strong_child_drain RZERO k = {}
strong_child_drain RONE  k = {}
```

So

```isabelle
rsize_set (strong_child_drain p k) = 0
≤ ctx_bound [] k = 0
```

### RCHAR

```isabelle
drain_ctxs (RCHAR c) = [(RCHAR c, 1)]
ctx_bound (drain_ctxs (RCHAR c)) k = 1 + (1 + rsize k)
```

The existing RCHAR local fact gives

```isabelle
rsize_set (strong_child_drain (RCHAR c) k) ≤ rsize k + 2
```

so the context bound is exact. The old potential bound still has one extra unit, since `drain_pot (RCHAR c) = 2` and `drain_w (RCHAR c) = 1`. 

### RALTS

Use `strong_child_drain_RALTS_ctx_bound`, not child-drain inclusion:

```isabelle
rsize_set (strong_child_drain (RALTS rs) k)
≤ Σ q∈rs. ctx_bound (drain_ctxs q) k
= ctx_bound (drain_ctxs (RALTS rs)) k
≤ drain_pot (RALTS rs) + drain_w (RALTS rs) * (1 + rsize k)
```

This is the zero-slack case. It closes because both `ctx_base` and `ctx_count` are additive over `concat`, exactly like `drain_pot` and `drain_w` are additive over RALTS.

### RSEQ

The already-green SEQ child containment can still be used:

```isabelle
strong_child_drain (RSEQ p q) k
  ⊆ strong_child_drain p (nseq q k)
   ∪ strong_child_drain q k
```

Let

```text
Cp = ctx_base  (drain_ctxs p)
Cq = ctx_base  (drain_ctxs q)
Np = ctx_count (drain_ctxs p)
Nq = ctx_count (drain_ctxs q)
b  = rsize q
m  = rsize k
```

Using `rsize (nseq q k) ≤ b + m + 1`:

```isabelle
left  ≤ Cp + Np * (1 + rsize (nseq q k))
      ≤ Cp + Np * (b + m + 2)

right ≤ Cq + Nq * (m + 1)
```

The context definition gives

```isabelle
ctx_base (drain_ctxs (RSEQ p q))
  = Cp + Np * (b + 1) + Cq

ctx_count (drain_ctxs (RSEQ p q))
  = Np + Nq
```

therefore

```isabelle
ctx_bound (drain_ctxs (RSEQ p q)) k
= Cp + Cq + Np * (b + m + 2) + Nq * (m + 1)
```

which matches the required bound exactly.

Then compare to the potential:

```isabelle
Cp + Np * (b + 1) + Cq
≤ drain_pot p + drain_w p * (b + 1) + drain_pot q
≤ drain_pot p + drain_pot q + drain_w p * (b + 2)
= drain_pot (RSEQ p q)
```

and

```isabelle
Np + Nq ≤ drain_w p + drain_w q = drain_w (RSEQ p q)
```

### RSTAR

Let

```text
C = ctx_base  (drain_ctxs p)
N = ctx_count (drain_ctxs p)
a = rsize p
m = rsize k
```

The direct star-context step gives

```isabelle
rsize_set (strong_child_drain (RSTAR p) k)
≤ (a + m + 2) + C + N * (a + m + 3)
```

because `rsize (RSTAR p) = a + 1` and `rsize (nseq (RSTAR p) k) ≤ a + m + 2`.

Now expand the star context list:

```isabelle
drain_ctxs (RSTAR p)
= (RSTAR p, a + 1) # map (ctx_extend (RSTAR p)) (drain_ctxs p)
```

so

```isabelle
ctx_base (drain_ctxs (RSTAR p))
= (a + 1) + C + N * (a + 2)

ctx_count (drain_ctxs (RSTAR p))
= N + 1
```

Therefore

```isabelle
ctx_bound (drain_ctxs (RSTAR p)) k
= (a + 1) + C + N * (a + 2) + (N + 1) * (m + 1)
= C + N * (a + m + 3) + a + m + 2
```

which is exactly the direct star-context bound.

Finally compare with the old potential. Since `C ≤ P = drain_pot p` and `N ≤ W = drain_w p`,

```isabelle
ctx_bound (drain_ctxs (RSTAR p)) k
≤ P + W * (a + m + 3) + a + m + 2
```

while

```isabelle
drain_pot (RSTAR p) + drain_w (RSTAR p) * (m + 1)
= P + (W + 1) * (a + 3) + (W + 1) * (m + 1)
= P + W * (a + m + 4) + a + m + 4
```

The slack is

```isabelle
(P + W*(a+m+4) + a+m+4)
-
(P + W*(a+m+3) + a+m+2)
= W + 2
```

So RSTAR closes with the same numerical slack as the prior memo, but without the false `star_entry ∪ child_drain` set inclusion. The previous memo’s star arithmetic was already correct; only the set route feeding it was wrong. 

---

## 5. The exact theorem stack to implement

Implement these as the new local obligations:

```isabelle
lemma drain_ctxs_count_le_w:
  "ctx_count (drain_ctxs p) ≤ drain_w p"

lemma drain_ctxs_base_le_pot:
  "ctx_base (drain_ctxs p) ≤ drain_pot p"

lemma strong_child_drain_RALTS_ctx_bound:
  "rsize_set (strong_child_drain (RALTS rs) k)
     ≤ sum_list (map (λq. ctx_bound (drain_ctxs q) k) rs)"

lemma strong_child_drain_RSTAR_ctx_step:
  "rsize_set (strong_child_drain (RSTAR p) k)
     ≤ rsize (RSTAR p) + (1 + rsize k)
       + ctx_bound (drain_ctxs p) (nseq (RSTAR p) k)"

lemma strong_child_drain_ctx_bound:
  "rsize_set (strong_child_drain p k)
     ≤ ctx_bound (drain_ctxs p) k"

lemma strong_child_drain_potential:
  "rsize_set (strong_child_drain p k)
     ≤ drain_pot p + drain_w p * (1 + rsize k)"
```

The first two are pure arithmetic/structural lemmas. The two new semantic lemmas are the only genuinely new design points: RALTS and RSTAR must be proved as direct context covers. SEQ/CHAR/RONE/RZERO can reuse the existing local facts.

---

## 6. Root arithmetic still closes

No change is needed to the green §5 potential arithmetic. The prior design already had:

```isabelle
lemma drain_pot_le_cubic_core:
  assumes "rntimes_free r"
  shows "drain_pot r ≤ rsize r * (rsize r + 2)^2"

lemma drain_child_budget_root_cubic:
  assumes "rntimes_free r"
  shows "drain_child_budget r RONE ≤ (rsize r + 3)^3"
```

with the calculation

```isabelle
drain_child_budget r RONE
= drain_pot r + 2 * drain_w r
≤ rsize r * (rsize r + 2)^2 + 2 * rsize r
≤ (rsize r + 3)^3
```

and slack

```isabelle
(rsize r + 3)^3
- (rsize r*(rsize r+2)^2 + 2*rsize r)
= 5*(rsize r)^2 + 21*rsize r + 27
```



The gate target is the same set-ledger cubic inequality over the deduplicated opened rows:

```isabelle
rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
  ≤ 2 * (rsize r + 3)^3
```



The final assembly remains:

```isabelle
actual gate ledger
≤ static/front cubic part
  + current normalized drain part
≤ (rsize r + 3)^3 + (rsize r + 3)^3
= 2 * (rsize r + 3)^3
```

The wrapper should continue to use the current-row drain carrier and the current normalized front, not the original-root carrier; that was already the intended final bridge shape. 

---

## Bottom line

Do not add RALTS credit and do not weaken the cubic. The fixed proof is:

```text
parent drain SET
  --not subset of child drain SETS
  but size-covered by child CONTEXT SLOTS
  whose count is drain_w
  and whose base cost is drain_pot.
```

RALTS closes because context slots concatenate exactly. RSTAR closes because the star constructor adds one entry slot and extends every body slot by the declared `RSTAR p` suffix, leaving `drain_w p + 2` slack.
