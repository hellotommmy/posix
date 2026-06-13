# GPT Pro verdict on the gate-bridge gap: the opened-boundary (suffix-edge) invariant

PROVENANCE: GPT Pro (web, high-reasoning), 2026-06-14, on the gate-bridge gap
(`GATE_BRIDGE_GAP.md`). Surfaced to all agents by the secretary.

STATUS: DESIGN PROPOSAL — not yet sample-checked, not yet Isabelle-verified.
Before heavy Isabelle, SAMPLE-CHECK at depth>=5 (extend `scratch_rowcount_check.py`
or the Scala smoke): (a) the potential bound
`rsize_set(opened_boundary_forms r k) <= open_pot r + zw2 r*(1 + rsize k)`, and
(b) the cubic arithmetic `open_pot r + zw2 r*2 <= (rsize r + 3)^3`. The verdict
itself says "exact constants can be tightened" — sampling tells you the right
constants. A deep CE => record it in `SUPER_LINEAR_PATTERNS.md` and adjust before
proving. The project has TWICE proved false statements that passed shallow
sampling; do not skip the deep check.

TL;DR (the design that closes gap option (ii) of `GATE_BRIDGE_GAP.md`):
- Carrier: `opened_boundary_forms r k = row_dlformss(rfrontier(sigma r k) UNION acc r k) - odfront k`,
  where `odfront k = row_dlformss(rfrontier k)`. The OPENED analog of the D-law
  boundary `(rfrontier(sigma r k) UNION acc r k) - rfrontier k`, with `row_dlformss`
  applied BEFORE subtracting `odfront k`.
- WHY it works: a `1`/pass-through branch contributes ZERO new opened forms — its
  contribution is exactly `odfront k`, already subtracted. That is the dedup /
  suffix-sharing that makes the RONE-pair tower harmless. Set-native: no list
  cost, no square-sum.
- Potential `open_pot` charges strict suffix crossings (RONE pays 0). Target:
  `rsize_set(opened_boundary_forms r k) <= open_pot r + zw2 r*(1+rsize k)`; cubic.
- Telescoping SEQ case: the middle suffix `odfront(sigma q k)` is subtracted on the
  left and supplied on the right — cancels exactly as in the D law.
- Strong simplifier: prove CARRIER PRESERVATION (rows stay in the global
  opened-boundary carrier), NOT cost monotonicity (the known-false "S shrinks D
  rowwise", `rsimpStrong_raw_row_dlforms_cost_not_monotone`).
- rtail_nf vs clean: clean/rntimes_free on the budget side; rtail_nf only on the
  strong-closure preservation side — do NOT feed strong rows back into the D law.
- The 9-lemma implementation stack is in section 8 below. Execute it in order.

---

## Design memo: use an **opened-boundary / suffix-edge** invariant, not a per-row opener bound

The bridge I would try to land is **not** the square-sum gate `(i)`. It is a set-level version of the D-law boundary, with `row_dlformss` pushed into the same telescoping shape that made the row-count proof work. The right carrier is:

> **the set of strict opened suffix-edges introduced by a regex body before a continuation `k`, after subtracting the opened frontier already owned by `k`.**

That subtraction is the key. A `1`/pass-through branch contributes **zero new opened forms**; it only reaches `k`, whose opened forms are already in the boundary term being subtracted. This is exactly the suffix-sharing that makes the RONE tower harmless for the deduplicated set while the list opener explodes. The gap file says the remaining object must be a deduplicated set bound, and explicitly rules out square-sum and non-dedup list routes; this carrier is set-native from the start.  

---

## 1. Carrier: `opened_boundary_forms r k`

Let

```isabelle
odfront k = row_dlformss (rfrontier k)
```

where `rfrontier` is the top-alternative frontier from the D-law side, and `row_dlformss` is the set opener from the gate. The opener `D` already opens top alternatives and `(Σ ps) · k` into the set-union of `D (σ⋆ p k)`, not into a list, which is exactly the deduplicating object the theorem measures. 

Define the opened D-boundary:

```isabelle
opened_boundary_forms r k =
  row_dlformss
    (rfrontier (rsimp4_SEQ_atom r k) ∪ apder_term_frontier_acc r k)
  - odfront k
```

Read this as the opened analogue of the proved D-law boundary

```isabelle
(rfrontier (σ r k) ∪ acc r k) - rfrontier k
```

but with `row_dlformss` applied before subtraction. That order matters: it removes all opened suffix forms already supplied by `k`, including the exponentially many list paths that merely re-enter the same suffix.

For bucket language, define:

```isabelle
seq_edges X = {(h,t). RSEQ h t ∈ X}

tails X = {t. ∃h. RSEQ h t ∈ X}
bucket X t = {h. RSEQ h t ∈ X}
```

Then the sequence part is exactly the weighted incidence ledger

```isabelle
Σ t∈tails X. Σ h∈bucket X t. rsize (RSEQ h t)
```

not `card heads * Σ tails`, and not `Σ row_size^2`. The invariant should bound this **incidence sum** directly:

```isabelle
rsize_set (opened_boundary_forms r k)
  ≤ open_pot r + apder_zw2 r * (1 + rsize k)
```

This says: each strict head occurrence in `r` may carry the continuation `k` once; pass-through/unit branches carry it zero times because they are subtracted as `odfront k`.

That is the degree collapse.

---

## 2. The potential: `open_pot`

Use a numerical potential that charges **strict crossings of a suffix**, not paths through alternatives.

A good first Isabelle target is:

```isabelle
fun open_pot where
  open_pot RZERO = 0
| open_pot RONE  = 0
| open_pot (RCHAR c) = 2
| open_pot (RALTS rs) = sum_list (map open_pot rs)
| open_pot (RSEQ p q) =
    open_pot p + open_pot q + apder_zw2 p * (rsize q + 2)
| open_pot (RSTAR p) =
    open_pot p + (apder_zw2 p + 1) * (rsize (RSTAR p) + 2)
```

The exact constants can be tightened, but this shape is the important part:

* `RONE` pays **0**. This is the RONE-tower fix.
* `RSEQ p q` charges every strict position in `p` once for crossing the suffix `q`.
* `RSTAR p` charges the body positions for crossing the re-entry suffix `p*`, plus one star credit, matching the `zw2` “+1 per star” convention from the D law. The roadmap records that `zw2` is letters plus one per star and is bounded by size on the clean fragment. 

The two key arithmetic lemmas should be:

```isabelle
lemma opened_boundary_forms_le_open_pot:
  assumes clean: "apder_clean r"
      and nf:    "apder_nf r"          (* or whatever normal-form guard is live *)
      and free:  "rntimes_free r"
  shows
    "rsize_set (opened_boundary_forms r k)
       ≤ open_pot r + apder_zw2 r * (1 + rsize k)"
```

and

```isabelle
lemma open_pot_cubic:
  assumes clean: "apder_clean r"
      and free:  "rntimes_free r"
  shows
    "open_pot r + apder_zw2 r * 2 ≤ (rsize r + 3)^3"
```

The second lemma should be routine arithmetic once `apder_zw2 r ≤ rsize r` is available on the clean/rntimes-free fragment. It is deliberately cubic even though the real behaviour may be quadratic; a cubic potential leaves slack for `RSTAR` and `σ/σ⋆` normalization constants.

---

## 3. Recursive proof sketch for the opened-boundary law

The central structural lemma should not be stated as a rowwise monotonicity of `S`, and it should not mention list cost. State it as a telescoping inclusion/ledger law over the opened boundary:

```isabelle
lemma opened_boundary_rec:
  "opened_boundary_forms RZERO k = {}"
  "opened_boundary_forms RONE  k = {}"

  "opened_boundary_forms (RCHAR c) k
     ⊆ row_dlformss (rfrontier (rsimp4_SEQ_atom (RCHAR c) k))"

  "opened_boundary_forms (RALTS rs) k
     ⊆ ⋃r∈set rs. opened_boundary_forms r k"

  "opened_boundary_forms (RSEQ p q) k
     ⊆ opened_boundary_forms p (rsimp4_SEQ_atom q k)
        ∪ opened_boundary_forms q k"

  "opened_boundary_forms (RSTAR p) k
     ⊆
        (row_dlformss (rfrontier (rsimp4_SEQ_atom (RSTAR p) k)) - odfront k)
        ∪ opened_boundary_forms p (rsimp4_SEQ_atom (RSTAR p) k)"
```

The `RSEQ` case is the real telescoping step. Expanding the definitions gives:

```text
∂(σ (p·q) k) = ∂(σ p (σ q k))

acc(p·q,k) = acc(p, σ q k) ∪ acc(q,k)
```

The opened forms introduced by `p` are compared against `odfront (σ q k)`. The opened forms introduced by `q` include that same `odfront (σ q k)` boundary and compare against `odfront k`. Thus the middle suffix cancels exactly as in the D law:

```text
odfront(σ q k)   is subtracted from the left piece
odfront(σ q k)   is supplied by the right piece
```

This is the opened/suffix-sharing analogue of the telescoping invariant that made `#(acc(r,k) - ∂k) ≤ w(r)` work. The difference is that we telescope **opened suffix sets**, not raw row counts.

For `RALTS`, set union makes overlaps free. This is where the list refutation is avoided: a `1` branch does not recursively copy `D(k)` into a list; it contributes nothing outside `odfront k`.

For `RSTAR`, the star’s own frontier row is paid by the `+1` star credit, and the body is handled under continuation `σ(p*,k)`. Use the `σ⋆` size/normalization lemmas only at the `row_dlformss` boundary, because `D` opens `(Σ ps) · k` via `rsimp7_SEQ_atom`.

---

## 4. Static carrier theorem that closes the actual gate

The clean target should be a static opened carrier theorem:

```isabelle
lemma afactored1_opened_boundary_carrier:
  assumes clean: "apder_clean r"
      and nf:    "apder_nf r"
      and free:  "rntimes_free r"
  shows
    "row_dlformss (set (afactored1 r u))
       ⊆ odfront RONE ∪ opened_boundary_forms r RONE"
```

This is the opened analogue of the existing static-row containment. The roadmap says the front is already staticized and that row count/row size are controlled through `apder_rows`; the new theorem replaces the too-lossy “each row opens quadratically” wrapper with an opened carrier that has already deduplicated suffixes. 

Then add the strong simplifier closure bridge:

```isabelle
lemma strong_dlform_closure_opened_boundary_carrier:
  assumes clean: "apder_clean r"
      and nf:    "apder_nf r"
      and free:  "rntimes_free r"
  shows
    "rsimpStrong_dlform_closure (set (afactored1 r u))
       ⊆ odfront RONE ∪ opened_boundary_forms r RONE"
```

This is the direct replacement for missing gap option `(ii)`:

```isabelle
lemma rsimpStrong_dlform_closure_cubic:
  assumes clean: "apder_clean r"
      and nf:    "apder_nf r"
      and free:  "rntimes_free r"
  shows
    "rsize_set
       (rsimpStrong_dlform_closure (set (afactored1 r u)))
     ≤ 2 * (rsize r + 3)^3"
```

The final gate then follows from the already checked containment

```isabelle
row_dlformss (rpder_strong_rows_raw c (afactored1 r s))
  ⊆ rsimpStrong_dlform_closure (set (afactored1 r (s @ [c])))
```

which is listed as proven in the gap file. 

---

## 5. How to discharge the strong simplifier/prune part

The strong simplifier and pruner remove zeros, flatten alternatives, deduplicate, and prune later rows using earlier rows with the same suffix. The pipeline definitions make clear that `∆c` is `nub/flts/prune/flts` over `map S ∘ npderc`, and that the pruner only modifies later rows of shape `(Σ ms)·k` against earlier rows `(Σ ls)·k`. 

For the carrier theorem, prove **carrier preservation**, not cost monotonicity:

```isabelle
lemma rsimpStrong_raw_preserves_opened_boundary_carrier:
  assumes "q ∈ apder_rows r"
      and clean: "apder_clean r"
      and nf: "apder_nf r"
      and free: "rntimes_free r"
  shows
    "row_dlforms (rsimpStrong_raw q)
       ⊆ odfront RONE ∪ opened_boundary_forms r RONE"
```

Then lift through `flts`, `nub`, and `prune` by subset monotonicity.

This avoids the known false lemma “`S` shrinks `D` rowwise.” The full statement explicitly records a checked counterexample where `∥D(S p)∥ > ∥D(p)∥`, so the preservation theorem must say only that simplification stays inside the global opened-boundary carrier. 

The prune case should be especially clean: replacing `(Σ ms)·k` by `σ⋆(⊕(ms \ ls), k)` removes heads under the same tail `k`. In the suffix-edge carrier, that is a subset operation on `bucket k`; it cannot introduce a new tail, and it cannot introduce a new head not already in `ms`.

---

## 6. Why this specifically kills the RONE-pair tower

For a row like

```text
(Σ [1, π]) · T
```

the list opener recursively opens both branches. The `1` branch reopens all of `T`, and this causes the exponential list tower. The full problem statement records this as a checked refutation of any non-deduplicated list-cost route. 

In the opened-boundary carrier:

```isabelle
opened_boundary_forms (RALTS [RONE, π]) T
  ⊆ opened_boundary_forms RONE T ∪ opened_boundary_forms π T
  = {} ∪ opened_boundary_forms π T
```

The `1` branch vanishes because its contribution is exactly `odfront T`, which has already been subtracted. The tower therefore adds only the strict `π`-side suffix edges at each level. That gives the expected polynomial set ledger and explains why deduplication is not a cosmetic detail but the invariant itself.

---

## 7. Where `rtail_nf` versus `clean` matters

Keep the guards separated.

`clean` / `rntimes_free` belongs to the **ordinary front and budget side**:

```isabelle
apder_clean r
apder_nf r
rntimes_free r
apder_zw2 r ≤ rsize r
```

This is where the D-law/static-row machinery applies. The roadmap notes that the D law and static cubic front are established on the clean fragment, and that bounded repetition `{n}` needs later treatment because `{0}` can carry an empty-but-present frontier without paying the plain weight. 

`rtail_nf` belongs to the **strong simplifier closure side**. After `rsimpStrong_raw`, rows are only tail-normal, not fully clean; do not feed those rows back into the D law or `apder_clean` induction. Use `rtail_nf` only to prove syntactic preservation facts such as:

```isabelle
rtail_nf q ⟹
row_dlforms (rsimpStrong_raw q)
  ⊆ opened-boundary-carrier-of-original-root
```

This distinction is load-bearing around `σ⋆` star absorption and reassociation. The carrier should compare tails in the same normalized representation that `row_dlforms` uses, but the numeric credit should still be charged to the original clean root.

---

## 8. Minimal lemma stack to implement

I would implement in this order:

```isabelle
definition odfront where
  "odfront k = row_dlformss (rfrontier k)"
```

```isabelle
definition opened_boundary_forms where
  "opened_boundary_forms r k =
     row_dlformss
       (rfrontier (rsimp4_SEQ_atom r k) ∪ apder_term_frontier_acc r k)
     - odfront k"
```

Then prove the recursive inclusions:

```isabelle
opened_boundary_forms_RZERO
opened_boundary_forms_RONE
opened_boundary_forms_RCHAR
opened_boundary_forms_RALTS_subset
opened_boundary_forms_RSEQ_subset      (* main telescoping lemma *)
opened_boundary_forms_RSTAR_subset
```

Then the potential bound:

```isabelle
opened_boundary_forms_le_open_pot:
  rsize_set (opened_boundary_forms r k)
    ≤ open_pot r + apder_zw2 r * (1 + rsize k)
```

Then the cubic arithmetic:

```isabelle
open_pot_cubic_clean:
  apder_clean r ⟹ rntimes_free r ⟹
  open_pot r + apder_zw2 r * 2 ≤ (rsize r + 3)^3
```

Then the static/strong carrier bridge:

```isabelle
afactored1_opened_boundary_carrier:
  row_dlformss (set (afactored1 r u))
    ⊆ odfront RONE ∪ opened_boundary_forms r RONE
```

```isabelle
rsimpStrong_dlform_closure_opened_boundary_carrier:
  rsimpStrong_dlform_closure (set (afactored1 r u))
    ⊆ odfront RONE ∪ opened_boundary_forms r RONE
```

Finally:

```isabelle
actual_gate_bridge_from_opened_boundary:
  rsize_set
    (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
  ≤ 2 * (rsize r + 3)^3
```

The conceptual invariant is the opened version of the D law:

> `1`-branches and nullable pass-throughs are suffix imports, not new forms; subtract `odfront k`. Strict heads are the only things that pay, and each strict head pays for the suffix it crosses once in a deduplicated set ledger.

That is the bridge I would bet on.
