# S1 lane (claude-S1) — findings, fail-stop & PIVOT report

**Branch** `claude/route1-S1` · **File** `r1bnd/Card_Route1_Bnd.thy` · **Session** `Posix_Card_Route1_Bnd`
(builds GREEN, no sorry, ~1s on warm private heap). Date: 2026-06-21.

## ⚠ LANE BYPASSED (read first)
The `claude-seq` lane found a **D-bound route** that makes the whole route-1 cubic gate
GREEN (0 sorry) modulo **one** hypothesis — and it **bypasses this lane entirely**
(`boundary_term_absorb`, `seq_head_core_le_rsize`, `singleton_size_nf`, verdict_G3/G4).
See memory `route1-gate-via-dbound-ralts-nut`. The route proves the general-continuation
D-bound `card(strong_apder_acc r k − strong_apder_acc RONE k) ≤ rsize r` directly by
induction on `r` (the GREEN reassoc-clean carrier subsets `strong_apder_acc_{RSEQ,RSTAR,
RCHAR}_subset` + `card_Un_Diff_telescope_le` + `strong_apder_acc_RONE_sigma_subset` +
a new leaf `star_root_diff_base_le_one`), then specialises at `k=RONE` via the bridge.
**The lone remaining nut is `RALTS_diff`** (general-k RALTS cover, the COVER lane):
`apder_nf (RALTS rs) ⟹ apder_nf k ⟹ card(strong_apder_acc (RALTS rs) k −
strong_apder_acc RONE k) ≤ rsize (RALTS rs)`.

**Consequence for this lane:** `boundary_term_absorb`/`S1` are no longer on the critical
path. I am standing down on them (do NOT keep racing the GPT bnd lane on absorb/S1). The
analysis below is preserved because **`RALTS_diff` is the SAME cross-prune wall**, and the
green reduction + the wall-characterisation here apply to it directly.

## What is GREEN & committed (`r1bnd/Card_Route1_Bnd.thy`, commit `1a67349`, no sorry)
- `rsimpStrong_dlform_closure_Un` — closure distributes over `∪`.
- `strong_apder_acc_decomp_self`: `Aself(t,k) = B(s4 t k) ∪ single_term t k`.
- `strong_apder_acc_decomp_alt`:  `Aalt(t,k)  = single_root t k ∪ single_term t k`.
- `boundary_term_absorb_lhs_eq` / `_rhs_eq`.

(`B k = strong_apder_acc RONE k`, `Aself = strong_apder_acc t k`,
`Aalt = strong_apder_acc (RALTS[t]) k`, `X = B(s4 t k)−B k`, `R = single_root−B k`,
`T = single_term−B k`.)

## The kickoff route is FALSE (sampling artifact) — DROP it
The prescribed RSEQ split `X ⊆ rsimpStrong_raw\`(single_root − B)` + `card_image_le` is
FALSE. **Minimal CE** (exhaustive enum, confirmed by 2 independent workflow agents):
`t = a·([a·a*])` = `RSEQ(C a, RALTS[RSEQ(C a, RSTAR(C a))])` (rsize 7; the singleton-ALT
wrapper is essential — 0 violations for all RSEQ-roots ≤ 6), `k = a*`. There `X = R =
{a·(a·(a*·a*))}` but `S\`R = {a·(a·a*)}` **over**-collapses the buried `a*·a*→a*`.
All 8 S-image/subset variants fail 3000+× over the adversarial nf pool; the card targets
hold 0-viol. (The *named* killer `t=a·a*,k=a*` SATISFIES the route — which is why the
bnd lane's 0/5768 validation missed the wall.)

## Where the difficulty really lives (validated; corroborated by the workflow)
Both targets reduce, via the GREEN glue above, to a single inequality and then to ONE
irreducible card-injection brick:

1. **absorb ⟺ `card(Aself t k − B k) ≤ card(Aalt t k − B k)`** (the decomps; green).
2. **absorb concentrates entirely in S1** (set-algebra, all 0-viol, independently
   re-verified): `Dr ≤ Dalt ⟺ |X−T| ≤ |R−T|`; with the clean subset **`R∩T ⊆ X`**
   (0-viol) we get `|R∩T| ≤ |X∩T|`, so `|X|≤|R| ∧ |R∩T|≤|X∩T| ⟹ |X−T|≤|R−T|`
   (subtraction-free nat arithmetic, 0-viol). `R∩T ⊆ X` traces to
   `single_root ∩ single_term ⊆ row_dlforms(S(s4 t k))` (0-viol) — green-able.
   **So `boundary_term_absorb` is NOT an independent wall; it is S1 + clean glue.**
3. **S1 (`|X|≤|R|`) is the irreducible wall.** It reduces (clean arithmetic) to
   **A1base**: `|row_dlforms(S(s4 t k))| ≤ |row_dlforms(S(RSEQ(RALTS[t],k)))|` (0-viol).
   A1base is the **σ7 collapse-asymmetry**: `s4 t k` and `RSEQ(RALTS[t],k)` have nearly-
   equal `row_dlforms` *before* the final `S`, but `S` collapses the deeply-plugged `s4`
   form MORE (σ7 fires only on a *leading* `a*·a*`). This is a genuine card-injection on
   the symmetric difference with **NO set-relation form**: `X⊆R` (242 viol),
   `X−T⊆R−T` (172), `S(s4 t k)=S(RSEQ(RALTS[t],k))` (267), the S-surjection `R↠X` (561),
   per-branch `X-piece ⊆ S(R-piece)` (342) are ALL refuted on the pool.
   (`|X|==|R|` strict in 380/213840 ⇒ not even a bijection.) Peeling the outer SEQ makes
   it self-similar (no structural induction). = [[card-ralts-telescope-structural-wall]].

The workflow's TELESCOPE route reaches the same wall from the other side: `Dr ≤ Dalt ⟺
card(A1) ≤ card(Rdiff)` (A1=X−T−Bk, Rdiff=R−T−Bk); non-SEQ closes by `card_mono`
(`X' = single_root` exactly for CHAR/STAR, k∉{0,1}); SEQ reduces by IH to an **ADD brick**
which is the same cross-prune injection in subtraction-free card form.

## RALTS_diff is the SAME wall (why this matters for the live route)
`RALTS_diff` = `Dr(RALTS rs, k) ≤ rsize(RALTS rs)`. Via the GREEN
`strong_apder_acc_RALTS_subset`, `Aalt(rs,k) ⊆ single_root(rs,k) ∪ ⋃_q Aself(q,k)`, so
`Dr(RALTS rs,k) ≤ card(single_root(rs,k) − B k) + Σ_q Dr(q,k)`; the IH bounds `Σ_q Dr(q,k)
≤ Σ rsize q`, leaving the obligation **`card(single_root(rs,k) − B k − ⋃_q Aself(q,k)) ≤ 1`**
— i.e. "the wrapped-RALTS root opens to ≤ 1 new row not already covered by the branches".
That residual bound IS the cross-prune / σ7 collapse-asymmetry wall characterised above.
The clean cover `A(RALTS rs)k ⊆ B k ∪ ⋃_q A q k` is FALSE (cross-prune residual).

## Recommendation
1. **DROP** the kickoff's asymmetric image split (falsified; minimal CE above).
2. **Stand down on `boundary_term_absorb`/`S1`** — bypassed by the D-bound route.
3. The remaining critical path is **`RALTS_diff`** (general-k RALTS cover, COVER lane).
   Its core obligation = bound the cross-prune root residual by 1 — the same wall. The
   subtraction-free reductions and the A1base characterisation here are the relevant
   levers; a clean attack likely needs an **amortized/charging** argument or an
   **Antimirov-PDER bridge** (per project history), not another subset/image lemma.
4. The committed GREEN decomposition lemmas (`*_decomp_self/_alt`, `*_Un`) are reusable
   for any RALTS-cover formalisation.

Evidence (local, gitignored): `pro_ask_round2/scratch_s1_*.py`, `scratch_sweep.py`,
`scratch_diag*.py`; workflow run `wf_f90e26f4-262` (Confirm phase corroborated all of the
above; 2 derive routes converge on the wall; the adversarial-verify + synthesis agents
died on transient API 529 — their route content is preserved in the run output).
