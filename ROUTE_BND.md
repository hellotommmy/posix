# LANE BOUNDARY — prove S1 + boundary_term_absorb

You are ONE lane of a parallel route-1 formalization (POSIX cubic size-bound, Isabelle/HOL). A Secretary supervises
and merges your green proof into the integration. **Prove your lemmas; build green; no `sorry`; fail-stop + report.**
Work only in `r1bnd/Card_Route1_Bnd.thy`.

## Read first
- `pro_ask_round2/DEFINITIONS.txt` (functions + green lemmas), `pro_ask_round2/verdict_G3.md` (the L2 proof + helpers).
  Green base `cubic/DirectUniverseCubic.thy` (do NOT modify).

## YOUR TARGETS (prove S1 first, then boundary_term_absorb via S1)
```isabelle
(* S1 — the clean, collision-free sufficient condition (validated 0/629,868) *)
lemma boundary_excess_le_root_excess:
  "card (strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
     <= card (single_root t k - strong_apder_acc RONE k)"

(* boundary_term_absorb — from S1 + disjointness of collapsed-boundary forms from term rows *)
lemma boundary_term_absorb:
  assumes "apder_nf t" "apder_nf k"
  shows
    "card ((strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
            \<union> (single_term t k - strong_apder_acc RONE k))
       <= card (strong_apder_acc (RALTS [t]) k - strong_apder_acc RONE k)"
```
where `single_root q k = rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))`,
`single_term q k = rsimpStrong_dlform_closure (apder_term_frontier_acc q k)` (both defined in your file).

## ★ The proof-level steer (validated by the Secretary)
Prove `boundary_term_absorb` **VIA S1**, NOT a raw injection. Useful facts:
- the decomposition `strong_apder_acc (RALTS [t]) k = single_root t k \<union> single_term t k` (provable by unfolding
  `strong_apder_acc_def`/`rsimpStrong_dlform_closure_def`; `apder_term_frontier_acc (RALTS [t]) k = apder_term_frontier_acc t k`).
- so RHS `= card ((single_root t k \<union> single_term t k) - B k)`, and the LHS shares the `(single_term t k - B k)` term;
  after cancelling it, the content is exactly S1 (`boundary-excess <= root-excess`) plus that collapsed-boundary forms
  are disjoint from genuine term rows (0 coincidences measured). S1 is collision-free BY CONSTRUCTION (it is a single
  `card_mono`-style inequality between two excess sets), so no injection bookkeeping is needed.

## BUILD — ISOLATED HEAP (required; the other lanes build concurrently)
Do NOT use the shared `.ps1` build — it shares the heap store with the other lanes and WILL corrupt it. Use your OWN
private heap (first build ~2min; then seconds):
```
& 'C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc "export USER_HOME=/cygdrive/c/Users/Chengsong/Documents/posix-route1/bnd/.isa_home && export HOME=\$USER_HOME && cd /cygdrive/c/Users/Chengsong/Documents/posix-route1/bnd && '/cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle' build -d . Posix_Card_Route1_Bnd"
```
Exit 0 = green.

## Discipline / report
0 sorry. Grep `DEFINITIONS.txt §D`
for green names. If you suspect a lemma is FALSE, STOP + report the minimal `t`+`k`. Commit small on `card/route1-bnd`;
report the proof text + build result when green.
