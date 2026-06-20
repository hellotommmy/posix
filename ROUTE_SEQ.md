# LANE SEQ-HEAD — prove seq_head_core_le_rsize

You are ONE lane of a parallel route-1 formalization (POSIX cubic size-bound, Isabelle/HOL). A Secretary supervises
and merges your green proof. **Prove ONE lemma; build green; no `sorry`; fail-stop + report.** Work only in
`r1seq/Card_Route1_Seq.thy`.

## Read first
- `pro_ask_round2/DEFINITIONS.txt` (functions + green lemmas), `pro_ask_round2/verdict_G3.md` (the L2 proof — your
  lemma is its §2.2 helper; it leaves the RSEQ-head and RALTS-head cases `sorry` — that is YOUR work).
  Green base `cubic/DirectUniverseCubic.thy` (do NOT modify).

## YOUR TARGET
```isabelle
lemma seq_head_core_le_rsize:
  assumes "apder_nf h" "apder_nf t" "apder_nf k"
  shows
    "card ((single_root (RSEQ h t) k \<union> single_term h (rsimp4_SEQ_atom t k))
           - (strong_apder_acc RONE k \<union> strong_apder_acc RONE (rsimp4_SEQ_atom t k)))
     <= rsize h"
```
where `single_root q k = rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))`,
`single_term q k = rsimpStrong_dlform_closure (apder_term_frontier_acc q k)` (defined in your file).

## ★ The proof-level steer (validated by the Secretary)
Induction on `h` (cases RZERO/RONE/RCHAR/RSEQ/RALTS), `arbitrary: t k`. This lemma absorbs the tail-doubling
`(x*·a*)·a* -> x*·(a*·a*)`; `rsize h` pays for the residual rows.
- RCHAR: the term part is `strong_apder_acc RONE (rsimp4_SEQ_atom t k)`; after subtracting both bases, only the
  singleton root can remain ⇒ `card <= 1 = rsize (RCHAR c)`.
- RSEQ `h1 h2`: use `rsimp4_SEQ_atom (RSEQ h1 h2) c = rsimp4_SEQ_atom h1 (rsimp4_SEQ_atom h2 c)`; split into the
  `h1`-core (IH, `<= rsize h1`) and an `h2` boundary-plus-term absorbed against `D1 h2 (rsimp4_SEQ_atom t k) <= rsize h2`
  (IH). See verdict_G3 §2.2 for the exact decomposition.
- RALTS-head: distribute branch origins via the L1 **singleton cover** `strong_apder_acc (RALTS rs) k \<subseteq>
  (\<Union>q. strong_apder_acc (RALTS[q]) k)` and sum the branch budgets. L1 is being proved in the parallel COVER lane —
  **state it as an extra `assumes` (a hypothesis) and report that dependency**; the Secretary supplies the green L1.

## BUILD — ISOLATED HEAP (required; the other lanes build concurrently)
Do NOT use the shared `.ps1` build — it shares the heap store with the other lanes and WILL corrupt it. Use your OWN
private heap (first build ~2min; then seconds):
```
& 'C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc "export USER_HOME=/cygdrive/c/Users/Chengsong/Documents/posix-route1/seq/.isa_home && export HOME=\$USER_HOME && cd /cygdrive/c/Users/Chengsong/Documents/posix-route1/seq && '/cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle' build -d . Posix_Card_Route1_Seq"
```
Exit 0 = green.

## Discipline / report
0 sorry. Grep `DEFINITIONS.txt §D`
for green names. If you suspect FALSE, STOP + report minimal `h`/`t`/`k`. Commit small on `card/route1-seq`; report
the proof text + which dependency (L1) you assumed, when green.
