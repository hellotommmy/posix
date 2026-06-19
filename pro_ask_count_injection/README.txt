pro_ask_count_injection — self-contained GPT-5.5 / Pro design ask for the ONE open lemma (2026-06-19)
=====================================================================================================

The whole cubic size-bound proof (Isabelle/HOL, POSIX regex lexer) is GREEN (0 sorry) EXCEPT one linear row-COUNT
lemma, now pinned by three independent prover agents to a single cross-prune step. This folder asks an external
model for the concrete Isabelle proof of exactly that step.

HOW TO USE
1. Open a fresh GPT-5.5 (or Pro) session.
2. Paste the entire PROMPT.txt.
3. ATTACH (or paste after it) BOTH:
     - DEFINITIONS.txt  — every function + cited green lemma, VERBATIM from the source (this is what makes the ask
                          truly self-contained; the model must use these exact defs, not approximate ones).
     - CARD_FRONTIER.md — the one-page state summary.
4. ENABLE the model's Python/code-interpreter tool. The model does NOT need to write or machine-check Isabelle (we
   formalize). PROMPT.txt §0 makes it MANDATORY to build a faithful Python model of the definitions, test its proposed
   injection/invariant on the witness family + the named counterexamples, ITERATE until 0 violations, and only then
   write up the DESIGN + the RECURSIVE DEFINITIONS of any new function it introduces (reporting what it validated +
   the Python code). The deliverable is design + recursive defs + Python evidence — NOT an Isabelle proof. This is the
   fix for the previous attempt, which returned an untested (and false) construction.
5. Save the reply as verdict_count_injection.md in this folder.

VALIDATION DISCIPLINE (important — two past "validated TRUE" claims here were sampling artifacts)
The Secretary VALIDATES any returned construction on the witness family (scratch_strong_card_bridge.py /
scratch_direct_universe_cubic.py + witness_gen.py, incl. the a*.a* / SEQ killers) BEFORE any worker formalizes it.
Do not trust a verdict's "0 violations" claim without re-running it.

WHAT'S BEING ASKED (one line)
A definable injection / transport ledger (branch-origin level) OR a reachable-continuation invariant that closes the
LEAKY RALTS step of the diff-card induction on the strong_apder_acc carrier:
   card( strong_apder_acc (RALTS rs) k - strong_apder_acc RONE k )
      <= ( SUM_{q in set rs} card( strong_apder_acc q k - strong_apder_acc RONE k ) ) + 1.
The other three constructor steps (RCHAR/RSEQ/RSTAR) are already clean + written; this one step closes the Gate.

FILES
  PROMPT.txt          — the ask (paste this).
  DEFINITIONS.txt     — verbatim Isabelle defs + green-lemma statements (attach this).
  CARD_FRONTIER.md    — current proof state (attach this).
  README.txt          — this file.
