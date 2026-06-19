GPT-5.5 / Pro design asks — 3 lanes on the ONE open lemma of the cubic Gate (2026-06-19)
=========================================================================================

The whole cubic size-bound proof for a POSIX regex lexer is GREEN (Isabelle/HOL, 0 sorry) EXCEPT one
linear ROW-COUNT lemma. Three independent worktree agents (Claude/Opus) are FORMALIZING; these prompts
ask GPT-5.5 for the DESIGN STRATEGY of three of those lanes (the 4th lane, the "ledger", already has a
Pro verdict — PRO_LEDGER_VERDICT.md). Each prompt is self-contained.

HOW TO USE
- Open a fresh GPT-5.5 (or Pro) session per lane. Paste the whole PROMPT_<lane>.txt.
- Optionally ATTACH `CARD_FRONTIER.md` (in this folder) for the full state + green-brick line numbers.
- Save the reply as `verdict_<lane>.md` in this folder. The Secretary VALIDATES every verdict on the
  witness family before any worker formalizes it (two past "validated TRUE" claims were sampling artifacts).

THE THREE PROMPTS
- PROMPT_count_injection.txt  — the count route's hard core: absorb the RSEQ-strong cross-prune via a
  definable injection / transport ledger (complements / hardens the ledger lane's crux lemmas).
- PROMPT_positions.txt        — a GLOBAL position/Glushkov injection giving a LINEAR card bound
  (card(U r) <= a*awidth(r)+b or a*rsize(r)+b); note awidth+1 alone may be too tight.
- PROMPT_rewrite.txt          — the thesis Ch5/6 near-identity rewrite ->r' transporting the closed-form
  cubic bound from once-strong to step-wise-strong (sidesteps the count entirely).

GROUND RULES for GPT (stated in each prompt): give a CONCRETE, Isabelle-formalizable lemma chain (exact
statements, the induction variable, which existing facts to cite), NOT prose. Do not re-propose the refuted
routes. If no such strategy exists, say so precisely and characterize what a correct proof must track.
