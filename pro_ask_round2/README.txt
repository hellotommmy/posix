ROUND 2 — offload the validated singleton-cover design to 4 parallel GPT-5.5 sessions (2026-06-20)
================================================================================================

A GPT-5.5 round produced a design (DESIGN.md) for the last open lemma of the cubic Gate; we independently
re-validated it (faithful model, adversarial sweep — L2 singleton-size 75000/0, L1 cover 4999/0, global 0 viol).
The design is SOUND empirically; what remains is to pin down the two key lemmas (L1 cover, L2 singleton-size) tightly
enough to formalize. These 4 prompts split that across independent sessions so GPT does the heavy lifting; we (and an
in-house Isabelle agent) do only the final Isabelle transcription.

THE 4 LANES (run each in its OWN fresh GPT-5.5 session, with the Python tool ENABLED):
  G1  PROMPT_G1_redteam.txt    -- ADVERSARY. Tries to BREAK the design (find any CE to L1/L2/global), much harder than
                                  we did. This is the GATE: if it finds a CE, the others are moot. Highest priority.
  G2  PROMPT_G2_cover.txt      -- proves L1 (branch-origin singleton cover) via a provenance-tagged prune model +
                                  Isabelle proof skeleton.
  G3  PROMPT_G3_singleton.txt  -- proves L2 (singleton-size D(ALTS[q],k) <= rsize q), the CRUX, by induction on q +
                                  Isabelle proof skeleton. (Hardest; most valuable.)
  G4  PROMPT_G4_assemble.txt   -- assumes L1+L2, assembles the full top-down proof skeleton + a final global Python
                                  re-validation. (Can run now in parallel; its output is independent of G2/G3's proofs.)

HOW TO RUN each lane:
  1. Open a fresh GPT-5.5 session; ENABLE its Python / code-interpreter tool.
  2. Paste PROMPT_Gx.txt.
  3. ATTACH:  DEFINITIONS.txt  (verbatim Isabelle defs)  AND  DESIGN.md  (the design + lemma chain + validation status).
     (CARD_FRONTIER.md is optional extra context.)
  4. Save the reply as verdict_Gx.md in this folder.

GROUND RULES baked into every prompt: GPT does NOT write/verify Isabelle (web has no prover) — it gives DESIGN +
RECURSIVE DEFINITIONS + PYTHON EVIDENCE + an Isabelle proof SKELETON we transcribe. It must Python-validate (and
CE-hunt) before asserting, and include its harness.

WHAT WE DO WITH THE RESULTS (Secretary): re-validate every "0 violations" claim on our witness family BEFORE trusting
it (this project has had THREE sampling-artifact false positives — most recently the "+1 step", which a single-branch
test missed). Our faithful validator is secretary_validator.py (in this folder). Once L1+L2's proofs are solid and
re-validated, an in-house Isabelle agent formalizes the chain in cubic/ (the Gate is already green modulo this count).

PRIORITY: G1 (gate) + G3 (crux) first; G2 and G4 in parallel. If G1 finds a CE, stop and bring it back.
