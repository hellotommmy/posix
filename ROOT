(* FROZEN BASE — admin-locked theories, in base/. Built ONCE into a heap image (-b) and
   LOADED (not rebuilt) by the active leaf. GeneralRegexBound is (global) so the active
   files' bare `imports GeneralRegexBound` resolves to this parent session's loaded theory. *)
session Posix_Base in "base" = "HOL-Library" +
  options [document = false]
  theories
    "HOL-Library.Sublist"
    "RegLangs"
    "PosixSpec"
    "Lexer"
    "LexerSimp"
    "Blexer"
    "BlexerSimp"
    "BasicIdentities"
    "ClosedForms"
    "GeneralRegexBound" (global)
    "ClosedFormsBounds"
    "FBound"

(* ACTIVE leaf — the cubic-bound work, in active/. Parent = Posix_Base, so the frozen base
   loads from its heap image; only these two files recompile on edit (~47s vs ~104s). *)
session Posix_Antimirov in "active" = "Posix_Base" +
  options [document = false]
  theories
    "AntimirovFactoredTransition"
    "AntimirovNormalFrontier"

(* DIRECT-UNIVERSE CUBIC ROUTE (2026-06-17) — fast leaf over the Posix_Antimirov heap, in cubic/.
   Edits to the cubic theories rebuild ONLY this leaf (Antimirov loads from heap, ~seconds), so the
   workers iterate fast and never recompile the 37k-line active file.
   Build this lane with:  scripts\codex-isabelle-build-posix.ps1 -Session Posix_Cubic. *)
session Posix_Cubic in "cubic" = "Posix_Antimirov" +
  options [document = false]
  theories
    "DirectUniverseCubic_L3"
    "DirectUniverseCubic"

(* ROUTE-1 FORMALIZATION LANE (2026-06-20) — the validated singleton-cover linear row-count.
   Child of Posix_Cubic (green base loads from heap; only Card_Route1 recompiles).
   Build: scripts\codex-isabelle-build-posix.ps1 -Session Posix_Card_Route1 *)
session Posix_Card_Route1 in "card" = "Posix_Cubic" +
  options [document = false]
  theories
    "Card_Route1"

(* REWRITE FALLBACK LANE (2026-06-17) — independent Ch5/Ch6-style near-identity
   rewrite relation for the step-wise-strong vs once-strong derivative route.
   Build with: scripts\codex-isabelle-build-posix.ps1 -Session Posix_Rewrite_Fallback. *)
session Posix_Rewrite_Fallback in "rewrite" = "Posix_Base" +
  options [document = false]
  theories
    "RewriteFallback"
