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

(* REWRITE FALLBACK LANE (2026-06-17) — independent Ch5/Ch6-style near-identity
   rewrite relation for the step-wise-strong vs once-strong derivative route.
   Build with: scripts\codex-isabelle-build-posix.ps1 -Session Posix_Rewrite_Fallback. *)
session Posix_Rewrite_Fallback in "rewrite" = "Posix_Base" +
  options [document = false]
  theories
    "RewriteFallback"

(* ROUTE-2 / N-ROUTE (2026-06-20) — normalized append + normalizer; fast leaf over the
   frozen Posix_Base heap (only needs rrexp + rsize from BasicIdentities), in cubic/Normalized/.
   Isolated session name => own build DB => safe alongside the primary lanes.
   Build with: scripts\codex-isabelle-build-posix.ps1 -Session Posix_Norm. *)
session Posix_Norm in "cubic/Normalized" = "Posix_Base" +
  options [document = false]
  theories
    "NormalizedAppend"
    "NormalizedStrong"
    "NormalizedOpening"
