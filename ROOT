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
