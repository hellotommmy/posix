# POSIX Lexing with Bitcoded Regular Expressions

Run the code with

```isabelle build -c -v -d . Posix```

Tested with Isabelle2021-1.


* RegLangs.thy (contains basic definitions for Regular Languages, chapter 2)

* PosixSpec.thy (contains values and POSIX definitions, chapter 2)

* Lexer.thy (first algorithm by Sulzmann & Lu without simplification, chapter 2)

* LexerSimp.thy (correctness for simple-minded simplification rules, chapter 2)

* Blexer.thy (second algorithm by Sulzmann & Lu without simplification, chapter 3)

* BlexerSimp.thy (correctness for simplification rules with effective de-duplication, chapter 4)

* Finite Bound Result: (chapter 5)
  	 BasicIdentidies.thy
	 ClosedForms.thy
	 GeneralRegexBound
	 ClosedFormBounds.thy
	 FBound.thy

