# Build modularization — VALIDATED, ready to land at a worker checkpoint (2026-06-14)

Heap-image the frozen base so editing the active file rebuilds only it. Tested green
in an isolated worktree; measured **edit-cycle 103.7s → 46.7s (~55% faster)**, frozen
base (28k GeneralRegexBound + 15k FBound + 9 others) NOT re-elaborated on active edits.

## The fix (the non-obvious part)
A bare cross-session import (`imports GeneralRegexBound`) is qualified by the CURRENT
session and looked up as source — it resolves to a PARENT-session theory only if that
theory is declared **`(global)`** in ROOT. So mark `GeneralRegexBound (global)` IN ROOT
ONLY; the active `.thy` files keep `imports GeneralRegexBound` verbatim (zero source edits).

## Target layout
- `base/`  : the 11 frozen theories (RegLangs..GeneralRegexBound, ClosedFormsBounds, FBound)
- `active/`: AntimirovFactoredTransition.thy, AntimirovNormalFrontier.thy
- New ROOT:
```
session Posix_Base in "base" = "HOL-Library" +
  options [document = false]
  theories
    "HOL-Library.Sublist"
    "RegLangs" "PosixSpec" "Lexer" "LexerSimp" "Blexer" "BlexerSimp"
    "BasicIdentities" "ClosedForms"
    "GeneralRegexBound" (global)
    "ClosedFormsBounds" "FBound"

session Posix_Antimirov in "active" = "Posix_Base" +
  options [document = false]
  theories
    "AntimirovFactoredTransition"
    "AntimirovNormalFrontier"
```

## LAND RUNBOOK (only at a coordinated pause — BOTH workers committed + idle)
The land MOVES the active `.thy` file (`.` → `active/`), so it MUST happen when no
worker has uncommitted edits to it (else their `pull --rebase --autostash` conflicts on
the moved path). Steps (in the shared tree, branch codex/backref-values):
```bash
cd .../posix-codex
git pull --rebase --autostash
mkdir -p base active
git mv RegLangs.thy PosixSpec.thy Lexer.thy LexerSimp.thy Blexer.thy BlexerSimp.thy \
       BasicIdentities.thy ClosedForms.thy GeneralRegexBound.thy ClosedFormsBounds.thy FBound.thy base/
git mv AntimirovFactoredTransition.thy AntimirovNormalFrontier.thy active/
# replace ROOT with the two-session content above
# replace scripts/codex-isabelle-build-posix.ps1 with the worktree version
#   (adds -Session param default Posix_Antimirov; per-session mutex …_Build_$Session;
#    auto -b when $Session ends in _Base)
isabelle build -b -d . Posix_Base       # one-time, ~83s, persists the heap image
isabelle build -d . Posix_Antimirov     # active lane, must be GREEN (~47s)
git add -A && git commit && git push     # NOTE: -A acceptable ONLY during the coordinated freeze
```
Then announce in STEER: active file is now `active/AntimirovFactoredTransition.thy`
(identical content); build with `scripts\codex-isabelle-build-posix.ps1` (defaults to
`-Session Posix_Antimirov`). jEdit/PIDE: open the new path, pick session `Posix_Antimirov`
(auto-loads the `Posix_Base` heap).

## Caveats
- `(global)` claims the name `GeneralRegexBound` globally; the land REPLACES the old
  single `Posix` session, so no clash. Don't build the old `Posix` ROOT alongside this.
- Only `GeneralRegexBound` needs `(global)` (the single import boundary the active files
  cross). A future active file importing another base theory by bare name needs that base
  theory `(global)` too, or a `Posix_Base.That` qualified import.

## Status
Validated artifacts live in the worktree `posix-codex-opt2` (branch `opt-modular-build2`).
NOT landed. Land at: a brief coordinated pause of A+B (sooner = faster remaining builds),
or at gate-close. Secretary drives the land once workers are confirmed committed + idle.
