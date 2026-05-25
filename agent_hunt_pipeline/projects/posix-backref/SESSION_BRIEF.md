# POSIX Backref Session Brief

Read this first when context is scarce. It is intentionally shorter than the
full handoff.

## Current Branch

- Work branch: `codex/backref-values`
- Base: `origin/main`
- PR #1 is already merged into `origin/main` at `e207e04`.
- The old pilot commit `e78ca15` is included in this branch.

## Build

Use:

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/backref_check.ps1 -SkipFetch
```

The underlying Isabelle command is:

```powershell
C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe -lc 'cd /cygdrive/c/Users/Chengsong/Documents/AIPV2026Notes/posix && /cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle build -v -d pilot BackRefPilot'
```

## Checked Layers

- `BackRefLang.thy`:
  - `brexp`
  - `BL`
  - `xnullable`
  - `xder`
  - `xnullable_correctness`
  - `xder_correctness`
  - `xders_correctness`

- `BackRefValues.thy`:
  - `bval`
  - `bflat`
  - `BPrf`
  - `BL_flat_BPrf`
  - `bmkeps`
  - `bmkeps_flat`
  - `bmkeps_BPrf`

## Current Semantic Issue

The current `backref_lang A B cs` models:

```isabelle
{x @ y @ rev cs @ x | x y. x \<in> A \<and> y \<in> B}
```

The user wants a more general blueprint:

```isabelle
{s1 @ s2 @ s3 @ rev cs @ s2 @ s4 | s1 s2 s3 s4.
  s1 \<in> L1 \<and> s2 \<in> L2 \<and> s3 \<in> L3 \<and> s4 \<in> L4}
```

Treat this as a statement-blueprint expansion. Do not rewrite old proofs unless
the admin explicitly approves the migration.

## Current Next Tasks

### Opus (Cursor) -- value-theoretic path
1. Draft `binjval` for the current checked pilot (BR-005).
2. Prove `bflat (binjval r c v) = c # bflat v` (BR-011).
3. Prove `BPrf (binjval r c v) r` (BR-012).

### GPT-5.5 (Codex CLI) -- implementation path
1. Create `BackRefBlexer.thy` with bitcoded backref lexer definitions.
2. Extend `arexp` with `ABACKREF`/`AHALF`/`ARESIDUE`, reference `backRef.sc`.
3. Define `fuse`/`intern`/`erase`/`bnullable`/`bmkeps`/`bder` for new constructors.

### After both paths converge
1. Draft derivative/value story for generalized `backref_lang4`.
2. Define `BBACKREF4` etc. and repeat the above for the generalized case.

## Latest Check

- 2026-05-24: `backref_bounty_guard.py` passed.
- 2026-05-24: `backref_role_guard.py --role admin` passed.
- 2026-05-24: Isabelle `BackRefPilot` passed.

## Do Not Touch

- `Blexer.thy`
- `BlexerSimp.thy`
- bounds files
- closed-form files
