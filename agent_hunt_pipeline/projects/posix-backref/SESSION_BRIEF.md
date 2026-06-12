# POSIX Backref Session Brief

Read this first when context is scarce. It is intentionally shorter than the
full handoff.

## Current Fable/Cubic Run Override

If this session is about the non-backref cubic-bound/Fable run, do not use the
old BackRefPilot task list below as the active task.  Instead read:

- `agent_hunt_pipeline/projects/posix-backref/FABLE_CUBIC_HANDOFF_2026_06_11.md`
- the last 200 lines of `PROGRESS_BACKREF.md`

### Cubic/Fable Build Discipline

For the current `Posix` cubic-bound run, use the repository wrappers from the
repo root. Do not use the old `BackRefPilot` command in the Build section for
this task.

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check
powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300
```

Run only one Isabelle build at a time. If `codex-proof-workers.ps1 -Action
Check` reports a worker, wait for it or read its output; do not start another
build. Prefer foreground builds for local proof fixes so the first failing
Isabelle line is visible. If the UI requires a background build, immediately
read the generated `.output` file and fix the exact first failing proof; do not
launch another background build until that worker has finished.

Treat every `Background shell failed` label as a proof obligation to inspect,
not as a command problem. The important line is usually the first
`*** Failed to finish proof` block in the task output. Avoid broad
`simp add: card_eq_sum`, `auto`, or `blast` on large goals; use `simp only:`
or a named helper lemma and keep each proof step small.

The active branch is still `codex/backref-values`, but the current work is the
POSIX cubic-bound route around `afactored1_strong_dlform_universe`,
active-suffix buckets, pair budgets, and owner/DAG accounting.  The old pilot
items below are historical context unless the user explicitly asks to resume
the backreference pilot.

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

For live Codex + Cursor/Opus runs, read
`agent_hunt_pipeline/projects/posix-backref/DUAL_AGENT_COORDINATION.md` before
assigning overlapping work.

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
