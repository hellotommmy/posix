# Dual-Agent Coordination: POSIX Backreference Pilot

This file is the short current-state operating plan for running Codex Desktop/CLI
and Cursor/Opus together on the shared branch `codex/backref-values`.

## Current Network Assumption

Cursor/Opus may reconnect inside a long-running command and fail to switch
network nodes before the current chat stalls. Therefore Cursor should not be the
primary owner of long Isabelle builds. Cursor is best used for local proof
editing and short checks; Codex or a plain PowerShell terminal should own final
`BackRefPilot` builds and commits when the network is unstable.

Do not start headless Cursor Agent/Opus 4.7 as a fallback unless Chengsong
explicitly asks for it. The intended Opus route is Cursor IDE with Opus 4.6 Max.

## Resource Leases

Two agents may work in parallel, but they must not share the same live resource.

| Resource | Rule |
| --- | --- |
| `BackRefValues.thy` | Single-writer. Whoever owns the current proof task owns this file until a checked commit is pushed. |
| `BackRefLang.thy` | Separate-writer only for language-blueprint tasks such as `backref_lang4`; do not change frozen statements without admin approval. |
| New pilot files | Preferred parallel lane for Codex after BR-014, e.g. `BackRefBlexer.thy` or a blueprint-only theory. |
| Isabelle build cache | Single-builder. Only one full `BackRefPilot` build should run at a time. |
| `loop-config.json` | Local coordination only. Do not include it in theorem/proof commits unless explicitly requested. |

## Current Assignment

- Cursor/Opus lane: finish and preserve the current BR-014 `BackRefValues.thy`
  proof work if it is already open in Cursor.
- Codex lane: when Opus is editing `BackRefValues.thy`, work only on
  non-overlapping planning/new-file tasks, or act as build/check/commit steward.
- If Cursor is reconnecting or the build pane is stale, Codex may verify and
  commit already-written checked proof work from the `posix-opus` clone, but
  must not discard dirty Cursor edits.

## Stable Build Command

Use a timeout wrapper so a proof-method loop cannot run all night:

```powershell
& C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe -lc "cd '/cygdrive/c/Users/Chengsong/Documents/AIPV2026Notes/posix-opus' && timeout 240s '/cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle' build -v -d pilot BackRefPilot"
```

If this times out, inspect the reported `command "... " running for ...`
line, narrow that proof, and rerun. Do not start a second build while the first
one is alive.

## Why `fun` Was Slow

The old `fun (sequential) binjval` definition forced Isabelle's function package
to compile many nested, overlapping `bval` patterns plus a catch-all fallback.
Cold builds spent around 200 seconds at the `fun` command. The faster form is a
`primrec` over `brexp` with explicit `case v of ...` branches, which avoids the
heavy function-package pattern analysis and termination machinery.

## Parallel Work Pattern

1. Start each agent in a separate clone or worktree on the shared branch.
2. At task start, run `git fetch origin codex/backref-values` and inspect
   `git status --short --branch`.
3. If the worktree is dirty, inspect and preserve the dirty diff before pulling.
4. Claim a file lane in the prompt before editing.
5. Avoid full builds while the other agent is building.
6. Commit only checked theorem/proof work. Keep local hook/config changes out of
   proof commits unless they are the actual task.
7. Push small checked commits; the other agent fetches and continues.

## Good Current Split After BR-014

- Opus: proof-worker lane in `BackRefValues.thy` for POSIX/value lemmas.
- Codex: blueprint/new-file lane for `backref_lang4` migration notes or pilot
  `BackRefBlexer.thy`, without touching production `Blexer.thy`, `BlexerSimp.thy`,
  bounds, or closed-form theories.

