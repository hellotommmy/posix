# Dual-Agent Coordination: POSIX Backreference Pilot

This file is the short current-state operating plan for running two Codex CLI
workers together on the shared branch `codex/backref-values`.

## Current Network Assumption

Cursor/Opus is retired for overnight work on this project. It repeatedly stalled
inside reconnects during long commands under the current network conditions, so
the robust overnight mode is two Codex CLI workers in two separate clones.

Do not start headless Cursor Agent/Opus 4.7 as a fallback unless Chengsong
explicitly asks for it. The intended Opus route is Cursor IDE with Opus 4.6 Max.
For the current run, do not use Opus at all.

## Resource Leases

Two agents may work in parallel, but they must not share the same live resource.

| Resource | Rule |
| --- | --- |
| `BackRefValues.thy` | Single-writer. Agent B owns this file for BR-015 until a checked commit is pushed or the lock is released. |
| `BackRefLang.thy` | Separate-writer only for language-blueprint tasks such as `backref_lang4`; do not change frozen statements without admin approval. |
| New pilot files | Agent A's preferred lane for BR-022 statement/proof-prep, without touching Agent B's `BackRefValues.thy`. |
| Isabelle build cache | Single-builder. The local CI script uses a global mutex; do not bypass it with manual concurrent builds. |
| `loop-config.json` | Local coordination only. Do not include it in theorem/proof commits unless explicitly requested. |

## Current Assignment

- Agent A lane (`posix-codex`): BR-022 bounded-fragment statement blueprint and
  non-conflicting pilot-only proof-prep. Do not edit `BackRefValues.thy`.
- Agent B lane (`posix-codex-b`): BR-015 POSIX value ordering in
  `BackRefValues.thy`. Do not edit Agent A's new blueprint files except to
  resolve sync conflicts.
- `posix-opus` is inactive. It may contain local Cursor hook settings, but it is
  not an active proof worker.

## Stable Build Command

Use the local CI wrapper so a proof-method loop cannot run all night and so
only one Isabelle build touches the shared cache at a time:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -PilotOnly -Role admin -NoCertificate
```

If this times out, inspect the reported `command "... " running for ...`
line, narrow that proof, and rerun. Do not start a second build while the first
one is alive.

## Proof Performance Budget

For this pilot, a few-hundred-line proof check should normally complete in
about 5-10 seconds. A single Isabelle command running for 200 seconds is
extremely abnormal and must be treated as a defect in the definition or proof
script, not as normal progress.

Operational rule:

- At about 0.5 seconds for `auto`/`simp`/broad proof search, if it has not
  returned, abandon it and replace it by explicit cases/helper lemmas.
- At 10 seconds on one command, identify the command and source line.
- At 30 seconds, stop broad automation and rewrite the proof locally.
- At 120 seconds, interrupt or let the timeout wrapper kill the build.
- At 200 seconds, do not rerun unchanged; replace the resource-intensive line
  or fix the looping/search root cause.

Preferred repairs:

- change heavy `fun` commands with nested overlapping patterns into `primrec`
  or explicit `case` definitions when possible;
- replace broad `auto`/`force`/`blast`/`metis`/`elim!` calls by targeted rules
  as soon as they visibly hang;
- introduce helper lemmas and explicit Isar proof steps;
- use constructor-specific eliminators instead of handing automation the whole
  inductive relation.

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
5. Use `isabelle_ci.ps1` for builds; it serializes local Isabelle builds.
6. Commit only checked theorem/proof work. Keep local hook/config changes out of
   proof commits unless they are the actual task.
7. Push small checked commits; the other agent fetches and continues.

## Good Current Split After BR-014

- Codex Agent B: proof-worker lane in `BackRefValues.thy` for BR-015
  POSIX/value ordering.
- Codex Agent A: blueprint/new-file lane for BR-022 and BR-019 statement prep,
  without touching production `Blexer.thy`, `BlexerSimp.thy`, bounds, or
  closed-form theories.
