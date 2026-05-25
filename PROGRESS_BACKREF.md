# POSIX Backreference Progress

Last updated: 2026-05-25

## Current Branch

- Branch: `codex/backref-values`
- Base: `origin/main`
- PR #1 status: merged into `origin/main` at `e207e04`

## Build

Checked command:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin
```

Latest result:

- PASS on 2026-05-25 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, and Isabelle `BackRefPilot`.
- Local CI certificate is generated only after both sessions pass:
  `agent_hunt_pipeline/certificates/local_ci_certificate.json` (ignored by git).

## Completed

- `BackRefLang.thy` defines pilot `brexp`.
- `BackRefLang.thy` proves:
  - `xnullable_correctness`
  - `xder_correctness`
  - `xders_correctness`
  - `backref_lang_as_backref_lang4`
- `BackRefValues.thy` now defines:
  - `bval`
  - `bflat`
  - `BPrf`
- `BackRefValues.thy` proves:
  - `BL_flat_BPrf1`
  - `BL_flat_BPrf2`
  - `BL_flat_BPrf`
  - `bmkeps_flat`
  - `bmkeps_BPrf`
- Local/remote CI scaffolding now checks:
  - no Isabelle proof-bypass markers;
  - bounty board invariants and checked artifacts;
  - full inherited `Posix` session;
  - pilot `BackRefPilot` session;
  - GitHub Actions artifact certificate after successful proof checking.

## Current Headline Theorem

```isabelle
lemma BL_flat_BPrf:
  "BL r = {bflat v | v. BPrf v r}"
```

This is the value/Prf/flat correspondence layer for the pilot language,
including `BBACKREF`, `BHALF`, and `BRESIDUE`.

## Next Small Tasks

1. Draft `binjval` for one-character derivative reconstruction.
2. Prove `bflat (binjval r c v) = c # bflat v` when `BPrf v (xder c r)`.
3. Prove `BPrf (binjval r c v) r` when `BPrf v (xder c r)`.
4. Only then consider lexer-style recursion.
5. In parallel, draft derivative/value story for generalized `backref_lang4`
   before migrating the datatype.

## Do Not Start Yet

- Do not touch `Blexer.thy`.
- Do not touch `BlexerSimp.thy`.
- Do not touch bounds or closed-form theories.
- Do not claim a finite derivative bound for backreferences.

## Open Design Questions

- Whether `rep` should remain pure reconstruction metadata in values, or later
  become part of a stronger value invariant.
- Whether `BBackref` value evidence should carry both the captured value and
  the replayed copy explicitly. The current checked design carries one captured
  value and flattens it twice.
- Whether the pilot should migrate from the current two-language
  `backref_lang A B cs` to the generalized four-language
  `backref_lang4 L1 L2 L3 L4 cs`. The old definition is now checked as the
  special case `backref_lang4 {[]} A B {[]} cs`.
