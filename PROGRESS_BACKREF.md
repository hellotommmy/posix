# POSIX Backreference Progress

Last updated: 2026-05-27 (BR-022 bounded-fragment blueprint)

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

- PASS on 2026-05-27 local time (2026-05-26 UTC) with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`,
  and local CI certificate generation after adding `BackRefBoundedBlueprint.thy`.
  The new theory defines a semantic bounded-language/finite-left-quotient
  blueprint and proves `bounded_BBACKREF_finite_derivative_languages` and
  `bounded_GBACKREF4_finite_derivative_languages`; `BackRefBoundedBlueprint`
  replayed in about 0.27 seconds after replacing an expensive nested-image
  proof route.
- Coordination update on 2026-05-26: Cursor/Opus retired for overnight work;
  two Codex CLI workers are now the intended parallel setup. Codex Agent B owns
  BR-015 and `BackRefValues.thy`; Codex Agent A owns BR-022 and must stay on
  non-conflicting pilot-only statement/proof-prep. Local PowerShell CI now uses
  a global Isabelle build mutex so the two clones do not collide in the shared
  Isabelle cache.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard after adding the generalized `gabbsimp` and
  per-step `gbblexer_step_simp` layer in `BackRefGBlexer.thy`. A pilot-only
  precheck passed first; `BackRefGBlexer` replayed in about 2.3 seconds.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  local CI certificate generation, and explicit statement guard after adding
  generalized bitcoded retrieve transport in `BackRefGBlexer.thy`. A
  pilot-only precheck also passed; `BackRefGBlexer` replayed in about 1.9
  seconds and the timed proof work avoided broad nullable-tail automation.
- PASS on 2026-05-26 with direct Isabelle `BackRefPilot` build under a
  120-second timeout -- standalone generalized bitcoded lexer definitions
  in `BackRefGBlexer.thy` with `gbblexer_defined_iff`. The new theory replayed
  in about 0.9 seconds. Final full local CI also passed with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix` (0:03 elapsed), Isabelle
  `BackRefPilot` (0:03 elapsed), local CI certificate generation, and explicit
  statement guard.
- PASS on 2026-05-26 with direct Isabelle `BackRefPilot` build under a
  120-second timeout -- standalone generalized constructor lexer with
  `gblexer`, `gblexer_GPrf`, `gblexer_flat`, and `gblexer_correctness`.
  `BackRefLang4Values` replayed in about 1.4 seconds in the direct build.
  Final full local CI also passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate
  generation, and explicit statement guard.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, explicit statement guard, and
  local CI certificate generation -- generalized constructor injection
  evidence with `ginjval`, `ginjval_flat`, and `ginjval_GPrf`. A broad proof
  first timed out; it was replaced with explicit constructor/local-shape
  proofs, and `BackRefLang4Values` replayed in about 2.2 seconds in the final
  direct timed build.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and statement guard --
  generalized constructor epsilon evidence with `gmkeps`, `gmkeps_flat`, and
  `gmkeps_GPrf`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and statement guard --
  generalized constructor value correspondence with `GBL_flat_GPrf` and
  `gxders_GBL_flat_GPrf`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and statement guard --
  generalized constructor/value bridge with `GBACKREF4_flat_BPrf4` and
  `gxders_GBACKREF4_flat_BPrf4`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and statement guard -- standalone generalized constructor pilot with
  `gxder_correctness` and `gxders_correctness`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and statement guard -- BR-016 generalized `backref_lang4`
  value-evidence blueprint with `backref_lang4_flat_BPrf4`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and statement guard -- BR-020
  complete per-step bitcoded derivative simplifier with
  `bblexer_step_simp_correctness`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and statement guard -- BR-020 partial post-derivative bitcoded simplifier
  with `bblexer_simp_correctness`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and statement guard -- BR-018 bitcoded derivative retrieve transport and
  `bblexer_blexer_retrieve`.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and statement guard -- BR-018 partial bitcoded retrieve layer for nullable
  derivative evidence.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` and Isabelle `BackRefPilot` -- BR-017 bitcoded
  backreference lexer definitions in a separate pilot file.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and statement guard -- BR-008 generalized `backref_lang4` derivative story.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, worker role guard,
  and Isabelle `BackRefPilot` (0:04 elapsed) -- blexer definition and correctness.
- PASS on 2026-05-26 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` (0:05 elapsed) -- BR-014 blexer POSIX correctness
  plus `binjval` definition speedup.
- Previous PASS on 2026-05-26 with direct Isabelle `BackRefPilot`
  cold build (0:16 elapsed) after replacing slow `fun` processing.
- Previous PASS on 2026-05-26 with no-cheat guard, bounty guard, worker role guard,
  and Isabelle `BackRefPilot` (3:03 elapsed).
- Previous PASS on 2026-05-25 with no-cheat guard, bounty guard, admin role guard,
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
  - `backref_lang4I`
  - `Der_backref_lang4` (BR-008)
- `BackRefLang4Pilot.thy` now defines:
  - `gbrexp` with `GBASE`, `GALT`, and `GBACKREF4`
  - `GBL`, `gnullable`, `gtail4`, `gxder`, and `gxders`
- `BackRefLang4Pilot.thy` proves:
  - `gnullable_correctness`
  - `BL_gtail4`
  - `gxder_correctness`
  - `gxders_append`
  - `gxders_snoc`
  - `gxders_correctness`
- `BackRefBoundedBlueprint.thy` now defines:
  - `bounded_language`
  - `finite_left_quotients`
  - `suffix_closure`
  - `finite_BL_derivatives`
  - `finite_GBL_derivatives`
  - `BL_bounded`
  - `GBL_bounded`
  - `bounded_backref4_components`
- `BackRefBoundedBlueprint.thy` proves:
  - `bounded_language_finite`
  - `finite_left_quotients_if_finite_language`
  - `finite_left_quotients_if_bounded_language`
  - `bounded_BL_finite_derivative_languages`
  - `bounded_GBL_finite_derivative_languages`
  - `bounded_backref_lang_finite_left_quotients`
  - `bounded_backref_lang4_finite_left_quotients`
  - `bounded_BBACKREF_finite_derivative_languages`
  - `bounded_GBACKREF4_finite_derivative_languages`
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
  - `BPrf_xder_residue`
  - `binjval_flat` (BR-011)
  - `BPrf_BNTIMES_prepend`
  - `binjval_BPrf` (BR-012)
  - `blexer_BPrf` (BR-013)
  - `blexer_flat` (BR-013)
  - `blexer_correct_None` (BR-013)
  - `blexer_correct_Some` (BR-013)
  - `blexer_correctness` (BR-014 packaging)
  - `BPosix_binjval` (BR-014)
  - `blexer_POSIX` (BR-014)
  - `blexer_POSIX_iff` (BR-014)
- `BackRefBlexer.thy` now defines:
  - `bbit` with `BZ`, `BS`, and `Backbit`
  - annotated `barexp` constructors including `BABACKREF`, `BAHALF`,
    and `BARESIDUE`
  - `berase`, `bfuse`, `baintern`, `bbnullable`, `bbmkeps`, `bbder`,
    `bbders`, and `bblexer`
- `BackRefBlexer.thy` proves:
  - `berase_bfuse`
  - `berase_baintern`
  - `bbnullable_correctness`
  - `berase_bbder_residue`
  - `berase_bbder`
  - `berase_bbders`
  - `bblexer_defined_iff`
  - `berase_bbsimp`
  - `bbnullable_bbsimp`
  - `bretrieve_bbsimp`
  - `bbmkeps_bbsimp`
  - `bblexer_simp_correctness`
  - `bbders_simp`
  - `bblexer_step_simp`
  - `bbders_simp_bretrieve_blexer`
  - `bblexer_step_simp_correctness`
  - `bbmkeps_bretrieve`
  - `bretrieve_bfuse`
  - `bbder_bretrieve`
  - `bbders_bretrieve_blexer`
  - `bblexer_bretrieve_original`
  - `bblexer_blexer_retrieve`
  - `bblexer_bretrieve`
  - `bblexer_retrieve_correctness`
- `BackRefLang4Values.thy` now defines:
  - `bval4` with `BBackref4`
  - `bflat4`
  - `BPrf4`
  - `gbval` with `GVBase`, `GVLeft`, `GVRight`, and `GVBackref4`
  - `gflat`
  - `GPrf`
  - `gmkeps`
  - `gbackref4_from_tail`
  - `ginjval`
- `BackRefLang4Values.thy` proves:
  - `backref_lang4_flat_BPrf4_1`
  - `backref_lang4_flat_BPrf4_2`
  - `backref_lang4_flat_BPrf4`
  - `backref_lang_flat_BPrf4_special`
  - `GBACKREF4_flat_BPrf4`
  - `gxders_GBACKREF4_flat_BPrf4`
  - `GBL_flat_GPrf1`
  - `GBL_flat_GPrf2`
  - `GBL_flat_GPrf`
  - `gxders_GBL_flat_GPrf`
  - `gmkeps_flat`
  - `gmkeps_GPrf`
  - `gbackref4_from_tail_flat`
  - `gbackref4_from_tail_GPrf`
  - `gbackref4_from_xder_tail_flat`
  - `gbackref4_from_xder_tail_GPrf`
  - `ginjval_flat`
  - `ginjval_GPrf`
  - `gblexer`
  - `gblexer_GPrf`
  - `gblexer_flat`
  - `gblexer_correct_None`
  - `gblexer_correct_Some`
  - `gblexer_correctness`
- `BackRefGBlexer.thy` now defines:
  - `gabexp` with `GABASE`, `GAALTs`, and `GABACKREF4`
  - `gerase`, `gfuse`, `gaintern`, `gabnullable`, `gamkeps`, `gretrieve`,
    `gabbtail4`, `gabder`, `gabders`, and `gbblexer`
- `BackRefGBlexer.thy` proves:
  - `gerase_gfuse`
  - `gerase_gaintern`
  - `gabnullable_correctness`
  - `gamkeps_gretrieve`
  - `berase_gabbtail4`
  - `gerase_gabder`
  - `gerase_gabders`
  - `gbblexer_defined_iff`
  - `gretrieve_gfuse`
  - `gabder_gretrieve`
  - `gabders_gretrieve_gblexer`
  - `gbblexer_gblexer_retrieve`
  - `gbblexer_gretrieve`
  - `gbblexer_retrieve_correctness`
  - `gerase_gabbsimp`
  - `gabnullable_gabbsimp`
  - `gretrieve_gabbsimp`
  - `gamkeps_gabbsimp`
  - `gerase_gabders_simp`
  - `gabnullable_gabders_simp`
  - `gabders_simp_gretrieve_gblexer`
  - `gbblexer_simp_correctness`
  - `gbblexer_step_simp_defined_iff`
  - `gbblexer_step_simp_correctness`
- Local/remote CI scaffolding now checks:
  - no Isabelle proof-bypass markers;
  - bounty board invariants and checked artifacts;
  - full inherited `Posix` session;
  - pilot `BackRefPilot` session;
  - GitHub Actions artifact certificate after successful proof checking.
- Agent loop scaffolding now includes:
  - WSL/tmux repeated-prompt testing;
  - Cursor Hooks for Opus worker loops;
  - `SLEEP_RUNBOOK.md` for parallel Codex Desktop + Cursor/Opus starts.

## Current Headline Theorem

```isabelle
lemma BL_flat_BPrf:
  "BL r = {bflat v | v. BPrf v r}"
```

This is the value/Prf/flat correspondence layer for the pilot language,
including `BBACKREF`, `BHALF`, and `BRESIDUE`.

## Next Small Tasks

1. ~~Draft `binjval` for one-character derivative reconstruction.~~ DONE (BR-005)
2. ~~Prove `bflat (binjval r c v) = c # bflat v` when `BPrf v (xder c r)`.~~ DONE (BR-011)
3. ~~Prove `BPrf (binjval r c v) r` when `BPrf v (xder c r)`.~~ DONE (BR-012)
4. ~~Define and prove `blexer` for pilot `brexp` (BR-013).~~ DONE (BR-013)
5. ~~Prove `blexer` correctness for pilot `brexp` (BR-014).~~ DONE (BR-014)
6. ~~Draft derivative story for generalized `backref_lang4`.~~ DONE (BR-008)
7. ~~Start BR-017 bitcoded backreference lexer definitions in a new pilot file.~~ DONE (BR-017)
8. ~~Finish derivative-retrieve/decode-to-original-value correctness for BR-018.~~ DONE (BR-018)
9. ~~Finish BR-020 simplification rules for the bitcoded lexer.~~ DONE (BR-020)
10. ~~Finish BR-016 generalized value pilot.~~ DONE (BR-016)
11. ~~Add standalone generalized constructor derivative pilot.~~ DONE
12. ~~Bridge generalized constructor derivatives to `BPrf4` value evidence.~~ DONE
13. ~~Add generalized constructor value correspondence for all `gbrexp`.~~ DONE
14. ~~Add generalized constructor one-step value injection.~~ DONE
15. ~~Package a standalone generalized `gblexer` from `gnullable`/`gmkeps`/`gxder`/`ginjval`.~~ DONE
16. ~~Draft standalone generalized bitcoded lexer layer in a new theory.~~ DONE
    (`BackRefGBlexer.thy`)
17. ~~Extend generalized bitcoded layer with derivative retrieve transport
    relating `gbblexer` to `gblexer`.~~ DONE
18. ~~Optional next generalized bitcoded layer: add a conservative
    `gabbsimp`/step-simplifier story mirroring `BackRefBlexer.thy`.~~ DONE
19. ~~Add BR-022 bounded-fragment statement blueprint.~~ DONE
20. Remaining open lanes: BR-015 remains locked by Codex Agent B. BR-019
    now has a checked semantic finite-derivative-language blueprint, but
    should still wait until an admin accepts the bounded-fragment statement
    for any production bounds or closed-form work.

## BR-022 Bounded-Fragment Statement Blueprint (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit on top of `19e32b8`
- Agent lane: Codex Agent A new-file bounded-fragment blueprint lane
- Files changed: `BackRefBoundedBlueprint.thy`, `pilot/ROOT`,
  `PROGRESS_BACKREF.md`, `BACKREF_BOUNTIES.md`
- New checked definitions:
  - `bounded_language`
  - `finite_left_quotients`
  - `suffix_closure`
  - `finite_BL_derivatives`
  - `finite_GBL_derivatives`
  - `BL_bounded`
  - `GBL_bounded`
  - `bounded_backref4_components`
- New checked lemmas/theorems:
  - `bounded_language_finite`
  - `finite_left_quotients_if_finite_language`
  - `finite_left_quotients_if_bounded_language`
  - `bounded_BL_finite_derivative_languages`
  - `bounded_GBL_finite_derivative_languages`
  - `bounded_backref_lang_finite_left_quotients`
  - `bounded_backref_lang4_finite_left_quotients`
  - `bounded_BBACKREF_finite_derivative_languages`
  - `bounded_GBACKREF4_finite_derivative_languages`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `BackRefPilot` (0:13 elapsed), and no certificate;
    `BackRefBoundedBlueprint` replayed in about 0.25 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:13
    elapsed), and local CI certificate generation; `BackRefBoundedBlueprint`
    replayed in about 0.27 seconds.
  - Explicit statement guard PASS: 2 frozen theory files checked, no
    statement modifications.
- Performance note:
  - An earlier nested-product image proof for `backref_lang4` caused an
    abnormal long proof command and left a child build alive after the outer
    timeout. The child build was stopped, and the proof route was replaced by
    the simpler bounded-language path.
- Notes:
  - This is semantic statement/proof-prep for BR-019: bounded component
    languages imply finitely many semantic derivative languages for current
    `BBACKREF` and generalized `GBACKREF4`.
  - This does not claim a finite syntactic derivative-state bound and does not
    touch `BackRefValues.thy`, production `Blexer*`, bounds, or closed-form
    theories.
- Next smallest safe step: wait for Agent B's BR-015 result or admin approval
  of the precise BR-019 bounded-fragment theorem statement.

## Generalized Bitcoded Simplifier (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit on top of `32e5ff7`
- Agent lane: Codex new-file generalized bitcoded pilot lane
- Files changed: `BackRefGBlexer.thy` (+243 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked definitions:
  - `gabbsimp`
  - `gabders_simp`
  - `gbblexer_simp`
  - `gbblexer_step_simp`
- New checked lemmas/theorems:
  - `gerase_gabbsimp`
  - `gabnullable_gabbsimp`
  - `gabbsimp_gfuse`
  - `gretrieve_gabbsimp`
  - `gamkeps_gabbsimp`
  - `gerase_gabders_simp`
  - `gabnullable_gabders_simp`
  - `gabders_simp_gabnullable_gblexer`
  - `gabders_simp_gretrieve_gblexer`
  - `gbblexer_simp_correctness`
  - `gbblexer_step_simp_defined_iff`
  - `gbblexer_step_simp_correctness`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `BackRefPilot` (0:14 elapsed), and local CI certificate
    generation; `BackRefGBlexer` replayed in about 2.3 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI
    certificate generation.
  - Explicit statement guard PASS: 2 frozen theory files checked, no statement
    modifications.
- Notes:
  - This mirrors the existing `BackRefBlexer.thy` simplifier story at the
    generalized annotated layer and proves exact preservation of `gbblexer`.
  - This remains additive in `BackRefGBlexer.thy`; it does not touch frozen
    `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production `Blexer*`, bounds,
    closed-form theories, or Opus's BR-015 lock.
- Next smallest safe step: keep BR-019 blocked until an explicit
  bounded-fragment statement is accepted, or wait for Opus/admin direction on
  the remaining POSIX ordering lane.

## Generalized Bitcoded Retrieve Transport (2026-05-26)

- Branch: `codex/backref-values`
- Commit: uncommitted working-tree step on top of `cd72208`; `git fetch
  --all --prune` succeeded and `git pull --rebase --autostash origin
  codex/backref-values` reported already up to date before the edit.
- Agent lane: Codex new-file generalized bitcoded pilot lane
- Files changed: `BackRefGBlexer.thy` (+356 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked lemmas/theorems:
  - `gretrieve_alts_append`
  - `gretrieve_gfuse`
  - `gretrieve_gbackref4_from_tail`
  - `gretrieve_gbackref4_from_xder_tail`
  - `gabder_GAALTs_gretrieve`
  - `gabder_gretrieve`
  - `gabders_gabnullable_gblexer`
  - `gabders_gretrieve_gblexer`
  - `gbblexer_gretrieve_original`
  - `gbblexer_gblexer_retrieve`
  - `gbblexer_gretrieve`
  - `gbblexer_retrieve_correctness`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `BackRefPilot` (0:10 elapsed), and local CI certificate
    generation; `BackRefGBlexer` replayed in about 1.9 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03
    elapsed), and local CI certificate generation.
  - Explicit statement guard PASS: 2 frozen theory files checked, no statement
    modifications.
- Notes:
  - This is additive generalized bitcoded infrastructure only. It does not
    touch frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production
    `Blexer*`, bounds, closed-form theories, or Opus's BR-015 lock.
  - The nested nullable `GBACKREF4` tail branch is proved explicitly through
    `gabbtail4` and `gbackref4_from_tail`; no slow broad proof method was kept.
- Next smallest safe step: optionally mirror the checked `bbsimp`/per-step
  simplifier story for the generalized bitcoded layer, or wait for admin
  direction on BR-019's bounded-fragment statement.

## Generalized Bitcoded Lexer (2026-05-26)

- Branch: `codex/backref-values`
- Commit: uncommitted working-tree step on top of `ea9c7d0`; `git fetch
  --all --prune` succeeded and `git pull --rebase --autostash origin
  codex/backref-values` reported already up to date before the edit.
- Agent lane: Codex new-file generalized bitcoded pilot lane
- Files changed: `BackRefGBlexer.thy`, `pilot/ROOT`, `PROGRESS_BACKREF.md`
- New checked definitions:
  - `gabexp`, an annotated expression layer for `gbrexp`
  - `gerase`, `gfuse`, `gaintern`, and `gabnullable`
  - `gamkeps`, `gretrieve_alts`, and `gretrieve`
  - `gabbtail4`, `gabder`, `gabders`, and `gbblexer`
- New checked lemmas:
  - `gerase_gfuse`
  - `gerase_gaintern`
  - `gabnullable_correctness`
  - `gamkeps_gretrieve`
  - `berase_gabbtail4`
  - `gerase_gabder`
  - `gerase_gabders`
  - `gbblexer_defined_iff`
- Build: direct `timeout 120s isabelle build -v -d pilot BackRefPilot` PASS
  (0:13 elapsed, `BackRefGBlexer` 0.873s); final full local CI PASS with
  no-cheat guard, bounty guard, admin role guard, Isabelle `Posix` (0:03
  elapsed), Isabelle `BackRefPilot` (0:03 elapsed), and local CI certificate
  generation. Explicit statement guard PASS.
- Notes:
  - This is an additive new-file checkpoint and does not touch frozen `brexp`, `BL`,
    `xnullable`, `xder`, `BPrf`, production `Blexer*`, bounds, or closed-form
    theories.
  - The generalized `Backbit` retrieve order records prefix evidence first,
    then the captured `r2` string, matching the `backref_lang4` capture role.
  - A stale zero-CPU Isabelle build worker had been live for more than two
    hours; it was stopped before starting the timed direct build.
- Next smallest safe step: extend this layer with derivative retrieve transport
  relating `gbblexer` to `gblexer`.

## Standalone Generalized Constructor Lexer (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit; the branch was clean and synchronized with
  `origin/codex/backref-values` before this edit.
- Agent lane: Codex generalized constructor/value bridge lane
- Files changed: `BackRefLang4Values.thy`, `PROGRESS_BACKREF.md`
- New checked definition:
  - `gblexer`, a standalone lexer for the `gbrexp` layer using
    `gnullable`/`gmkeps`, `gxder`, and `ginjval`
- New checked lemmas/theorem:
  - `gblexer_GPrf`
  - `gblexer_flat`
  - `gblexer_correct_None`
  - `gblexer_correct_Some`
  - `gblexer_correctness`
- Build: direct `timeout 120s isabelle build -v -d pilot BackRefPilot` PASS
  (0:13 elapsed, `BackRefLang4Values` 1.441s); final full local CI PASS with
  no-cheat guard, bounty guard, admin role guard, Isabelle `Posix` (0:03
  elapsed), Isabelle `BackRefPilot` (0:04 elapsed), local CI certificate
  generation, and explicit statement guard PASS.
- Notes:
  - This is additive generalized-constructor packaging and does not touch
    frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production lexer files,
    bounds theories, or Opus's BR-015 lock.
  - It mirrors the checked `blexer` proof shape at the standalone generalized
    layer rather than adding POSIX ordering rules for `gbrexp`.
- Next smallest safe step: either commit this additive checkpoint or wait for
  BR-015/BR-019 direction from the admin.

## Generalized Constructor Injection Evidence (2026-05-26)

- Branch: `codex/backref-values`
- Commit: uncommitted working-tree step on top of local `986a4ca`; the branch
  was clean before this edit and `git fetch --all --prune` succeeded.
- Agent lane: Codex generalized constructor/value bridge lane
- Files changed: `BackRefLang4Values.thy` (+179 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked definitions:
  - `gbackref4_from_tail`, extracting `GBACKREF4` evidence from the checked
    post-capture tail value shape
  - `ginjval`, one-character derivative value reconstruction for `gbrexp`
- New checked lemmas:
  - `gbackref4_from_tail_flat`
  - `gbackref4_from_tail_GPrf`
  - `gbackref4_from_xder_tail_flat`
  - `gbackref4_from_xder_tail_GPrf`
  - `ginjval_flat`
  - `ginjval_GPrf`
- Build: direct `timeout 90s isabelle build -v -d pilot BackRefPilot` PASS
  (0:16 elapsed, `BackRefLang4Values` 2.172s); pilot-only local CI PASS with
  no-cheat guard, bounty guard, admin role guard, Isabelle `BackRefPilot`
  (0:05 elapsed), and local CI certificate generation; final full local CI
  PASS with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), certificate
  generation, and explicit statement guard PASS.
- Performance note:
  - An earlier broad `auto` over the whole `gbrexp` induction timed out after
    the wrapper's 300 second limit and left a child build running; the child
    build was stopped, and the proof was replaced with explicit `GALT` value
    cases plus localized backreference/tail helper lemmas.
- Notes:
  - This is additive generalized-constructor infrastructure and does not touch
    frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production lexer files,
    bounds theories, or Opus's BR-015 lock.
- Next smallest safe step: optionally package a `gblexer` for the standalone
  `gbrexp` layer from `gnullable`/`gmkeps`/`gxder`/`ginjval`; keep BR-015
  reserved for Opus and keep BR-019 blocked until an explicit bounded-fragment
  statement is accepted.

## Generalized Constructor Epsilon Evidence (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit; remote fetch was blocked by an HTTPS TLS
  handshake failure before work, and local `HEAD` matched
  `origin/codex/backref-values`.
- Agent lane: Codex generalized constructor/value bridge lane
- Files changed: `BackRefLang4Values.thy` (+20 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked definition:
  - `gmkeps`, nullable epsilon evidence for `GBASE`, `GALT`, and
    `GBACKREF4`
- New checked lemmas:
  - `gmkeps_flat`
  - `gmkeps_GPrf`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:14 elapsed), and local CI
  certificate generation; final full local CI PASS with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`,
  statement guard, and certificate generation.
- Notes:
  - This is additive generalized-constructor infrastructure and does not touch
    frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production lexer files,
    bounds theories, or Opus's BR-015 lock.
  - `gmkeps` mirrors `bmkeps` at the generalized layer and reuses checked
    component epsilon evidence for `GBACKREF4`.
- Next smallest safe step: keep BR-015 reserved for Opus; keep BR-019 blocked
  until an explicit bounded-fragment statement is accepted.

## Generalized Constructor Value Correspondence (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex generalized constructor/value bridge lane
- Files changed: `BackRefLang4Values.thy` (+90 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked definitions:
  - `gbval`, value evidence for the standalone `gbrexp` constructor layer
  - `gflat`, flattening `GBASE`, `GALT`, and `GBACKREF4` evidence
  - `GPrf`, proof evidence for `GBASE`, `GALT`, and `GBACKREF4`
- New checked lemmas/theorems:
  - `GBL_flat_GPrf1`
  - `GBL_flat_GPrf2`
  - `GBL_flat_GPrf`
  - `gxders_GBL_flat_GPrf`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:09 elapsed), and local CI
  certificate generation; final full local CI PASS with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`,
  statement guard, and certificate generation.
- Notes:
  - This extends the standalone generalized constructor pilot without
    modifying frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`, production
    lexer files, or bounds theories.
  - `GVBackref4` reuses the existing checked `BPrf4` evidence rather than
    duplicating the four-component value bridge.
- Next smallest safe step: leave BR-015 to Opus and keep BR-019 blocked until
  an admin accepts an explicit bounded-fragment statement.

## Generalized Constructor/Value Bridge (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex generalized constructor/value bridge lane
- Files changed: `BackRefLang4Values.thy` (+20/-1 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked theorems:
  - `GBACKREF4_flat_BPrf4`, connecting the standalone `GBACKREF4`
    constructor language to the four-component `BPrf4` evidence set
  - `gxders_GBACKREF4_flat_BPrf4`, lifting that bridge through generalized
    derivatives via `gxders_correctness`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:09 elapsed), and local CI
  certificate generation; final full local CI PASS with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix` (0:03 elapsed),
  Isabelle `BackRefPilot` (0:03 elapsed), and certificate generation.
- Notes:
  - This only imports `BackRefLang4Pilot` into `BackRefLang4Values.thy` and
    adds bridge theorems.
  - It does not modify frozen `brexp`, `BL`, `xnullable`, `xder`, `BPrf`,
    production lexer files, or bounds theories.
- Next smallest safe step: leave BR-015 to Opus and keep BR-019 blocked until
  an admin accepts an explicit bounded-fragment statement.

## Generalized backref_lang4 Constructor Pilot (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex generalized constructor blueprint lane
- Files changed: `BackRefLang4Pilot.thy`, `pilot/ROOT`,
  `PROGRESS_BACKREF.md`
- New checked definitions:
  - `gbrexp`, a standalone generalized expression layer wrapping existing
    `brexp` with `GBASE`, `GALT`, and `GBACKREF4`
  - `GBL`, `gnullable`, `gtail4`, `gxder`, and `gxders`
- New checked lemmas/theorems:
  - `gnullable_correctness`
  - `BL_gtail4`
  - `gxder_correctness`
  - `gxders_append`
  - `gxders_snoc`
  - `gxders_correctness`
- Build: full local CI PASS with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03
  elapsed), and statement guard.
- Notes:
  - This does not modify frozen `brexp`, `BL`, `xnullable`, `xder`, or
    `backref_lang`.
  - `gxder` uses `Der_backref_lang4` and represents the post-capture tail via
    the existing `BSEQ r3 (BSEQ (BRESIDUE (rev cs) (rev cs)) r4)` language.
  - This is a checked statement blueprint for a later admin-approved migration
    to real `BBACKREF4`-style constructors.
- Next smallest safe step: leave BR-015 to Opus and keep BR-019 blocked until
  the bounded-fragment statement is explicit.

## BR-016 Generalized backref_lang4 Value Pilot (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex generalized value blueprint lane
- Files changed: `BackRefLang4Values.thy`, `pilot/ROOT`,
  `PROGRESS_BACKREF.md`, `BACKREF_BOUNTIES.md`
- New checked definitions:
  - `bval4` with `BBackref4`
  - `bflat4`, flattening to `s1 @ s2 @ s3 @ rev cs @ s2 @ s4`
  - `BPrf4`, reusing existing `BPrf` evidence for the four component
    `brexp` languages
- New checked lemmas/theorems:
  - `backref_lang4_flat_BPrf4_1`
  - `backref_lang4_flat_BPrf4_2`
  - `backref_lang4_flat_BPrf4`
  - `backref_lang_flat_BPrf4_special`
- Build: full local CI PASS with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:04
  elapsed), and statement guard.
- Notes:
  - This is a blueprint theory only. It does not migrate the frozen `brexp`
    datatype or change `backref_lang`, `BL`, `xder`, `BPrf`, or `bval`.
  - The special-case corollary checks that the old two-language
    `backref_lang` is represented by the four-language value story with
    empty prefix and tail languages.
- Next smallest safe step: leave BR-015 to Opus; defer BR-019 until the bounded
  fragment statement is explicit.

## BR-020 Per-Step Derivative Simplifier (2026-05-26)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex new-file implementation lane
- Files changed: `BackRefBlexer.thy`, `PROGRESS_BACKREF.md`,
  `BACKREF_BOUNTIES.md`
- New checked definitions:
  - `bbders_simp`
  - `bblexer_step_simp`
- New checked lemmas/theorem:
  - `berase_bbders_simp`
  - `bbnullable_bbders_simp`
  - `bbders_simp_bbnullable_blexer`
  - `bbders_simp_bretrieve_blexer`
  - `bblexer_step_simp_defined_iff`
  - `bblexer_step_simp_correctness`
- Build: full local CI PASS with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and statement guard.
- Notes:
  - `bbders_simp` applies `bbsimp` after each bitcoded derivative step.
  - The proof reuses the existing retrieve transport: simplifying a derivative
    preserves retrieval for any checked derivative value, then induction over
    the input string recovers the same bitcode as `bblexer`.
- Next smallest safe step: BR-016 generalized value evidence, unless Opus
  releases or completes BR-015 first.

## BR-020 Post-Derivative Simplifier Partial (2026-05-26)

- Branch: `codex/backref-values`
- Commit: `968c32b`
- Agent lane: Codex new-file implementation lane
- Files changed: `BackRefBlexer.thy` (+174), `PROGRESS_BACKREF.md`
- New checked definitions:
  - `bbsimp`
  - `bblexer_simp`
- New checked lemmas/theorem:
  - `bfuse_append`
  - `berase_bbsimp`
  - `bbnullable_bbsimp`
  - `bbsimp_bfuse`
  - `bretrieve_stars_bbsimp`
  - `bretrieve_bbsimp`
  - `bbmkeps_bbsimp`
  - `bblexer_simp_correctness`
- Build: full local CI PASS with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04
  elapsed), and statement guard.
- Notes:
  - This is a conservative post-derivative simplifier:
    `bblexer_simp r s` simplifies `bbders (baintern r) s` once before the
    nullable/epsilon-code check.
  - It proves exact preservation of `bblexer`; it does not yet prove a
    `bbders_simp` loop that simplifies after each character derivative.
- Next smallest safe step: decide whether to extend BR-020 to a per-step
  `bbders_simp` theorem, or switch to BR-016 generalized value evidence.

## BR-018 Bitcoded Backreference Lexer Correctness (2026-05-26)

- Branch: `codex/backref-values`
- Agent lane: Codex new-file implementation lane
- Files changed: `BackRefBlexer.thy`, `PROGRESS_BACKREF.md`,
  `BACKREF_BOUNTIES.md`
- Bitcode semantic fixes:
  - `bretrieve` for `BABACKREF` now emits `Backbit (rev cs @ bflat v1)`,
    so retrieval from non-null capture values records the full captured string.
  - `bbder` now carries `bbmkeps r` into the transition from `BABACKREF` to
    `BAHALF`, matching the Scala reference shape where nullable capture
    evidence is preserved when replay begins.
- New checked lemmas/theorem:
  - `bretrieve_stars_append`
  - `bretrieve_alts_append`
  - `bretrieve_bfuse`
  - `bbder_residue_bretrieve`
  - `bbder_BAALTs_bretrieve`
  - `bbder_bretrieve`
  - `bbders_bbnullable_blexer`
  - `bbders_bretrieve_blexer`
  - `bblexer_bretrieve_original`
  - `bblexer_blexer_retrieve`
- Build: direct Isabelle `BackRefPilot` PASS with 90s timeout wrapper
  (0:09 elapsed after the final proof edit); full local CI PASS with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:04 elapsed),
  Isabelle `BackRefPilot` (0:04 elapsed), and statement guard.
- Notes:
  - `bblexer_blexer_retrieve` proves
    `bblexer r s = map_option (bretrieve (baintern r)) (blexer r s)`.
  - A broad proof attempt caused a timeout before this final structure; it was
    replaced with explicit list/case lemmas per the proof-performance rule.
- Next smallest safe step: BR-020 simplification rules in the new pilot file,
  or BR-016 generalized value pilot if avoiding simplification work.

## BR-018 Retrieve Layer Partial (2026-05-26)

- Branch: `codex/backref-values`
- Agent lane: Codex new-file implementation lane
- Files changed: `BackRefBlexer.thy` (+157 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked definitions:
  - `bretrieve_alts`
  - `bretrieve_stars`
  - `bretrieve`
- New checked lemmas/theorem:
  - `bretrieve_stars_replicate`
  - `bbmkeps_BAALTs_bretrieve`
  - `bbmkeps_bretrieve`
  - `bblexer_bretrieve`
  - `bblexer_retrieve_correctness`
- Build: full local CI PASS; no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and statement guard.
- Notes:
  - This does not complete BR-018 yet. It proves that nullable bitcoded
    evidence from an annotated derivative is exactly retrieval from
    `bmkeps (berase r)`, and packages the result for `bblexer`.
  - The next proof step should connect retrieval across `bbder`/`binjval` or
    define a decode/flex bridge back to the original `blexer` value.
- Next smallest safe step: prove a `bbder` retrieval transport lemma analogous
  to ordinary `bder_retrieve`, likely after adding any small helper facts for
  `bfuse` and backreference transition cases.

## BR-017 Bitcoded Backreference Lexer Definitions (2026-05-26)

- Branch: `codex/backref-values`
- Agent lane: Codex new-file implementation lane
- Files changed: `BackRefBlexer.thy`, `pilot/ROOT`, `PROGRESS_BACKREF.md`,
  `BACKREF_BOUNTIES.md`
- New checked definitions:
  - `bbit` with `Backbit string`
  - `barexp` with ordinary pilot constructors plus `BABACKREF`, `BAHALF`,
    and `BARESIDUE`
  - `berase`, `bfuse`, `baintern`, `bbnullable`, `bbmkeps`, `bbder`,
    `bbders`, and `bblexer`
- New checked lemmas:
  - `berase_bfuse`
  - `berase_baintern`
  - `bbnullable_correctness`
  - `berase_bbder_residue`
  - `berase_bbder`
  - `berase_bbders`
  - `bblexer_defined_iff`
- Build: full local CI PASS; Isabelle `Posix` (0:03 elapsed) and Isabelle
  `BackRefPilot` (0:03 elapsed).
- Notes:
  - The theory imports `BackRefValues` and does not modify production
    `Blexer.thy` or `BlexerSimp.thy`.
  - The derivative mirrors the checked `xder` shape after erasure. `Backbit`
    is emitted by nullable backreference evidence and by the transition to
    replay/half state.
- Next smallest safe step: BR-018 should add the retrieve/decode or code-value
  correctness story for the new bitcoded pilot.

## BR-008 Generalized backref_lang4 Derivative Story (2026-05-26)

- Branch: `codex/backref-values`
- Agent lane: Codex language-blueprint lane
- Files changed: `BackRefLang.thy`, `PROGRESS_BACKREF.md`,
  `BACKREF_BOUNTIES.md`
- New checked lemmas:
  - `backref_lang4I`
  - `Der_backref_lang4`
- Statement summary:
  - derivative splits into prefix derivative;
  - nullable-prefix capture derivative with accumulator update `c # cs`;
  - nullable-prefix and nullable-capture tail derivative
    `Der c (L3 ;; ({rev cs} ;; L4))`.
- Build: full local CI PASS; Isabelle `Posix` (0:35 elapsed) and
  Isabelle `BackRefPilot` (0:04 elapsed). Earlier pilot-only check passed in
  0:06 elapsed inside Isabelle.
- Guards: no-cheat, bounty, admin role guard, and statement guard pass
- Next smallest safe step: draft BR-016 value evidence shape for the
  generalized language without migrating the frozen datatype yet, or start
  BR-017 in a new `BackRefBlexer.thy` lane.

## BR-014 blexer POSIX Correctness (2026-05-26)

- Branch: `codex/backref-values`
- Agent lane: Opus proof lane with Codex stabilization/build verification
- Files changed: `BackRefValues.thy`, `PROGRESS_BACKREF.md`,
  `BACKREF_BOUNTIES.md`, and short coordination docs
- New checked lemmas:
  - `BPosix_BSTAR_value_shape`
  - `BPosix_BNTIMES_empty_replicate`
  - `blexer_correctness`
  - `BPosix_binjval`
  - `blexer_POSIX`
  - `blexer_POSIX_iff`
- Performance fix:
  - replaced slow `fun (sequential) binjval` with `primrec binjval`
    over `brexp` plus explicit `case v of ...` branches.
  - cold `BackRefPilot` build no longer spends about 200 seconds processing
    the `fun` command; checked cold build completed in about 16 seconds.
- Build: Isabelle `BackRefPilot` PASS
- Guards: no-cheat, bounty, role guard pass

## Do Not Start Yet

- Do not touch `Blexer.thy`.
- Do not touch `BlexerSimp.thy`.
- Do not touch bounds or closed-form theories.
- Do not claim a finite derivative bound for backreferences.

## blexer Definition and Correctness (2026-05-26)

- Branch: `codex/backref-values`
- Agent: Opus (Cursor headless recovery)
- Files changed: `BackRefValues.thy` (+53 lines), `PROGRESS_BACKREF.md`
- New checked definitions and lemmas:
  - `blexer`: lexer function for pilot `brexp` using `xder`/`binjval`/`bmkeps`
  - `blexer_BPrf`: soundness (`blexer r s = Some v \<Longrightarrow> BPrf v r`)
  - `blexer_flat`: flat correctness (`blexer r s = Some v \<Longrightarrow> bflat v = s`)
  - `blexer_correct_None`: rejection correctness (`s \<notin> BL r \<longleftrightarrow> blexer r s = None`)
  - `blexer_correct_Some`: full characterization
    (`s \<in> BL r \<longleftrightarrow> (\<exists>v. blexer r s = Some v \<and> BPrf v r \<and> bflat v = s)`)
- Build: Isabelle `BackRefPilot` PASS (0:04 elapsed)
- Guards: no-cheat, bounty, worker role all pass
- This completes BR-013. Next: BR-014 (blexer correctness w.r.t. POSIX ordering).

## binjval Correctness Proofs (2026-05-26)

- Branch: `codex/backref-values`
- Agent: Opus (Cursor headless recovery)
- Files changed: `BackRefValues.thy` (+17 lines), `PROGRESS_BACKREF.md`
- New checked lemmas:
  - `BPrf_xder_residue`: eliminates `BPrf v (xder_residue c cs rep)`
  - `binjval_flat`: `bflat (binjval r c v) = c # bflat v` (BR-011)
  - `BPrf_BNTIMES_prepend`: helper for BNTIMES value prepend
  - `binjval_BPrf`: `BPrf (binjval r c v) r` when `BPrf v (xder c r)` (BR-012)
- Build: Isabelle `BackRefPilot` PASS (3:03 elapsed)
- Guards: no-cheat, bounty, worker role all pass
- Blocker resolved: BNTIMES case in `binjval_BPrf` needed explicit helper
  because `BPrf.intros(7)` pattern `BStars (vs1 @ vs2)` does not unify with
  `BStars (v # ws1 @ ws2)` (Cons vs append).

## Governance Upgrade (2026-05-25)

- Branch: `codex/backref-values`
- Agent: Opus (Cursor)
- Authorized by: admin (Chengsong)
- Changes:
  - `BOUNTY_PROTOCOL.md`: rewritten to replicate Agent Hunt paper mechanics
    (competitive-collaborative system, 50k pool, 10% deposit locks, max 10 locks,
    lock-or-lose, sub-bounties, early-finish bonus, effort estimates, statement
    immutability).
  - `BACKREF_BOUNTIES.md`: added pool tracking, effort estimate columns,
    new bounties BR-011 through BR-020, updated lock rules to max 10.
  - `CLAUDE.md` (project profile): expanded bounty discipline section with
    full Agent Hunt mechanics, added statement immutability section, added
    guard scripts table.
  - `backref_bounty_guard.py`: upgraded to enforce max 10 locks, pool cap,
    effort estimate validation, sub-bounty ledger actions, lock deposit
    verification (10% of bounty).
  - `backref_statement_guard.py`: new guard enforcing frozen statement
    immutability by comparing against snapshots.
  - `agent_hunt_pipeline/snapshots/`: frozen snapshots of BackRefLang.thy
    and BackRefValues.thy.
- Guard results: all four guards pass.
- Build: no theory file changes; Isabelle build not required.

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
