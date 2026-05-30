# POSIX Backreference Progress

Last updated: 2026-05-31 (cubic partial-derivative universe checkpoint)

## Cubic Size-Bound Research Kickoff (2026-05-31)

- Branch: `codex/backref-values` at `89b40aa` before this kickoff note.
  Remote `origin/codex/backref-values` was already up to date with the checked
  reachable `BACKREF4` `cs` counterexample.
- Current dirty files before this note were this progress log plus local backup
  files `BackRefLang.thy~`, `BackRefLang4Pilot.thy~`, and `Lexer.thy~`. The
  backup files remain intentionally untracked and should not be committed.
- New research target from Chengsong: investigate how to reduce the size bound
  to cubic in the regex size for the non-backref fragment. Backreferences are
  explicitly excluded from the bounded fragment. The likely direction is a
  stronger, redesigned `bsimp` inspired by Antimirov partial derivatives and
  Chengsong's thesis final chapter, with a new 50k bounty pool and 25k reserved
  for the new simplifier definition.
- Important constraint: the new bound work must not weaken the checked
  backreference correctness path. Any new simplifier should have a clearly
  delimited non-backref fragment theorem first, then connect back to the
  current original files only through proved preservation lemmas.
- Checked first implementation checkpoint:
  - Added new bounty tasks `BR-031` through `BR-034` and raised the project
    pool to 100k simulated USD. `BR-032` reserves 25k for the new simplifier
    definition.
  - Added proof-only `rsimp3`/`rders_simp3` in `BasicIdentities.thy`.
    `rsimp3` keeps zero/one simplification, alternative flattening, and
    duplicate removal, and adds the Antimirov-style step that distributes a
    sequence over a left `RALTS` frontier. It intentionally does not distribute
    over right `RALTS`, because that would move right-side alternative choice
    bits before the left value in the annotated lexer.
  - Proved `RL_rsimp3`, the semantic preservation theorem for `rsimp3`.
  - Added annotated `bsimp3`/`bders_simp3` in `BlexerSimp.thy`, mirroring the
    left-frontier distribution while preserving right-hand choice-bit order.
  - Added `bsimp3_rerase` and `rders_simp3_size` in `FBound.thy`, establishing
    the transfer bridge from annotated states back to proof-only `rrexp`.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: define a non-backref partial-derivative universe whose
  elements are generated from original subterms and continuation contexts, then
  prove a cubic cardinality bound for that universe and show `rders_simp3`
  stays inside it.
- Checked second implementation checkpoint:
  - Added `rsubterms`, `rcontinuations`, and
    `partial_derivative_universe` in `GeneralRegexBound.thy`.
  - Proved `partial_derivative_universe_card_cubic`:
    `card (partial_derivative_universe r) <= (rsize r + 3)^3`.
    This is the first finite-universe replacement for the older
    `sizeNregex`-style counting argument; it is still an overapproximation,
    not yet the final closure theorem for `rders_simp3`.
  - Kept the proof granular: explicit `card_Un3_le`, `card_Un4_le`, image
    cardinality, and cubic padding lemmas. No long-running `auto`/`fun`
    proof search was introduced.
  - Local CI passed for both `Posix` and `BackRefPilot` after this checkpoint.
- Next research target: prove membership/closure, first for one derivative
  step and then for `rders_simp3`, showing that every generated frontier atom
  stays in `partial_derivative_universe r` for the non-backref fragment.
- Checked third implementation checkpoint:
  - Added `rlinear_continuations`, which keeps only syntactically reachable
    continuation contexts: sequence suffixes, star loop contexts, and bounded
    `RNTIMES r k` counters from the original `RNTIMES r n` node.
  - Proved `card_rlinear_continuations_le_rsize`, replacing the deliberately
    broad global-counter continuation set with a linear one.
  - Added `partial_derivative_frontier_universe` and proved
    `partial_derivative_frontier_universe_card_quadratic`:
    `card (partial_derivative_frontier_universe r) <= (rsize r + 2)^2`.
    This is the stronger cubic-size route: a quadratic number of frontier
    atoms times a linear atom-size bound, instead of the earlier cubic
    cardinality overapproximation.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: prove every element of the quadratic frontier universe
  has size at most linear in `rsize r`, then prove `rsimp3`/`rders_simp3`
  frontier membership for the non-backref fragment.
- Checked fourth implementation checkpoint:
  - Proved `rsubterms_member_size_le_rsize` and
    `rlinear_continuations_member_size_le_rsize`.
  - Proved `partial_derivative_frontier_universe_member_size_linear`:
    any atom in the quadratic frontier universe has structural size at most
    `Suc (rsize r + rsize r)`.
  - Corrected `partial_derivative_frontier_universe` to include reachable
    continuations themselves, not only `RSEQ p k` pairs. This is necessary
    because `rsimp3_SEQ_atom RONE k` simplifies directly to `k`.
    The cardinality theorem remains quadratic.
  - This establishes the two numeric ingredients for a cubic result:
    quadratic many frontier atoms, each of linear size. The remaining proof
    obligation is semantic/closure-shaped: show the actual `rsimp3` derivative
    frontier is a subset of this universe for the non-backref fragment.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: define a small `rfrontier`/normal-form extractor and
  prove closure lemmas for `rsimp3_SEQ`, then lift to one derivative step.
- Checked fifth implementation checkpoint:
  - Added proof-only `rsimp4`/`rders_simp4` in `BasicIdentities.thy`.
    `rsimp4` extends `rsimp3` by reassociating left-nested sequences:
    `SEQ (SEQ p k1) k2` is simplified recursively into a head-plus-continuation
    shape. This is the structural move needed for a cubic Antimirov-style
    frontier proof; without it, closure wants nested continuation towers.
  - Proved `RL_rsimp4`, the language preservation theorem.
  - The first draft used overlapping catch-all equations for `rsimp4_SEQ_atom`;
    that produced awkward split goals. The checked version uses explicit
    constructor equations, following the project rule that slow or strange
    proof states should be removed at the definition/proof-shape level.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: port `rsimp4` to annotated `bsimp4`, prove the
  `rerase` bridge, then use the quadratic frontier universe for closure.
- Checked sixth implementation checkpoint:
  - Added annotated `bsimp4`/`bders_simp4` in `BlexerSimp.thy`.
    The reassociation clause mirrors `rsimp4`: an `ASEQ` on the left is
    recursively converted into a head-plus-continuation shape while keeping
    bit prefixes in the corresponding annotated nodes.
  - Added `bsimp4_rerase` and `rders_simp4_size` in `FBound.thy`, proving
    that the annotated simplifier erases to `rsimp4`.
  - One subtle proof repair: `rerase_bsimp4_ASEQ` needs `rerase_fuse`
    explicitly, because the `AONE` case simplifies to `fuse (bs @ bs2) r2`
    while `rsimp4` sees only `rerase r2`.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: prove `rsimp4` frontier closure into
  `partial_derivative_frontier_universe`, then state the first actual cubic
  non-backref `rders_simp4` size theorem.
- Checked seventh implementation checkpoint:
  - Added recursive `rfrontier`/`rfrontiers` in `GeneralRegexBound.thy`.
    `RALTS` frontiers are now recursive, so nested alternatives are treated
    like Antimirov frontier sets rather than opaque syntax nodes.
  - Proved normalization lemmas for `rsimp_ALTs`, `rflts`, and `rdistinct`:
    if input frontiers are inside a set `U`, the normalized frontier remains
    inside `U`.
  - Added `rseq_sources` and `rfrontier_rsimp4_SEQ_subset`. This isolates the
    next closure obligation: to prove `rsimp4_SEQ` stays in a universe, it is
    enough to prove the row atoms `rsimp4_SEQ_atom x r2` stay there for each
    source `x` actually sequenced.
  - Local CI passed for both `Posix` and `BackRefPilot`.
- Next research target: prove row-atom closure for the quadratic frontier
  universe, or refine the continuation universe if the proof exposes a missing
  syntactic continuation shape.

## Worker B Original Bitcoded/Simplifier Checkpoint (2026-05-27)

- Branch: `codex/backref-values` at `d8f84f7`; `git fetch --all --prune`
  found no newer remote core-constructor work. The worktree had only the two
  untracked backup files `BackRefLang.thy~` and `BackRefLang4Pilot.thy~`
  before this checkpoint.
- Scope respected: only `Blexer.thy` and `PROGRESS_BACKREF.md` were changed
  by Worker B.
  `RegLangs.thy`, `PosixSpec.thy`, `Lexer.thy`, and `LexerSimp.thy` were read
  only.
- Initial core blocker: before the concurrent edit, original `RegLangs.thy`
  still had only
  `ZERO/ONE/CH/SEQ/ALT/STAR/NTIMES`, and original `PosixSpec.thy` still has
  only `Void/Char/Seq/Right/Left/Stars`. Therefore the BR-027/BR-028
  constructor cases for `BACKREF4/HALF/RESIDUE`, the corresponding original
  value constructors, and the `injval`/`mkeps` bridge are not yet available.
  Worker B did not fake wrappers or introduce `bbit`, `barexp`, `gabexp`, or
  any new `BackRef*` wrapper files.
- Checked original-file scaffold added:
  - `Blexer.thy:erase_AALTs_ignore_bits [simp]`, mirroring the pilot
    `berase_BAALTs_ignore_bits` fact directly in the original `arexp` layer.
    This is a non-conflicting helper for future retrieve/derivative proofs
    where `AALTs` bit prefixes must not affect erasure.
- Precise BR-027 port sections to apply once Worker A lands the original core
  constructors:
  - Extend original `bit` with `Backbit string` unless admin chooses a
    different in-band string encoding.
  - Extend original `arexp` with annotated cases matching the frozen core
    arities: `ABACKREF4` for `BACKREF4`, `AHALF` for `HALF`, and `ARESIDUE`
    for `RESIDUE`. Use only these original constructors.
  - Port the pilot `BackRefGBlexer.gaintern/gabder/gretrieve` shape into
    original `intern/bder/retrieve`, and port the simple
    `BackRefBlexer.bbder_residue` shape into original `bder` for `RESIDUE`.
  - Preserve the original theorem names and interfaces:
    `erase_bder`, `retrieve_code`, `bmkeps_retrieve`, `bder_retrieve`,
    `MAIN_decode`, and `blexer_correctness`.
- Precise BR-028 port sections queued after BR-027 parses:
  - Add `eq1`, `flts`, `bsimp_ASEQ`, `bsimp_AALTs`, and `bsimp` cases for the
    new annotated constructors without replacing the aggressive rewrite route.
  - Extend `rrewrite/srewrite` only with constructor context rules and any
    approved semantics-preserving backreference simplifications.
  - Repair, in order, `rewrites_to_bsimp`, `rewrite_preserves_bder`,
    `central`, `main_blexer_simp`, and `blexersimp_correctness`.
- BR-029/BR-030 blocker: `BasicIdentities.thy`, `ClosedForms.thy`,
  `ClosedFormsBounds.thy`, `FBound.thy`, and `GeneralRegexBound.thy` still
  depend on the pre-migration `rrexp` skeleton. Their TODOs require admin/core
  approval on whether to migrate the closed-form chain to `rexp` or
  temporarily extend `rrexp`; Worker B made no speculative datatype edit.
- Build before the concurrent core edit:
  `powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin`
  passed after the scaffold with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:04
  elapsed), and local CI certificate generation. Baseline before the edit also
  passed with cached `Posix`/`BackRefPilot`.
- Final build after a concurrent `RegLangs.thy` core-constructor edit appeared
  in the worktree failed before Worker B-owned files were replayed. Failure:
  Isabelle could not prove termination of `RegLangs.thy:der` for the
  `BACKREF4` tail call
  `der c (SEQ r3 (SEQ (RESIDUE (rev cs) (rev cs)) r4))`. `RegLangs.thy` is
  outside Worker B's write scope, so this checkpoint stops with that blocker
  instead of editing the core layer.

## Original-File Migration Audit (2026-05-27)

- Admin direction: stop growing `BackRef*` wrapper files as bounty targets.
  Future bounty should only count direct extensions of the original `rexp`,
  `val`, `arexp`, `lexer`, `blexer`, `bsimp`, and bounds theorem chain.
- Round status: two subagents completed two read-only audit rounds:
  - semantic/value lane: `RegLangs.thy`, `PosixSpec.thy`, `Lexer.thy`,
    `LexerSimp.thy`
  - bitcoded/bounds lane: `Blexer.thy`, `BlexerSimp.thy`,
    `BasicIdentities.thy`, `GeneralRegexBound.thy`, `ClosedForms.thy`,
    `ClosedFormsBounds.thy`, `FBound.thy`
- Comment-only TODOs were added to original files. They mark which
  datatype/function/theorem families need definition augmentation, proof
  constructor cases, deletion/migration, or admin approval.
- New low-value active bounty: BR-023 `Original-file migration TODO audit`
  for admin review. No payout collected yet.
- Admin approval is required before implementation for the exact `rexp`
  constructor shape, value constructors/flattening, POSIX priority rule,
  bit-code representation, and whether bounds-only `rrexp` is removed or
  temporarily retained.
- Proof-performance rule remains mandatory: any Isabelle command running around
  10 seconds must be split or narrowed; a 200 second `fun`/proof command is a
  bug to fix, not a normal build delay.

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

- PASS on 2026-05-27 (abbypan) with no-cheat guard after adding simple lexer
  derivative-prefix API (`blexer_xders_*` family) to `BackRefValues.thy`.
  New checked lemmas mirror the existing `gblexer_gxders_*` family from
  `BackRefLang4Values.thy`, filling the asymmetry between simple and
  generalized lexer APIs. New facts:
  `blexer_xders_defined_BL_iff`,
  `blexer_xders_None_BL_iff`,
  `blexer_xders_Some_BL`,
  `xders_BPrf_BL_iff`,
  `blexer_xders_defined_BPrf_iff`,
  `blexer_xders_None_BPrf_iff`,
  `blexer_xders_Some_BPrf`,
  `blexer_xders_BPrf_obtains`,
  `blexer_xders_BL_obtains`,
  `blexer_xders_BL_cases`,
  `blexer_xders_BPrf_cases`,
  `blexer_xders_defined_POSIX_iff`,
  `blexer_xders_Some_POSIX`,
  `blexer_xders_None_POSIX_iff`,
  `blexer_xders_POSIX_obtains`,
  `blexer_xders_POSIX_cases`.
  The simple side now has POSIX-specific derivative-prefix lemmas that the
  generalized side does not yet have. Files changed:
  `BackRefValues.thy` (+170 lines), `PROGRESS_BACKREF.md`.

- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding individual left-quotient finite/card
  wrappers in the bounded-fragment blueprint. New checked facts in
  `BackRefBoundedBlueprint.thy` package `BL_bound`/`GBL_bound` results for
  single `Ders` quotients, derivative residual quotients, and the ordinary
  `BBACKREF` plus generalized `GBACKREF4` constructor instances, including
  `BL_bound_left_quotient_finite`,
  `GBL_bound_left_quotient_finite`,
  `BL_bound_left_quotient_card_bound`,
  `GBL_bound_left_quotient_card_bound`,
  `BL_bound_xders_left_quotient_finite`,
  `GBL_bound_gxders_left_quotient_finite`,
  `BL_bound_BBACKREF_left_quotient_finite`,
  `GBL_bound_GBACKREF4_left_quotient_finite`,
  `BL_bound_residual_left_quotient_finite`,
  `GBL_bound_residual_left_quotient_finite`,
  `BL_bound_BBACKREF_residual_left_quotient_card_bound`, and
  `GBL_bound_GBACKREF4_residual_left_quotient_card_bound`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+226) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 4.298 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 4.277 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:35 elapsed), cached Isabelle
  `BackRefPilot` (0:03 elapsed), and local CI certificate generation;
  explicit statement guard PASS. After fast-forwarding to remote commit
  `82e2ca7`, the autostash conflict was limited to the `PROGRESS_BACKREF.md`
  title/order and both progress entries plus theory changes were preserved.
  Final post-sync full local CI passed with no-cheat guard, bounty guard,
  admin role guard, cached Isabelle `Posix` (0:04 elapsed), cached Isabelle
  `BackRefPilot` (0:05 elapsed), and local CI certificate generation;
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding ordinary and generalized bitcoded
  frontend derivative-prefix residual-evidence wrappers. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_xders_BPrf_retrieve_iff`,
  `bblexer_frontends_xders_defined_BPrf_iff`,
  `bblexer_frontends_xders_None_BPrf_iff`,
  `bblexer_frontends_xders_Some_BPrf`,
  `bblexer_frontends_xders_BPrf_cases`,
  `gbblexer_frontends_gxders_GPrf_retrieve_iff`,
  `gbblexer_frontends_gxders_defined_GPrf_iff`,
  `gbblexer_frontends_gxders_None_GPrf_iff`,
  `gbblexer_frontends_gxders_Some_GPrf`, and
  `gbblexer_frontends_gxders_GPrf_cases`, packaging all three bitcoded
  frontend variants after a consumed derivative prefix `p` against explicit
  residual `BPrf`/`GPrf` evidence for `xders r p` / `gxders r p`. Files
  changed before this progress note: `BackRefBitcodedSummary.thy` (+168) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.905 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 1.019 seconds. Pre-progress full local CI passed with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix` (0:04 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed), and local CI certificate generation. After
  fast-forwarding to concurrent remote commit `abcd83e`, the autostash
  conflict was limited to the `BackRefBitcodedSummary.thy` generalized
  derivative-prefix insertion point and the `PROGRESS_BACKREF.md` title; both
  the remote `*_same_iff` wrappers and this residual-evidence wrapper set were
  preserved. Post-sync pilot-only local CI passed with `BackRefPilot` (0:18
  elapsed), with `BackRefBitcodedSummary` replaying in about 0.970 seconds.
  After rebasing over concurrent remote commit `645b9ec`, the conflict was
  limited to `PROGRESS_BACKREF.md` title/order and both progress entries plus
  theory changes were preserved. Final post-rebase full local CI passed with
  no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`, Isabelle
  `BackRefPilot`, and local CI certificate generation; explicit statement
  guard PASS. Next smallest safe step: stop until the admin opens a new
  bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS after adding ordinary and generalized
  derivative-prefix final retrieve correctness wrappers. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_xders_final_retrieve_correctness` and
  `gbblexer_frontends_gxders_final_retrieve_correctness`, packaging all three
  bitcoded frontend variants after a consumed derivative prefix `p` so any
  accepted output is the normalized residual final-retrieve output for
  `xders r (p @ s)` / `gxders r (p @ s)` and carries the corresponding
  `bmkeps`/`gmkeps` empty residual evidence. Files changed before this
  progress note: `BackRefBitcodedSummary.thy` (+44) and `PROGRESS_BACKREF.md`.
  Baseline pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.865 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 1.150 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:36 elapsed), cached Isabelle `BackRefPilot` (0:03 elapsed), and
  local CI certificate generation; explicit statement guard PASS. Final
  after-progress full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:37 elapsed), Isabelle `BackRefPilot` (0:18
  elapsed), `BackRefBitcodedSummary` replaying in about 0.988 seconds, and
  local CI certificate generation. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding ordinary and generalized bitcoded
  frontend derivative-prefix wrappers. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_xders_defined_BL_iff`,
  `bblexer_frontends_xders_None_BL_iff`,
  `bblexer_frontends_xders_Some_BL`,
  `bblexer_frontends_xders_BL_cases`,
  `bblexer_frontends_xders_final_cases`,
  `gbblexer_frontends_gxders_defined_GBL_iff`,
  `gbblexer_frontends_gxders_None_GBL_iff`,
  `gbblexer_frontends_gxders_Some_GBL`,
  `gbblexer_frontends_gxders_GBL_cases`, and
  `gbblexer_frontends_gxders_final_cases`, packaging all three bitcoded
  frontend variants after a consumed derivative prefix `p` against
  `p @ s` membership in the original ordinary/generalized language and the
  normalized residual final-retrieve output. Files changed before this
  progress note: `BackRefBitcodedSummary.thy` (+182) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.721 seconds. An initial post-edit proof attempt failed only for the
  bundled `Some` membership wrappers because `auto` did not extract the
  existential-defined equivalence strongly enough; the proof was narrowed to
  explicit per-frontend `blast` steps. Post-fix pilot-only local CI passed
  with `BackRefPilot` (0:18 elapsed), with `BackRefBitcodedSummary` replaying
  in about 2.025 seconds. Full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:34 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed, cached), and local CI certificate generation.
  After fast-forwarding to concurrent remote commit `57c8cdb`, the autostash
  conflict was limited to `PROGRESS_BACKREF.md` title/order and both progress
  entries plus theory changes were preserved. Final post-rebase full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:36 elapsed), Isabelle `BackRefPilot` (0:18 elapsed),
  `BackRefBitcodedSummary` replaying in about 0.930 seconds, and local CI
  certificate generation; explicit statement guard PASS. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only similarly
  direct downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS before rebasing over remote commit
  `97668d6`; during the rebase the broader remote derivative-prefix wrapper
  facts were preserved and the non-duplicated checked additions kept from this
  step are `bblexer_frontends_xders_same_iff` and
  `gbblexer_frontends_gxders_same_iff` in `BackRefBitcodedSummary.thy`.
  These package the three bitcoded frontend variants run on `xders r p` /
  `gxders r p` as rejecting together or accepting with one shared bit output
  exactly when `p @ s \<notin> BL r` / `p @ s \<notin> GBL r` or
  `p @ s \<in> BL r` / `p @ s \<in> GBL r`. Files changed before this
  progress note: `BackRefBitcodedSummary.thy` and `PROGRESS_BACKREF.md`.
  Next smallest safe step: stop until the admin opens a new bounty/phase, or
  add only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS after adding derivative-prefix `GPrf`
  packaging facts for the standalone generalized value lexer. New checked
  facts in `BackRefLang4Values.thy` are `gxders_GPrf_GBL_iff`,
  `gblexer_gxders_defined_GPrf_iff`,
  `gblexer_gxders_None_GPrf_iff`, `gblexer_gxders_Some_GPrf`,
  `gblexer_gxders_GPrf_obtains`, and
  `gblexer_gxders_GPrf_cases`, relating `gblexer (gxders r p) s`
  directly to explicit `GPrf` evidence for `gxders r p` and to
  `p @ s \<in> GBL r`. Files changed before this progress note:
  `BackRefLang4Values.thy` (+68) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefLang4Values` replaying in about 1.872 seconds. The first post-edit
  proof of `gxders_GPrf_GBL_iff` was too broad: simplification left two
  evidence-existence forms, and the next version still needed equality
  orientation normalization. It was replaced with an explicit chain through
  `s \<in> GBL (gxders r p)` plus a localized `auto` step. Post-fix pilot-only
  local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefLang4Values` replaying in about 2.061 seconds. Initial full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix`, Isabelle `BackRefPilot`, and local CI certificate generation;
  explicit statement guard PASS. After rebasing over concurrent remote commit
  `792a41d`, the progress conflict was limited to the title/order and both
  entries plus theory changes were preserved. Final post-rebase full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix`, Isabelle `BackRefPilot`, and local CI certificate generation;
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding ordinary and generalized bitcoded
  frontend final retrieve evidence wrappers. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_final_retrieve_correctness` and
  `gbblexer_frontends_final_retrieve_correctness`, packaging that any accepted
  result from any of the three bitcoded frontend variants is the normalized
  final derivative retrieve output and carries the corresponding
  `bmkeps`/`gmkeps` residual proof plus empty flat witness. Files changed
  before this progress note: `BackRefBitcodedSummary.thy` (+40) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.781 seconds. An initial proof attempt for the wrappers failed
  because the residual epsilon evidence did not follow from the normalized
  membership rewrite alone; the proof was narrowed to reuse the already
  checked per-frontend retrieve correctness lemmas. Post-fix pilot-only local
  CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.682 seconds. Full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:35 elapsed), Isabelle `BackRefPilot` (0:17 elapsed),
  `BackRefBitcodedSummary` replaying in about 0.720 seconds, and local CI
  certificate generation; explicit statement guard PASS. Sync note:
  `git pull --rebase --autostash origin codex/backref-values` fast-forwarded
  to `1dfb775`; the autostash conflicted only in `PROGRESS_BACKREF.md`, and
  both progress entries plus theory changes were preserved. Final post-sync
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:17 elapsed),
  `BackRefBitcodedSummary` replaying in about 1.716 seconds, and local CI
  certificate generation; explicit statement guard PASS. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only similarly
  direct downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after preserving the uncommitted generalized
  value-lexer case wrappers across the fast-forward to remote commit
  `3eb3be6` and adding derivative-prefix packaging facts for the standalone
  generalized value lexer. New checked facts in `BackRefLang4Values.thy` are
  `gblexer_gxders_defined_GBL_iff`, `gblexer_gxders_None_GBL_iff`,
  `gblexer_gxders_Some_GBL`, `gblexer_gxders_GBL_obtains`, and
  `gblexer_gxders_GBL_cases`, relating `gblexer (gxders r p) s` directly to
  `p @ s \<in> GBL r`. Files changed before this progress note:
  `BackRefLang4Values.thy` (+90 total since `3eb3be6`, including +47 in this
  step) and `PROGRESS_BACKREF.md`. Sync note: `git pull --rebase --autostash
  origin codex/backref-values` fast-forwarded to `3eb3be6`; the autostash
  conflicted only in `PROGRESS_BACKREF.md`, and both progress entries plus
  theory changes were preserved. Baseline post-sync pilot-only local CI passed
  with `BackRefPilot` (0:19 elapsed), with `BackRefLang4Values` replaying in
  about 2.084 seconds. An initial post-edit pilot check exposed an overly broad
  proof for `gblexer_gxders_GBL_obtains`; it was replaced by an explicit
  `s \<in> GBL (gxders r p)` step through `gxders_correctness`. Post-fix
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefLang4Values` replaying in about 2.174 seconds. Final full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:37 elapsed), Isabelle `BackRefPilot` (0:03 elapsed, cached), and local CI
  certificate generation; an explicit statement guard check also passed. After
  rebasing over concurrent remote commit `9a2d375`, the progress conflict was
  limited to title/order and both entries were preserved. Post-rebase
  pilot-only local CI passed with `BackRefPilot` (0:18 elapsed), with
  `BackRefLang4Values` replaying in about 2.690 seconds. Final post-rebase
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and local CI certificate generation; explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS after adding ordinary and generalized
  bitcoded frontend case wrappers keyed by the value lexer result. New checked
  facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_blexer_cases` and
  `gbblexer_frontends_gblexer_cases`, packaging that a failed
  `blexer`/`gblexer` run makes all three bitcoded frontend variants reject,
  while a successful value run gives the same retrieved bit output for all
  three frontend variants. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+38) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:18 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.631 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:18 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.784 seconds. Pre-progress
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:04 elapsed,
  cached), and local CI certificate generation; explicit statement guard PASS.
  Final
  after-progress full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:03
  elapsed), and local CI certificate generation; explicit statement guard
  PASS. Next smallest safe step: stop until the admin opens a new
  bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after preserving the uncommitted bitcoded frontend
  output equality wrappers across the fast-forward to remote commit `1ad2a3e`
  and adding ordinary/generalized frontend output uniqueness wrappers. New
  checked facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_output_unique` and
  `gbblexer_frontends_output_unique`, packaging that any two successful
  bitcoded frontend variants report the same bit output. Files changed before
  this progress note: `BackRefBitcodedSummary.thy` (+18 in this step, +42
  total uncommitted since `1ad2a3e`) and `PROGRESS_BACKREF.md`. Sync note:
  `git pull --rebase --autostash origin codex/backref-values` fast-forwarded
  to `1ad2a3e`; the autostash conflicted only in the progress title, and both
  progress entries plus theory changes were preserved. Baseline post-sync
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.637 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.719 seconds. Full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:35 elapsed), Isabelle `BackRefPilot` (0:03 elapsed, cached), and local CI
  certificate generation; explicit statement guard PASS. After rebasing over
  concurrent remote commit `b23b16a`, the progress conflict was limited to the
  title/order and all progress entries were preserved. Post-rebase pilot-only
  local CI passed with `BackRefPilot` (0:18 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.626 seconds. Final post-rebase
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and
  local CI certificate generation; explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding bitcoded frontend output equality
  wrappers for ordinary and generalized value evidence. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_blexer_retrieve_eq`,
  `bblexer_frontends_POSIX_retrieve_eq`, and
  `gbblexer_frontends_gblexer_retrieve_eq`, packaging that any reported bit
  output from the three frontend variants is the retrieve output for the
  known `blexer`/POSIX/`gblexer` value. Files changed before this progress
  note: `BackRefBitcodedSummary.thy` (+24) and `PROGRESS_BACKREF.md`.
  Baseline pilot-only local CI passed with `BackRefPilot` (0:16 elapsed),
  with `BackRefBitcodedSummary` replaying in about 0.545 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.582 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:34 elapsed), Isabelle `BackRefPilot` (0:03 elapsed, cached), and
  local CI certificate generation; explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding direct generalized value-lexer accept/reject case
  wrappers. New checked facts in `BackRefLang4Values.thy` are
  `gblexer_defined_GBL_iff`, `gblexer_None_GBL_iff`,
  `gblexer_GBL_cases`, and `gblexer_GPrf_cases`, packaging the standalone
  generalized value lexer against `GBL` membership and explicit `GPrf`
  evidence without changing `gbrexp`, `GBL`, `gxder`, `GPrf`, or production
  lexer files. Files changed before this progress note:
  `BackRefLang4Values.thy` (+43) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:18 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefLang4Values` replaying in about 1.980 seconds. Pre-progress full
  local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:04 elapsed,
  cached), and local CI certificate generation. Final after-progress full
  local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation; a subsequent explicit statement guard
  check also passed. Next smallest safe step: stop until the admin opens a new
  bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding generalized value-lexer evidence packaging facts.
  New checked facts in `BackRefLang4Values.thy` are `gblexer_Some_GBL`,
  `gblexer_GBL_obtains`, `gblexer_defined_GPrf_iff`, and
  `gblexer_None_GPrf_iff`, aligning the standalone generalized value lexer
  with the ordinary value and bitcoded wrapper style without changing
  `gbrexp`, `GBL`, `gxder`, or `GPrf`. Files changed before this progress
  note: `BackRefLang4Values.thy` (+35) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). An initial
  post-edit pilot check exposed one overly implicit option-case proof in
  `gblexer_None_GPrf_iff`; the proof was replaced by an explicit
  `None`-versus-`Some` equivalence. Post-fix pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefLang4Values` replaying in about
  2.208 seconds. Pre-progress full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed, cached), and local CI certificate generation.
  Final after-progress full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:18 elapsed), `BackRefLang4Values` replaying in about 2.043 seconds, and
  local CI certificate generation. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding explicit accept/reject case wrappers for the
  ordinary and generalized bitcoded frontend groups keyed by final derivative
  nullability. New checked facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_xnullable_cases` and
  `gbblexer_frontends_gnullable_cases`, packaging all three frontend variants
  to reject together when `xnullable (xders r s)` / `gnullable (gxders r s)`
  is false and to return the same normalized final retrieval bit witness when
  it is true. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+66) and `PROGRESS_BACKREF.md`. Baseline
  synced pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.494 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.550 seconds. Pre-progress full
  local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:37 elapsed), Isabelle `BackRefPilot` (0:03 elapsed,
  cached), and local CI certificate generation. Explicit after-progress guards
  passed: statement guard, no-cheat guard, bounty guard, and admin role guard.
  Final after-progress full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot`
  (0:18 elapsed), `BackRefBitcodedSummary` replaying in about 0.668 seconds,
  and local CI certificate generation. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS after adding derivative-nullability
  wrappers for the ordinary and generalized bitcoded frontend groups. New
  checked facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_xnullable_iff`,
  `bblexer_frontends_xnullable_same_iff`,
  `gbblexer_frontends_gnullable_iff`, and
  `gbblexer_frontends_gnullable_same_iff`, packaging all three frontend
  variants against the nullable final derivative (`xnullable (xders r s)` /
  `gnullable (gxders r s)`) and the shared accepted-input bit witness. Files
  changed before this progress note: `BackRefBitcodedSummary.thy` (+110) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.479 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.517 seconds. Pre-progress full local CI passed with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix` (0:37 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed, cached), and local CI certificate generation;
  explicit statement guard PASS. After fast-forwarding to concurrent remote
  commit `e0aee64` and then rebasing over `23fb6c1`, the progress conflicts
  were limited to title/order; all progress entries were preserved. Final
  post-rebase full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:17
  elapsed), `BackRefBitcodedSummary` replaying in about 0.564 seconds, and
  local CI certificate generation; explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct semantic left-quotient and
  residual-left-quotient finiteness/cardinality wrappers in
  `BackRefBoundedBlueprint.thy`. New checked facts are
  `bounded_language_left_quotient_finite`,
  `bounded_language_left_quotient_card_bound`,
  `bounded_backref_lang_left_quotient_finite`,
  `bounded_backref_lang4_left_quotient_finite`,
  `bounded_backref_lang_left_quotient_card_bound`,
  `bounded_backref_lang4_left_quotient_card_bound`,
  `bounded_language_residual_left_quotient_finite`,
  `bounded_language_residual_left_quotient_card_bound`,
  `bounded_backref_lang_residual_left_quotient_finite`,
  `bounded_backref_lang4_residual_left_quotient_finite`,
  `bounded_backref_lang_residual_left_quotient_card_bound`, and
  `bounded_backref_lang4_residual_left_quotient_card_bound`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+142) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:19 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 5.2 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 4.7 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle
  `BackRefPilot` (0:16 elapsed), local CI certificate generation, and
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct semantic left-quotient member
  length wrappers in `BackRefBoundedBlueprint.thy`. New checked facts are
  `bounded_language_left_quotient_length_bound`,
  `bounded_language_left_quotient_length_bound_mono`,
  `bounded_backref_lang_left_quotient_length_bound`,
  `bounded_backref_lang4_left_quotient_length_bound`,
  `bounded_backref_lang_left_quotient_length_bound_mono`, and
  `bounded_backref_lang4_left_quotient_length_bound_mono`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+65) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 3.8 seconds. Post-edit pilot-only local CI passed with `BackRefPilot`
  (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in about 4.5
  seconds. Full local CI passed with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:03
  elapsed), local CI certificate generation, and explicit statement guard
  PASS. Next smallest safe step: stop until the admin opens a new
  bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS after adding exact accept/reject case
  wrappers for the ordinary and generalized bitcoded frontend groups. New
  checked facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_BL_final_cases` and
  `gbblexer_frontends_GBL_final_cases`, packaging all three frontend variants
  to reject together outside `BL`/`GBL` and to return the same normalized
  unsimplified final retrieval expression on accepted inputs. Files changed
  before this progress note: `BackRefBitcodedSummary.thy` (+70) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.244 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.307 seconds. Final after-progress full local CI passed with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:36 elapsed),
  Isabelle `BackRefPilot` (0:17 elapsed), `BackRefBitcodedSummary` replaying
  in about 0.323 seconds, and local CI certificate generation; explicit
  statement guard passed. After fast-forwarding to concurrent remote commit
  `8f6b34e`, the autostash conflicted only in the progress title; both
  progress entries were preserved. Post-sync pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.302 seconds. Final post-sync full local CI passed with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:35 elapsed),
  Isabelle `BackRefPilot` (0:17 elapsed), `BackRefBitcodedSummary` replaying
  in about 0.280 seconds, and local CI certificate generation; explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. After rebasing over concurrent commit `4643efa`, both
  the compact accept/reject wrappers and the final-case wrappers were
  preserved. Post-rebase pilot-only local CI passed with `BackRefPilot` (0:18
  elapsed), with `BackRefBitcodedSummary` replaying in about 0.533 seconds.
  Final post-rebase full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:17 elapsed), `BackRefBitcodedSummary` replaying in about 0.590 seconds,
  and local CI certificate generation; explicit statement guard PASS.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding compact accept/reject iff wrappers
  for the ordinary and generalized bitcoded frontend groups. New checked facts
  in `BackRefBitcodedSummary.thy` are `bblexer_frontends_all_None_iff`,
  `bblexer_frontends_same_Some_iff`, `gbblexer_frontends_all_None_iff`, and
  `gbblexer_frontends_same_Some_iff`, packaging that all three frontend
  variants reject exactly outside `BL`/`GBL` and have a shared `Some` witness
  exactly on accepted inputs. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+48) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.244 seconds. Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:18 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.449 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:34 elapsed), Isabelle `BackRefPilot` (0:18 elapsed),
  `BackRefBitcodedSummary` replaying in about 0.408 seconds, local CI
  certificate generation, and explicit statement guard PASS. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only similarly
  direct downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after preserving the uncommitted final-same wrappers across the
  sync with remote commit `d3e6736` and adding normalized `Some` iff wrappers
  for the ordinary and generalized bitcoded frontend groups. New checked facts
  in `BackRefBitcodedSummary.thy` are `bblexer_frontends_BL_same_iff` and
  `gbblexer_frontends_GBL_same_iff`, packaging all three frontend variants to
  use the same unsimplified final retrieval expression in their accepted-input
  characterization. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+56 total since `d3e6736`, including +24 in
  this step) and `PROGRESS_BACKREF.md`. Sync note: `git pull --rebase
  --autostash origin codex/backref-values` fast-forwarded to `d3e6736`; the
  autostash conflicted only in the progress title, and both progress entries
  were preserved. Baseline synced pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.225 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.275 seconds. Pre-progress full local CI passed with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle
  `BackRefPilot` (0:17 elapsed), `BackRefBitcodedSummary` replaying in about
  0.282 seconds, and local CI certificate generation. Final after-progress
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:18 elapsed),
  `BackRefBitcodedSummary` replaying in about 0.290 seconds, local CI
  certificate generation, and explicit statement guard PASS. After rebasing
  over concurrent commit `ec2957d`, pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBitcodedSummary` replaying in
  about 0.264 seconds; final post-rebase full local CI passed with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:04 elapsed),
  Isabelle `BackRefPilot` (0:04 elapsed), local CI certificate generation, and
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `BackRefPilot`, and final full local CI after adding direct
  residual left-quotient member length wrappers in
  `BackRefBoundedBlueprint.thy`. New checked facts are
  `bounded_language_residual_left_quotient_length_bound`,
  `bounded_language_residual_left_quotient_length_bound_mono`,
  `bounded_backref_lang_residual_left_quotient_length_bound`,
  `bounded_backref_lang4_residual_left_quotient_length_bound`,
  `bounded_backref_lang_residual_left_quotient_length_bound_mono`, and
  `bounded_backref_lang4_residual_left_quotient_length_bound_mono`. Files
  changed before this progress note: `BackRefBoundedBlueprint.thy` (+87) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:19 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 3.8 seconds. Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 3.8 seconds. Full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot`
  (0:03 elapsed), and local CI certificate generation. After rebasing over
  concurrent commit `59345fb`, final post-rebase full local CI passed with
  no-cheat guard, bounty guard, admin role guard, Isabelle `Posix` (0:35
  elapsed), Isabelle `BackRefPilot` (0:17 elapsed), local CI certificate
  generation, and explicit statement guard PASS. Next smallest safe step:
  stop until the admin opens a new bounty/phase, or add only similarly direct
  downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `BackRefPilot`, and final full local CI after adding direct
  residual-derivative member length wrappers in
  `BackRefBoundedBlueprint.thy`. New checked facts are
  `BL_bound_residual_derivative_length_bound`,
  `GBL_bound_residual_derivative_length_bound`,
  `BL_bound_residual_derivative_length_bound_mono`,
  `GBL_bound_residual_derivative_length_bound_mono`,
  `BL_bound_BBACKREF_residual_derivative_length_bound`,
  `GBL_bound_GBACKREF4_residual_derivative_length_bound`,
  `BL_bound_BBACKREF_residual_derivative_length_bound_mono`, and
  `GBL_bound_GBACKREF4_residual_derivative_length_bound_mono`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+87) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed). An initial post-edit pilot check exposed a
  local theorem-instantiation error in two monotone constructor wrappers; the
  proofs were narrowed to use `OF assms(...)` plus the remaining family member
  arguments. Post-fix pilot-only local CI passed with `BackRefPilot` (0:17
  elapsed), with `BackRefBoundedBlueprint` replaying in about 3.2 seconds.
  Full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation. After-progress explicit guards passed:
  bounty guard, no-cheat guard, statement guard, and admin role guard. Final
  after-progress pilot-only local CI passed with `BackRefPilot` (0:17 elapsed),
  with `BackRefBoundedBlueprint` replaying in about 3.5 seconds. Next smallest
  safe step: stop until the admin opens a new bounty/phase, or add only
  similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding monotone family-member length wrappers
  in `BackRefBoundedBlueprint.thy`. New checked facts are
  `bounded_strings_family_member_length_bound_mono`,
  `BL_bound_derivative_family_member_length_bound_mono`,
  `GBL_bound_derivative_family_member_length_bound_mono`,
  `BL_bound_residual_derivative_family_member_length_bound_mono`,
  `GBL_bound_residual_derivative_family_member_length_bound_mono`,
  `BL_bound_left_quotient_family_member_length_bound_mono`,
  `GBL_bound_left_quotient_family_member_length_bound_mono`,
  `BL_bound_xders_left_quotient_family_member_length_bound_mono`,
  `GBL_bound_gxders_left_quotient_family_member_length_bound_mono`,
  `BL_bound_BBACKREF_derivative_family_member_length_bound_mono`,
  `GBL_bound_GBACKREF4_derivative_family_member_length_bound_mono`,
  `BL_bound_BBACKREF_residual_derivative_family_member_length_bound_mono`,
  `GBL_bound_GBACKREF4_residual_derivative_family_member_length_bound_mono`,
  `BL_bound_BBACKREF_left_quotient_family_member_length_bound_mono`,
  `GBL_bound_GBACKREF4_left_quotient_family_member_length_bound_mono`,
  `BL_bound_BBACKREF_xders_left_quotient_family_member_length_bound_mono`, and
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_member_length_bound_mono`.
  Files changed before this progress note: `BackRefBoundedBlueprint.thy`
  (+183) and `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 4.0 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle
  `BackRefPilot` (0:03 elapsed), local CI certificate generation, and explicit
  statement guard PASS. After rebasing over concurrent commit `10be0c0`, final
  post-rebase full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:17
  elapsed), local CI certificate generation, `BackRefBoundedBlueprint`
  replaying in about 3.8 seconds, and explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding normalized final-result wrappers for the ordinary
  and generalized bitcoded lexer frontend groups. New checked facts in
  `BackRefBitcodedSummary.thy` are `bblexer_frontends_final_same` and
  `gbblexer_frontends_final_same`, packaging all three frontend variants to
  return the same unsimplified final retrieval expression on accepted
  `BL`/`GBL` inputs and `None` otherwise. Files changed before this progress
  note: `BackRefBitcodedSummary.thy` (+32) and `PROGRESS_BACKREF.md`.
  Baseline pilot-only local CI passed with `BackRefPilot` (0:17 elapsed).
  Post-edit pilot-only local CI passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBitcodedSummary` replaying in about 0.267 seconds. Pre-progress
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:34 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation. Final after-progress full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix`, Isabelle `BackRefPilot`, local CI certificate generation, and
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding accept/reject case wrappers for the ordinary and
  generalized bitcoded lexer frontend groups. New checked facts in
  `BackRefBitcodedSummary.thy` are `bblexer_frontends_BL_cases` and
  `gbblexer_frontends_GBL_cases`, packaging each frontend family into one
  case split: either the input is outside `BL`/`GBL` and all three frontends
  reject, or the input is accepted and all three frontends return the same
  bitcode witness. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+54) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBitcodedSummary` replaying in about 0.208 seconds. Pre-progress
  full local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:36 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation. Final after-progress full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), local CI
  certificate generation, and explicit statement guard PASS. After rebasing
  over concurrent commit `a202417`, final post-rebase full local CI passed
  with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`
  (0:03 elapsed), Isabelle `BackRefPilot` (0:16 elapsed), local CI
  certificate generation, `BackRefBitcodedSummary` replaying in about 0.599
  seconds, and explicit statement guard PASS. Next smallest safe step: stop
  until the admin opens a new bounty/phase, or add only similarly direct
  downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `BackRefPilot`, and final full local CI after rebasing over
  concurrent commit `f8a12a2` and adding direct constructor-specialized
  bounded-family member-length wrappers in `BackRefBoundedBlueprint.thy`.
  New checked facts are
  `BL_bound_BBACKREF_derivative_family_member_length_bound`,
  `GBL_bound_GBACKREF4_derivative_family_member_length_bound`,
  `BL_bound_BBACKREF_residual_derivative_family_member_length_bound`,
  `GBL_bound_GBACKREF4_residual_derivative_family_member_length_bound`,
  `BL_bound_BBACKREF_left_quotient_family_member_length_bound`,
  `GBL_bound_GBACKREF4_left_quotient_family_member_length_bound`,
  `BL_bound_BBACKREF_xders_left_quotient_family_member_length_bound`, and
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_member_length_bound`.
  Files changed before this progress note: `BackRefBoundedBlueprint.thy`
  (+88) and `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:19 elapsed). Pre-rebase post-edit pilot-only local CI
  passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBoundedBlueprint` replaying in about 3.9 seconds. Final
  post-rebase full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate
  generation, and explicit statement guard PASS. Next smallest safe step:
  stop until the admin opens a new bounty/phase, or add only similarly direct
  downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation after adding same-witness accepted-input wrappers for all
  ordinary and generalized bitcoded lexer frontends. New checked facts in
  `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_BL_obtains_same` and
  `gbblexer_frontends_GBL_obtains_same`, packaging that the ordinary,
  post-derivative simplified, and per-step simplified frontends return the
  same bitcode witness on accepted `BL`/`GBL` inputs. Files changed before
  this progress note: `BackRefBitcodedSummary.thy` (+30) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed) and `BackRefBitcodedSummary` replaying in
  about 0.208 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:36 elapsed), Isabelle
  `BackRefPilot` (0:17 elapsed), local CI certificate generation, and
  `BackRefBitcodedSummary` replaying in about 0.184 seconds. A final
  after-progress verification pass also passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:03 elapsed), Isabelle
  `BackRefPilot` (0:03 elapsed), local CI certificate generation, and explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. After rebasing over concurrent commit `3932865`,
  final post-rebase full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:18 elapsed), local CI certificate generation, `BackRefBitcodedSummary`
  replaying in about 0.239 seconds, and explicit statement guard PASS.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `BackRefPilot`, and final full local CI after rebasing over
  `e6bed9d`, preserving the residual left-quotient length wrappers, and adding
  direct bounded-family member-length wrappers in `BackRefBoundedBlueprint.thy`.
  New checked facts on top of the preserved residual length wrappers are
  `bounded_strings_family_member_length_bound`,
  `BL_bound_derivative_family_member_length_bound`,
  `GBL_bound_derivative_family_member_length_bound`,
  `BL_bound_residual_derivative_family_member_length_bound`,
  `GBL_bound_residual_derivative_family_member_length_bound`,
  `BL_bound_left_quotient_family_member_length_bound`,
  `GBL_bound_left_quotient_family_member_length_bound`,
  `BL_bound_xders_left_quotient_family_member_length_bound`, and
  `GBL_bound_gxders_left_quotient_family_member_length_bound`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+152 total since
  `e6bed9d`, including +78 for the new family-member wrappers) and
  `PROGRESS_BACKREF.md`. Post-sync pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), and post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 3.6 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, local CI
  certificate generation, and explicit statement guard PASS. Next smallest
  safe step: stop until the admin opens a new bounty/phase, or add only
  similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `BackRefPilot`, and final full local CI after rebasing over
  `85e7ba5` and preserving the direct bounded-language wrapper work. New
  checked facts in `BackRefBitcodedSummary.thy` are
  `bblexer_frontends_blexer_Some_retrieve`,
  `bblexer_frontends_BL_obtains`, and
  `gbblexer_frontends_GBL_obtains`, packaging successful ordinary value-lexer
  retrieval and accepted-input bitcode witnesses for all ordinary and
  generalized bitcoded frontends. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+38) and `PROGRESS_BACKREF.md`. Post-sync
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBitcodedSummary` replaying in about 0.161 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:36 elapsed), Isabelle `BackRefPilot` (0:17 elapsed), local CI
  certificate generation, and `BackRefBitcodedSummary` replaying in about
  0.214 seconds. Next smallest safe step: stop until the admin opens a new
  bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct member-length wrappers for
  residual left-quotient families in `BackRefBoundedBlueprint.thy`. New
  checked facts are `BL_bound_xders_left_quotient_length_bound`,
  `GBL_bound_gxders_left_quotient_length_bound`,
  `BL_bound_xders_left_quotient_length_bound_mono`,
  `GBL_bound_gxders_left_quotient_length_bound_mono`,
  `BL_bound_BBACKREF_xders_left_quotient_length_bound`,
  `GBL_bound_GBACKREF4_gxders_left_quotient_length_bound`,
  `BL_bound_BBACKREF_xders_left_quotient_length_bound_mono`, and
  `GBL_bound_GBACKREF4_gxders_left_quotient_length_bound_mono`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+74) and
  `PROGRESS_BACKREF.md`. Baseline pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint` replaying in
  about 3.5 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:35 elapsed), Isabelle
  `BackRefPilot` (0:17 elapsed), and local CI certificate generation; explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct bounded-language wrappers in
  `BackRefBoundedBlueprint.thy`. New checked facts package the original
  `BL r`/`GBL r` languages from successful `BL_bound`/`GBL_bound`
  calculations into bounded-string subsets, cardinality bounds, finiteness,
  member length bounds, monotone variants, and direct `BBACKREF`/`GBACKREF4`
  specializations. New facts include `BL_bound_subset_bounded_strings`,
  `GBL_bound_subset_bounded_strings`, `BL_bound_card_bound`,
  `GBL_bound_card_bound`, `BL_bound_finite`, `GBL_bound_finite`,
  `BL_bound_length_bound`, `GBL_bound_length_bound`,
  `BL_bound_BBACKREF_subset_bounded_strings`,
  `GBL_bound_GBACKREF4_subset_bounded_strings`,
  `BL_bound_BBACKREF_card_bound`, `GBL_bound_GBACKREF4_card_bound`,
  `BL_bound_BBACKREF_finite`, `GBL_bound_GBACKREF4_finite`,
  `BL_bound_BBACKREF_length_bound`, and
  `GBL_bound_GBACKREF4_length_bound`, with monotone variants for each bound
  family. Files changed before this progress note:
  `BackRefBoundedBlueprint.thy` (+303). Baseline pilot-only local CI passed
  with `BackRefPilot` (0:16 elapsed). Post-edit pilot-only local CI passed
  with `BackRefPilot` (0:17 elapsed), with `BackRefBoundedBlueprint`
  replaying in about 4.1 seconds. Final full local CI passed with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:40 elapsed),
  Isabelle `BackRefPilot` (0:19 elapsed), and local CI certificate
  generation; explicit statement guard PASS. After rebasing over remote commit
  `4b952c2`, pilot-only local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 3.8 seconds. Final full
  post-rebase local CI passed with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:36 elapsed), Isabelle `BackRefPilot` (0:17
  elapsed), and local CI certificate generation; explicit statement guard
  PASS. Next smallest safe step: stop until the admin opens a new bounty/phase
  or explicitly asks for more direct packaging. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after
  rebasing over concurrent commit `a6f9492` and preserving its membership
  implication wrappers in `BackRefBitcodedSummary.thy`. New checked facts are
  `bblexer_frontends_blexer_iff` and `gbblexer_frontends_gblexer_iff`,
  packaging direct value-lexer `Some`/`None` iff summaries for all ordinary
  and generalized bitcoded lexer frontends. Files changed before this progress
  note: `BackRefBitcodedSummary.thy` (+30) and `PROGRESS_BACKREF.md`.
  Post-rebase pilot-only local CI passed with `BackRefPilot` (0:18 elapsed),
  with `BackRefBitcodedSummary` replaying in about 0.460 seconds. Final full
  local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:39 elapsed), Isabelle `BackRefPilot` (0:16 elapsed),
  local CI certificate generation, and explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after
  rebasing over concurrent commit `d04e3ba` and preserving its raw-language
  final-result wrappers in `BackRefBitcodedSummary.thy`. New checked facts on
  top of that commit are `bblexer_frontends_defined_BL_iff`,
  `bblexer_frontends_Some_BL`, `gbblexer_frontends_defined_GBL_iff`, and
  `gbblexer_frontends_Some_GBL`. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+26). Baseline pilot-only local CI before the
  rebase passed with `BackRefPilot` (0:17 elapsed), and the immediate
  post-edit pilot-only local CI passed with `BackRefPilot` (0:18 elapsed).
  Post-rebase pilot-only local CI passed with `BackRefPilot` (0:17 elapsed),
  with `BackRefBitcodedSummary` replaying in about 0.145 seconds. Final full
  local CI after continuing the rebase passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:34 elapsed), Isabelle
  `BackRefPilot` (0:03 elapsed), and local CI certificate generation; explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after adding
  direct raw-language final-result summary wrappers for all ordinary and
  generalized bitcoded lexer frontends in `BackRefBitcodedSummary.thy`. New
  checked facts are `bblexer_frontends_final_membership`,
  `bblexer_frontends_BL_iff`, `gbblexer_frontends_final_membership`, and
  `gbblexer_frontends_GBL_iff`. Files changed before this progress note:
  `BackRefBitcodedSummary.thy` (+66) and `PROGRESS_BACKREF.md`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed), with
  `BackRefBitcodedSummary` replaying in about 0.132 seconds. After rebasing
  over concurrent commit `3ca06b2` and preserving its value-lexer progress
  note, final full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:16
  elapsed), and local CI certificate generation; `BackRefBitcodedSummary`
  replayed in about 0.119 seconds, and explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after adding
  value-lexer packaging wrappers in `BackRefValues.thy`. New checked facts are
  `blexer_Some_BL`, `blexer_BL_obtains`, `blexer_defined_BPrf_iff`,
  `blexer_None_BPrf_iff`, `blexer_defined_POSIX_iff`, and
  `blexer_None_POSIX_iff`. Files changed before this progress note:
  `BackRefValues.thy` (+84). Baseline pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed). An initial post-edit pilot replay exposed two
  overly terse `None` wrapper proofs; those were replaced with explicit option
  cases. After rebasing over remote commit `4b17049`, pilot-only local CI
  passed with `BackRefPilot` (0:17 elapsed), `BackRefValues` replaying in about
  11.0 seconds, and the synced `BackRefBitcodedSummary` theory replaying in
  about 0.099 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:03 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed), and local CI certificate generation; explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only similarly direct downstream packaging facts if
  explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding direct retrieve-iff summary wrappers
  for all ordinary and generalized bitcoded lexer frontends in
  `BackRefBitcodedSummary.thy`. New checked facts are
  `bblexer_frontends_POSIX_retrieve_iff`,
  `bblexer_frontends_BPrf_retrieve_iff`,
  `bblexer_frontends_defined_BPrf_iff`,
  `bblexer_frontends_None_BPrf_iff`, and
  `gbblexer_frontends_GPrf_retrieve_iff`. Files changed before this progress
  note: `BackRefBitcodedSummary.thy` (+56) and `PROGRESS_BACKREF.md`.
  Baseline pilot-only local CI passed with `BackRefPilot` (0:17 elapsed).
  Post-edit pilot-only local CI passed with `BackRefPilot` (0:17 elapsed),
  with `BackRefBitcodedSummary` replaying in about 0.131 seconds. Final full
  local CI passed with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation; explicit statement guard PASS. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after
  rebasing over concurrent commit `8e5377e` and adding the new downstream
  packaging theory `BackRefBitcodedSummary.thy` to `pilot/ROOT`. New checked
  facts are `bblexer_frontends_eq`,
  `bblexer_frontends_blexer_retrieve`,
  `bblexer_frontends_POSIX_retrieve`,
  `bblexer_frontends_defined_POSIX_iff`,
  `bblexer_frontends_None_POSIX_iff`, `gbblexer_frontends_eq`,
  `gbblexer_frontends_gblexer_retrieve`,
  `gbblexer_frontends_gblexer_Some_retrieve`,
  `gbblexer_frontends_defined_GPrf_iff`, and
  `gbblexer_frontends_None_GPrf_iff`. Files changed before this progress
  note: `BackRefBitcodedSummary.thy` (+86) and `pilot/ROOT` (+1), with
  `PROGRESS_BACKREF.md` updated for the checked step and rebase note.
  Baseline pilot-only local CI passed with `BackRefPilot` (0:16 elapsed).
  Post-edit pilot-only local CI passed with `BackRefPilot` (0:17 elapsed),
  with `BackRefBitcodedSummary` replaying in about 0.064 seconds. Final
  post-rebase full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:16
  elapsed), and local CI certificate generation; explicit statement guard
  PASS. Next smallest safe step: stop until the admin opens a new bounty/phase,
  or add only similarly direct downstream packaging facts if explicitly
  requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after
  preserving the synced derivative member-length wrappers and adding semantic
  left-quotient member-length wrappers in `BackRefBoundedBlueprint.thy`. New
  checked facts in this final tree are `BL_bound_xders_length_bound`,
  `GBL_bound_gxders_length_bound`, `BL_bound_xders_length_bound_mono`,
  `GBL_bound_gxders_length_bound_mono`,
  `BL_bound_BBACKREF_xders_length_bound`,
  `GBL_bound_GBACKREF4_gxders_length_bound`,
  `BL_bound_BBACKREF_xders_length_bound_mono`,
  `GBL_bound_GBACKREF4_gxders_length_bound_mono`,
  `BL_bound_left_quotient_length_bound`,
  `GBL_bound_left_quotient_length_bound`,
  `BL_bound_left_quotient_length_bound_mono`,
  `GBL_bound_left_quotient_length_bound_mono`,
  `BL_bound_BBACKREF_left_quotient_length_bound`,
  `GBL_bound_GBACKREF4_left_quotient_length_bound`,
  `BL_bound_BBACKREF_left_quotient_length_bound_mono`, and
  `GBL_bound_GBACKREF4_left_quotient_length_bound_mono`. Files changed before
  this progress note: `BackRefBoundedBlueprint.thy` (+140) and
  `PROGRESS_BACKREF.md`. After rebasing over remote commit `8002257`,
  baseline pilot-only local CI passed with `BackRefPilot` (0:17 elapsed);
  post-edit pilot-only local CI passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 2.7 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:30 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and local CI
  certificate generation; explicit statement guard PASS. After rebasing over
  concurrent commit `44e86e8`, final full local CI passed again with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:03 elapsed),
  Isabelle `BackRefPilot` (0:17 elapsed), and local CI certificate generation;
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  explicit statement guard, and Isabelle `Posix` + `BackRefPilot` after adding
  direct member-length wrappers for bounded derivative residual languages in
  `BackRefBoundedBlueprint.thy`. New checked facts are
  `BL_bound_xders_length_bound`, `GBL_bound_gxders_length_bound`,
  `BL_bound_xders_length_bound_mono`, `GBL_bound_gxders_length_bound_mono`,
  `BL_bound_BBACKREF_xders_length_bound`,
  `GBL_bound_GBACKREF4_gxders_length_bound`,
  `BL_bound_BBACKREF_xders_length_bound_mono`, and
  `GBL_bound_GBACKREF4_gxders_length_bound_mono`. Files changed before this
  progress note: `BackRefBoundedBlueprint.thy` (+68). Baseline pilot-only
  local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit pilot-only
  local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 2.6 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix` (0:31 elapsed), Isabelle `BackRefPilot` (0:12 elapsed), and local CI
  certificate generation; explicit statement guard PASS. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only similarly
  direct downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct checked-evidence existence and
  rejection wrappers for the ordinary and generalized bitcoded lexer frontends.
  New checked facts are `bblexer_defined_BPrf_iff`,
  `bblexer_None_BPrf_iff`, `bblexer_simp_defined_BPrf_iff`,
  `bblexer_simp_None_BPrf_iff`,
  `bblexer_step_simp_defined_BPrf_iff`,
  `bblexer_step_simp_None_BPrf_iff`,
  `gbblexer_defined_GPrf_iff`, `gbblexer_None_GPrf_iff`,
  `gbblexer_simp_defined_GPrf_iff`,
  `gbblexer_simp_None_GPrf_iff`,
  `gbblexer_step_simp_defined_GPrf_iff`, and
  `gbblexer_step_simp_None_GPrf_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+29) and `BackRefGBlexer.thy` (+29). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed), with
  `BackRefBlexer` replaying in about 5.1 seconds and `BackRefGBlexer`
  replaying in about 2.0 seconds. Final full local CI passed with no-cheat
  guard, bounty guard, admin role guard, Isabelle `Posix` (0:35 elapsed),
  Isabelle `BackRefPilot` (0:17 elapsed), and local CI certificate generation;
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct POSIX evidence existence and
  rejection wrappers for the ordinary bitcoded lexer frontends. New checked
  facts are `bblexer_defined_POSIX_iff`, `bblexer_None_POSIX_iff`,
  `bblexer_simp_defined_POSIX_iff`, `bblexer_simp_None_POSIX_iff`,
  `bblexer_step_simp_defined_POSIX_iff`, and
  `bblexer_step_simp_None_POSIX_iff`. Files changed before this progress note:
  `BackRefBlexer.thy` (+93). Baseline pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed), with `BackRefBlexer` replaying in about 5.2
  seconds. Final full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix` (0:33 elapsed), Isabelle `BackRefPilot` (0:16
  elapsed), and local CI certificate generation. Next smallest safe step: stop
  until the admin opens a new bounty/phase, or add only similarly direct
  downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct residual-language bounded-string
  wrappers from successful `BL_bound`/`GBL_bound` calculations in
  `BackRefBoundedBlueprint.thy`. New checked facts package subset, cardinality,
  monotone subset/cardinality, and finiteness wrappers for `BL (xders r s)` and
  `GBL (gxders r s)`, plus constructor-specific `BBACKREF` and `GBACKREF4`
  versions:
  `BL_bound_xders_subset_bounded_strings`,
  `GBL_bound_gxders_subset_bounded_strings`,
  `BL_bound_xders_card_bound`, `GBL_bound_gxders_card_bound`,
  `BL_bound_xders_subset_bounded_strings_mono`,
  `GBL_bound_gxders_subset_bounded_strings_mono`,
  `BL_bound_xders_card_bound_mono`, `GBL_bound_gxders_card_bound_mono`,
  `BL_bound_xders_finite`, `GBL_bound_gxders_finite`,
  `BL_bound_BBACKREF_xders_subset_bounded_strings`,
  `GBL_bound_GBACKREF4_gxders_subset_bounded_strings`,
  `BL_bound_BBACKREF_xders_card_bound`,
  `GBL_bound_GBACKREF4_gxders_card_bound`,
  `BL_bound_BBACKREF_xders_subset_bounded_strings_mono`,
  `GBL_bound_GBACKREF4_gxders_subset_bounded_strings_mono`,
  `BL_bound_BBACKREF_xders_card_bound_mono`,
  `GBL_bound_GBACKREF4_gxders_card_bound_mono`,
  `BL_bound_BBACKREF_xders_finite`, and
  `GBL_bound_GBACKREF4_gxders_finite`. Files changed before this progress
  note: `BackRefBoundedBlueprint.thy` (+220). Baseline pilot-only local CI
  passed with `BackRefPilot` (0:16 elapsed). Post-edit pilot-only local CI
  passed with `BackRefPilot` (0:17 elapsed) after fixing direct wrapper proofs
  to unfold `BL_bounded`/`GBL_bounded`; `BackRefBoundedBlueprint` replayed in
  about 3.1 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local
  CI certificate generation; explicit statement guard PASS. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only similarly
  direct downstream packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding the direct value-lexer POSIX
  characterization `blexer_POSIX_correctness`, proving
  `blexer r s = Some v \<longleftrightarrow> s \<in> r \<rightarrow> v` from the existing
  POSIX soundness and determinism facts. Files changed before this progress
  note: `BackRefValues.thy` (+20). Baseline pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:18 elapsed), with `BackRefValues` replaying in about 9.7
  seconds. Final full local CI passed with no-cheat guard, bounty guard, admin
  role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, statement guard, and
  local CI certificate generation. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct nullable-result wrappers for the
  ordinary and generalized bitcoded lexer frontends. New checked facts are
  `bblexer_None_xnullable_iff`, `bblexer_Some_xnullable_iff`,
  `bblexer_simp_None_xnullable_iff`,
  `bblexer_simp_Some_xnullable_iff`,
  `bblexer_step_simp_None_xnullable_iff`,
  `bblexer_step_simp_Some_xnullable_iff`,
  `gbblexer_None_gnullable_iff`, `gbblexer_Some_gnullable_iff`,
  `gbblexer_simp_None_gnullable_iff`,
  `gbblexer_simp_Some_gnullable_iff`,
  `gbblexer_step_simp_None_gnullable_iff`, and
  `gbblexer_step_simp_Some_gnullable_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+30) and `BackRefGBlexer.thy` (+30). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed);
  `BackRefBlexer` replayed in about 4.6 seconds and `BackRefGBlexer` replayed
  in about 1.9 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and
  local CI certificate generation. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding constructor-specific derivative-residue
  left-quotient wrappers from successful `BL_bound`/`GBL_bound` calculations
  for `BBACKREF` and `GBACKREF4` in `BackRefBoundedBlueprint.thy`. New
  checked facts are
  `BL_bound_BBACKREF_xders_left_quotient_family_subset_bounded_strings`,
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_subset_bounded_strings`,
  `BL_bound_BBACKREF_xders_left_quotient_family_card_bound`,
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_card_bound`,
  `BL_bound_BBACKREF_xders_left_quotient_family_subset_bounded_strings_mono`,
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_subset_bounded_strings_mono`,
  `BL_bound_BBACKREF_xders_left_quotient_family_card_bound_mono`,
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_card_bound_mono`,
  `BL_bound_BBACKREF_xders_left_quotient_family_finite`, and
  `GBL_bound_GBACKREF4_gxders_left_quotient_family_finite`. Files changed
  before this progress note: `BackRefBoundedBlueprint.thy` (+139). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 2.5 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix`, Isabelle `BackRefPilot`, and local CI certificate generation. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct downstream packaging facts if explicitly requested.
  Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct derivative-residue
  left-quotient wrappers from successful `BL_bound`/`GBL_bound` calculations
  in `BackRefBoundedBlueprint.thy`. New checked facts are
  `BL_bound_xders_left_quotient_family_subset_bounded_strings`,
  `GBL_bound_gxders_left_quotient_family_subset_bounded_strings`,
  `BL_bound_xders_left_quotient_family_card_bound`,
  `GBL_bound_gxders_left_quotient_family_card_bound`,
  `BL_bound_xders_left_quotient_family_subset_bounded_strings_mono`,
  `GBL_bound_gxders_left_quotient_family_subset_bounded_strings_mono`,
  `BL_bound_xders_left_quotient_family_card_bound_mono`,
  `GBL_bound_gxders_left_quotient_family_card_bound_mono`,
  `BL_bound_xders_left_quotient_family_finite`, and
  `GBL_bound_gxders_left_quotient_family_finite`. Files changed before this
  progress note: `BackRefBoundedBlueprint.thy` (+140). Baseline pilot-only
  local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit pilot-only
  local CI passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 3.3 seconds. Final full local
  CI passed with no-cheat guard, bounty guard, admin role guard, Isabelle
  `Posix`, Isabelle `BackRefPilot`, and local CI certificate generation. After
  rebasing over concurrent commit `0267ce9`, full local CI passed again with
  Isabelle `Posix`, Isabelle `BackRefPilot`, local CI certificate generation,
  and explicit statement guard PASS. Next smallest safe step: stop until the
  admin opens a new bounty/phase, or add only similarly direct downstream
  packaging facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct success-to-membership and
  membership-to-success obtain wrappers for the ordinary and generalized
  bitcoded lexer frontends. New checked facts are `bblexer_Some_BL`,
  `bblexer_BL_obtains`, `bblexer_simp_Some_BL`,
  `bblexer_simp_BL_obtains`, `bblexer_step_simp_Some_BL`,
  `bblexer_step_simp_BL_obtains`, `gbblexer_Some_GBL`,
  `gbblexer_GBL_obtains`, `gbblexer_simp_Some_GBL`,
  `gbblexer_simp_GBL_obtains`, `gbblexer_step_simp_Some_GBL`, and
  `gbblexer_step_simp_GBL_obtains`. Files changed before this progress note:
  `BackRefBlexer.thy` (+30) and `BackRefGBlexer.thy` (+30). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed);
  `BackRefBlexer` replayed in about 4.0 seconds and `BackRefGBlexer` replayed
  in about 1.9 seconds. Final full local CI passed with Isabelle `Posix`
  (0:29 elapsed), Isabelle `BackRefPilot` (0:03 elapsed), and local CI
  certificate generation. After rebasing over concurrent commit `65631e1`,
  full local CI passed again with Isabelle `Posix` (0:04 elapsed), Isabelle
  `BackRefPilot` (0:17 elapsed), local CI certificate generation, and explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only explicitly requested downstream convenience
  wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct semantic left-quotient wrappers
  from successful `BL_bound`/`GBL_bound` calculations in
  `BackRefBoundedBlueprint.thy`. New checked facts expose raw
  `{Ders s (BL r) | s. True}` and `{Ders s (GBL r) | s. True}` subset,
  cardinality, monotone, and finite wrappers over `bounded_strings`, plus
  constructor-specific `BBACKREF` and `GBACKREF4` packages. Files changed before
  this progress note: `BackRefBoundedBlueprint.thy` (+244). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 3.5 seconds. Final full local CI
  passed with no-cheat guard, bounty guard, admin role guard, Isabelle `Posix`,
  Isabelle `BackRefPilot`, and local CI certificate generation. After rebasing
  over concurrent commit `4c950f5`, the checked-value retrieve bridge progress
  note was preserved; post-rebase full local CI passed with Isabelle `Posix`
  (0:04 elapsed), Isabelle `BackRefPilot` (0:19 elapsed),
  `BackRefBoundedBlueprint` replaying in about 2.6 seconds, local CI
  certificate generation, and explicit statement guard PASS. Next smallest
  safe step: stop until the admin opens a new bounty/phase, or add only
  similarly direct downstream packaging facts if explicitly requested. Blockers:
  none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct checked-value retrieve wrappers
  for the ordinary and generalized bitcoded lexer frontends. New checked facts
  are `bblexer_BPrf_retrieve_iff`, `bblexer_simp_BPrf_retrieve_iff`,
  `bblexer_step_simp_BPrf_retrieve_iff`, `gbblexer_GPrf_retrieve_iff`,
  `gbblexer_simp_GPrf_retrieve_iff`, and
  `gbblexer_step_simp_GPrf_retrieve_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+19) and `BackRefGBlexer.thy` (+20). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed);
  `BackRefBlexer` replayed in about 4.2 seconds and `BackRefGBlexer` replayed
  in about 2.7 seconds. Final full local CI passed with Isabelle `Posix`
  (0:29 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and local CI
  certificate generation. After rebasing over concurrent commit `ce0492f`,
  full local CI passed again with Isabelle `Posix` (0:04 elapsed), Isabelle
  `BackRefPilot` (0:16 elapsed), local CI certificate generation, and explicit
  statement guard PASS. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only explicitly requested downstream convenience
  wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct equality wrappers from bitcoded
  lexer outputs to known value-lexer outputs. New checked facts are
  `bblexer_blexer_retrieve_eq`, `bblexer_simp_blexer_retrieve_eq`,
  `bblexer_step_simp_blexer_retrieve_eq`,
  `gbblexer_gblexer_retrieve_eq`, `gbblexer_simp_gblexer_retrieve_eq`, and
  `gbblexer_step_simp_gblexer_retrieve_eq`. Files changed before this
  progress note: `BackRefBlexer.thy` (+18) and `BackRefGBlexer.thy` (+18).
  Baseline pilot-only local CI passed with `BackRefPilot` (0:16 elapsed).
  Post-edit pilot-only local CI passed with `BackRefPilot` (0:16 elapsed);
  `BackRefBlexer` replayed in about 4.3 seconds and `BackRefGBlexer` replayed
  in about 2.1 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:34 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed), local CI certificate generation, and explicit
  statement guard PASS. Rebase over concurrent commit `79e263f` preserved both
  the new equality wrappers and the concurrently added `None` bridges.
  Post-rebase full local CI passed again with Isabelle `Posix` (0:03 elapsed),
  Isabelle `BackRefPilot` (0:03 elapsed), local CI certificate generation, and
  explicit statement guard PASS. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only similarly direct downstream packaging
  facts if explicitly requested. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct `None` bridges from the ordinary
  and generalized bitcoded lexer frontends back to the corresponding value
  lexer output. New checked facts are `bblexer_None_blexer_iff`,
  `bblexer_simp_None_blexer_iff`,
  `bblexer_step_simp_None_blexer_iff`, `gbblexer_None_gblexer_iff`,
  `gbblexer_simp_None_gblexer_iff`, and
  `gbblexer_step_simp_None_gblexer_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+12) and `BackRefGBlexer.thy` (+12). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:16 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:17 elapsed);
  `BackRefBlexer` replayed in about 4.6 seconds and `BackRefGBlexer` replayed
  in about 2.5 seconds. Full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI
  certificate generation; the final run after this progress note replayed
  `Posix` in 0:04 elapsed and `BackRefPilot` in 0:16 elapsed. Next smallest
  safe step: stop until the admin opens a new bounty/phase, or add only
  explicitly requested downstream convenience wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct `Some` bridges from the ordinary
  and generalized bitcoded lexer frontends back to the corresponding value
  lexer output. New checked facts are `bblexer_Some_blexer_iff`,
  `bblexer_simp_Some_blexer_iff`, `bblexer_step_simp_Some_blexer_iff`,
  `gbblexer_Some_gblexer_iff`, `gbblexer_simp_Some_gblexer_iff`, and
  `gbblexer_step_simp_Some_gblexer_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+16) and `BackRefGBlexer.thy` (+16). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:12 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:11 elapsed);
  `BackRefBlexer` replayed in about 5.5 seconds and `BackRefGBlexer` replayed
  in about 2.0 seconds. After rebasing over concurrent commits `ea8d1f6` and
  `588bf64`, final full local CI passed with no-cheat guard, bounty guard,
  admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI
  certificate generation. Next smallest safe step: stop until the admin opens a
  new bounty/phase, or add only explicitly requested downstream convenience
  wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct POSIX-evidence output wrappers
  for the ordinary bitcoded lexer frontends in `BackRefBlexer.thy`. New checked
  facts are `bblexer_POSIX_retrieve`, `bblexer_POSIX_retrieve_eq`,
  `bblexer_simp_POSIX_retrieve`, `bblexer_simp_POSIX_retrieve_eq`,
  `bblexer_step_simp_POSIX_retrieve`, and
  `bblexer_step_simp_POSIX_retrieve_eq`. Files changed before this progress
  note: `BackRefBlexer.thy` (+33). Baseline pilot-only local CI passed with
  `BackRefPilot` (0:11 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:11 elapsed) and `BackRefBlexer` replaying in about 4.1
  seconds. Final full local CI passed with Isabelle `Posix`, Isabelle
  `BackRefPilot`, and local CI certificate generation. Next smallest safe
  step: stop until the admin opens a new bounty/phase, or add only explicitly
  requested downstream convenience wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct POSIX-evidence retrieve wrappers
  for the ordinary bitcoded lexer frontends in `BackRefBlexer.thy`. New checked
  facts are `bblexer_POSIX_retrieve_iff`,
  `bblexer_simp_POSIX_retrieve_iff`, and
  `bblexer_step_simp_POSIX_retrieve_iff`. Files changed before this progress
  note: `BackRefBlexer.thy` (+41). Baseline pilot-only local CI passed with
  `BackRefPilot` (0:11 elapsed). Post-edit pilot-only local CI passed with
  `BackRefPilot` (0:11 elapsed) and `BackRefBlexer` replaying in about 4.1
  seconds. Final full local CI passed with Isabelle `Posix` (0:31 elapsed),
  Isabelle `BackRefPilot` (0:04 elapsed), and local CI certificate generation.
  Next smallest safe step: stop until the admin opens a new bounty/phase, or
  add only explicitly requested downstream convenience wrappers. Blockers:
  none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct `Some` result-characterization
  wrappers for the ordinary and generalized bitcoded lexer frontends, on top
  of the existing final-membership equations. New checked facts are
  `bblexer_Some_iff`, `bblexer_simp_Some_iff`,
  `bblexer_step_simp_Some_iff`, `gbblexer_Some_iff`,
  `gbblexer_simp_Some_iff`, and `gbblexer_step_simp_Some_iff`. Files changed
  before this progress note: `BackRefBlexer.thy` (+18) and
  `BackRefGBlexer.thy` (+18). After rebasing over parallel commit `464afc2`,
  pilot-only local CI passed with `BackRefPilot` (0:11 elapsed),
  `BackRefBlexer` replaying in about 4.3 seconds, and `BackRefGBlexer`
  replaying in about 2.4 seconds. Final full local CI passed with Isabelle
  `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:11 elapsed), and local
  CI certificate generation. Next smallest safe step: stop until the admin
  opens a new bounty/phase, or add only explicitly requested downstream
  convenience wrappers. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct language-membership and `None`
  wrappers for the ordinary and generalized bitcoded lexer frontends in
  `BackRefBlexer.thy` and `BackRefGBlexer.thy`. New checked facts are
  `bblexer_final_membership`, `bblexer_None_iff`,
  `bblexer_simp_final_membership`, `bblexer_simp_None_iff`,
  `bblexer_step_simp_final_membership`, `bblexer_step_simp_None_iff`,
  `gbblexer_final_membership`, `gbblexer_None_iff`,
  `gbblexer_simp_final_membership`, `gbblexer_simp_None_iff`,
  `gbblexer_step_simp_final_membership`, and
  `gbblexer_step_simp_None_iff`. Files changed before this progress note:
  `BackRefBlexer.thy` (+36) and `BackRefGBlexer.thy` (+36). Baseline
  pilot-only local CI passed with `BackRefPilot` (0:11 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:11 elapsed);
  `BackRefBlexer` replayed in about 4.7 seconds and `BackRefGBlexer` replayed
  in about 2.0 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix` (0:29 elapsed), Isabelle
  `BackRefPilot` (0:04 elapsed), and local CI certificate generation. Next
  smallest safe step: stop until the admin opens a new bounty/phase, or add
  only similarly direct packaging facts if explicitly requested. Blockers:
  none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct semantic residual left-quotient
  wrappers for bounded `backref_lang` and `backref_lang4` in
  `BackRefBoundedBlueprint.thy`. New checked facts expose subset,
  cardinality, monotone, and finite wrappers for
  `{Ders t (Ders s (backref_lang A B cs)) | t. True}` and the analogous
  `backref_lang4` family. Pilot-only local CI passed with `BackRefPilot`
  (0:11 elapsed) and `BackRefBoundedBlueprint` replaying in about 3.2 seconds.
  Final full local CI passed with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:30 elapsed), Isabelle `BackRefPilot` (0:04
  elapsed), and local CI certificate generation. After rebasing over
  `80c636b`, full local CI passed again with Isabelle `Posix` (0:04 elapsed),
  Isabelle `BackRefPilot` (0:11 elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding unconditional final-derivative retrieve
  equations for the ordinary and generalized bitcoded lexers in
  `BackRefBlexer.thy` and `BackRefGBlexer.thy`. New checked facts are
  `bblexer_final_retrieve`, `bblexer_simp_final_retrieve`,
  `bblexer_step_simp_final_retrieve`, `gbblexer_final_retrieve`,
  `gbblexer_simp_final_retrieve`, and
  `gbblexer_step_simp_final_retrieve`. Files changed before this progress
  note: `BackRefBlexer.thy` (+60) and `BackRefGBlexer.thy` (+60).
  Baseline pilot-only local CI passed with `BackRefPilot` (0:11 elapsed).
  Post-edit pilot-only local CI passed with `BackRefPilot` (0:11 elapsed);
  `BackRefBlexer` replayed in about 4.8 seconds and `BackRefGBlexer` replayed
  in about 1.8 seconds. Final full local CI passed with Isabelle `Posix`
  (0:32 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and local CI
  certificate generation. After rebasing over `8b8f1e0`, full local CI passed
  again with Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:12
  elapsed), and local CI certificate generation. Next smallest safe step:
  either add similarly direct `None`/membership wrappers for the bitcoded lexer
  frontends, or stop until the admin opens a new bounty/phase. Blockers: none.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding residual left-quotient family helpers in
  `BackRefBoundedBlueprint.thy`. New checked facts expose
  `left_quotient_family_Ders_subset`, `finite_left_quotient_family_Ders`,
  `left_quotient_family_Ders_card_le`, and bounded-string universe/cardinality
  wrappers for `{Ders t (Ders s A) | t. True}`. Pilot-only local CI passed with
  `BackRefPilot` (0:11 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 2.2 seconds. Final full local CI passed with no-cheat guard, bounty
  guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local
  CI certificate generation; explicit statement guard PASS.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct equality wrappers between the
  post-derivative and per-step simplified bitcoded lexers in
  `BackRefBlexer.thy` and `BackRefGBlexer.thy`. New checked facts are
  `bblexer_simp_step_simp_eq` and `gbblexer_simp_step_simp_eq`. Baseline
  pilot-only local CI passed with `BackRefPilot` (0:11 elapsed). Post-edit
  pilot-only local CI passed with `BackRefPilot` (0:10 elapsed);
  `BackRefBlexer` replayed in about 4.1 seconds and `BackRefGBlexer` replayed
  in about 1.9 seconds. Final full local CI passed with Isabelle `Posix`
  (0:30 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and local CI
  certificate generation. After rebasing over `ade8125`, full local CI passed
  again with Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:11
  elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding direct retrieve/transport wrappers for
  the ordinary and generalized simplified bitcoded lexers in
  `BackRefBlexer.thy` and `BackRefGBlexer.thy`. New checked facts expose the
  exact simplified derivative expression used by `bblexer_simp`,
  `bblexer_step_simp`, `gbblexer_simp`, and `gbblexer_step_simp`, plus direct
  `map_option` transport from `blexer`/`gblexer` outputs. Final pilot-only
  local CI passed with `BackRefPilot` (0:10 elapsed); `BackRefBlexer` replayed
  in about 4.1 seconds and `BackRefGBlexer` replayed in about 2.0 seconds.
  Final full local CI passed with no-cheat guard, bounty guard, admin role
  guard, Isabelle `Posix` (0:31 elapsed), Isabelle `BackRefPilot` (0:04
  elapsed), and local CI certificate generation. After rebasing over
  `5f7ee75`, full local CI passed again with Isabelle `Posix` (0:04 elapsed),
  Isabelle `BackRefPilot` (0:11 elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding residual derivative-family
  subset/cardinality helpers in `BackRefBoundedBlueprint.thy`. New checked
  facts expose `BL_residual_derivative_family_subset`,
  `GBL_residual_derivative_family_subset`,
  `finite_BL_residual_derivative_family`,
  `finite_GBL_residual_derivative_family`,
  `BL_residual_derivative_family_card_le`, and
  `GBL_residual_derivative_family_card_le`. Pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 2.5 seconds. Final full local CI passed with Isabelle `Posix` (0:37
  elapsed), Isabelle `BackRefPilot` (0:16 elapsed), and local CI certificate
  generation; explicit statement guard PASS. After rebasing over `9981ea5`,
  full local CI passed again with Isabelle `Posix` (0:03 elapsed), Isabelle
  `BackRefPilot` (0:16 elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding residual finite-quotient closure
  helpers in `BackRefBoundedBlueprint.thy`. New checked facts expose
  `Ders_append`, `finite_left_quotients_Ders`,
  `finite_BL_derivatives_iff_left_quotients`,
  `finite_GBL_derivatives_iff_left_quotients`,
  `finite_BL_derivatives_xders`, and `finite_GBL_derivatives_gxders`.
  Pilot-only local CI passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 2.6 seconds. Final full local
  CI passed with Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot`
  (0:04 elapsed), local CI certificate generation, and explicit statement
  guard PASS.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding direct finite-left-quotient
  wrappers for successful `BL_bound`/`GBL_bound` calculations in
  `BackRefBoundedBlueprint.thy`. New checked facts expose
  `finite_left_quotients (BL r)`/`finite_left_quotients (GBL r)`, their
  already-derived `xders`/`gxders` states, and constructor-specific
  `BBACKREF`/`GBACKREF4` variants. Pilot-only local CI passed with
  `BackRefPilot` (0:16 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 2.6 seconds. Final full local CI passed with Isabelle `Posix` (0:04
  elapsed), Isabelle `BackRefPilot` (0:04 elapsed), local CI certificate
  generation, and explicit statement guard PASS.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding direct predicate wrappers for
  derivative residues in `BackRefBoundedBlueprint.thy`. New checked facts
  expose `finite_BL_derivatives (xders r s)` and
  `finite_GBL_derivatives (gxders r s)` from successful `BL_bound`/`GBL_bound`
  calculations, plus constructor-specific `BBACKREF` and `GBACKREF4`
  variants. Pilot-only local CI passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 1.7 seconds. Final full local
  CI passed with Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:04 elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding raw finite-set wrappers for
  semantic left-quotient families in `BackRefBoundedBlueprint.thy`. New
  checked facts expose `finite {Ders s A | s. True}` for bounded languages
  and specialize that wrapper to `backref_lang` and `backref_lang4`.
  Pilot-only local CI passed with `BackRefPilot` (0:15 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 1.7 seconds. Full local CI
  passed with Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:03 elapsed), and local CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding explicit finite-set wrappers for
  bounded derivative and residual derivative language families in
  `BackRefBoundedBlueprint.thy`. New checked facts expose raw
  `finite {...}` theorems for `BL_bound`/`GBL_bound` families and the
  constructor-specific `BBACKREF`/`GBACKREF4` packages, complementing the
  existing bounded-string subset/cardinality statements. Pilot-only local CI
  passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 2.1 seconds. Final full local
  CI passed with Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI
  certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding constructor-specific residual
  derivative-family finite-universe/cardinality wrappers in
  `BackRefBoundedBlueprint.thy`. New checked facts specialize the residual
  derivative-family subset/cardinality bounds to `BBACKREF` and `GBACKREF4`,
  and add monotone residual variants for larger external bounded-string
  universes. Pilot-only local CI passed with `BackRefPilot` (0:16 elapsed)
  and `BackRefBoundedBlueprint` replaying in about 1.7 seconds. Final full
  local CI passed with Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI
  certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding residual derivative-family
  finite-universe/cardinality wrappers in `BackRefBoundedBlueprint.thy`. New
  checked facts show that, from a successful `BL_bound`/`GBL_bound`, the
  derivative family reachable after any already consumed prefix still lies in
  the original `Pow (bounded_strings n)` universe and satisfies the same
  `2 ^ card (bounded_strings n)` cardinal upper bound. Pilot-only local CI
  passed with `BackRefPilot` (0:16 elapsed) and `BackRefBoundedBlueprint`
  replaying in about 2.0 seconds. Final full local CI passed with Isabelle
  `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and local
  CI certificate generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
  and local CI certificate generation after adding semantic left-quotient
  finite-universe/cardinality wrappers in `BackRefBoundedBlueprint.thy`. New
  checked facts place `{Ders s A | s. True}` for any bounded language inside
  `Pow (bounded_strings n)` with an explicit `2 ^ card (bounded_strings n)`
  bound, and specialize that package to `backref_lang` and `backref_lang4`
  with exact and larger external bounds. A pilot-only precheck passed with
  `BackRefPilot` (0:15 elapsed), and `BackRefBoundedBlueprint` replayed in
  about 1.5 seconds.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding monotone finite-universe/cardinality
  wrappers in `BackRefBoundedBlueprint.thy`. New checked facts allow derivative
  language families from successful `BL_bound`/`GBL_bound` calculations, and
  the constructor-specific `BBACKREF`/`GBACKREF4` packages, to be placed in
  `Pow (bounded_strings m)` for any larger external bound `m`; corresponding
  cardinal bounds use `2 ^ card (bounded_strings m)`. Pilot-only local CI
  passed with `BackRefPilot` (0:16 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 1.3 seconds. Final full local
  CI passed with Isabelle `Posix`, Isabelle `BackRefPilot`, and certificate
  generation.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  and Isabelle `BackRefPilot` after adding constructor-specific BR-019
  finite-universe/cardinality wrappers in `BackRefBoundedBlueprint.thy`. New
  checked facts state that bounded `BBACKREF` and `GBACKREF4` derivative
  language families are subsets of the relevant `Pow (bounded_strings n)` and
  satisfy the corresponding `2 ^ card (bounded_strings n)` upper bound.
  Pilot-only local CI passed with `BackRefPilot` (0:15 elapsed) and
  `BackRefBoundedBlueprint` replaying in about 1.2 seconds. The bounty guard
  accepted the BR-019 lock/collect ledger update. Final full local CI passed
  with Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03
  elapsed), and certificate generation. Explicit statement guard PASS.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  and local CI certificate generation after adding a finite derivative-family
  universe package in `BackRefBoundedBlueprint.thy`. New checked facts define
  `bounded_strings`, prove it finite, place every derivative language from a
  successful `BL_bound`/`GBL_bound` calculation inside
  `Pow (bounded_strings n)`, and give the explicit cardinal upper bound
  `2 ^ card (bounded_strings n)`. A pilot-only precheck also passed with
  `BackRefPilot` (0:11 elapsed) and `BackRefBoundedBlueprint` replaying in
  about 2.2 seconds.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:29 elapsed), Isabelle `BackRefPilot`, and local CI
  certificate generation after adding a BR-019 syntactic derivative-closure
  package in `BackRefBoundedBlueprint.thy`. New checked facts show that
  successful `BL_bound`/`GBL_bound` calculations remain defined after one
  derivative and after any `xders`/`gxders` derivative sequence, and that each
  syntactically bounded derivative expression again has a finite derivative
  language family. A pilot-only precheck also passed with `BackRefPilot`
  (0:11 elapsed) and `BackRefBoundedBlueprint` replaying in about 1.3 seconds.
  Closing verification after the progress update passed with Isabelle `Posix`
  (0:04 elapsed), Isabelle `BackRefPilot` (0:03 elapsed), certificate
  generation, and explicit statement guard PASS. After rebasing over the
  remote BR-015 completion commit, full local CI passed again with Isabelle
  `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:10 elapsed),
  certificate generation, and explicit statement guard PASS.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:11 elapsed),
  local CI certificate generation, and explicit statement guard after adding a
  BR-019 derivative-family bound package in `BackRefBoundedBlueprint.thy`. New
  checked facts show that semantic boundedness is preserved by
  `Ders`/`xders`/`gxders`, that every derivative language from a successful
  `BL_bound`/`GBL_bound` calculation is bounded by the same bound, and that
  syntactically bounded `BBACKREF` and `GBACKREF4` constructors have finite
  derivative-language families. `BackRefBoundedBlueprint` replayed in about
  0.8 seconds.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding syntactic bounded-fragment proof-prep
  in `BackRefBoundedBlueprint.thy`: bounded-language closure lemmas,
  conservative `BL_bound`/`GBL_bound` calculators, soundness lemmas, and
  finite derivative-language corollaries. Final full local CI also passed with
  Isabelle `Posix` (0:32 elapsed), Isabelle `BackRefPilot`, and local CI
  certificate generation; `BackRefBoundedBlueprint` replayed in about 1.1
  seconds in the pilot-only check.
- PASS on 2026-05-27 local time (2026-05-26 UTC) with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`,
  and local CI certificate generation after completing BR-015 in
  `BackRefValues.thy`. New checked facts include
  `BPosix_empty_bmkeps`, `BSEQ_split_unique`, and `BPosix_determ`;
  `BackRefValues` replayed in about 9.3 seconds. Early broad eliminations over
  `BPosix_elims` timed out because they destructed recursive POSIX assumptions;
  the checked proof uses named-target cases and small split/empty helpers.
- PASS on 2026-05-27 local time (2026-05-26 UTC) with no-cheat guard,
  bounty guard, admin role guard, Isabelle `Posix`, Isabelle `BackRefPilot`,
  and local CI certificate generation after adding `BackRefBoundedBlueprint.thy`.
  The new theory defines a semantic bounded-language/finite-left-quotient
  blueprint and proves `bounded_BBACKREF_finite_derivative_languages` and
  `bounded_GBACKREF4_finite_derivative_languages`; `BackRefBoundedBlueprint`
  replayed in about 0.27 seconds after replacing an expensive nested-image
  proof route.
- PASS on 2026-05-27 with no-cheat guard, bounty guard, admin role guard, and
  Isabelle `BackRefPilot` after adding BR-015 helper lemmas in
  `BackRefValues.thy`: `bval_list_eq_zipI`, `BBACKREF_split_cases`,
  `BBACKREF_split_unique`, and `BPosix_BBACKREF_value_unique`. The first
  broad `BPosix_determ` attempt and an early split proof timed out because
  `append_eq_append_conv2` was handed to recursive simplification; the checked
  version uses a one-shot `iffD1` step and explicit witnesses.
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

## Semantic Residual Backref Quotient Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-blueprint proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+89 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked theorems:
  - `bounded_backref_lang_residual_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang4_residual_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang_residual_left_quotient_family_card_bound`
  - `bounded_backref_lang4_residual_left_quotient_family_card_bound`
  - `bounded_backref_lang_residual_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang4_residual_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang_residual_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang4_residual_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang_residual_left_quotient_family_finite`
  - `bounded_backref_lang4_residual_left_quotient_family_finite`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:11 elapsed), and local CI certificate
  generation; `BackRefBoundedBlueprint` replayed in about 3.2 seconds. Final
  full local CI PASS with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:30 elapsed), Isabelle `BackRefPilot` (0:04 elapsed), and
  local CI certificate generation. After rebasing over `80c636b`, full local
  CI passed again with Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot`
  (0:11 elapsed), and local CI certificate generation.
- Notes:
  - This is additive semantic proof packaging in the bounded-fragment
    blueprint. It does not touch `BackRefValues.thy`, frozen language/value
    statements, production lexer files, or production bounds/closed-form
    theories.
  - The new wrappers specialize the generic residual left-quotient family
    universe/cardinality facts to `backref_lang` and `backref_lang4`, matching
    the existing direct left-quotient wrappers.
- Next smallest safe step: stop unless the admin opens a new bounty/statement
  target, or continue only with similarly small non-conflicting blueprint
  packaging.

## Residual Left-Quotient Family Helpers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-blueprint proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+91 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked lemmas/theorems:
  - `left_quotient_family_Ders_subset`
  - `finite_left_quotient_family_Ders`
  - `left_quotient_family_Ders_card_le`
  - `bounded_language_residual_left_quotient_family_subset_bounded_strings`
  - `bounded_language_residual_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_language_residual_left_quotient_family_card_bound`
  - `bounded_language_residual_left_quotient_family_card_bound_mono`
  - `bounded_language_residual_left_quotient_family_finite`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:11 elapsed), and no certificate
  generation; `BackRefBoundedBlueprint` replayed in about 2.2 seconds. Final
  full local CI PASS with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
  generation; explicit statement guard PASS.
- Notes:
  - This is additive proof packaging in the bounded-fragment blueprint. It
    does not touch `BackRefValues.thy`, frozen language/value statements,
    production lexer files, or production bounds/closed-form theories.
  - The new lemmas expose the exact residual quotient-family subset behind
    `finite_left_quotients_Ders` and package bounded-string universe and
    cardinality bounds for quotient families after an already-consumed prefix.
- Next smallest safe step: stop unless the admin opens a new bounty/statement
  target, or continue only with similarly small non-conflicting blueprint
  packaging.

## Residual Derivative-Family Subset Helpers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-blueprint proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+68 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked lemmas:
  - `BL_residual_derivative_family_subset`
  - `GBL_residual_derivative_family_subset`
  - `finite_BL_residual_derivative_family`
  - `finite_GBL_residual_derivative_family`
  - `BL_residual_derivative_family_card_le`
  - `GBL_residual_derivative_family_card_le`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:16 elapsed), and no certificate
  generation; `BackRefBoundedBlueprint` replayed in about 2.5 seconds. Final
  full local CI PASS with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:37 elapsed), Isabelle `BackRefPilot` (0:16 elapsed),
  local CI certificate generation, and explicit statement guard PASS. After
  rebasing over `9981ea5`, full local CI passed again with Isabelle `Posix`
  (0:03 elapsed), Isabelle `BackRefPilot` (0:16 elapsed), and local CI
  certificate generation.
- Notes:
  - This is additive proof packaging in the bounded-fragment blueprint. It
    does not touch `BackRefValues.thy`, frozen language/value statements,
    production lexer files, or production bounds/closed-form theories.
  - The new subset lemmas expose that a derivative family reachable after an
    already-consumed prefix is included in the original derivative-language
    family, giving direct finite/cardinality reuse without redoing append
    reasoning at each bounded wrapper.
- Next smallest safe step: if continuing Agent A work, keep packaging small
  generic closure facts in `BackRefBoundedBlueprint.thy` or stop until the
  admin opens a new bounty/statement target.

## Residual Finite-Quotient Closure Helpers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-blueprint proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy`, `PROGRESS_BACKREF.md`
- New checked lemmas:
  - `Ders_append`
  - `finite_left_quotients_Ders`
  - `finite_BL_derivatives_iff_left_quotients`
  - `finite_GBL_derivatives_iff_left_quotients`
  - `finite_BL_derivatives_xders`
  - `finite_GBL_derivatives_gxders`
- Build: pilot-only local CI PASS with no-cheat guard, bounty guard, admin
  role guard, Isabelle `BackRefPilot` (0:16 elapsed), and no certificate
  generation; `BackRefBoundedBlueprint` replayed in about 2.6 seconds. Final
  full local CI PASS with no-cheat guard, bounty guard, admin role guard,
  Isabelle `Posix` (0:35 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
  local CI certificate generation, and explicit statement guard PASS.
- Notes:
  - This is additive proof packaging in the bounded-fragment blueprint. It
    does not touch `BackRefValues.thy`, frozen language/value statements,
    production lexer files, or production bounds/closed-form theories.
  - The new closure lemmas expose that finite derivative-language predicates
    are stable under already-consumed prefixes without requiring a fresh
    `BL_bound`/`GBL_bound` calculation.
- Next smallest safe step: continue with small quotient/derivative packaging
  only if it remains non-conflicting and admin-useful.

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
  - `BL_bound`
  - `GBL_bound`
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
  - `Ders_append`
  - `finite_left_quotients_Ders`
  - `finite_BL_derivatives_iff_left_quotients`
  - `finite_GBL_derivatives_iff_left_quotients`
  - `finite_BL_derivatives_xders`
  - `finite_GBL_derivatives_gxders`
  - bounded-language closure lemmas for union, sequencing, fixed powers, and
    zero-bounded stars
  - constructor-level `BL_bounded`/`GBL_bounded` closure lemmas
  - `bounded_language_Ders`
  - `BL_bounded_xders`
  - `GBL_bounded_gxders`
  - `BL_bound_sound`
  - `GBL_bound_sound`
  - `BL_bound_finite_derivative_languages`
  - `GBL_bound_finite_derivative_languages`
  - `BL_bound_xders_bounded`
  - `GBL_bound_gxders_bounded`
  - `BL_bound_derivative_family_bounded`
  - `GBL_bound_derivative_family_bounded`
  - `BL_bound_xder_residue_defined`
  - `BL_bound_xder_defined`
  - `GBL_bound_gxder_defined`
  - `BL_bound_xders_defined`
  - `GBL_bound_gxders_defined`
  - `BL_bound_xders_finite_derivative_languages`
  - `GBL_bound_gxders_finite_derivative_languages`
  - `BL_bound_BBACKREF_finite_derivative_languages`
  - `GBL_bound_GBACKREF4_finite_derivative_languages`
  - `bounded_strings`
  - `finite_bounded_strings`
  - `BL_bound_derivative_family_subset_bounded_strings`
  - `GBL_bound_derivative_family_subset_bounded_strings`
  - `BL_bound_derivative_family_card_bound`
  - `GBL_bound_derivative_family_card_bound`
  - `BL_bound_derivative_family_finite`
  - `GBL_bound_derivative_family_finite`
  - `BL_bound_residual_derivative_family_subset_bounded_strings`
  - `GBL_bound_residual_derivative_family_subset_bounded_strings`
  - `BL_bound_residual_derivative_family_card_bound`
  - `GBL_bound_residual_derivative_family_card_bound`
  - `BL_bound_residual_derivative_family_finite`
  - `GBL_bound_residual_derivative_family_finite`
  - `BL_bound_xders_finite_BL_derivatives`
  - `GBL_bound_gxders_finite_GBL_derivatives`
  - `BL_bound_residual_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_residual_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_residual_derivative_family_card_bound_mono`
  - `GBL_bound_residual_derivative_family_card_bound_mono`
  - `BL_bound_BBACKREF_residual_derivative_family_subset_bounded_strings`
  - `GBL_bound_GBACKREF4_residual_derivative_family_subset_bounded_strings`
  - `BL_bound_BBACKREF_residual_derivative_family_card_bound`
  - `GBL_bound_GBACKREF4_residual_derivative_family_card_bound`
  - `BL_bound_BBACKREF_residual_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_GBACKREF4_residual_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_BBACKREF_residual_derivative_family_card_bound_mono`
  - `GBL_bound_GBACKREF4_residual_derivative_family_card_bound_mono`
  - `BL_bound_BBACKREF_residual_derivative_family_finite`
  - `GBL_bound_GBACKREF4_residual_derivative_family_finite`
  - `BL_bound_BBACKREF_xders_finite_BL_derivatives`
  - `GBL_bound_GBACKREF4_gxders_finite_GBL_derivatives`
  - `bounded_language_left_quotient_family_subset_bounded_strings`
  - `bounded_language_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_language_left_quotient_family_card_bound`
  - `bounded_language_left_quotient_family_card_bound_mono`
  - `bounded_language_left_quotient_family_finite`
  - `bounded_backref_lang_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang4_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang_left_quotient_family_card_bound`
  - `bounded_backref_lang4_left_quotient_family_card_bound`
  - `bounded_backref_lang_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang4_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang4_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang_left_quotient_family_finite`
  - `bounded_backref_lang4_left_quotient_family_finite`
  - `BL_bound_BBACKREF_derivative_family_subset_bounded_strings`
  - `GBL_bound_GBACKREF4_derivative_family_subset_bounded_strings`
  - `BL_bound_BBACKREF_derivative_family_card_bound`
  - `GBL_bound_GBACKREF4_derivative_family_card_bound`
  - `BL_bound_BBACKREF_derivative_family_finite`
  - `GBL_bound_GBACKREF4_derivative_family_finite`
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
  - `BPosix_empty_bmkeps`
  - `BSEQ_split_unique`
  - `BPosix_determ` (BR-015)
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
  - `bblexer_simp_defined_iff`
  - `bblexer_simp_blexer_retrieve`
  - `bblexer_simp_retrieve_correctness`
  - `bbders_simp`
  - `bblexer_step_simp`
  - `bbders_simp_bretrieve_blexer`
  - `bblexer_step_simp_correctness`
  - `bblexer_step_simp_retrieve_correctness`
  - `bblexer_step_simp_blexer_retrieve`
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
  - `gbblexer_simp_defined_iff`
  - `gbblexer_simp_gblexer_retrieve`
  - `gbblexer_simp_retrieve_correctness`
  - `gbblexer_step_simp_defined_iff`
  - `gbblexer_step_simp_correctness`
  - `gbblexer_step_simp_retrieve_correctness`
  - `gbblexer_step_simp_gblexer_retrieve`
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
20. ~~Complete BR-015 POSIX value ordering with `BPosix_determ`.~~ DONE
21. ~~Complete BR-019 bounded fragment theorem for backreferences.~~ DONE
22. BR-019 now has a checked semantic finite-derivative-language blueprint and
    checked syntactic bounded-fragment proof-prep through
    `BL_bound_finite_derivative_languages` and
    `GBL_bound_finite_derivative_languages`, plus derivative-family boundedness
    and syntactic derivative-closure/constructor packages. The latest package
    also places the derivative-language family for bounded `BBACKREF` and
    `GBACKREF4` constructors inside the finite universe
    `Pow (bounded_strings n)` with explicit cardinal bounds. The residual
    derivative-family package shows the same original universe/cardinality
    bound after any already consumed prefix, and the latest wrapper package
    specializes those residual facts to `BBACKREF`/`GBACKREF4` with monotone
    larger-universe variants. The current finite-wrapper packages also expose
    raw `finite {...}` facts for semantic left quotients, derivative families,
    and residual derivative families. The newest residue-predicate wrappers
    expose direct `finite_BL_derivatives`/`finite_GBL_derivatives` facts for
    arbitrary already-derived states, including constructor-specific
    `BBACKREF`/`GBACKREF4` states. The latest predicate wrapper package also
    exposes `finite_left_quotients` facts for successful syntactic bounds and
    for already-derived bounded states, including constructor-specific
    `BBACKREF`/`GBACKREF4` states. No active bounty remains on
    `BACKREF_BOUNTIES.md`; production bounds or closed-form work should still
    wait for a new admin task.
23. ~~Add direct retrieve/transport wrappers for simplified bitcoded lexers.~~
    DONE
24. ~~Package direct equality between post-derivative and per-step simplified
    bitcoded lexer entry points.~~ DONE

## Simplified Lexer Equality Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent B implementation packaging lane
- Files changed: `BackRefBlexer.thy` (+4), `BackRefGBlexer.thy` (+4),
  `PROGRESS_BACKREF.md`
- New checked theorems:
  - `bblexer_simp_step_simp_eq`
  - `gbblexer_simp_step_simp_eq`
- Build:
  - Baseline pilot-only local CI PASS with no-cheat guard, bounty guard, admin
    role guard, and Isabelle `BackRefPilot` (0:11 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:10 elapsed);
    `BackRefBlexer` replayed in about 4.1 seconds and `BackRefGBlexer`
    replayed in about 1.9 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:30 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed), and local CI certificate generation.
  - Post-rebase full local CI PASS over remote `ade8125` with no-cheat guard,
    bounty guard, admin role guard, Isabelle `Posix` (0:03 elapsed), Isabelle
    `BackRefPilot` (0:11 elapsed), and local CI certificate generation.
- Notes:
  - This is additive theorem packaging only. It identifies the two checked
    simplified lexer entry points directly, without changing definitions,
    semantics, frozen statements, production `Blexer*`, bounds files, or
    closed-form theories.
- Next smallest safe step: no active bounty remains; wait for an admin-created
  production integration task or a new bounty before changing frozen semantics,
  production lexers, bounds, or closed-form theories.

## Simplified Bitcoded Transport Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `03625a6`
- Agent lane: Codex Agent B implementation packaging lane
- Files changed: `BackRefBlexer.thy` (+54), `BackRefGBlexer.thy` (+54),
  `PROGRESS_BACKREF.md`
- New checked theorems:
  - `bblexer_simp_defined_iff`
  - `bblexer_simp_blexer_retrieve`
  - `bblexer_simp_retrieve_correctness`
  - `bblexer_step_simp_retrieve_correctness`
  - `bblexer_step_simp_blexer_retrieve`
  - `gbblexer_simp_defined_iff`
  - `gbblexer_simp_gblexer_retrieve`
  - `gbblexer_simp_retrieve_correctness`
  - `gbblexer_step_simp_retrieve_correctness`
  - `gbblexer_step_simp_gblexer_retrieve`
- Build:
  - Pre-edit baseline pilot-only local CI PASS with no-cheat guard, bounty
    guard, admin role guard, and Isabelle `BackRefPilot` (0:11 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:11 elapsed);
    `BackRefBlexer` replayed in about 4.7 seconds and `BackRefGBlexer` replayed
    in about 1.9 seconds.
  - Final pilot-only local CI PASS after the direct transport wrappers with
    no-cheat guard, bounty guard, admin role guard, and Isabelle
    `BackRefPilot` (0:10 elapsed); `BackRefBlexer` replayed in about 4.1
    seconds and `BackRefGBlexer` replayed in about 2.0 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:31 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed), and local CI certificate generation.
  - Post-rebase full local CI PASS over remote `5f7ee75` with no-cheat guard,
    bounty guard, admin role guard, Isabelle `Posix` (0:04 elapsed),
    Isabelle `BackRefPilot` (0:11 elapsed), and local CI certificate
    generation.
- Notes:
  - This is additive theorem packaging only. It does not change lexer
    definitions, semantics, frozen statements, `BackRefBoundedBlueprint.thy`,
    production `Blexer*`, bounds files, or closed-form theories.
  - The new wrappers characterize the actual simplified derivative expression
    used by each simplified bitcoded lexer and expose the direct
    `map_option` transport from `blexer`/`gblexer`, instead of requiring users
    to rewrite through the base `bblexer`/`gbblexer` retrieve theorem.
- Next smallest safe step: no active bounty remains; wait for an admin-created
  production integration task or a new bounty before changing frozen semantics,
  production lexers, bounds, or closed-form theories.

## Finite Left-Quotient Predicate Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `159374c`
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+368 current theory delta
  before this progress note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_finite_left_quotients`
  - `GBL_bound_finite_left_quotients`
  - `BL_bound_xders_finite_left_quotients`
  - `GBL_bound_gxders_finite_left_quotients`
  - `BL_bound_BBACKREF_finite_left_quotients`
  - `GBL_bound_GBACKREF4_finite_left_quotients`
  - `BL_bound_BBACKREF_xders_finite_left_quotients`
  - `GBL_bound_GBACKREF4_gxders_finite_left_quotients`
- Build:
  - Pre-edit dirty-state pilot-only local CI PASS with no-cheat guard, bounty
    guard, admin role guard, and Isabelle `BackRefPilot` (0:04 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:16 elapsed);
    `BackRefBoundedBlueprint` replayed in about 2.6 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed), local CI certificate generation, and explicit statement guard
    PASS.
- Notes:
  - This is additive theorem packaging over the checked syntactic boundedness
    calculator and already checked `xders`/`gxders` boundedness facts.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Derivative Residue Predicate Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `159374c`
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+294 current theory delta
  before this progress note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_xders_finite_BL_derivatives`
  - `GBL_bound_gxders_finite_GBL_derivatives`
  - `BL_bound_BBACKREF_xders_finite_BL_derivatives`
  - `GBL_bound_GBACKREF4_gxders_finite_GBL_derivatives`
- Build:
  - Pre-edit dirty-state pilot-only local CI PASS with no-cheat guard, bounty
    guard, admin role guard, and Isabelle `BackRefPilot` (0:03 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:16 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.7 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed), and local CI certificate generation.
- Notes:
  - This is additive theorem packaging over already checked residual
    derivative-family finite-set facts.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Semantic Left-Quotient Finite Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `159374c`
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+267 current theory delta
  before this progress note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `bounded_language_left_quotient_family_finite`
  - `bounded_backref_lang_left_quotient_family_finite`
  - `bounded_backref_lang4_left_quotient_family_finite`
- Build:
  - Pre-edit dirty-state pilot-only local CI PASS with no-cheat guard, bounty
    guard, admin role guard, and Isabelle `BackRefPilot` (0:03 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:15 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.7 seconds.
  - Full local CI PASS with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:03 elapsed),
    and local CI certificate generation.
- Notes:
  - This is additive theorem packaging over the existing
    `finite_left_quotients` bounded-language package.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Finite Derivative-Family Wrappers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `159374c`
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+246 total worktree delta
  before this progress note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_derivative_family_finite`
  - `GBL_bound_derivative_family_finite`
  - `BL_bound_residual_derivative_family_finite`
  - `GBL_bound_residual_derivative_family_finite`
  - `BL_bound_BBACKREF_residual_derivative_family_finite`
  - `GBL_bound_GBACKREF4_residual_derivative_family_finite`
  - `BL_bound_BBACKREF_derivative_family_finite`
  - `GBL_bound_GBACKREF4_derivative_family_finite`
- Build:
  - Existing dirty state pilot-only local CI PASS with no-cheat guard, bounty
    guard, admin role guard, and Isabelle `BackRefPilot` (0:03 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:16 elapsed);
    `BackRefBoundedBlueprint` replayed in about 2.1 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
    generation.
- Notes:
  - This is additive theorem packaging over already checked finite-derivative,
    residual subset, and constructor-specific bounded-string universe facts.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Constructor Residual Derivative-Family Bounds (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `159374c`
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+174 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_residual_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_residual_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_residual_derivative_family_card_bound_mono`
  - `GBL_bound_residual_derivative_family_card_bound_mono`
  - `BL_bound_BBACKREF_residual_derivative_family_subset_bounded_strings`
  - `GBL_bound_GBACKREF4_residual_derivative_family_subset_bounded_strings`
  - `BL_bound_BBACKREF_residual_derivative_family_card_bound`
  - `GBL_bound_GBACKREF4_residual_derivative_family_card_bound`
  - `BL_bound_BBACKREF_residual_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_GBACKREF4_residual_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_BBACKREF_residual_derivative_family_card_bound_mono`
  - `GBL_bound_GBACKREF4_residual_derivative_family_card_bound_mono`
- Build:
  - Pre-edit pilot-only local CI PASS with no-cheat guard, bounty guard, admin
    role guard, and Isabelle `BackRefPilot` (0:03 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:16 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.7 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix`, Isabelle `BackRefPilot`, and local CI certificate
    generation.
- Notes:
  - This is additive theorem packaging over the checked residual
    derivative-family universe bounds and the constructor-specific
    `BL_bound`/`GBL_bound` arithmetic wrappers.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Residual Derivative-Family Universe Bounds (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+60 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_residual_derivative_family_subset_bounded_strings`
  - `GBL_bound_residual_derivative_family_subset_bounded_strings`
  - `BL_bound_residual_derivative_family_card_bound`
  - `GBL_bound_residual_derivative_family_card_bound`
- Build:
  - Pre-edit pilot-only local CI PASS with no-cheat guard, bounty guard, admin
    role guard, and Isabelle `BackRefPilot` (0:04 elapsed).
  - Post-edit pilot-only local CI PASS with no-cheat guard, bounty guard,
    admin role guard, and Isabelle `BackRefPilot` (0:16 elapsed);
    `BackRefBoundedBlueprint` replayed in about 2.0 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed), and local CI certificate generation.
- Notes:
  - This is additive theorem packaging over `xders_append`/`gxders_append` and
    the existing `bounded_strings` finite universe.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## Semantic Left-Quotient Finite-Universe Bounds (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+117 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked theorems:
  - `bounded_language_left_quotient_family_subset_bounded_strings`
  - `bounded_language_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_language_left_quotient_family_card_bound`
  - `bounded_language_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang4_left_quotient_family_subset_bounded_strings`
  - `bounded_backref_lang_left_quotient_family_card_bound`
  - `bounded_backref_lang4_left_quotient_family_card_bound`
  - `bounded_backref_lang_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang4_left_quotient_family_subset_bounded_strings_mono`
  - `bounded_backref_lang_left_quotient_family_card_bound_mono`
  - `bounded_backref_lang4_left_quotient_family_card_bound_mono`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:15 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.5 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:03
    elapsed), and certificate generation.
- Notes:
  - This is additive theorem packaging over the semantic bounded-language
    layer and the checked `backref_lang`/`backref_lang4` boundedness lemmas.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## BR-019 Monotone Finite-Universe Bounds (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+116 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked lemmas:
  - `bounded_strings_mono`
  - `bounded_language_subset_bounded_strings_mono`
- New checked theorems:
  - `BL_bound_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_derivative_family_card_bound_mono`
  - `GBL_bound_derivative_family_card_bound_mono`
  - `BL_bound_BBACKREF_derivative_family_subset_bounded_strings_mono`
  - `GBL_bound_GBACKREF4_derivative_family_subset_bounded_strings_mono`
  - `BL_bound_BBACKREF_derivative_family_card_bound_mono`
  - `GBL_bound_GBACKREF4_derivative_family_card_bound_mono`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:04 elapsed).
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03
    elapsed), and certificate generation.
  - Explicit statement guard PASS.
- Notes:
  - This is an additive theorem-packaging step over the checked BR-019
    finite-universe package.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
  - No active bounty remains in `BACKREF_BOUNTIES.md`.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; otherwise keep future work to additive pilot-only
  packaging.

## BR-019 Constructor Finite-Universe Bounds (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment theorem packaging lane
- Files changed: `BackRefBoundedBlueprint.thy` (+54 before this progress
  note), `BACKREF_BOUNTIES.md` (+6/-3 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked theorems:
  - `BL_bound_BBACKREF_derivative_family_subset_bounded_strings`
  - `GBL_bound_GBACKREF4_derivative_family_subset_bounded_strings`
  - `BL_bound_BBACKREF_derivative_family_card_bound`
  - `GBL_bound_GBACKREF4_derivative_family_card_bound`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:15 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.2 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:03 elapsed), Isabelle `BackRefPilot` (0:03
    elapsed), and local CI certificate generation.
  - Explicit statement guard PASS.
  - Bounty guard PASS after moving BR-019 to completed and recording
    `L-CODEX-A-019`.
- Bounty:
  - BR-019 is now marked DONE with Codex as owner.
  - The active bounty table is empty; allocated and collected pool totals both
    stand at 24,970.
- Notes:
  - This is additive theorem packaging over the already checked
    `BL_bound`/`GBL_bound` finite-universe package.
  - It does not touch `BackRefValues.thy`, production `Blexer*`, old bounds, or
    closed-form theories.
- Next smallest safe step: wait for an admin-created production integration or
  statement-freeze task; no active bounty remains in `BACKREF_BOUNTIES.md`.

## BR-019 Finite Derivative-Family Universe Package (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+90 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked definitions:
  - `bounded_strings`, the finite universe of strings with length at most a
    successful syntactic bound
- New checked lemmas/theorems:
  - `finite_bounded_strings`
  - `bounded_language_subset_bounded_strings`
  - `card_Pow_finite`
  - `BL_bound_derivative_family_subset_bounded_strings`
  - `GBL_bound_derivative_family_subset_bounded_strings`
  - `BL_bound_derivative_family_card_bound`
  - `GBL_bound_derivative_family_card_bound`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:11 elapsed);
    `BackRefBoundedBlueprint` replayed in about 2.2 seconds.
  - Full local CI PASS with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:04 elapsed),
    and local CI certificate generation.
- Performance note:
  - The first draft failed fast on finite-list and powerset-cardinality proof
    details; the checked version uses explicit `finite_lists_length_le`,
    `card_image`, and `card_mono` steps. No slow proof command was accepted.
- Notes:
  - This does not touch `BackRefValues.thy`, production `Blexer*`, bounds, or
    closed-form theories.
  - This strengthens the BR-019 bounded-fragment blueprint from "finite" to an
    explicit finite universe/cardinality bound for derivative languages.
- Next smallest safe step: ask the admin whether the accumulated
  `BL_bound`/`GBL_bound` finite-universe package is enough to mark BR-019 done,
  or whether a production-facing theorem name/statement should be frozen first.

## BR-019 Syntactic Derivative-Closure Package (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+186 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked lemmas/theorems:
  - `BL_bound_xder_residue_defined`
  - `BL_bound_xder_defined`
  - `GBL_bound_gxder_defined`
  - `BL_bound_xders_defined`
  - `GBL_bound_gxders_defined`
  - `BL_bound_xders_finite_derivative_languages`
  - `GBL_bound_gxders_finite_derivative_languages`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:11 elapsed);
    `BackRefBoundedBlueprint` replayed in about 1.3 seconds.
  - Full local CI PASS with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (0:29 elapsed), Isabelle `BackRefPilot`, and local CI
    certificate generation.
  - Closing full local CI PASS after this progress update with no-cheat guard,
    bounty guard, admin role guard, Isabelle `Posix` (0:04 elapsed), Isabelle
    `BackRefPilot` (0:03 elapsed), and local CI certificate generation.
  - Post-rebase full local CI PASS after replaying over the remote BR-015
    completion commit with no-cheat guard, bounty guard, admin role guard,
    Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:10 elapsed),
    and local CI certificate generation.
  - Explicit statement guard PASS: 2 frozen theory files checked, no statement
    modifications.
- Performance note:
  - The first draft failed fast because three existential witnesses were left
    implicit. The checked proof uses explicit residue cases and explicit
    witness choices; no slow proof command was accepted.
- Notes:
  - This proves syntactic closure of the conservative `BL_bound` and
    `GBL_bound` calculators under `xder`/`gxder` and `xders`/`gxders`.
  - This still does not touch `BackRefValues.thy`, production `Blexer*`,
    bounds, or closed-form theories.
- Next smallest safe step: run the statement guard and commit this checked
  additive package; then keep BR-015 reserved for Codex Agent B and ask admin
  whether the accumulated `BL_bound`/`GBL_bound` packages are sufficient for
  BR-019's production target.

## BR-019 Derivative-Family Bound Package (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent A bounded-fragment proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+77 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked lemmas/theorems:
  - `bounded_language_Ders`
  - `BL_bounded_xders`
  - `GBL_bounded_gxders`
  - `BL_bound_xders_bounded`
  - `GBL_bound_gxders_bounded`
  - `BL_bound_derivative_family_bounded`
  - `GBL_bound_derivative_family_bounded`
  - `BL_bound_finite_left_quotients`
  - `GBL_bound_finite_left_quotients`
  - `BL_bound_xders_finite_left_quotients`
  - `GBL_bound_gxders_finite_left_quotients`
  - `BL_bound_BBACKREF_finite_left_quotients`
  - `GBL_bound_GBACKREF4_finite_left_quotients`
  - `BL_bound_BBACKREF_xders_finite_left_quotients`
  - `GBL_bound_GBACKREF4_gxders_finite_left_quotients`
  - `BL_bound_BBACKREF_finite_derivative_languages`
  - `GBL_bound_GBACKREF4_finite_derivative_languages`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:10 elapsed);
    `BackRefBoundedBlueprint` replayed in about 0.7 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:04 elapsed), Isabelle `BackRefPilot` (0:11
    elapsed), and local CI certificate generation; `BackRefBoundedBlueprint`
    replayed in about 0.8 seconds.
  - Explicit statement guard PASS: 2 frozen theory files checked, no statement
    modifications.
- Performance note:
  - The first `bounded_language_Ders` proof failed fast on a local length
    arithmetic step. The checked proof uses an explicit `Ders` membership
    witness and a length chain; no slow command was accepted.
- Notes:
  - This is still bounded-fragment proof-prep for BR-019. It does not claim a
    finite syntactic derivative-state bound.
  - This does not touch `BackRefValues.thy`, production `Blexer*`, bounds, or
    closed-form theories.
- Next smallest safe step: BR-015 is complete; ask admin
  whether the `BL_bound`/`GBL_bound` and derivative-family boundedness
  statements are acceptable as the BR-019 production target.

## BR-019 Syntactic Bounded Fragment Proof-Prep (2026-05-27)

- Branch: `codex/backref-values`
- Commit: `3418f0f`
- Agent lane: Codex Agent A bounded-fragment proof-prep lane
- Files changed: `BackRefBoundedBlueprint.thy` (+288 before this progress
  note), `PROGRESS_BACKREF.md`
- New checked definitions:
  - `BL_bound`, a conservative syntactic bound calculator for current `brexp`
  - `GBL_bound`, the corresponding calculator for standalone generalized
    `gbrexp`
- New checked lemmas/theorems:
  - bounded-language closure for empty/singleton languages, union, sequencing,
    fixed powers, and zero-bounded stars
  - constructor-level `BL_bounded` lemmas for non-star constructors,
    `BNTIMES`, zero-bounded `BSTAR`, `BBACKREF`, `BHALF`, and `BRESIDUE`
  - constructor-level `GBL_bounded` lemmas for `GBASE`, `GALT`, and
    `GBACKREF4`
  - `BL_bound_sound`
  - `GBL_bound_sound`
  - `BL_bound_finite_derivative_languages`
  - `GBL_bound_finite_derivative_languages`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:10 elapsed); `BackRefBoundedBlueprint`
    replayed in about 1.1 seconds.
  - Final full local CI PASS with no-cheat guard, bounty guard, admin role
    guard, Isabelle `Posix` (0:32 elapsed), Isabelle `BackRefPilot` (0:04
    elapsed/no rebuild), and local CI certificate generation.
- Performance note:
  - Initial proof scripts failed fast on local helper facts. The checked version
    uses explicit induction/case facts for `bounded_language_pow` and
    `bounded_language_star_zero`, avoiding broad search.
- Notes:
  - This remains semantic proof-prep for BR-019 and does not claim a finite
    syntactic derivative-state bound.
  - This does not touch `BackRefValues.thy`, production `Blexer*`, bounds, or
    closed-form theories.
- Next smallest safe step: BR-015 is complete; ask admin
  whether the `BL_bound`/`GBL_bound` statements are acceptable as the BR-019
  bounded-fragment production target.

## BR-015 POSIX Value Ordering Complete (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent B, BR-015 POSIX value ordering
- Files changed: `BackRefValues.thy` (+356 before progress/bounty notes),
  `PROGRESS_BACKREF.md`, `BACKREF_BOUNTIES.md`
- New checked helper lemmas:
  - `bval_list_eq_replicateI`
  - `BPosix_empty_bmkeps`
  - `BSEQ_split_unique`
- New checked theorem:
  - `BPosix_determ`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:16 elapsed); `BackRefValues`
    replayed in about 8.9 seconds.
  - Final post-rebase full local CI PASS with no-cheat guard, bounty guard,
    admin role guard, Isabelle `Posix` (0:03 elapsed/no rebuild), Isabelle
    `BackRefPilot` (0:11 elapsed), and local CI certificate generation;
    `BackRefValues` replayed in about 9.3 seconds.
  - Explicit statement guard PASS: 2 frozen theory files checked, no statement
    modifications.
- Performance note:
  - Initial `BPosix_determ` attempts timed out when `auto elim!: BPosix_elims`
    was used in contexts containing recursive POSIX premises. The checked proof
    case-splits only the named target derivation and reuses
    `BPosix_BBACKREF_value_unique` for the backreference constructor.
- Notes:
  - BR-015 is now marked collected in `BACKREF_BOUNTIES.md`.
  - No production `Blexer*`, bounds, closed-form, or frozen language semantics
    files were touched.
- Next smallest safe step:
  - Leave BR-019 blocked pending admin acceptance of the bounded-fragment
    statement.

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

## BR-015 Backreference POSIX Split Helpers (2026-05-27)

- Branch: `codex/backref-values`
- Commit: this checked commit
- Agent lane: Codex Agent B, BR-015 POSIX value ordering
- Files changed: `BackRefValues.thy` (+122 before this progress note),
  `PROGRESS_BACKREF.md`
- New checked lemmas:
  - `bval_list_eq_zipI`
  - `BBACKREF_split_cases`
  - `BBACKREF_split_unique`
  - `BPosix_BBACKREF_value_unique`
- Build:
  - Pilot-only local CI PASS with no-cheat guard, bounty guard, admin role
    guard, and Isabelle `BackRefPilot` (0:08 elapsed); `BackRefValues` replayed
    in about 5.6 seconds after the final helper proof.
- Performance note:
  - A broad `BPosix_determ` attempt and an early version of
    `BBACKREF_split_unique` timed out. Root cause: using
    `append_eq_append_conv2` as a simplification rule recursively rewrote newly
    generated append equalities. The checked proof applies it once through
    `iffD1` in `BBACKREF_split_cases` and then constructs greedy-condition
    contradiction witnesses explicitly.
- Next smallest safe step:
  - Prove `BPosix_determ` by reusing `BPosix_BBACKREF_value_unique` and
    replacing broad `cases`/`auto` blocks by constructor-specific eliminations.

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
