# Posix Backref Design Log

This file records semantic design changes that affect later proofs. It is meant
to be read before continuing long-running agent work.

## 2026-05-31: Cubic non-backref size-bound direction

- The current 50k cubic-size bounty is for the non-backref fragment only.
  `RBACKREF4`, `RHALF`, and `RRESIDUE` remain excluded from the bounded
  fragment because their payload strings can grow with input, not just regex
  size.
- The strongest checked candidate is no longer eager `rsimp5` row products.
  `rsimp5` is language-correct, but checked counterexamples show that full
  right-side row-product distribution wants a larger universe than the current
  cubic accounting can justify.
- The current preferred route is the normalized Antimirov row-list driver:
  `rpder_norm_list`, `rpder_norm_rows`, and `rpders_norm1_rows`, mirrored by
  `bpder_norm_rows` in the annotated layer and connected by erasure lemmas in
  `FBound.thy`.
- The accounting target is the combined universe
  `partial_derivative_cubic_universe r =
   partial_derivative_path_universe r union
   partial_derivative_frontier_universe r`. The path side has linear
  cardinality and quadratic member size; the frontier side has quadratic
  cardinality and linear member size. The checked partition lemma avoids the
  quartic bound that would come from multiplying the union cardinality by the
  worst member size.
- New checked closure support:
  `set_rflts_subset_rsubterms_list`,
  `rpder_norm_rows_single_path_subterms_subset`,
  `rsubterms_linear_continuation_subset`, and
  `rsubterms_frontier_universe_member_subset`. These lemmas show where the
  real remaining theorem lives: repeated normalized rows must be shown to stay
  in the original combined universe, or the simplifier must be redesigned so
  that this invariant is structurally obvious.
- Do not claim BR-032/BR-033 completion for wrappers or restatements. A valid
  claim needs a checked new algorithmic definition or the repeated-state
  closure theorem, plus the standard Isabelle/guard run.

## 2026-05-29: Structured proof-shape rule

- Do not start difficult Isabelle proofs by throwing broad `auto` at the whole
  goal. Split first by datatype constructor or inductive case, expose the case
  facts, and keep the goal shape close to the semantic proof idea.
- For production proofs, a single line taking more than about 1-2 seconds is
  already suspect. Prefer a named helper lemma with only the branch-specific
  assumptions over accepting a slow monolithic tactic line.
- If a branch is still complex, make it a named helper lemma with only the
  assumptions needed for that branch. This keeps later repair local and avoids
  burying the invariant inside a giant proof state.
- Use broad automation only after the structure is understood. An early `auto`
  can rewrite, split, or simplify away information in a way that leaves a less
  recoverable goal.
- `Blexer.thy:bder_retrieve_ABACKREF4` follows this rule: the old 16-branch
  `auto` proof was split into prefix, capture, r3-tail, residue-tail, and
  r4-tail retrieve lemmas, then reassembled with explicit nullable cases.

## 2026-05-28: Long-run execution model

- The 4h40m work interval was a single Codex Desktop conversation that kept
  making bounded tool calls, patches, and proof-check attempts. It was not two
  still-running spawned agents.
- A disconnected UI can interrupt the current conversation. Detached CLI/tmux
  loops survive only when they were actually started in tmux or a background
  process group.
- For robust overnight work, prefer the WSL/tmux loop scripts in
  `agent_hunt_pipeline` and keep every proof command under an explicit timeout.
- Human proof-search rule added after the `Blexer.thy:bder_retrieve` slowdown:
  `auto`/`simp`/broad proof search that does not return within roughly 0.5s
  should be treated as the wrong tactic. Split the goal immediately instead of
  letting the command run for tens of seconds.

## 2026-05-28: Why `injval` is `primrec`

- Earlier definitions with nested, overlapping pattern matching made Isabelle's
  function package spend too long on generated obligations and simplification.
- The current direction is to recurse structurally on `rexp` only, and inspect
  the derivative value with local `case` expressions inside each constructor.
- If a proof command around `injval` runs for tens of seconds, split it into
  constructor-specific lemmas instead of adding broader `auto`/`cases` calls.

## 2026-05-28: `RESIDUE` injection invariant

- `injval r c v` maps a value for `der c r` back to a value for `r`; therefore
  the expression and the value differ by exactly the consumed character `c`.
- For `RESIDUE cs rep`, a valid derivative value must be `Residue ds rep` where
  `cs = c # ds`. Injection must reject any mismatched tail or representation.
- This also affects `HALF` and the residue-tail branch of `BACKREF4`; they must
  validate the residue value before reconstructing the original value.

## 2026-05-28: Status of `rep`

- `rep` is currently intended as reconstruction metadata for the original replay
  string, while `cs` is the remaining residue to consume.
- The current language semantics does not use `rep` directly, so the field is
  suspicious unless maintained by explicit proof invariants.
- Short-term policy: keep `rep` only with equality checks during residue
  injection. Deleting it is a separate migration across `RegLangs`, `PosixSpec`,
  `Lexer`, `Blexer`, and the proof scripts.

## 2026-05-28: Current `injval_inj` proof boundary

- `RESIDUE`, `HALF`, BACKREF4 prefix-only, and BACKREF4 prefix/capture
  injectivity have been split into named helper lemmas.
- The remaining direct proof case is BACKREF4 with both `nullable r1` and
  `nullable r2`. Continue by splitting `nullable r3`, then prove tail3,
  residue-tail, and tail4 branch disjointness as small lemmas.
- Do not replace this with a broad `auto` over all value splits; previous runs
  reached 90-200 seconds on that line.

## 2026-05-28: BACKREF4 value-shape guards

- `injval` now rejects malformed BACKREF4 branch values instead of silently
  ignoring stale metadata.
- Prefix branches require the derivative value to carry the same `cs`.
- Capture branches require the derivative value to carry `c # cs`.
- Tail3 branches require the intermediate residue value to be exactly
  `Residue (rev cs) (rev cs)`.
- Tail-residue branches use `inj_residue (rev cs) (rev cs) c res`; the checked
  invariant is `rev cs = c # ds`, hence `cs = rev ds @ [c]`.
- Tail4 is accepted only when `rev cs = []`.
