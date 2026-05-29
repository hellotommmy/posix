# Posix Backref Design Log

This file records semantic design changes that affect later proofs. It is meant
to be read before continuing long-running agent work.

## 2026-05-29: Structured proof-shape rule

- Do not start difficult Isabelle proofs by throwing broad `auto` at the whole
  goal. Split first by datatype constructor or inductive case, expose the case
  facts, and keep the goal shape close to the semantic proof idea.
- If a branch is still complex, make it a named helper lemma with only the
  assumptions needed for that branch. This keeps later repair local and avoids
  burying the invariant inside a giant proof state.
- Use broad automation only after the structure is understood. An early `auto`
  can rewrite, split, or simplify away information in a way that leaves a less
  recoverable goal.

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
