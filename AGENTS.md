# Agent Instructions

This repository is running a controlled Agent Hunt style pilot for POSIX
regular expressions with backreference-like constructors.

All coding agents must read root `CLAUDE.md` and then the project profile at
`agent_hunt_pipeline/projects/posix-backref/CLAUDE.md` before editing. The
name is kept for compatibility with Claude Code and with the workflow described
in the 130k Lines Formal Topology paper, but the rules apply equally to Codex,
Claude Code, and any other coding agent working in this repository.

Short version:

- Work only on the backreference pilot unless explicitly instructed.
- Do not touch `Blexer*`, bounds, or closed-form theories before the
  value/Prf/flat pilot is checked.
- Fetch before work, build after work, and record progress in
  `PROGRESS_BACKREF.md`.
- Treat slow Isabelle commands as proof-script bugs. Human rule of thumb:
  `auto`/`simp`/broad proof search should normally return within about 0.5s;
  if it visibly hangs, abandon that tactic and split the proof. A small pilot
  check should usually finish in 5-10 seconds, and a 200 second command is never
  normal.
- Preserve proof shape before using automation: split by datatype constructor
  or inductive case first, expose the relevant assumptions, and move complex
  branches into named helper lemmas. Do not fire broad `auto` at an undigested
  goal; it can rewrite or split the state into a harder, less recoverable form.
- Cubic-bound candidates must pass Scala smoke tests before proof work. Broad
  grids and bounded regex enumeration live in
  `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`, not as large Isabelle
  `eval` lemmas. The gate compares exact decoded POSIX values against the
  baseline lexer, then checks shared-suffix pruning and the thesis Chapter 7
  three-layer-star family. If a candidate is known to miss a required pruning
  rule or fails exact POSIX value smoke, retire or re-scope it instead of
  proving around the defect. Before proof/bounty work, run the optional
  deterministic random smoke, e.g. `scala_cubic_smoke.ps1 -RandomCases 2000`;
  default CI keeps this off so the branch can stay green while diagnostics are
  recorded.
- The cubic route must reconcile Antimirov-style row/set deduplication with
  POSIX value preservation. Naively distributing `(a+b)c` to `ac+bc` can change
  value shape (`Seq (Left x) y` vs `Left (Seq x y)`), so use pruning,
  delayed/indexed linear forms, reconstruction, or a generalized POSIX-value
  equivalence before claiming a proof route.
- Do not treat destructive sequence reassociation as a POSIX-value-preserving
  output rewrite. Scala smoke localized a `bsimpCubic` value bug to
  `(x.y).z -> x.(y.z)`: full reassociation controls the Chapter 7 size trace
  but fails deterministic random value smoke, while `no-reassoc` preserves
  values but grows too much. Reassociation may be used only as a comparison
  key, proof device, or generalized-value transfer route until a checked
  bitcode/value reconstruction theorem exists.
- Use DAG/shared-row diagnostics to guide the next cubic design, but do not
  confuse them with a completed tree-size theorem. Current smoke shows that
  value-safe `no-reassoc` has large tree size but much smaller exact DAG and
  shape-DAG size on the Chapter 7 family. This supports a hash-consed
  row-universe, delayed linear-form, or reconstruction-based route; it is not
  a bounty claim until the representation and POSIX-value transfer are checked.
- The optional Scala `-SharedNoReassoc` switch is retained as the shared-state
  diagnostic entry point, but the shared store now follows the current
  `-SeqMode`. It interns value-safe states and checks that expanding the final
  shared root decodes to the baseline POSIX value. Future work should move
  derivative/simplification onto node IDs or delayed rows directly, then prove
  the expansion/reconstruction theorem in Isabelle.
- The `expanded-keyed-no-reassoc` diagnostic implements virtual expanded
  pruning keys: an accumulator that has seen `(a+b).c` may also index `a.c` and
  `b.c` for coverage, while still emitting `no-reassoc` output syntax. This is
  promising smoke evidence for the Antimirov row idea, but any stronger pruning
  key must pass exact POSIX value smoke before proof or bounty work starts.
- Distinguish tree-size evidence from shared-representation evidence. On the
  thesis Figure 7.6 `k=5` family, `bsimpStrong` gives the expected
  hundreds-scale ordinary tree behavior; `expanded-keyed-no-reassoc` still has
  larger ordinary trees while keeping exact DAG/shape-DAG compact. Do not claim
  that a DAG plateau reproduces the thesis tree plot unless the theorem target
  is explicitly a shared-row/DAG representation with reconstruction.
- Before treating thesis-style `bsimpStrong` as a POSIX candidate, run
  `scala_cubic_smoke.ps1 -CheckStrong`. It currently fails on
  `STAR (STAR (CH a))` with input `a`, because nested-star value structure is
  collapsed. That failure is a design fact: a tree-level strong route needs a
  repaired value-safe simplifier or a checked generalized-value transfer.
- `bsimpStrongSafe` is only a CE-driven diagnostic baseline. It disables the
  strong output rewrites that are known to destroy POSIX values, and it passes
  deeper random smoke, but its tree size no longer matches the thesis plateau.
  Use it to identify value hazards. The target route is a small strong regex
  plus value transformers/reconstruction, not merely a weaker safe output
  simplifier.
- `scala_cubic_smoke.ps1 -TraceStrongRecon` checks the first local
  reconstruction sketches for the CE-driven strong route. Passing this sketch
  is only route evidence; it does not replace a compositional certificate across
  derivative steps. The current version also runs annotated-value local
  certificate laws; extend those laws before trusting any new strong rewrite.
- `scala_cubic_smoke.ps1 -CheckStrongCoreCert` checks the current compositional
  certificate prototype for the sequence/star core of `bsimpStrong` on
  derivative-generated expressions. It now includes alternation
  flatten/distinct certificates, but not shared-suffix row pruning.
- `scala_cubic_smoke.ps1 -TraceStrongCore` compares the certified core size
  against thesis `bsimpStrong`; use it to measure the remaining pruning gap.
- Never store tokens or secrets.

Reusable pipeline files, scripts, and templates live in `agent_hunt_pipeline/`.
