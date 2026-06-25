# ⭐ THIS WORKTREE'S TASK — ROUTE-1 FORMALIZATION (read ROUTE1.md FIRST)

You are in the `card/route1-formalize` worktree. **Read `ROUTE1.md` (repo root) FIRST** — it is your task:
formalize the Secretary-validated singleton-cover linear row-count into `card/Card_Route1.thy`, build
`-Session Posix_Card_Route1`, NO `sorry`, fail-stop + report. The two proof-level corrections (L1 via SAA-cover,
L2 `boundary_term_absorb` via S1) are in ROUTE1.md — follow them; do NOT use the verdicts' broken routes. The
general rules below still apply.

---

# Agent Instructions

This repository runs a controlled Agent Hunt style workflow, currently aimed
at one goal: the non-backref POSIX cubic size bound (the set-ledger gate).
The rules apply equally to Codex, Claude Code, and any other coding agent.

All agents must read, in order: `MAINLINE.md` (root), the last ~200 lines of
`PROGRESS_BACKREF.md`, and the project rules at
`agent_hunt_pipeline/projects/posix-backref/CLAUDE.md`. `DOC_INDEX.md`
catalogs everything else; look details up on demand.

Short version of the rules:

- The live target, checked facts, and dead routes are in `MAINLINE.md`.
  Route statements in older files are historical; do not act on them.
- The backref pilot chain (BackRefLang/BackRefValues/BackRefBlexer/
  BackRefGBlexer/BackRefBitcodedSummary/BackRefBoundedBlueprint) is COMPLETE
  and frozen. Any instruction to create or extend those files is stale.
- One small checked step at a time. Build after every meaningful change with
  the repo wrappers (`scripts\codex-isabelle-build-posix.ps1`; one build at a
  time — `scripts\codex-proof-workers.ps1 -Action Check` first). Update the
  tail of `PROGRESS_BACKREF.md`, commit, and PUSH EACH GREEN COMMIT IMMEDIATELY
  (`git push origin HEAD:<your-lane-branch>`, explicit refspec) — never batch or
  defer the push; an unpushed green commit is invisible to the integrator and the
  other lanes.
- A red background shell on a build is an Isabelle proof failure: read the
  first `*** Failed to finish proof` block, change ONE small named lemma, and
  never relaunch a build while the first failing goal is unchanged.
- Treat slow Isabelle commands as proof-script bugs: broad `auto`/`simp`
  should return in ~0.5 s; if a command visibly hangs, split the proof.
  Preserve proof shape before automation — case-split first, then targeted
  rules; complex branches become named helper lemmas.
- Search before creating; never duplicate existing lemmas/definitions.
  Wrapper-only packaging is not progress and not bounty-eligible.
- Never throw away useful work: no `git reset --hard`, no reverts without
  salvage, justify any file shrink in the commit message.
- No `sorry`/`oops`/axioms/statement weakening; frozen statements are
  enforced by the statement guard. Run all four guard scripts before pushing.
- Long-running proof/search/fuzz commands must be bounded; clean up stale
  `poly`/`isabelle`/`java` workers you own (`codex-proof-workers.ps1`), never
  blanket-kill unrelated sessions.
- For any NEW executable simplifier/algorithm candidate, Scala smoke comes
  before proof work (`agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1`,
  exact POSIX values mandatory). Two standing value facts: destructive
  sequence reassociation `(x.y).z -> x.(y.z)` is NOT POSIX-value-preserving,
  and `bsimpStrong` alone is a recognition gate, not a value candidate.
- Do not wait idle for another agent unless a live worker or a tracked edit
  in your target region is visible. Coordinate through the PROGRESS tail.
- Never store tokens or secrets.

Reusable pipeline files, scripts, and templates live in `agent_hunt_pipeline/`.
