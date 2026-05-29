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
- Never store tokens or secrets.

Reusable pipeline files, scripts, and templates live in `agent_hunt_pipeline/`.
