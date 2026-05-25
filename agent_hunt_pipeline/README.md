# Reusable Agent Hunt Pipeline

This directory contains reusable scaffolding for running long-lived coding
agents in the style described by the 130k Lines Formal Topology and Agent Hunt
papers.

The core pattern is:

```text
CLI coding agent
+ terminal multiplexer
+ idle watcher
+ project rules file
+ proof checker
+ git
+ progress and bounty files
```

## Layout

- `scripts/`: reusable watcher, idle re-prompt, bounty, role, check, and tmux
  recurrence test scripts.
- `templates/`: generic files to copy into a new project.
- `references/`: notes about public Agent Hunt and 130k source material.
- `projects/`: project-specific profiles. The current profile is
  `projects/posix-backref/CLAUDE.md`.
- `WINDOWS_RUNBOOK.md`: how to test idle re-prompting on this machine.

## How To Reuse

For another project:

1. Copy `templates/CLAUDE.template.md` into the new project's profile folder.
2. Fill in project paths, checker commands, allowed edit areas, and stop rules.
3. Put a short root `CLAUDE.md` in the target repo that points at the profile.
4. Copy or adapt `scripts/backref_idle_watch.sh` or `scripts/idle_reprompt.py`.
5. Add project progress and bounty files.
6. Add a local CI wrapper and a remote workflow that run the proof checker.
7. Make every agent read the profile, fetch, build, and update progress.

## Tmux Recurrence Test

After WSL Ubuntu and tmux are installed, run:

```bash
cd /mnt/c/Users/Chengsong/Documents/AIPV2026Notes/posix
bash agent_hunt_pipeline/scripts/test_tmux_recurring_prompt.sh
```

This verifies the 130k-paper pattern: the same recurring instruction is sent
again whenever the tmux pane becomes idle.

## Notes

This directory now contains both the agent-running scaffolding and the local CI
wrapper used by this project. It is still not a replacement for human review:
the trusted proof event is the Isabelle build, while generated certificates are
audit receipts for passed checks.

On this Windows machine, `tmux` was not found on PATH during setup. The
cross-platform `scripts/idle_reprompt.py` cwd/dry-run mode was tested and can
detect an unchanged repo state, then emit the next prompt. Actual CLI injection
still requires a terminal multiplexer such as tmux, GNU Screen, WSL tmux, or an
IDE/terminal automation bridge that can receive the emitted prompt.
