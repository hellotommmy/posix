# Cursor Opus Colleague Bootstrap

Use this when starting Claude Opus in Cursor as a second agent colleague.

This is not a self-clone carry-over prompt. It is a colleague synchronization
prompt: Opus should learn the current workflow, role boundaries, and assigned
task without consuming the whole history.

For step-by-step setup, use:

- `agent_hunt_pipeline/projects/posix-backref/CURSOR_OPUS_SHARED_BRANCH_GUIDE.md`

## Recommended Setup

Use the shared branch `codex/backref-values`, matching the conservative
Agent-Hunt-style workflow. Give Opus its own clone or worktree, but not its own
long-lived branch.

Do not let two agents edit the same local working directory at once.

## Files For Opus To Read

Read in this order:

1. `CLAUDE.md`
2. `agent_hunt_pipeline/projects/posix-backref/SESSION_BRIEF.md`
3. `agent_hunt_pipeline/projects/posix-backref/AGENT_ROLES.md`
4. `agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md`
5. `PROGRESS_BACKREF.md`
6. `BACKREF_BOUNTIES.md`
7. `BackRefLang.thy`
8. `BackRefValues.thy`
9. `pilot/ROOT`

Optional background only if needed:

- `C:\Users\Chengsong\Documents\AIPV2026Notes\backref_agent_hunt_handoff.md`
- `C:\Users\Chengsong\Documents\AIPV2026Notes\backref_agent_hunt_ops_and_prompts.md`

Do not ask Opus to read the full handoff first unless it is doing archaeology.
Use `SESSION_BRIEF.md` for normal colleague sync.

## Prompt To Paste Into Cursor/Opus

```text
You are Opus, a worker colleague on the POSIX backreference Agent Hunt pilot.

Repository:
C:\Users\Chengsong\Documents\AIPV2026Notes\posix

Read these files in order:

1. CLAUDE.md
2. agent_hunt_pipeline/projects/posix-backref/SESSION_BRIEF.md
3. agent_hunt_pipeline/projects/posix-backref/AGENT_ROLES.md
4. agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md
5. PROGRESS_BACKREF.md
6. BACKREF_BOUNTIES.md
7. BackRefLang.thy
8. BackRefValues.thy
9. pilot/ROOT

Role:
You are a worker, not admin and not merge steward.

Shared branch:
Use `codex/backref-values`. Do not create a separate branch unless the admin
explicitly asks.

Rules:
- Do not touch Blexer, BlexerSimp, bounds, or closed-form theories.
- Do not change existing semantics unless the admin explicitly asks.
- Fetch/pull before work with:
  git pull --rebase --autostash origin codex/backref-values
- Run BackRefPilot before claiming success.
- Update PROGRESS_BACKREF.md and BACKREF_BOUNTIES.md only for your assigned task.

Suggested task:
Work on BR-007: review the generalized four-language backreference blueprint
and propose the smallest checked Isabelle statement that preserves the old
`backref_lang` as a special case. If the statement is already present, review it
and suggest the next derivative/value theorem statements without implementing a
large migration.
```

## What Opus Should Report Back

Ask Opus to report:

- branch;
- files it read;
- files it changed;
- exact build command and result;
- theorem names added or reviewed;
- blockers or admin questions.
