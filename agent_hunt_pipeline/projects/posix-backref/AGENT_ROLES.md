# POSIX Backref Agent Roles

This file defines the working roles for the POSIX backreference Agent Hunt
pilot. It is a coordination and guard input, not a proof artifact.

## Role Assignments

| Agent | Role | Shared Branch | Write Scope | Notes |
| --- | --- | --- | --- | --- |
| Chengsong | Admin | any | any | Human project owner. Decides semantics and statement changes. |
| Codex | Admin/Worker | `codex/backref-values` | current branch scope | Current session. May edit governance while setting up pipeline. |
| MergeSteward | Steward | `codex/backref-values` | integration only | Resolves mechanical conflicts, stops on semantic conflicts. |
| Opus | Worker | `codex/backref-values` | assigned task only | Intended Cursor/Claude Opus colleague. |
| Alice | Worker | `codex/backref-values` | assigned task only | Optional future worker. |
| Bob | Worker | `codex/backref-values` | assigned task only | Optional future worker. |

## What "Admin" Means

The admin is the human authority for:

- changing semantics of `backref_lang`, `BL`, `xder`, `BPrf`, or values;
- freezing or unfreezing theorem statements;
- approving edits to old lexer or bounds files;
- clearing stale locks;
- deciding whether a false statement should be replaced.

Default admin: Chengsong.

## What "Merge Steward" Means

The merge steward is a role assigned by prompt and lock ownership. A steward may:

- fetch and inspect the shared branch;
- merge or rebase clean branches;
- resolve mechanical conflicts;
- update progress and bounty status;
- run Isabelle and guard checks.

The steward must stop for admin on:

- datatype or semantics conflicts;
- theorem statement conflicts;
- conflicts in `BackRefLang.thy`;
- any edit to `Blexer*`, bounds, or closed-form files.

## What "Worker" Means

Workers prove assigned tasks and do not alter governance or frozen semantics.

Workers may normally edit:

- `BackRefValues.thy`
- future assigned pilot theories;
- `PROGRESS_BACKREF.md`
- `BACKREF_BOUNTIES.md`, only for their own locks/status;
- project notes under their assigned task.

Workers must not edit:

- root `CLAUDE.md`;
- `agent_hunt_pipeline/projects/posix-backref/CLAUDE.md`;
- `BackRefLang.thy`, unless explicitly assigned by admin;
- old lexer/bounds/closed-form theories.

## How To Set A Role

There is no hidden IDE setting. Set a role by all of:

1. Start the agent with a prompt saying its agent name and role.
2. Put it on the shared branch `codex/backref-values`.
3. Record task ownership or lock in `BACKREF_BOUNTIES.md`.
4. Run `agent_hunt_pipeline/scripts/backref_role_guard.py --role <role>`
   before commit.

For stronger GitHub enforcement, add branch protection and CODEOWNERS review
rules. The local pilot currently uses guard scripts and project discipline.
