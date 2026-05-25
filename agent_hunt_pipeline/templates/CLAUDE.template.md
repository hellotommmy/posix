# Rules for Working on <PROJECT NAME>

These are the authoritative work instructions for coding agents in this
repository.

## Project Identity

- Project:
- Repository:
- Main remote:
- Checker:
- Current phase:

## Source Documents

Read these before substantial work:

- `<handoff file>`
- `<progress file>`
- `<bounty or task file>`

## Core Principle

First create a checked statement blueprint. Then prove obligations in small,
checked steps. Do not let agents freely change definitions or theorem
statements after the blueprint is frozen.

## Strict Prohibitions

- Do not store secrets.
- Do not weaken statements to make proofs easy.
- Do not add unchecked axioms.
- Do not revert other agents' work.
- Do not use destructive git commands.
- Do not edit outside the assigned scope.

## Allowed Edit Areas

Worker agents may edit:

- `<file or folder>`

Only admin or merge stewards may edit:

- `<frozen definitions>`
- `<rules files>`
- `<governance files>`

## Mandatory Start Sequence

1. Read this file.
2. Read progress and handoff files.
3. Run `git fetch --all --prune`.
4. Run `git status --short --branch`.
5. Inspect recent history.
6. Run the checker before proof edits.

## Build Or Check Command

```sh
<checker command>
```

## Work Strategy

- Make one small checked step at a time.
- Search before adding helpers.
- Prefer local proof style.
- Record blockers.
- Stop if a statement looks false.

## Bounty Discipline

- Open tasks live in `<bounty file>`.
- Lock only the assigned task.
- Locks expire after 24 hours.
- Completion requires a passing checker run.
- Bounties do not override correctness.

## Statement Governance

Statement changes require:

- old statement;
- proposed replacement;
- reason;
- downstream impact;
- checker status.

Ask admin before major changes.

## Git Discipline

- Choose either a shared branch or branch-per-agent model explicitly.
- Fetch before work.
- Build before commit.
- Pull or rebase before push.
- Do not force push shared branches.

## Merge Steward Rules

The steward may resolve mechanical conflicts. The steward must stop for admin
on semantic or statement conflicts.

## Progress Files

Update progress after every checked step:

- branch;
- files changed;
- checker command;
- result;
- theorem status;
- next task;
- blockers.

## Long-Running CLI Loop

Recommended setup:

```text
CLI agent + tmux + idle watcher + rules file + checker + git
```

The idle watcher only re-prompts an idle CLI. It does not replace checking,
git discipline, or review.

## Stop Conditions

Stop and report if:

- checker fails and the fix is not local;
- a statement appears false;
- semantics must change;
- a frozen statement conflicts;
- a secret appears.

## Final Report

Report branch, changed files, checked result, next task, and questions.
