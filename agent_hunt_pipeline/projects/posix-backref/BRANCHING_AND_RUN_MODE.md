# Branching And Run Mode

This file explains the shared-branch run mode for this POSIX backreference
pilot.

## What The Role Names Mean

- **Admin**: the human owner who may approve semantic or statement changes.
- **Worker**: an agent proving assigned tasks.
- **Merge steward**: an agent that resolves mechanical conflicts on the shared
  branch, but stops on semantic conflicts.

These are workflow roles. They are not special GitHub account types unless the
repo owner later adds branch protection, CODEOWNERS, or required reviews.

## Did Agent Hunt Use One Branch Or One Branch Per Agent?

The public papers do not expose the exact complete git topology. What they do
say is:

- agents used git for synchronization;
- frequent pull, commit, and push cycles were mandatory;
- locks had to be pushed immediately;
- agents were forbidden to modify others' locks, partial proofs, or sandboxes;
- guard scripts were run locally before commits.

That reads closest to a **shared integration branch / shared mainline** model,
or at least a common branch that all active agents frequently pulled and pushed.
The public text does not show a branch-per-agent PR workflow.

So this project now defaults to a shared branch, to stay closer to the public
Agent Hunt description.

## Default Mode: Shared Branch

All agents work on the same shared branch:

```text
codex/backref-values
```

Rules:

- every agent fetches/pulls before work;
- every lock/status change is committed quickly;
- agents avoid the same theorem/file section;
- guard scripts run before commit;
- conflicts are resolved immediately or handed to steward.

Why:

- closest to the described Agent Hunt rhythm;
- everyone sees locks and progress immediately;
- less PR overhead.

Risks:

- higher chance of same-file conflicts;
- one careless push can break everyone;
- harder for the user if they do not want to merge or resolve conflicts.

## Exception Mode: Quarantine Branch

A temporary separate branch may still be used only when:

- an agent is doing an experiment that may break the branch;
- a large refactor needs isolation;
- the admin explicitly asks for it.

## Recommendation For This Repo

Use `codex/backref-values` as the shared working branch for Codex, Opus, and any
other active worker.

Important: shared branch does **not** mean same local working directory. Each
agent should have its own clone or worktree, all checked out to
`codex/backref-values`. They synchronize through:

```powershell
git pull --rebase --autostash origin codex/backref-values
git push origin codex/backref-values
```

If a pull/rebase conflicts, the merge steward resolves only mechanical
conflicts. Semantic conflicts go to the admin.
