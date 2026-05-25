# Cursor Opus Shared-Branch Guide

This is the foolproof runbook for starting Claude Opus in Cursor as a second
agent on the same shared branch as Codex.

Shared branch:

```text
codex/backref-values
```

Important: same branch does not mean same local folder. Use a separate clone or
worktree for Cursor/Opus so two agents do not edit the same working directory
at the same time.

## Step 0: Make Sure The Shared Branch Exists Remotely

From the Codex working copy:

```powershell
cd C:\Users\Chengsong\Documents\AIPV2026Notes\posix
git status --short --branch
git branch --show-current
```

Expected branch:

```text
codex/backref-values
```

Before Opus can clone it from GitHub, the branch and current checked work must
be committed and pushed:

```powershell
git add .
git commit -m "Add backreference values and agent hunt pipeline"
git push -u origin codex/backref-values
```

Only do this after the local gate passes.

## Step 1: Clone For Cursor/Opus

Use a separate folder, for example:

```powershell
cd C:\Users\Chengsong\Documents\AIPV2026Notes
git clone https://github.com/hellotommmy/posix.git posix-opus
cd posix-opus
git fetch origin
git switch codex/backref-values
```

If `git switch codex/backref-values` fails, the branch has not been pushed yet.

Open this folder in Cursor:

```text
C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus
```

## Step 2: Give Opus This Prompt

Paste this into Cursor/Opus:

```text
You are Opus, a worker colleague on the POSIX backreference Agent Hunt pilot.

Repository:
C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus

Shared branch:
codex/backref-values

Read these files in order:

1. CLAUDE.md
2. agent_hunt_pipeline/projects/posix-backref/SESSION_BRIEF.md
3. agent_hunt_pipeline/projects/posix-backref/AGENT_ROLES.md
4. agent_hunt_pipeline/projects/posix-backref/BRANCHING_AND_RUN_MODE.md
5. agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md
6. PROGRESS_BACKREF.md
7. BACKREF_BOUNTIES.md
8. BackRefLang.thy
9. BackRefValues.thy
10. pilot/ROOT

Role:
You are a worker, not admin and not merge steward.

Before editing:
Run:
git pull --rebase --autostash origin codex/backref-values
git status --short --branch

Rules:
- Do not create a separate branch.
- Do not touch Blexer, BlexerSimp, bounds, or closed-form theories.
- Do not change semantics or theorem statements unless the admin explicitly asks.
- Claim or lock exactly one task in BACKREF_BOUNTIES.md before proof work.
- Run the local CI gate before claiming success:
  powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/backref_check.ps1 -SkipFetch -Role worker
- Before pushing:
  git pull --rebase --autostash origin codex/backref-values
  powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/backref_check.ps1 -SkipFetch -Role worker
  git push origin codex/backref-values

Suggested first task:
Review BR-008: draft the derivative/value story for generalized backref_lang4.
If you implement anything, keep it small and checked.

Report back:
- branch;
- files changed;
- task locked or completed;
- exact local CI gate result;
- push result;
- any admin questions.
```

## Step 3: Confirm Opus Can Commit And Pass The Local Gate

In Cursor's terminal:

```powershell
git status --short --branch
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/backref_check.ps1 -SkipFetch -Role worker
```

Expected:

- `backref_bounty_guard.py` passes;
- `backref_role_guard.py --role worker` passes for worker-scope edits;
- Isabelle `BackRefPilot` passes.

Then commit:

```powershell
git add <files changed by Opus>
git commit -m "Work on <task id>"
```

## Step 4: Shared-Branch Sync / Auto-Integration

There is no PR auto-merge in this shared-branch mode. The shared-branch
equivalent is:

```powershell
git pull --rebase --autostash origin codex/backref-values
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/backref_check.ps1 -SkipFetch -Role worker
git push origin codex/backref-values
```

What this handles automatically:

- remote branch moved forward;
- Opus has local commits;
- changes do not conflict textually;
- local uncommitted edits can be temporarily stashed.

What it cannot safely handle:

- two agents changed the same proof lines;
- semantic definitions changed;
- theorem statements changed;
- `BackRefLang.thy` conflicts;
- old lexer/bounds files changed.

If that happens, stop and assign the MergeSteward role:

```text
You are MergeSteward on shared branch codex/backref-values.
Resolve only mechanical conflicts. Stop for admin on semantic or statement conflicts.
Run the local CI gate before pushing.
```

## Step 5: Remote CI Status

As of this setup, this repository has no `.github/workflows` CI file. So
"CI pass" currently means the local CI gate:

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/backref_check.ps1 -SkipFetch -Role worker
```

Adding true GitHub Actions CI for Isabelle is a separate task.

