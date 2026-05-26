# Sleep Runbook: Codex + Opus Parallel Work

Use this when starting an overnight two-agent run:

- Codex in Codex Desktop on `C:\Users\Chengsong\Documents\AIPV2026Notes\posix`.
- Opus in Cursor on a separate clone, usually
  `C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus`.
- Both use shared branch `codex/backref-values`.

Do not put both agents in the same local folder.

## Before Starting

In the Codex folder:

```powershell
cd C:\Users\Chengsong\Documents\AIPV2026Notes\posix
git status --short --branch
git pull --ff-only
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin
git push
```

Expected:

- clean git status;
- local CI passes;
- branch is up to date with `origin/codex/backref-values`.

## Start Codex CLI Loop

For the unattended Codex side, start the WSL tmux launcher from the Codex
folder:

```powershell
cd C:\Users\Chengsong\Documents\AIPV2026Notes\posix
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/start_codex_tmux.ps1
```

Watch it with:

```powershell
wsl -d Ubuntu -- tmux attach -t codex-backref
```

The prompt passed to each Codex CLI `exec` iteration is:

```text
agent_hunt_pipeline/scripts/codex_cli_resume_prompt.txt
```

## Start Codex Desktop

If you are using Codex Desktop instead of the CLI loop, open a fresh Codex
Desktop conversation in `C:\Users\Chengsong\Documents\AIPV2026Notes\posix` and
paste:

```text
We are continuing the POSIX backreference Agent Hunt workflow on branch codex/backref-values.

Read CLAUDE.md first, then:
agent_hunt_pipeline/projects/posix-backref/SESSION_BRIEF.md
PROGRESS_BACKREF.md
BACKREF_BOUNTIES.md
agent_hunt_pipeline/projects/posix-backref/CLAUDE.md

Role: Codex is admin/worker. Opus may be running in Cursor in a separate clone on the same shared branch. Fetch first. Work with any remote changes, do not revert other agents, and keep commits small. Stay within the current pilot phase: value/Prf/flat and generalized backref_lang4 planning before Blexer or bounds. Run guards and Isabelle CI before claiming progress. If remote moved, pull/rebase safely. If there is a conflict or semantic question, stop and report.

Continue the next smallest useful checked step.
```

Codex Desktop does not currently receive tmux or Cursor hook injections. Use
the Codex CLI loop above for fully unattended overnight work.

## Start Cursor/Opus Folder

Create or refresh the separate clone:

```powershell
cd C:\Users\Chengsong\Documents\AIPV2026Notes
if (-not (Test-Path .\posix-opus)) {
  git clone https://github.com/hellotommmy/posix.git posix-opus
}
cd .\posix-opus
git fetch origin
git switch codex/backref-values
git pull --ff-only
git config core.autocrlf true
```

Open this folder in Cursor:

```text
C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus
```

Enable Cursor loop config:

```powershell
Copy-Item agent_hunt_pipeline/projects/posix-backref/loop-config.cursor-opus.json loop-config.json
```

The tracked hook files are:

```text
.cursor/hooks.json
.cursor/hooks/posix_loop.ps1
.cursor/hooks/posix_loop.sh
```

If Cursor asks whether to allow workspace hooks, approve the hook for this
workspace. To stop the loop, delete or rename `loop-config.json`.

## Initial Cursor/Opus Prompt

Paste into Cursor Agent:

```text
You are an Opus thinking worker colleague on the POSIX backreference Agent Hunt pilot.

Repository:
C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus

Shared branch:
codex/backref-values

Read CLAUDE.md first, then read:
agent_hunt_pipeline/projects/posix-backref/SESSION_BRIEF.md
agent_hunt_pipeline/projects/posix-backref/AGENT_ROLES.md
agent_hunt_pipeline/projects/posix-backref/BRANCHING_AND_RUN_MODE.md
agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md
PROGRESS_BACKREF.md
BACKREF_BOUNTIES.md
BackRefLang.thy
BackRefValues.thy
pilot/ROOT

You are a worker, not admin. Stay on the shared branch. Start with git status --short --branch and git diff; if clean, fetch and fast-forward to origin/codex/backref-values before edits. Work on one small worker-scope task at a time, using PROGRESS_BACKREF.md as the first source of truth and BACKREF_BOUNTIES.md for bounty status. Do not touch production Blexer/BlexerSimp, bounds, closed-form theories, frozen statements, or governance files. Pilot BackRefValues.thy `blexer` work is allowed only when it is the current checked bounty task. Run the worker guard and BackRefPilot build before commit. Commit small, pull --rebase --autostash, rerun the guard, and push. Stop for merge conflicts or semantic uncertainty.
```

After Opus stops once, Cursor Hooks should call `.cursor/hooks/posix_loop.ps1`,
run the validation command in `loop-config.json`, and re-prompt automatically
until the hook limit is reached.

## Protect Dirty Cursor Work

Cursor/Opus may disconnect before it reaches a checked commit. To avoid losing
half-finished proof search, run the dirty snapshot watcher from the Codex clone.
It does not stage, commit, stash, reset, pull, push, or edit the Opus worktree;
it only saves local ignored snapshots of dirty diffs and changed file copies:

```powershell
cd C:\Users\Chengsong\Documents\AIPV2026Notes\posix
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/dirty_worktree_snapshot.ps1 -Background -RepoPath C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus -PollSeconds 60 -MinIntervalSeconds 120
```

Snapshots are written under:

```text
C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus\agent_hunt_pipeline\run\dirty_snapshots
```

Inspect the latest snapshot with:

```powershell
Get-ChildItem C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus\agent_hunt_pipeline\run\dirty_snapshots -Directory | Sort-Object LastWriteTime -Descending | Select-Object -First 1
Get-Content C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus\agent_hunt_pipeline\run\dirty_snapshots\snapshot_watch.log -Tail 40
```

## Opus Watchdog Warning

Current recommended Opus route: use Cursor IDE manually in
`C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus` with Opus 4.6 Max.
Do not use headless `cursor-agent` fallback for Opus unless you explicitly want
that separate model-routing and billing path.

The watchdog no longer starts any Opus model by default. If run without
`-EnableHeadlessStart`, it only logs that a restart would be skipped:

```powershell
cd C:\Users\Chengsong\Documents\AIPV2026Notes\posix
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/opus_cursor_agent_watchdog.ps1 -Background
```

If you deliberately choose the headless path, pass both `-EnableHeadlessStart`
and an explicit model. Avoid 4.7 here unless you are willing to consume Cursor
Max Mode rapidly:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/opus_cursor_agent_watchdog.ps1 -Background -ResetState -MaxRestarts 50 -EnableHeadlessStart -Model auto
```

Watch it with:

```powershell
Get-Content C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus\agent_hunt_pipeline\logs\opus_watchdog.log -Tail 80
Get-ChildItem C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus\agent_hunt_pipeline\logs\opus_cursor_agent_*.log | Sort-Object LastWriteTime -Descending | Select-Object -First 1
```

Stop it with:

```powershell
Get-CimInstance Win32_Process |
  Where-Object { $_.CommandLine -match 'opus_cursor_agent_watchdog.ps1' } |
  ForEach-Object { Stop-Process -Id $_.ProcessId }
```

## Confirm The Loop Is Armed

In Cursor's terminal:

```powershell
Test-Path loop-config.json
Get-Content .cursor/hooks.json
powershell -NoProfile -ExecutionPolicy Bypass -File .cursor/hooks/posix_loop.ps1
```

Expected output is JSON with:

```json
{"decision":"continue", ...}
```

## Morning Recovery

In each clone:

```powershell
git status --short --branch
git log --oneline --decorate -n 10
git pull --rebase --autostash origin codex/backref-values
```

Then check GitHub Actions for the latest `codex/backref-values` run. Trust only
commits whose GitHub Isabelle CI passes.
