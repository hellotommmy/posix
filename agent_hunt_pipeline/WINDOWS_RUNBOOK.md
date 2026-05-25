# Windows Runbook: Dual-Agent Overnight Loop

This is the foolproof guide for running Opus (Cursor) and GPT-5.5 (Codex CLI)
concurrently on the POSIX backreference pilot, replicating the Agent Hunt /
130k Lines paper automation.

## How The Paper Did It

From the 130k Lines paper (arxiv:2604.07455):

> Both agents ran in an automated tmux-based loop: a script monitors the
> session and re-issues the prompt ("Read CLAUDE.md and follow instructions")
> whenever the agent finishes or stalls.

> Of 764 non-system user messages, 635 (83.1%) were automatically issued
> prompts "Read CLAUDE.md".

The key mechanism: **idle detection + automatic re-prompting**.

## One-Click Start

From the `posix-opus` repository root:

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/start_overnight.ps1
```

This does everything: runs guards, syncs git, starts GPT-5.5 in WSL tmux
with idle watching, and starts the Opus idle detector.

### What It Starts

| Agent | Where | Automation | Prompt File |
| --- | --- | --- | --- |
| GPT-5.5 | WSL tmux session `gpt55-backref` | Fully automatic (idle watch re-prompts) | `gpt55_resume_prompt.txt` |
| Opus | Cursor IDE (manual initial prompt) | Semi-automatic (idle detector prints reminder) | `opus_resume_prompt.txt` |

### Why Opus Is Semi-Automatic

Cursor is a GUI IDE. Unlike Claude Code or Codex CLI, it cannot receive
tmux `send-keys` injections. The workaround:

1. The script starts an idle detector that prints the resume prompt when
   the repo state is unchanged (meaning the agent has stopped working).
2. You paste the initial prompt into Cursor, then go to sleep.
3. When you wake up, check if Opus stopped and paste the prompt again.
4. GPT-5.5 in tmux runs fully autonomously all night.

## Manual Setup (If One-Click Fails)

### Step A: Start GPT-5.5 in WSL tmux

```powershell
wsl -d Ubuntu
```

Inside Ubuntu:

```bash
cd /mnt/c/Users/Chengsong/Documents/AIPV2026Notes/posix-opus
git config core.autocrlf true
tmux new-session -d -s gpt55-backref -x 160 -y 50
tmux send-keys -t gpt55-backref 'cd /mnt/c/Users/Chengsong/Documents/AIPV2026Notes/posix-opus && codex' Enter

# Wait for agent CLI to start
sleep 10

# Start idle watcher
BACKREF_PROMPT_FILE=agent_hunt_pipeline/scripts/gpt55_resume_prompt.txt \
  nohup bash agent_hunt_pipeline/scripts/backref_idle_watch.sh \
    gpt55-backref:0.0 120 \
    > agent_hunt_pipeline/logs/gpt55_idle_watch.log 2>&1 &

echo "GPT-5.5 loop started. PID: $!"
```

### Step B: Start Opus in Cursor

1. Open Cursor on `C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus`
2. Start a new Agent chat
3. Paste this prompt:

```text
Read CLAUDE.md and agent_hunt_pipeline/projects/posix-backref/CLAUDE.md. You are Opus, a worker on shared branch codex/backref-values in the posix-opus clone. Fetch first, check branch. Your assigned task: work on binjval definition and correctness proofs (BR-005, BR-011, BR-012) in BackRefValues.thy. Study xder in BackRefLang.thy to understand derivative shapes. Define binjval case-by-case. Run Isabelle BackRefPilot build. Update PROGRESS_BACKREF.md. Commit small checked steps. Do not touch Blexer, bounds, or frozen statements. Stop only when blocked or after a useful checked checkpoint.
```

4. Let it run.

### Step C: Monitor

```powershell
# Watch GPT-5.5 tmux session
wsl -d Ubuntu -- tmux attach -t gpt55-backref

# Check GPT-5.5 idle watcher log
type agent_hunt_pipeline\logs\gpt55_idle_watch.log

# Check recent git activity from both agents
git log --oneline --all -20

# Check bounty board
type BACKREF_BOUNTIES.md
```

## Task Division

| Agent | Primary Task | Files | Bounties |
| --- | --- | --- | --- |
| Opus | binjval definition + correctness | BackRefValues.thy | BR-005, BR-011, BR-012 |
| GPT-5.5 | Bitcoded backref lexer | BackRefBlexer.thy (new) | BR-013, BR-017 |

Both agents work on the shared branch `codex/backref-values`. Conflicts are
minimized because they edit different files.

## Customization

### Change interval (default 120 seconds)

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/start_overnight.ps1 -IntervalSeconds 60
```

### Change GPT agent command (default "codex")

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/start_overnight.ps1 -GptAgent "claude"
```

### Dry run (see what would happen without starting anything)

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/start_overnight.ps1 -DryRun
```

## Stopping

```powershell
# Stop Opus idle detector: Ctrl+C in the PowerShell window

# Stop GPT-5.5 tmux session
wsl -d Ubuntu -- tmux kill-session -t gpt55-backref
```

## Previous Single-Agent Setup

The older single-agent setup (Level 1-3) is still available:

### Level 1: Cross-Platform Dry Run

```powershell
$tmp = Join-Path $env:TEMP 'backref_idle_test'
if (Test-Path $tmp) { Remove-Item -Recurse -Force $tmp }
python agent_hunt_pipeline/scripts/idle_reprompt.py --watch-cwd . --prompt-file agent_hunt_pipeline/scripts/backref_resume_prompt.txt --state-dir $tmp --once --dry-run
python agent_hunt_pipeline/scripts/idle_reprompt.py --watch-cwd . --prompt-file agent_hunt_pipeline/scripts/backref_resume_prompt.txt --state-dir $tmp --once --dry-run
```

### Level 2: Continuous Prompt Emitter

```powershell
python agent_hunt_pipeline/scripts/idle_reprompt.py --watch-cwd . --prompt-file agent_hunt_pipeline/scripts/backref_resume_prompt.txt --interval 60
```

### Level 3: True tmux Injection (WSL)

```bash
cd /mnt/c/Users/Chengsong/Documents/AIPV2026Notes/posix-opus
tmux new -s backref-agent
# ... start agent in the tmux pane ...
# In another terminal:
bash agent_hunt_pipeline/scripts/backref_idle_watch.sh backref-agent:0.0 60
```

## Tested

- Single-agent tmux loop: tested 2026-05-25, PASS (5 injections).
- Cross-platform idle detection: tested 2026-05-24, PASS.
- Dual-agent script: created 2026-05-25.
