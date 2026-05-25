# Windows Runbook For Idle Re-Prompting

This machine currently has:

- Python 3.12 available.
- `wsl.exe` available, but no Linux distribution installed.
- no `tmux` on Windows PATH.

Therefore two levels are available.

## Level 1: Cross-Platform Dry Run, Works Now

This checks whether the repo state is unchanged across two runs. If unchanged,
it emits the next prompt. It does not inject text into a terminal.

From:

```powershell
C:\Users\Chengsong\Documents\AIPV2026Notes\posix
```

Run:

```powershell
$tmp = Join-Path $env:TEMP 'backref_idle_test'
if (Test-Path $tmp) { Remove-Item -Recurse -Force $tmp }
python agent_hunt_pipeline/scripts/idle_reprompt.py --watch-cwd . --prompt-file agent_hunt_pipeline/scripts/backref_resume_prompt.txt --state-dir $tmp --once --dry-run
python agent_hunt_pipeline/scripts/idle_reprompt.py --watch-cwd . --prompt-file agent_hunt_pipeline/scripts/backref_resume_prompt.txt --state-dir $tmp --once --dry-run
```

Expected:

- first run: `baseline/changed: no prompt ...`
- second run: `DRY-RUN would reprompt ...`

This was tested successfully on 2026-05-24.

## Level 2: Continuous Prompt Emitter, Works Now

This prints a prompt whenever the watched repo state is unchanged. Another
program or a human can paste it into the agent.

```powershell
python agent_hunt_pipeline/scripts/idle_reprompt.py --watch-cwd . --prompt-file agent_hunt_pipeline/scripts/backref_resume_prompt.txt --interval 60
```

Stop with `Ctrl+C`.

## Level 3: True tmux-Style Injection

To reproduce the paper-style loop, install WSL Ubuntu and tmux:

```powershell
wsl --install -d Ubuntu
```

Restart if Windows asks. Then inside Ubuntu:

```bash
sudo apt update
sudo apt install -y tmux git python3
cd /mnt/c/Users/Chengsong/Documents/AIPV2026Notes/posix
tmux new -s backref-agent
```

In the tmux pane, start the CLI agent manually, for example Codex or Claude
Code if installed there.

In another WSL terminal:

```bash
cd /mnt/c/Users/Chengsong/Documents/AIPV2026Notes/posix
bash agent_hunt_pipeline/scripts/backref_idle_watch.sh backref-agent:0.0 60
```

This watches the tmux pane. If it is unchanged across checks, it sends the
resume prompt and Enter.

## Important Limit

The cross-platform script can detect idle state and produce the next prompt.
It cannot type into Cursor or Codex Desktop by itself. Actual injection needs a
terminal target such as tmux, or a separate IDE automation bridge.

