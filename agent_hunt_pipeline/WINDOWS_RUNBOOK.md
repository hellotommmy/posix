# Windows Runbook For Idle Re-Prompting

This machine currently has:

- Python 3.12 available.
- WSL2 Ubuntu available.
- `tmux 3.6` available inside Ubuntu.
- no `tmux` on Windows PATH.

Therefore three levels are available.

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

## One-Time WSL Git Setup

When using the Windows worktree through `/mnt/c/...`, configure this repo so
WSL Git agrees with Windows Git about CRLF line endings:

```bash
cd /mnt/c/Users/Chengsong/Documents/AIPV2026Notes/posix
git config core.autocrlf true
git status --short --branch
```

Expected:

```text
## codex/backref-values...origin/codex/backref-values
```

Without this local config, WSL Git may show many false modifications that are
only CRLF/LF differences.

## Level 3: True tmux-Style Injection

To reproduce the paper-style loop, use WSL Ubuntu and tmux:

```powershell
wsl -d Ubuntu
```

Inside Ubuntu:

```bash
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

## Tested tmux Loop

The injection loop was tested on 2026-05-25 with a dummy tmux session:

```bash
cd /mnt/c/Users/Chengsong/Documents/AIPV2026Notes/posix
tmux kill-session -t backref-loop-test 2>/dev/null || true
tmux new-session -d -s backref-loop-test bash
sleep 1
BACKREF_TMUX_LOG_DIR=agent_hunt_pipeline/logs/tmux-test \
  timeout 8s bash agent_hunt_pipeline/scripts/backref_idle_watch.sh backref-loop-test:0.0 2
tmux capture-pane -t backref-loop-test:0.0 -p -S -80
tmux kill-session -t backref-loop-test
```

Expected capture includes the resume prompt from
`agent_hunt_pipeline/scripts/backref_resume_prompt.txt`. In the dummy bash
session it appears as `Command 'Read' not found`, which is fine: the point of
the test is confirming that tmux injection happened.

Use `BACKREF_TMUX_LOG_DIR=agent_hunt_pipeline/logs/...` for tests so captures
stay in an ignored log directory.

## Tested Recurring Paper Prompt

The paper-style repeated prompt loop is covered by:

```bash
cd /mnt/c/Users/Chengsong/Documents/AIPV2026Notes/posix
bash agent_hunt_pipeline/scripts/test_tmux_recurring_prompt.sh
```

This starts a fake tmux agent, points `backref_idle_watch.sh` at the original
recurring prompt from the 130k Lines Formal Topology paper, waits for repeated
idle cycles, and asserts that the exact same prompt was injected at least twice.

Latest observed result on 2026-05-25:

```text
PASS: recurring tmux prompt injected 5 times
Prompt: Read the file CLAUDE.md . Treat it as authoritative work instructions. Follow those instructions exactly for all subsequent actions and responses. That means work as long as possible (as specified) without stopping.
```

The watcher strips trailing whitespace before sending, so agents do not receive
an accidental extra space from a prompt file's final newline.

## Important Limit

The cross-platform script can detect idle state and produce the next prompt.
It cannot type into Cursor or Codex Desktop by itself. Actual injection needs a
terminal target such as tmux, or a separate IDE automation bridge.
