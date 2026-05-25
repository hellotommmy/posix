<#
.SYNOPSIS
  One-click overnight dual-agent setup for the POSIX backreference pilot.

.DESCRIPTION
  Replicates the Agent Hunt / 130k Lines paper automation:
  1. For GPT-5.5 (Codex CLI in WSL tmux): starts a tmux session with idle
     watcher that re-prompts automatically when the agent stalls.
  2. For Opus (Cursor): starts the cross-platform idle detector that prints
     the resume prompt when the repo state is unchanged.
  3. Prints clear instructions for the manual Cursor step.

.NOTES
  Run from the posix-opus repository root:
    powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/start_overnight.ps1

  Prerequisites:
  - WSL2 Ubuntu with tmux installed
  - Codex CLI (or similar) available in WSL
  - Python 3 on Windows PATH
  - Cursor open on posix-opus folder
#>

param(
    [int]$IntervalSeconds = 120,
    [string]$GptAgent = "codex",
    [switch]$DryRun
)

$ErrorActionPreference = "Stop"
$repoRoot = Split-Path -Parent (Split-Path -Parent (Split-Path -Parent $PSCommandPath))
Push-Location $repoRoot

Write-Host "========================================" -ForegroundColor Cyan
Write-Host " POSIX Backref Overnight Agent Launcher " -ForegroundColor Cyan
Write-Host "========================================" -ForegroundColor Cyan
Write-Host ""

# --- Step 0: Verify prerequisites ---
Write-Host "[0] Checking prerequisites..." -ForegroundColor Yellow

$pythonOk = Get-Command python -ErrorAction SilentlyContinue
if (-not $pythonOk) {
    Write-Host "ERROR: python not found on PATH" -ForegroundColor Red
    exit 1
}

$wslOk = Get-Command wsl -ErrorAction SilentlyContinue
if (-not $wslOk) {
    Write-Host "WARNING: WSL not found. GPT-5.5 tmux loop will be skipped." -ForegroundColor Yellow
    Write-Host "         Only the Cursor/Opus idle detector will start." -ForegroundColor Yellow
}

Write-Host "  Python: OK" -ForegroundColor Green
Write-Host "  WSL:    $(if ($wslOk) { 'OK' } else { 'MISSING' })" -ForegroundColor $(if ($wslOk) { "Green" } else { "Yellow" })
Write-Host ""

# --- Step 1: Run guards before starting ---
Write-Host "[1] Running pre-flight guards..." -ForegroundColor Yellow

python agent_hunt_pipeline/scripts/backref_bounty_guard.py
if ($LASTEXITCODE -ne 0) { Write-Host "Bounty guard failed!" -ForegroundColor Red; exit 1 }

python agent_hunt_pipeline/scripts/backref_no_cheat_guard.py
if ($LASTEXITCODE -ne 0) { Write-Host "No-cheat guard failed!" -ForegroundColor Red; exit 1 }

python agent_hunt_pipeline/scripts/backref_statement_guard.py
if ($LASTEXITCODE -ne 0) { Write-Host "Statement guard failed!" -ForegroundColor Red; exit 1 }

Write-Host "  All guards pass." -ForegroundColor Green
Write-Host ""

# --- Step 2: Git sync ---
Write-Host "[2] Syncing shared branch..." -ForegroundColor Yellow
git fetch --all --prune
git pull --ff-only
git status --short --branch
Write-Host ""

# --- Step 3: Start GPT-5.5 in WSL tmux (if available) ---
if ($wslOk) {
    Write-Host "[3] Starting GPT-5.5 tmux loop in WSL..." -ForegroundColor Yellow

    $wslRepoPath = "/mnt/c/Users/Chengsong/Documents/AIPV2026Notes/posix-opus"
    $tmuxSession = "gpt55-backref"
    $promptFile = "agent_hunt_pipeline/scripts/gpt55_resume_prompt.txt"

    $wslScript = @"
cd $wslRepoPath
git config core.autocrlf true 2>/dev/null
tmux kill-session -t $tmuxSession 2>/dev/null || true
tmux new-session -d -s $tmuxSession -x 160 -y 50
sleep 1
tmux send-keys -t $tmuxSession 'cd $wslRepoPath' Enter
sleep 1
tmux send-keys -t $tmuxSession '$GptAgent' Enter
echo 'Waiting 10s for agent CLI startup...'
sleep 10
echo 'Starting idle watcher (interval: ${IntervalSeconds}s)...'
BACKREF_PROMPT_FILE=$wslRepoPath/$promptFile \
  nohup bash $wslRepoPath/agent_hunt_pipeline/scripts/backref_idle_watch.sh \
    ${tmuxSession}:0.0 $IntervalSeconds \
    > $wslRepoPath/agent_hunt_pipeline/logs/gpt55_idle_watch.log 2>&1 &
echo "Idle watcher PID: \$!"
echo 'GPT-5.5 loop started. Monitor with: wsl -d Ubuntu -- tmux attach -t $tmuxSession'
"@

    if ($DryRun) {
        Write-Host "  DRY-RUN: Would execute in WSL:" -ForegroundColor Cyan
        Write-Host $wslScript
    } else {
        New-Item -ItemType Directory -Path "agent_hunt_pipeline/logs" -Force | Out-Null
        wsl -d Ubuntu -- bash -c $wslScript
    }
    Write-Host ""
} else {
    Write-Host "[3] SKIP: WSL not available, GPT-5.5 tmux loop not started." -ForegroundColor Yellow
    Write-Host ""
}

# --- Step 4: Start Opus idle detector ---
Write-Host "[4] Starting Opus/Cursor idle detector..." -ForegroundColor Yellow
Write-Host "  This watches the repo and prints the resume prompt when idle." -ForegroundColor Gray
Write-Host "  In the 130k paper, 83% of prompts were automatic re-prompts." -ForegroundColor Gray
Write-Host ""

$opusPrompt = "agent_hunt_pipeline/scripts/opus_resume_prompt.txt"
$stateDir = ".agent-hunt/idle-opus"

if ($DryRun) {
    Write-Host "  DRY-RUN: Would run idle detector with interval ${IntervalSeconds}s" -ForegroundColor Cyan
} else {
    Write-Host "  Starting in background... (Ctrl+C to stop)" -ForegroundColor Green
    Write-Host ""
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host " MANUAL STEP FOR CURSOR/OPUS           " -ForegroundColor Cyan
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host ""
    Write-Host "1. Open Cursor on: C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus" -ForegroundColor White
    Write-Host "2. Start a new Agent chat" -ForegroundColor White
    Write-Host "3. Paste this initial prompt:" -ForegroundColor White
    Write-Host ""
    $initialPrompt = Get-Content $opusPrompt -Raw
    Write-Host "  $initialPrompt" -ForegroundColor Green
    Write-Host ""
    Write-Host "4. Let Opus work. When it stops, paste the prompt again." -ForegroundColor White
    Write-Host "   (The idle detector below will remind you when re-prompting is needed.)" -ForegroundColor Gray
    Write-Host ""
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host " MONITORING                            " -ForegroundColor Cyan
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host ""
    Write-Host "  GPT-5.5 tmux: wsl -d Ubuntu -- tmux attach -t gpt55-backref" -ForegroundColor Gray
    Write-Host "  GPT-5.5 log:  type agent_hunt_pipeline\logs\gpt55_idle_watch.log" -ForegroundColor Gray
    Write-Host "  Git status:   git log --oneline -5" -ForegroundColor Gray
    Write-Host ""
    Write-Host "Starting Opus idle detector (prints prompt when repo unchanged)..." -ForegroundColor Yellow
    Write-Host ""

    python agent_hunt_pipeline/scripts/idle_reprompt.py `
        --watch-cwd . `
        --prompt-file $opusPrompt `
        --state-dir $stateDir `
        --interval $IntervalSeconds
}

Pop-Location
