<#
.SYNOPSIS
  Start the Codex CLI side of the POSIX backreference overnight loop.

.DESCRIPTION
  This is the robust launcher for the current Codex clone. It runs pre-flight
  git/guard checks, starts Codex CLI in a WSL tmux session, accepts the initial
  workspace trust prompt, injects the project resume prompt, and starts the
  tmux idle watcher so the same prompt is re-issued whenever the pane stalls.
  If Codex asks for workspace trust, the launcher accepts it; otherwise it
  leaves the prompt line untouched before injecting the project prompt.

  The default agent command deliberately uses npx instead of the WindowsApps
  codex.exe path, because WSL can see that path but cannot execute it.

.EXAMPLE
  powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/start_codex_tmux.ps1
#>

param(
    [string]$Branch = "codex/backref-values",
    [string]$WslDistro = "Ubuntu",
    [string]$Session = "codex-backref",
    [int]$IntervalSeconds = 120,
    [int]$StartupDelaySeconds = 10,
    [string]$AgentCommand = "npx -y @openai/codex@0.133.0 -s danger-full-access -a never --no-alt-screen",
    [string]$PromptFile = "agent_hunt_pipeline/scripts/codex_cli_resume_prompt.txt",
    [switch]$SkipGitSync,
    [switch]$SkipPilotBuild,
    [switch]$KillExisting,
    [switch]$DryRun
)

$ErrorActionPreference = "Stop"

function Quote-Bash([string]$Value) {
    $escaped = $Value.Replace("'", "'\''")
    return "'" + $escaped + "'"
}

$repoRoot = Split-Path -Parent (Split-Path -Parent (Split-Path -Parent $PSCommandPath))
Push-Location $repoRoot

try {
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host " POSIX Backref Codex CLI tmux Launcher " -ForegroundColor Cyan
    Write-Host "========================================" -ForegroundColor Cyan
    Write-Host ""

    if (-not (Test-Path $PromptFile)) {
        throw "Prompt file not found: $PromptFile"
    }

    $currentBranch = (git branch --show-current).Trim()
    if ($currentBranch -ne $Branch) {
        throw "Wrong branch: $currentBranch. Expected: $Branch"
    }

    if (-not $SkipGitSync) {
        Write-Host "[1] Syncing shared branch..." -ForegroundColor Yellow
        git fetch origin $Branch
        git pull --rebase --autostash origin $Branch
        git status --short --branch
        Write-Host ""
    } else {
        Write-Host "[1] SKIP git sync." -ForegroundColor Yellow
        Write-Host ""
    }

    Write-Host "[2] Running guards..." -ForegroundColor Yellow
    python agent_hunt_pipeline/scripts/backref_bounty_guard.py
    python agent_hunt_pipeline/scripts/backref_no_cheat_guard.py
    python agent_hunt_pipeline/scripts/backref_statement_guard.py
    python agent_hunt_pipeline/scripts/backref_role_guard.py --role admin

    if (-not $SkipPilotBuild) {
        powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -PilotOnly -Role admin -NoCertificate
    } else {
        Write-Host "  SKIP pilot Isabelle build." -ForegroundColor Yellow
    }
    Write-Host ""

    Write-Host "[3] Checking WSL/tmux/Codex CLI..." -ForegroundColor Yellow
    $tmuxVersion = (wsl.exe -d $WslDistro -- bash -lc "tmux -V").Trim()
    Write-Host "  $tmuxVersion" -ForegroundColor Green

    $codexHelp = wsl.exe -d $WslDistro -- bash -lc "npx -y @openai/codex@0.133.0 --version"
    Write-Host "  Codex CLI: $($codexHelp.Trim())" -ForegroundColor Green
    Write-Host ""

    New-Item -ItemType Directory -Path "agent_hunt_pipeline/logs" -Force | Out-Null

    if ($repoRoot -match '^([A-Za-z]):\\(.*)$') {
        $drive = $Matches[1].ToLowerInvariant()
        $rest = $Matches[2] -replace '\\', '/'
        $wslRepo = "/mnt/$drive/$rest"
    } else {
        $wslRepo = (wsl.exe -d $WslDistro -- bash -lc "wslpath -a '$repoRoot'").Trim()
    }
    $promptWsl = "$wslRepo/$($PromptFile -replace '\\', '/')"
    $watcherWsl = "$wslRepo/agent_hunt_pipeline/scripts/backref_idle_watch.sh"
    $logWsl = "$wslRepo/agent_hunt_pipeline/logs/codex_idle_watch.log"
    $captureDirWsl = "$wslRepo/agent_hunt_pipeline/.agent-hunt/tmux-codex"
    $target = "${Session}:0.0"
    $killFlag = if ($KillExisting) { "1" } else { "0" }

    $repoQ = Quote-Bash $wslRepo
    $promptQ = Quote-Bash $promptWsl
    $watcherQ = Quote-Bash $watcherWsl
    $logQ = Quote-Bash $logWsl
    $captureDirQ = Quote-Bash $captureDirWsl
    $sessionQ = Quote-Bash $Session
    $targetQ = Quote-Bash $target

    $wslScript = @"
set -euo pipefail
cd $repoQ
mkdir -p agent_hunt_pipeline/logs agent_hunt_pipeline/.agent-hunt/tmux-codex
if tmux has-session -t $sessionQ 2>/dev/null; then
  if [[ '$killFlag' == '1' ]]; then
    tmux kill-session -t $sessionQ
  else
    echo 'tmux session already exists: $Session'
    echo 'Attach with: wsl -d $WslDistro -- tmux attach -t $Session'
    exit 4
  fi
fi
tmux new-session -d -s $sessionQ -x 160 -y 50
sleep 1
tmux send-keys -t $sessionQ 'cd $wslRepo && $AgentCommand' Enter
sleep $StartupDelaySeconds
capture=`$(tmux capture-pane -t $sessionQ -p -S -80 || true)
if printf '%s\n' "`$capture" | grep -q 'Do you trust'; then
  tmux send-keys -t $sessionQ Enter
  sleep 3
fi
prompt=`$(tr '\n' ' ' < $promptQ | sed 's/[[:space:]]*`$//')
tmux send-keys -t $sessionQ "`$prompt" Enter
BACKREF_PROMPT_FILE=$promptQ \
BACKREF_TMUX_LOG_DIR=$captureDirQ \
nohup bash $watcherQ $targetQ $IntervalSeconds > $logQ 2>&1 &
echo "Codex tmux session: $Session"
echo "Idle watcher PID: `$!"
echo "Attach: wsl -d $WslDistro -- tmux attach -t $Session"
echo "Log: $logWsl"
"@

    Write-Host "[4] Starting tmux loop..." -ForegroundColor Yellow
    if ($DryRun) {
        Write-Host $wslScript
        Write-Host ""
        Write-Host "Dry run complete. Nothing was started." -ForegroundColor Cyan
    } else {
        wsl.exe -d $WslDistro -- bash -lc $wslScript
        Write-Host ""
        Write-Host "Started. Attach with:" -ForegroundColor Green
        Write-Host "  wsl -d $WslDistro -- tmux attach -t $Session" -ForegroundColor White
        Write-Host "Watcher log:" -ForegroundColor Green
        Write-Host "  agent_hunt_pipeline\logs\codex_idle_watch.log" -ForegroundColor White
    }
} finally {
    Pop-Location
}
