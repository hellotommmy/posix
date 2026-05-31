<#
.SYNOPSIS
  Start the Codex CLI side of the POSIX backreference overnight loop.

.DESCRIPTION
  This is the robust launcher for the current Codex clone. It runs pre-flight
  git/guard checks, starts a WSL tmux session, and runs Codex CLI in recurring
  non-interactive `codex exec` iterations. This avoids fragile TUI key
  injection while preserving the paper-style repeated prompt loop.

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
    [int]$RunTimeoutSeconds = 7200,
    [string]$CodexExecCommand = "npx -y @openai/codex@0.133.0 exec --dangerously-bypass-approvals-and-sandbox -C .",
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
    New-Item -ItemType Directory -Path "agent_hunt_pipeline/run" -Force | Out-Null

    if ($repoRoot -match '^([A-Za-z]):\\(.*)$') {
        $drive = $Matches[1].ToLowerInvariant()
        $rest = $Matches[2] -replace '\\', '/'
        $wslRepo = "/mnt/$drive/$rest"
    } else {
        $wslRepo = (wsl.exe -d $WslDistro -- bash -lc "wslpath -a '$repoRoot'").Trim()
    }
    $promptWsl = "$wslRepo/$($PromptFile -replace '\\', '/')"
    $logWsl = "$wslRepo/agent_hunt_pipeline/logs/codex_idle_watch.log"
    $runnerWsl = "$wslRepo/agent_hunt_pipeline/run/codex_exec_loop.generated.sh"
    $killFlag = if ($KillExisting) { "1" } else { "0" }

    $repoQ = Quote-Bash $wslRepo
    $promptQ = Quote-Bash $promptWsl
    $logQ = Quote-Bash $logWsl
    $runnerQ = Quote-Bash $runnerWsl
    $sessionQ = Quote-Bash $Session

    $loopScript = @"
#!/usr/bin/env bash
set -u
cd $repoQ
mkdir -p agent_hunt_pipeline/logs
echo "[`$(date -Is)] Codex exec loop booted for $Session" | tee -a $logQ
while true; do
  ts=`$(date -Is)
  echo "" | tee -a $logQ
  echo "[`$ts] Starting Codex exec iteration" | tee -a $logQ
  if [[ ! -f $promptQ ]]; then
    echo "[`$ts] Prompt file missing: $promptWsl" | tee -a $logQ
    sleep $IntervalSeconds
    continue
  fi
  cat $promptQ | timeout $RunTimeoutSeconds $CodexExecCommand - 2>&1 | tee -a $logQ
  rc=`${PIPESTATUS[1]}
  done_ts=`$(date -Is)
  echo "[`$done_ts] Codex exec exit code: `$rc" | tee -a $logQ
  sleep $IntervalSeconds
done
"@

    $wslScript = @"
set -euo pipefail
cd $repoQ
mkdir -p agent_hunt_pipeline/logs agent_hunt_pipeline/run
if tmux has-session -t $sessionQ 2>/dev/null; then
  if [[ '$killFlag' == '1' ]]; then
    tmux kill-session -t $sessionQ
  else
    echo 'tmux session already exists: $Session'
    echo 'Attach with: wsl -d $WslDistro -- tmux attach -t $Session'
    exit 4
  fi
fi
tmux new-session -d -s $sessionQ -x 160 -y 50 "bash $runnerQ"
echo "Codex exec tmux session: $Session"
echo "Attach: wsl -d $WslDistro -- tmux attach -t $Session"
echo "Log: $logWsl"
"@

    Write-Host "[4] Starting tmux loop..." -ForegroundColor Yellow
    if ($DryRun) {
        Write-Host $wslScript
        Write-Host ""
        Write-Host "Dry run complete. Nothing was started." -ForegroundColor Cyan
    } else {
        $generatedScript = Join-Path $repoRoot "agent_hunt_pipeline/run/start_codex_tmux.generated.sh"
        $generatedLoop = Join-Path $repoRoot "agent_hunt_pipeline/run/codex_exec_loop.generated.sh"
        [System.IO.File]::WriteAllText($generatedScript, ($wslScript -replace "`r`n", "`n"), [System.Text.Encoding]::ASCII)
        [System.IO.File]::WriteAllText($generatedLoop, ($loopScript -replace "`r`n", "`n"), [System.Text.Encoding]::ASCII)
        $generatedScriptWsl = "$wslRepo/agent_hunt_pipeline/run/start_codex_tmux.generated.sh"
        wsl.exe -d $WslDistro -- bash $generatedScriptWsl
        Write-Host ""
        Write-Host "Started. Attach with:" -ForegroundColor Green
        Write-Host "  wsl -d $WslDistro -- tmux attach -t $Session" -ForegroundColor White
        Write-Host "Watcher log:" -ForegroundColor Green
        Write-Host "  agent_hunt_pipeline\logs\codex_idle_watch.log" -ForegroundColor White
    }
} finally {
    Pop-Location
}
