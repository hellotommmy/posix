<#
.SYNOPSIS
  Watch the Cursor/Opus clone and restart Opus with cursor-agent if it stalls.

.DESCRIPTION
  Cursor GUI hooks can continue a chat after a normal stop, but they cannot
  reliably recover from a frozen GUI or a network disconnect. This watchdog is
  an external fallback: when the Opus clone has been idle for long enough and no
  headless Cursor Agent is already running for that workspace, it starts a new
  headless Opus 4.6 Cursor Agent chat in that folder.

  It never resets, checks out, or pulls the target repository. The prompt tells
  the new agent to preserve any interrupted worktree edits first.

.EXAMPLE
  powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/opus_cursor_agent_watchdog.ps1 -Background

.EXAMPLE
  powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/opus_cursor_agent_watchdog.ps1 -Once -DryRun
#>

param(
    [string]$RepoPath = "C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus",
    [string]$Branch = "codex/backref-values",
    [string]$Model = "claude-4.6-opus-high-thinking",
    [string]$PromptFile = "",
    [int]$IdleMinutes = 15,
    [int]$PollSeconds = 60,
    [int]$CooldownMinutes = 20,
    [int]$MaxRestarts = 5,
    [string]$UseCursorHookPrompt = "true",
    [switch]$Once,
    [switch]$DryRun,
    [switch]$Background
)

$ErrorActionPreference = "Stop"

$scriptRoot = Split-Path -Parent $PSCommandPath
if (-not $PromptFile) {
    $PromptFile = Join-Path $scriptRoot "opus_cursor_agent_prompt.txt"
}
$script:UseCursorHookPromptEnabled = $UseCursorHookPrompt -notmatch '^(false|0|no)$'

function Quote-Arg([string]$Value) {
    '"' + ($Value -replace '"', '\"') + '"'
}

function Write-WatchLog([string]$Message) {
    $timestamp = Get-Date -Format "yyyy-MM-ddTHH:mm:ssK"
    $line = "[$timestamp] $Message"
    Write-Host $line
    Add-Content -LiteralPath $script:WatchLog -Value $line -Encoding UTF8
}

function Invoke-GitLines {
    param(
        [Parameter(ValueFromRemainingArguments = $true)]
        [string[]]$GitArgs
    )
    $output = & git -C $script:Repo @GitArgs 2>$null
    if ($LASTEXITCODE -ne 0) {
        return @()
    }
    return @($output)
}

function Get-RepoActivity {
    $head = (Invoke-GitLines "rev-parse" "--short" "HEAD" | Select-Object -First 1)
    $branch = (Invoke-GitLines "branch" "--show-current" | Select-Object -First 1)
    $changed = Invoke-GitLines "ls-files" "-m" "-o" "--exclude-standard"

    $latest = [DateTime]::MinValue
    foreach ($rel in $changed) {
        $path = Join-Path $script:Repo $rel
        if (Test-Path -LiteralPath $path) {
            $item = Get-Item -LiteralPath $path
            if ($item.LastWriteTime -gt $latest) {
                $latest = $item.LastWriteTime
            }
        }
    }

    if ($latest -eq [DateTime]::MinValue) {
        $epoch = (Invoke-GitLines "log" "-1" "--format=%ct" | Select-Object -First 1)
        if ($epoch) {
            $latest = [DateTimeOffset]::FromUnixTimeSeconds([int64]$epoch).LocalDateTime
        } else {
            $latest = Get-Date
        }
    }

    [pscustomobject]@{
        Branch = $branch
        Head = $head
        ChangedCount = $changed.Count
        LatestWrite = $latest
        Fingerprint = "$branch|$head|$($changed -join ';')|$($latest.ToFileTimeUtc())"
    }
}

function Get-RunningCursorAgents {
    $needle = [regex]::Escape($script:Repo.ToLowerInvariant())
    @(Get-CimInstance Win32_Process |
        Where-Object {
            $_.CommandLine -and
            $_.CommandLine.ToLowerInvariant() -match $needle -and
            ($_.CommandLine -match "cursor-agent" -or $_.CommandLine -match "index\.js")
        } |
        Select-Object ProcessId, Name, CommandLine)
}

function Get-HookPrompt {
    if (-not $script:UseCursorHookPromptEnabled) {
        return ""
    }

    $hook = Join-Path $script:Repo ".cursor\hooks\posix_loop.ps1"
    if (-not (Test-Path -LiteralPath $hook)) {
        $hook = Join-Path $script:Repo ".cursor\hooks\loop.ps1"
    }
    if (-not (Test-Path -LiteralPath $hook)) {
        return ""
    }

    try {
        Push-Location $script:Repo
        $raw = powershell -NoProfile -ExecutionPolicy Bypass -File $hook 2>&1 | Out-String
        Pop-Location
        $jsonStart = $raw.IndexOf("{")
        if ($jsonStart -lt 0) {
            return ""
        }
        $json = $raw.Substring($jsonStart) | ConvertFrom-Json
        if ($json.followup_message) {
            return $json.followup_message
        }
    } catch {
        try { Pop-Location } catch {}
        Write-WatchLog "Hook prompt failed: $($_.Exception.Message)"
    }
    return ""
}

function New-AgentPrompt {
    $base = Get-Content -LiteralPath $PromptFile -Raw
    $hookPrompt = Get-HookPrompt
    if ($hookPrompt) {
        return @"
$base

Cursor hook continuation message:
$hookPrompt
"@
    }
    return $base
}

function Start-OpusAgent([string]$Reason) {
    $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
    $runPrompt = Join-Path $script:RunDir "opus_agent_prompt_$timestamp.txt"
    $agentLog = Join-Path $script:LogDir "opus_cursor_agent_$timestamp.log"
    $runScript = Join-Path $script:RunDir "opus_cursor_agent_$timestamp.ps1"
    $prompt = New-AgentPrompt

    Set-Content -LiteralPath $runPrompt -Value $prompt -Encoding UTF8

    $body = @"
`$ErrorActionPreference = "Continue"
Set-Location -LiteralPath $(Quote-Arg $script:Repo)
`$prompt = Get-Content -LiteralPath $(Quote-Arg $runPrompt) -Raw
Add-Content -LiteralPath $(Quote-Arg $agentLog) -Value "[`$(Get-Date -Format o)] Starting cursor-agent model=$Model" -Encoding UTF8
& cursor-agent --print --trust --force --model $(Quote-Arg $Model) --workspace $(Quote-Arg $script:Repo) `$prompt *> $(Quote-Arg $agentLog)
`$code = `$LASTEXITCODE
Add-Content -LiteralPath $(Quote-Arg $agentLog) -Value "[`$(Get-Date -Format o)] cursor-agent exit code: `$code" -Encoding UTF8
exit `$code
"@
    [System.IO.File]::WriteAllText($runScript, ($body -replace "`r`n", "`n"), [System.Text.Encoding]::UTF8)

    Write-WatchLog "START Opus cursor-agent: reason=$Reason; model=$Model; log=$agentLog"
    if ($DryRun) {
        Write-WatchLog "DRY-RUN: would run $runScript"
        return $null
    }

    Start-Process -FilePath "powershell" `
        -ArgumentList @("-NoProfile", "-ExecutionPolicy", "Bypass", "-File", $runScript) `
        -WindowStyle Hidden | Out-Null
    return $agentLog
}

if ($Background) {
    $argsList = @(
        "-NoProfile", "-ExecutionPolicy", "Bypass",
        "-File", $PSCommandPath,
        "-RepoPath", $RepoPath,
        "-Branch", $Branch,
        "-Model", $Model,
        "-PromptFile", $PromptFile,
        "-IdleMinutes", "$IdleMinutes",
        "-PollSeconds", "$PollSeconds",
        "-CooldownMinutes", "$CooldownMinutes",
        "-MaxRestarts", "$MaxRestarts",
        "-UseCursorHookPrompt", "$UseCursorHookPrompt"
    )
    if ($Once) { $argsList += "-Once" }
    if ($DryRun) { $argsList += "-DryRun" }
    Start-Process -FilePath "powershell" -ArgumentList $argsList -WindowStyle Hidden | Out-Null
    Write-Host "Started Opus watchdog in background for $RepoPath"
    return
}

$script:Repo = (Resolve-Path -LiteralPath $RepoPath).Path
if (-not (Test-Path -LiteralPath (Join-Path $script:Repo ".git"))) {
    throw "RepoPath is not a git repository: $script:Repo"
}

$script:LogDir = Join-Path $script:Repo "agent_hunt_pipeline\logs"
$script:RunDir = Join-Path $script:Repo "agent_hunt_pipeline\run"
New-Item -ItemType Directory -Path $script:LogDir -Force | Out-Null
New-Item -ItemType Directory -Path $script:RunDir -Force | Out-Null
$script:WatchLog = Join-Path $script:LogDir "opus_watchdog.log"
$statePath = Join-Path $script:RunDir "opus_watchdog_state.json"

$state = [pscustomobject]@{
    Restarts = 0
    LastStart = $null
}
if (Test-Path -LiteralPath $statePath) {
    try {
        $state = Get-Content -LiteralPath $statePath -Raw | ConvertFrom-Json
    } catch {
        Write-WatchLog "Ignoring unreadable state file: $($_.Exception.Message)"
    }
}

Write-WatchLog "Watchdog boot: repo=$script:Repo; model=$Model; idle=${IdleMinutes}m; poll=${PollSeconds}s; maxRestarts=$MaxRestarts"

while ($true) {
    $activity = Get-RepoActivity
    $agents = @(Get-RunningCursorAgents)
    $now = Get-Date
    $idle = $now - $activity.LatestWrite
    $cooldownOk = $true
    if ($state.LastStart) {
        $lastStart = [DateTime]$state.LastStart
        $cooldownOk = (($now - $lastStart).TotalMinutes -ge $CooldownMinutes)
    }

    Write-WatchLog ("state branch={0} head={1} changed={2} idle={3:n1}m runningAgents={4} restarts={5}" -f `
        $activity.Branch, $activity.Head, $activity.ChangedCount, $idle.TotalMinutes, $agents.Count, $state.Restarts)

    if ($activity.Branch -ne $Branch) {
        Write-WatchLog "SKIP: target branch is $($activity.Branch), expected $Branch"
    } elseif ($agents.Count -gt 0) {
        Write-WatchLog "SKIP: cursor-agent already running for target workspace"
    } elseif ($state.Restarts -ge $MaxRestarts) {
        Write-WatchLog "SKIP: MaxRestarts reached"
    } elseif ($idle.TotalMinutes -lt $IdleMinutes) {
        Write-WatchLog "SKIP: workspace is not idle long enough"
    } elseif (-not $cooldownOk) {
        Write-WatchLog "SKIP: cooldown not elapsed"
    } else {
        $log = Start-OpusAgent ("idle {0:n1} minutes" -f $idle.TotalMinutes)
        if (-not $DryRun) {
            $state.Restarts = [int]$state.Restarts + 1
            $state.LastStart = (Get-Date).ToString("o")
            $state | ConvertTo-Json | Set-Content -LiteralPath $statePath -Encoding UTF8
        }
    }

    if ($Once) {
        break
    }
    Start-Sleep -Seconds $PollSeconds
}
