$ErrorActionPreference = "Continue"

$Workspace = Resolve-Path (Join-Path $PSScriptRoot "..\..")
$ConfigPath = if ($env:POSIX_LOOP_CONFIG) { $env:POSIX_LOOP_CONFIG } else { Join-Path $Workspace "loop-config.json" }
$StateDir = Join-Path $Workspace ".cursor\loop-state"
$LogDir = Join-Path $Workspace "agent_hunt_pipeline\logs\cursor-loop"
$StatePath = Join-Path $StateDir "state.json"

function Write-HookJson($Decision, $Message) {
    [ordered]@{
        decision = $Decision
        followup_message = $Message
    } | ConvertTo-Json -Compress
}

function Shorten($Text, $Limit) {
    if (-not $Text) { return "" }
    if ($Text.Length -le $Limit) { return $Text }
    return $Text.Substring(0, $Limit) + "`n...[truncated]..."
}

try {
    if (-not (Test-Path -LiteralPath $ConfigPath)) {
        Write-HookJson "stop" "POSIX loop is not enabled. To enable it, copy agent_hunt_pipeline/projects/posix-backref/loop-config.cursor-opus.json to loop-config.json in the workspace root."
        exit 0
    }

    $Config = Get-Content -LiteralPath $ConfigPath -Raw | ConvertFrom-Json
    if ($Config.enabled -eq $false) {
        Write-HookJson "stop" "POSIX loop-config.json has enabled=false."
        exit 0
    }

    $Task = [string]$Config.task
    if (-not $Task -or $Task.Trim() -eq "") {
        Write-HookJson "stop" "loop-config.json has no task."
        exit 0
    }

    New-Item -ItemType Directory -Force -Path $StateDir, $LogDir | Out-Null

    $Iteration = 1
    if (Test-Path -LiteralPath $StatePath) {
        try {
            $State = Get-Content -LiteralPath $StatePath -Raw | ConvertFrom-Json
            $Iteration = [int]$State.iteration + 1
        } catch {
            $Iteration = 1
        }
    }

    [ordered]@{
        iteration = $Iteration
        updated_utc = (Get-Date).ToUniversalTime().ToString("o")
        config = $ConfigPath
    } | ConvertTo-Json | Set-Content -LiteralPath $StatePath -Encoding utf8

    $ValidationMessage = ""
    $ValidationCommand = [string]$Config.validation_command
    $ValidationShell = if ($Config.validation_shell) { [string]$Config.validation_shell } else { "powershell" }
    $MaxOutputChars = if ($Config.max_output_chars) { [int]$Config.max_output_chars } else { 12000 }

    if ($ValidationCommand -and $ValidationCommand.Trim() -ne "") {
        $global:LASTEXITCODE = 0
        $Output = ""
        $ExitCode = 0
        try {
            if ($ValidationShell -eq "wsl") {
                $Output = (& wsl.exe -d Ubuntu -- bash -lc $ValidationCommand 2>&1 | Out-String).Trim()
            } elseif ($ValidationShell -eq "bash") {
                $Output = (& bash -lc $ValidationCommand 2>&1 | Out-String).Trim()
            } else {
                $Output = (Invoke-Expression $ValidationCommand 2>&1 | Out-String).Trim()
            }
            $ExitCode = if ($null -ne $LASTEXITCODE) { $LASTEXITCODE } else { 0 }
        } catch {
            $Output = ($_ | Out-String).Trim()
            $ExitCode = 1
        }

        $Stamp = Get-Date -Format "yyyyMMdd_HHmmss"
        $LogPath = Join-Path $LogDir "cursor_loop_${Stamp}_iter${Iteration}.log"
        $Output | Set-Content -LiteralPath $LogPath -Encoding utf8
        $Output = Shorten $Output $MaxOutputChars

        if ($ExitCode -ne 0) {
            $Template = if ($Config.on_validation_fail) { [string]$Config.on_validation_fail } else { "Validation failed. Fix the errors first.`n{errors}" }
            $ValidationMessage = $Template.Replace("{errors}", $Output)
        } else {
            $ValidationMessage = if ($Config.on_validation_pass) { [string]$Config.on_validation_pass } else { "Validation passed." }
        }
    }

    $Followup = @"
$ValidationMessage

LOOP ITERATION: $Iteration

ONGOING POSIX BACKREF TASK:
$Task
"@.Trim()

    Write-HookJson "continue" $Followup
    exit 0
} catch {
    Write-HookJson "stop" ("POSIX loop hook failed: " + ($_ | Out-String))
    exit 0
}
