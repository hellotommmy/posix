param(
  [switch]$SkipFetch,
  [switch]$PilotOnly,
  [ValidateSet("admin", "steward", "worker")]
  [string]$Role = "admin"
)

$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$Repo = Resolve-Path (Join-Path $ScriptDir "..\..")
$Repo = $Repo.Path
$LogDir = Join-Path $Repo "agent_hunt_pipeline\logs"
$RunDir = Join-Path $Repo "agent_hunt_pipeline\run"
New-Item -ItemType Directory -Force -Path $LogDir, $RunDir | Out-Null

$Stamp = Get-Date -Format "yyyyMMdd_HHmmss"
$Log = Join-Path $LogDir "isabelle_ci_$Stamp.log"
$Err = Join-Path $LogDir "isabelle_ci_$Stamp.err.log"
$Exit = Join-Path $RunDir "isabelle_ci_$Stamp.exit"
$PidFile = Join-Path $RunDir "isabelle_ci_latest.pid"
$MetaFile = Join-Path $RunDir "isabelle_ci_latest.json"
$Ci = Join-Path $ScriptDir "isabelle_ci.ps1"

$ArgList = @(
  "-NoProfile",
  "-ExecutionPolicy", "Bypass",
  "-File", $Ci,
  "-Role", $Role
)
if ($SkipFetch) { $ArgList += "-SkipFetch" }
if ($PilotOnly) { $ArgList += "-PilotOnly" }

$Wrapper = Join-Path $RunDir "isabelle_ci_$Stamp.ps1"
@"
& powershell $($ArgList -join ' ')
`$code = `$LASTEXITCODE
Set-Content -LiteralPath '$Exit' -Value `$code -Encoding utf8
exit `$code
"@ | Set-Content -LiteralPath $Wrapper -Encoding utf8

$Process = Start-Process `
  -FilePath "powershell" `
  -ArgumentList @("-NoProfile", "-ExecutionPolicy", "Bypass", "-File", $Wrapper) `
  -WorkingDirectory $Repo `
  -RedirectStandardOutput $Log `
  -RedirectStandardError $Err `
  -WindowStyle Hidden `
  -PassThru

Set-Content -LiteralPath $PidFile -Value $Process.Id -Encoding utf8
@{
  pid = $Process.Id
  started = (Get-Date).ToString("o")
  role = $Role
  pilot_only = [bool]$PilotOnly
  log = $Log
  stderr = $Err
  exit_file = $Exit
} | ConvertTo-Json | Set-Content -LiteralPath $MetaFile -Encoding utf8

Write-Host "Started Isabelle CI PID $($Process.Id)"
Write-Host "Log: $Log"
Write-Host "Stderr: $Err"
Write-Host "Status: powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/ci_status.ps1"
