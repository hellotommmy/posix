param(
  [int]$Tail = 60
)

$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$Repo = Resolve-Path (Join-Path $ScriptDir "..\..")
$Repo = $Repo.Path
$RunDir = Join-Path $Repo "agent_hunt_pipeline\run"
$MetaFile = Join-Path $RunDir "isabelle_ci_latest.json"

if (-not (Test-Path -LiteralPath $MetaFile)) {
  Write-Host "No Isabelle CI run metadata found."
  exit 0
}

$Meta = Get-Content -LiteralPath $MetaFile -Raw | ConvertFrom-Json
$Proc = Get-Process -Id $Meta.pid -ErrorAction SilentlyContinue

Write-Host "PID: $($Meta.pid)"
Write-Host "Started: $($Meta.started)"
Write-Host "Pilot only: $($Meta.pilot_only)"
Write-Host "Log: $($Meta.log)"
Write-Host "Stderr: $($Meta.stderr)"

if ($Proc) {
  Write-Host "Status: RUNNING"
  Write-Host "CPU seconds: $([math]::Round($Proc.CPU, 1))"
} elseif (Test-Path -LiteralPath $Meta.exit_file) {
  $Code = (Get-Content -LiteralPath $Meta.exit_file -Raw).Trim()
  Write-Host "Status: EXITED $Code"
} else {
  Write-Host "Status: NOT RUNNING; no exit file found"
}

if (Test-Path -LiteralPath $Meta.log) {
  Write-Host ""
  Write-Host "== Log tail =="
  Get-Content -LiteralPath $Meta.log -Tail $Tail
}

if (Test-Path -LiteralPath $Meta.stderr) {
  $ErrLines = Get-Content -LiteralPath $Meta.stderr -Tail $Tail
  if ($ErrLines) {
    Write-Host ""
    Write-Host "== Stderr tail =="
    $ErrLines
  }
}
