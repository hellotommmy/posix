param(
  [ValidateSet('Check', 'KillStale')]
  [string]$Action = 'Check',
  [int]$MinAgeMinutes = 10
)

$ErrorActionPreference = 'Stop'

$Repo = Split-Path -Parent $PSScriptRoot
$IsabelleHome = 'C:\Users\Chengsong\Isabelle2025-2'
$Names = @('isabelle', 'poly', 'polyml', 'python', 'python3', 'java')
$Now = Get-Date

function Test-RelatedProofWorker($Process) {
  $Name = [IO.Path]::GetFileNameWithoutExtension([string]$Process.Name).ToLowerInvariant()
  if (-not ($Names -contains $Name)) {
    return $false
  }

  $CommandLine = [string]$Process.CommandLine
  $ExecutablePath = [string]$Process.ExecutablePath
  return (
    $CommandLine.Contains($Repo) -or
    $CommandLine.Contains($IsabelleHome) -or
    $CommandLine.Contains('AIPV2026Notes') -or
    $CommandLine.Contains('Posix') -or
    $CommandLine.Contains('AntimirovFactoredTransition') -or
    $ExecutablePath.Contains($IsabelleHome) -or
    $ExecutablePath.Contains($Repo)
  )
}

$Workers =
  Get-CimInstance Win32_Process |
  Where-Object { Test-RelatedProofWorker $_ } |
  ForEach-Object {
    $AgeMinutes =
      if ($_.CreationDate) {
        [Math]::Round(($Now - $_.CreationDate).TotalMinutes, 1)
      } else {
        0
      }
    $WorkingSetMB =
      if ($_.WorkingSetSize) {
        [Math]::Round([double]$_.WorkingSetSize / 1MB, 1)
      } else {
        0
      }
    [PSCustomObject]@{
      Id = $_.ProcessId
      Name = $_.Name
      AgeMinutes = $AgeMinutes
      WorkingSetMB = $WorkingSetMB
      CommandLine = $_.CommandLine
    }
  }

if (-not $Workers) {
  Write-Host 'No matching proof-worker processes found.'
  exit 0
}

$Workers | Sort-Object Name, Id | Format-Table Id, Name, AgeMinutes, WorkingSetMB, CommandLine -AutoSize

if ($Action -eq 'KillStale') {
  $Stale = $Workers | Where-Object { $_.AgeMinutes -ge $MinAgeMinutes }
  if (-not $Stale) {
    Write-Host "No stale matching proof-worker processes older than $MinAgeMinutes minutes."
    exit 0
  }

  foreach ($Worker in $Stale) {
    Write-Host "Stopping stale proof worker $($Worker.Id) ($($Worker.Name)), age $($Worker.AgeMinutes)m."
    Stop-Process -Id $Worker.Id -Force -ErrorAction Stop
  }
}
