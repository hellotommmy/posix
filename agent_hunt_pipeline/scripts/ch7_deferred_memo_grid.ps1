param(
  [string]$Ks = "5,8",
  [int]$MaxN = 80,
  [int]$Step = 2,
  [string]$Lengths = "",
  [string]$OutDir = "agent_hunt_pipeline/reports/ch7_deferred_memo_grid",
  [switch]$LogY,
  [int]$TimeoutSeconds = 900
)

$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$GridScript = Join-Path $ScriptDir "ch7_size_grid.ps1"
$Metrics = "strongMemoTree,strongMemoActiveRows,strongMemoActiveKeys,strongMemoActiveMaxBucket,strongMemoActivePairBudget,strongMemoFinalActiveRows,strongMemoFinalActiveKeys,strongMemoFinalActiveMaxBucket,strongMemoFinalActivePairBudget,strongMemoStates,strongMemoSplitProbes,strongMemoSpanBound,strongMemoSplitBound"

$Params = @{
  Ks = $Ks
  MaxN = $MaxN
  Step = $Step
  Metrics = $Metrics
  OutDir = $OutDir
  TimeoutSeconds = $TimeoutSeconds
}

if ($Lengths.Trim().Length -gt 0) {
  $Params["Lengths"] = $Lengths
}

if ($LogY) {
  $Params["LogY"] = $true
}

& $GridScript @Params
