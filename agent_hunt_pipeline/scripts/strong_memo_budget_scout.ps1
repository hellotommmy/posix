param(
  [string]$Seeds = "20260602,20260603,20260604",
  [int]$RandomCases = 5000,
  [int]$RandomDepth = 6,
  [int]$RandomInputLength = 8,
  [double]$StrongCubicFactor = 1.0,
  [int]$StrongCubicMinRegexSize = 5,
  [int]$StrongCubicTop = 5,
  [string]$OutDir = "agent_hunt_pipeline/reports/strong_memo_budget_scout",
  [int]$TimeoutSeconds = 600
)

$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$Repo = Resolve-Path (Join-Path $ScriptDir "..\..")
$Repo = $Repo.Path
$SmokeScript = Join-Path $ScriptDir "scala_cubic_smoke.ps1"

Set-Location -LiteralPath $Repo

$OutDirPath = Join-Path $Repo $OutDir
New-Item -ItemType Directory -Force -Path $OutDirPath | Out-Null

$SeedList = $Seeds.Split(",") |
  ForEach-Object { $_.Trim() } |
  Where-Object { $_.Length -gt 0 }

if ($SeedList.Count -eq 0) {
  throw "At least one seed is required."
}

$Rows = New-Object System.Collections.Generic.List[object]

foreach ($SeedText in $SeedList) {
  $Seed = [long]$SeedText
  $LogPath = Join-Path $OutDirPath "seed_$Seed.log"
  Write-Host "== Strong memo budget scout seed=$Seed =="
  $Output = & $SmokeScript `
    -Route strong-memo `
    -SkipLegacyCubic `
    -CheckStrongDeferredMemo `
    -FindStrongCubicBudgetCE `
    -StrongCubicFactor $StrongCubicFactor `
    -StrongCubicMinRegexSize $StrongCubicMinRegexSize `
    -StrongCubicTop $StrongCubicTop `
    -RandomCases $RandomCases `
    -RandomDepth $RandomDepth `
    -RandomInputLength $RandomInputLength `
    -Seed $Seed `
    -TimeoutSeconds $TimeoutSeconds 2>&1
  $ExitCode = $LASTEXITCODE
  $Output | Set-Content -LiteralPath $LogPath
  if ($ExitCode -ne 0) {
    throw "Strong memo budget scout failed for seed $Seed; see $LogPath"
  }

  $Text = ($Output -join "`n")
  $NoCE = $Text.Contains("no strong cubic budget CE found")
  $WorstMatches = [regex]::Matches(
    $Text,
    "(?:worst strong cubic ratio=|#\d+:ratio=)([0-9.]+) label=([^;`r`n]+)"
  )
  $WorstRatio = ""
  $WorstLabel = ""
  if ($WorstMatches.Count -gt 0) {
    $Best = $WorstMatches |
      Sort-Object { [double]$_.Groups[1].Value } -Descending |
      Select-Object -First 1
    $WorstRatio = $Best.Groups[1].Value
    $WorstLabel = $Best.Groups[2].Value
  }

  $Rows.Add([pscustomobject]@{
    Seed = $Seed
    NoBudgetCE = $NoCE
    WorstRatio = $WorstRatio
    WorstLabel = $WorstLabel
    Log = "seed_$Seed.log"
  })
}

$SummaryPath = Join-Path $OutDirPath "summary.md"
$Lines = New-Object System.Collections.Generic.List[string]
$Lines.Add("# Strong Memo Budget Scout")
$Lines.Add("")
$Lines.Add("Generated: $(Get-Date -Format o)")
$Lines.Add("")
$Lines.Add("- Route: strong-memo")
$Lines.Add("- Random cases per seed: $RandomCases")
$Lines.Add("- Random depth/input length: $RandomDepth / $RandomInputLength")
$Lines.Add("- Cubic factor: $StrongCubicFactor * rsize(r)^3")
$Lines.Add("- Minimum regex size: $StrongCubicMinRegexSize")
$Lines.Add("")
$Lines.Add("| Seed | Budget CE? | Worst ratio | Witness | Log |")
$Lines.Add("| ---: | --- | ---: | --- | --- |")
foreach ($Row in $Rows) {
  $CeText = if ($Row.NoBudgetCE) { "no" } else { "yes or unknown" }
  $Witness = if ($Row.WorstLabel.Length -gt 0) {
    $Row.WorstLabel.Replace("|", "\|")
  } else {
    "-"
  }
  $Lines.Add("| $($Row.Seed) | $CeText | $($Row.WorstRatio) | $Witness | $($Row.Log) |")
}
$Lines.Add("")
$Lines.Add("A no entry means the smoke run found no final strong-tree witness")
$Lines.Add("above the configured cubic budget. This is smoke evidence only, not an")
$Lines.Add("Isabelle proof of the cubic theorem.")

$Lines | Set-Content -LiteralPath $SummaryPath
Write-Host "== Wrote strong memo budget scout report to $OutDirPath =="
