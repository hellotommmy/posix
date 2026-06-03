param(
  [string]$Seeds = "20260602,20260603,20260604",
  [int]$RandomCases = 5000,
  [int]$RandomDepth = 6,
  [int]$RandomInputLength = 8,
  [double]$RowsFactor = 1.0,
  [double]$PairFactor = 1.0,
  [int]$MinRegexSize = 5,
  [int]$Top = 5,
  [string]$OutDir = "agent_hunt_pipeline/reports/strong_memo_final_active_scout",
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

if ($RowsFactor -le 0.0 -and $PairFactor -le 0.0) {
  throw "At least one of RowsFactor or PairFactor must be positive."
}

$Rows = New-Object System.Collections.Generic.List[object]

foreach ($SeedText in $SeedList) {
  $Seed = [long]$SeedText
  $LogPath = Join-Path $OutDirPath "seed_$Seed.log"
  Write-Host "== Strong memo final-active scout seed=$Seed =="
  $Output = & $SmokeScript `
    -Route strong-memo `
    -SkipLegacyCubic `
    -CheckStrongDeferredMemo `
    -FindStrongFinalActiveBudgetCE `
    -StrongFinalActiveRowsFactor $RowsFactor `
    -StrongFinalActivePairFactor $PairFactor `
    -StrongFinalActiveMinRegexSize $MinRegexSize `
    -StrongFinalActiveTop $Top `
    -RandomCases $RandomCases `
    -RandomDepth $RandomDepth `
    -RandomInputLength $RandomInputLength `
    -Seed $Seed `
    -TimeoutSeconds $TimeoutSeconds 2>&1
  $ExitCode = $LASTEXITCODE
  $Output | Set-Content -LiteralPath $LogPath
  if ($ExitCode -ne 0) {
    throw "Strong memo final-active scout failed for seed $Seed; see $LogPath"
  }

  $Text = ($Output -join "`n")
  $NoCE = $Text.Contains("no strong final-active budget CE found")
  $RowsMatches = [regex]::Matches($Text, "rowsRatio=([0-9.]+) rows=([0-9]+) label=([^;`r`n]+)")
  $PairMatches = [regex]::Matches($Text, "pairRatio=([0-9.]+) pairBudget=([0-9]+) label=([^;`r`n]+)")
  $WorstRowsRatio = ""
  $WorstRowsLabel = ""
  if ($RowsMatches.Count -gt 0) {
    $BestRows = $RowsMatches |
      Sort-Object { [double]$_.Groups[1].Value } -Descending |
      Select-Object -First 1
    $WorstRowsRatio = $BestRows.Groups[1].Value
    $WorstRowsLabel = $BestRows.Groups[3].Value
  }
  $WorstPairRatio = ""
  $WorstPairLabel = ""
  if ($PairMatches.Count -gt 0) {
    $BestPair = $PairMatches |
      Sort-Object { [double]$_.Groups[1].Value } -Descending |
      Select-Object -First 1
    $WorstPairRatio = $BestPair.Groups[1].Value
    $WorstPairLabel = $BestPair.Groups[3].Value
  }

  $Rows.Add([pscustomobject]@{
    Seed = $Seed
    NoBudgetCE = $NoCE
    WorstRowsRatio = $WorstRowsRatio
    WorstRowsLabel = $WorstRowsLabel
    WorstPairRatio = $WorstPairRatio
    WorstPairLabel = $WorstPairLabel
    Log = "seed_$Seed.log"
  })
}

$SummaryPath = Join-Path $OutDirPath "summary.md"
$Lines = New-Object System.Collections.Generic.List[string]
$Lines.Add("# Strong Memo Final-Active Scout")
$Lines.Add("")
$Lines.Add("Generated: $(Get-Date -Format o)")
$Lines.Add("")
$Lines.Add("- Route: strong-memo")
$Lines.Add("- Random cases per seed: $RandomCases")
$Lines.Add("- Random depth/input length: $RandomDepth / $RandomInputLength")
$Lines.Add("- Rows budget: $RowsFactor * rsize(r)")
$Lines.Add("- Pair budget: $PairFactor * rsize(r)^2")
$Lines.Add("- Minimum regex size: $MinRegexSize")
$Lines.Add("")
$Lines.Add("| Seed | Budget CE? | Worst rows ratio | Rows witness | Worst pair ratio | Pair witness | Log |")
$Lines.Add("| ---: | --- | ---: | --- | ---: | --- | --- |")
foreach ($Row in $Rows) {
  $CeText = if ($Row.NoBudgetCE) { "no" } else { "yes or unknown" }
  $RowsWitness = if ($Row.WorstRowsLabel.Length -gt 0) {
    $Row.WorstRowsLabel.Replace("|", "\|")
  } else {
    "-"
  }
  $PairWitness = if ($Row.WorstPairLabel.Length -gt 0) {
    $Row.WorstPairLabel.Replace("|", "\|")
  } else {
    "-"
  }
  $Lines.Add("| $($Row.Seed) | $CeText | $($Row.WorstRowsRatio) | $RowsWitness | $($Row.WorstPairRatio) | $PairWitness | $($Row.Log) |")
}
$Lines.Add("")
$Lines.Add("A no entry means the smoke run found no final-active witness above")
$Lines.Add("the configured linear rows or quadratic pair-budget. This is smoke")
$Lines.Add("evidence for the strong-memo proof route, not an Isabelle proof.")

$Lines | Set-Content -LiteralPath $SummaryPath
Write-Host "== Wrote strong memo final-active scout report to $OutDirPath =="
