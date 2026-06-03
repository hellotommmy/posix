param(
  [string]$Seeds = "20260602,20260603,20260604",
  [int]$RandomCases = 5000,
  [int]$RandomDepth = 6,
  [int]$RandomInputLength = 8,
  [double]$RowsFactor = 1.0,
  [double]$PairFactor = 1.0,
  [double]$MemberFactor = 0.0,
  [double]$MemberDagFactor = 2.0,
  [double]$MemberShapeDagFactor = 2.0,
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

if ($RowsFactor -le 0.0 -and $PairFactor -le 0.0 -and $MemberFactor -le 0.0 -and
    $MemberDagFactor -le 0.0 -and $MemberShapeDagFactor -le 0.0) {
  throw "At least one final-active budget factor must be positive."
}

$Rows = New-Object System.Collections.Generic.List[object]

foreach ($SeedText in $SeedList) {
  $Seed = [long]$SeedText
  $LogPath = Join-Path $OutDirPath "seed_$Seed.log"
  Write-Host "== Strong memo final-active scout seed=$Seed =="
  $SmokeArgs = @(
    "-NoProfile",
    "-ExecutionPolicy", "Bypass",
    "-File", $SmokeScript,
    "-Route", "strong-memo",
    "-SkipLegacyCubic",
    "-CheckStrongDeferredMemo",
    "-FindStrongFinalActiveBudgetCE",
    "-StrongFinalActiveRowsFactor", $RowsFactor,
    "-StrongFinalActivePairFactor", $PairFactor,
    "-StrongFinalActiveMemberFactor", $MemberFactor,
    "-StrongFinalActiveMemberDagFactor", $MemberDagFactor,
    "-StrongFinalActiveMemberShapeDagFactor", $MemberShapeDagFactor,
    "-StrongFinalActiveMinRegexSize", $MinRegexSize,
    "-StrongFinalActiveTop", $Top,
    "-RandomCases", $RandomCases,
    "-RandomDepth", $RandomDepth,
    "-RandomInputLength", $RandomInputLength,
    "-Seed", $Seed,
    "-TimeoutSeconds", $TimeoutSeconds
  )
  $OldErrorActionPreference = $ErrorActionPreference
  $ErrorActionPreference = "Continue"
  $Output = & powershell @SmokeArgs 2>&1
  $ExitCode = $LASTEXITCODE
  $ErrorActionPreference = $OldErrorActionPreference
  $CleanOutput = @(
    $Output |
      ForEach-Object { [string]$_ -split "\r?\n" } |
      ForEach-Object { ($_ -replace "\s+$", "") }
  )
  while ($CleanOutput.Count -gt 0 -and $CleanOutput[-1].Length -eq 0) {
    if ($CleanOutput.Count -eq 1) {
      $CleanOutput = @()
    } else {
      $CleanOutput = @($CleanOutput[0..($CleanOutput.Count - 2)])
    }
  }
  $CleanOutput | Set-Content -LiteralPath $LogPath -Encoding utf8
  if ($ExitCode -ne 0) {
    throw "Strong memo final-active scout failed for seed $Seed; see $LogPath"
  }

  $Text = ($Output -join "`n")
  $NoCE = $Text.Contains("no strong final-active budget CE found")
  $RowsMatches = [regex]::Matches($Text, "rowsRatio=([0-9.]+) rows=([0-9]+) label=([^;`r`n]+)")
  $PairMatches = [regex]::Matches($Text, "pairRatio=([0-9.]+) pairBudget=([0-9]+) label=([^;`r`n]+)")
  $MemberMatches = [regex]::Matches($Text, "memberRatio=([0-9.]+) maxRowSize=([0-9]+).*? label=([^;`r`n]+)")
  $DagMatches = [regex]::Matches($Text, "dagRatio=([0-9.]+).*? label=([^;`r`n]+)")
  $ShapeDagMatches = [regex]::Matches($Text, "shapeRatio=([0-9.]+).*? label=([^;`r`n]+)")
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
  $WorstMemberRatio = ""
  $WorstMemberLabel = ""
  if ($MemberMatches.Count -gt 0) {
    $BestMember = $MemberMatches |
      Sort-Object { [double]$_.Groups[1].Value } -Descending |
      Select-Object -First 1
    $WorstMemberRatio = $BestMember.Groups[1].Value
    $WorstMemberLabel = $BestMember.Groups[3].Value
  }
  $WorstDagRatio = ""
  $WorstDagLabel = ""
  if ($DagMatches.Count -gt 0) {
    $BestDag = $DagMatches |
      Sort-Object { [double]$_.Groups[1].Value } -Descending |
      Select-Object -First 1
    $WorstDagRatio = $BestDag.Groups[1].Value
    $WorstDagLabel = $BestDag.Groups[2].Value
  }
  $WorstShapeDagRatio = ""
  $WorstShapeDagLabel = ""
  if ($ShapeDagMatches.Count -gt 0) {
    $BestShapeDag = $ShapeDagMatches |
      Sort-Object { [double]$_.Groups[1].Value } -Descending |
      Select-Object -First 1
    $WorstShapeDagRatio = $BestShapeDag.Groups[1].Value
    $WorstShapeDagLabel = $BestShapeDag.Groups[2].Value
  }

  $Rows.Add([pscustomobject]@{
    Seed = $Seed
    NoBudgetCE = $NoCE
    WorstRowsRatio = $WorstRowsRatio
    WorstRowsLabel = $WorstRowsLabel
    WorstMemberRatio = $WorstMemberRatio
    WorstMemberLabel = $WorstMemberLabel
    WorstDagRatio = $WorstDagRatio
    WorstDagLabel = $WorstDagLabel
    WorstShapeDagRatio = $WorstShapeDagRatio
    WorstShapeDagLabel = $WorstShapeDagLabel
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
$Lines.Add("- Member-size budget: $MemberFactor * rsize(r)")
$Lines.Add("- Member DAG budget: $MemberDagFactor * rsize(r)")
$Lines.Add("- Member shape-DAG budget: $MemberShapeDagFactor * rsize(r)")
$Lines.Add("- Pair budget: $PairFactor * rsize(r)^2")
$Lines.Add("- Minimum regex size: $MinRegexSize")
$Lines.Add("")
$Lines.Add("| Seed | Budget CE? | Worst rows ratio | Rows witness | Worst raw member ratio | Raw witness | Worst DAG ratio | DAG witness | Worst shape-DAG ratio | Shape-DAG witness | Worst pair ratio | Pair witness | Log |")
$Lines.Add("| ---: | --- | ---: | --- | ---: | --- | ---: | --- | ---: | --- | ---: | --- | --- |")
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
  $MemberWitness = if ($Row.WorstMemberLabel.Length -gt 0) {
    $Row.WorstMemberLabel.Replace("|", "\|")
  } else {
    "-"
  }
  $DagWitness = if ($Row.WorstDagLabel.Length -gt 0) {
    $Row.WorstDagLabel.Replace("|", "\|")
  } else {
    "-"
  }
  $ShapeDagWitness = if ($Row.WorstShapeDagLabel.Length -gt 0) {
    $Row.WorstShapeDagLabel.Replace("|", "\|")
  } else {
    "-"
  }
  $Lines.Add("| $($Row.Seed) | $CeText | $($Row.WorstRowsRatio) | $RowsWitness | $($Row.WorstMemberRatio) | $MemberWitness | $($Row.WorstDagRatio) | $DagWitness | $($Row.WorstShapeDagRatio) | $ShapeDagWitness | $($Row.WorstPairRatio) | $PairWitness | $($Row.Log) |")
}
$Lines.Add("")
$Lines.Add("A no entry means the smoke run found no final-active witness above")
$Lines.Add("the configured linear rows, exact-DAG member, shape-DAG member, raw member,")
$Lines.Add("or quadratic pair budget. This is smoke")
$Lines.Add("evidence for the strong-memo proof route, not an Isabelle proof.")

$Lines | Set-Content -LiteralPath $SummaryPath -Encoding utf8
Write-Host "== Wrote strong memo final-active scout report to $OutDirPath =="
