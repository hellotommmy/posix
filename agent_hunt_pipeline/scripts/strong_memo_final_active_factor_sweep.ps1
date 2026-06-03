param(
  [string]$Factors = "4,6,8",
  [string]$Seeds = "20260602,20260603,20260604",
  [int]$RandomCases = 5000,
  [int]$RandomDepth = 6,
  [int]$RandomInputLength = 8,
  [double]$RowsFactor = 1.0,
  [double]$PairFactor = 1.0,
  [double]$RowDagUniverseFactor = 3.0,
  [int]$MinRegexSize = 5,
  [int]$Top = 5,
  [string]$OutDir = "agent_hunt_pipeline/reports/strong_memo_final_active_factor_sweep",
  [int]$TimeoutSeconds = 900
)

$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$Repo = Resolve-Path (Join-Path $ScriptDir "..\..")
$Repo = $Repo.Path
$ScoutScript = Join-Path $ScriptDir "strong_memo_final_active_scout.ps1"

Set-Location -LiteralPath $Repo

$OutDirPath = Join-Path $Repo $OutDir
New-Item -ItemType Directory -Force -Path $OutDirPath | Out-Null

$FactorList = $Factors.Split(",") |
  ForEach-Object { $_.Trim() } |
  Where-Object { $_.Length -gt 0 } |
  ForEach-Object { [double]$_ }

if ($FactorList.Count -eq 0) {
  throw "At least one member factor is required."
}

function Format-FactorDir([double]$Factor) {
  return ("factor_{0}" -f $Factor.ToString("0.######")).Replace(".", "p")
}

function Get-BestSummaryRatio([string]$Text, [string]$Pattern) {
  $Matches = [regex]::Matches($Text, $Pattern)
  if ($Matches.Count -eq 0) {
    return ""
  }
  $Best = $Matches |
    Sort-Object { [double]$_.Groups[1].Value } -Descending |
    Select-Object -First 1
  return $Best.Groups[1].Value
}

function Get-FailureEvidence([string]$FactorDirPath) {
  $SeedLogs = Get-ChildItem -LiteralPath $FactorDirPath -Filter "seed_*.log" -ErrorAction SilentlyContinue
  foreach ($Log in $SeedLogs) {
    $Text = Get-Content -LiteralPath $Log.FullName -Raw
    $MaxRow = [regex]::Match($Text, "finalActiveMaxRowSize\s*=\s*([0-9]+)")
    $Rsize = [regex]::Match($Text, "(?m)^rsize\s*=\s*([0-9]+)")
    $Label = [regex]::Match($Text, "(?m)^label\s*=\s*(.+)$")
    $Failure = [regex]::Match($Text, "(?m)^failures\s*=\s*(.+)$")
    if ($MaxRow.Success -and $Rsize.Success) {
      $Ratio = [double]$MaxRow.Groups[1].Value / [double]$Rsize.Groups[1].Value
      return [pscustomobject]@{
        Ratio = ("{0:N6}" -f $Ratio)
        MaxRow = $MaxRow.Groups[1].Value
        Rsize = $Rsize.Groups[1].Value
        Label = if ($Label.Success) { $Label.Groups[1].Value.Trim() } else { "" }
        Failure = if ($Failure.Success) { $Failure.Groups[1].Value.Trim() } else { "" }
        Log = $Log.Name
      }
    }
  }
  return [pscustomobject]@{
    Ratio = ""
    MaxRow = ""
    Rsize = ""
    Label = ""
    Failure = ""
    Log = ""
  }
}

$Rows = New-Object System.Collections.Generic.List[object]

foreach ($Factor in $FactorList) {
  $FactorDirName = Format-FactorDir $Factor
  $FactorOutRel = (Join-Path $OutDir $FactorDirName).Replace("\", "/")
  $FactorOutAbs = Join-Path $Repo $FactorOutRel
  New-Item -ItemType Directory -Force -Path $FactorOutAbs | Out-Null
  $RunLog = Join-Path $FactorOutAbs "run.log"

  Write-Host "== Strong memo final-active factor sweep memberFactor=$Factor =="
  $Output = @()
  $ExitCode = 0
  try {
    $Output = & $ScoutScript `
      -Seeds $Seeds `
      -RandomCases $RandomCases `
      -RandomDepth $RandomDepth `
      -RandomInputLength $RandomInputLength `
      -RowsFactor $RowsFactor `
      -PairFactor $PairFactor `
      -MemberFactor $Factor `
      -RowDagUniverseFactor $RowDagUniverseFactor `
      -MinRegexSize $MinRegexSize `
      -Top $Top `
      -OutDir $FactorOutRel `
      -TimeoutSeconds $TimeoutSeconds 2>&1
    $ExitCode = $LASTEXITCODE
  } catch {
    $ExitCode = 1
    $Output += $_ | Out-String
  }
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
  $CleanOutput | Set-Content -LiteralPath $RunLog -Encoding utf8

  $SummaryPath = Join-Path $FactorOutAbs "summary.md"
  $Passed = $ExitCode -eq 0
  $WorstRowsRatio = ""
  $WorstMemberRatio = ""
  $WorstPairRatio = ""
  $FailureEvidence = Get-FailureEvidence $FactorOutAbs

  if (Test-Path -LiteralPath $SummaryPath) {
    $SummaryText = Get-Content -LiteralPath $SummaryPath -Raw
    $WorstRowsRatio = Get-BestSummaryRatio $SummaryText "Worst rows ratio\s*\|[^`r`n]*?([0-9]+\.[0-9]+)"
    $WorstMemberRatio = Get-BestSummaryRatio $SummaryText " \| ([0-9]+\.[0-9]+) \| random seed=.*?\| [0-9]+\.[0-9]+ \|"
    $WorstPairRatio = Get-BestSummaryRatio $SummaryText " \| ([0-9]+\.[0-9]+) \| .*? \| seed_"
    $MemberMatches = [regex]::Matches($SummaryText, "\| [0-9]+ \| no \| [0-9.]+ \| .*? \| ([0-9.]+) \| .*? \| [0-9.]+ \|")
    if ($MemberMatches.Count -gt 0) {
      $BestMember = $MemberMatches |
        Sort-Object { [double]$_.Groups[1].Value } -Descending |
        Select-Object -First 1
      $WorstMemberRatio = $BestMember.Groups[1].Value
    }
  }

  if (-not $Passed -and $FailureEvidence.Ratio.Length -gt 0) {
    $WorstMemberRatio = $FailureEvidence.Ratio
  }

  $Rows.Add([pscustomobject]@{
    Factor = $Factor
    Passed = $Passed
    WorstRowsRatio = $WorstRowsRatio
    WorstMemberRatio = $WorstMemberRatio
    WorstPairRatio = $WorstPairRatio
    Failure = $FailureEvidence.Failure
    FailureLabel = $FailureEvidence.Label
    FailureLog = $FailureEvidence.Log
    Report = if (Test-Path -LiteralPath $SummaryPath) { "$FactorDirName/summary.md" } else { "-" }
    RunLog = "$FactorDirName/run.log"
  })
}

$Summary = Join-Path $OutDirPath "summary.md"
$Lines = New-Object System.Collections.Generic.List[string]
$Lines.Add("# Strong Memo Final-Active Member-Factor Sweep")
$Lines.Add("")
$Lines.Add("Generated: $(Get-Date -Format o)")
$Lines.Add("")
$Lines.Add("- Seeds: $Seeds")
$Lines.Add("- Random cases per seed: $RandomCases")
$Lines.Add("- Random depth/input length: $RandomDepth / $RandomInputLength")
$Lines.Add("- Rows budget: $RowsFactor * rsize(r)")
$Lines.Add("- Pair budget: $PairFactor * rsize(r)^2")
$Lines.Add("- Row-DAG universe budget: $RowDagUniverseFactor * rsize(r)")
$Lines.Add("- Minimum regex size: $MinRegexSize")
$Lines.Add("")
$Lines.Add("| Member factor | Result | Worst member ratio | Failure | Failure label | Report | Run log |")
$Lines.Add("| ---: | --- | ---: | --- | --- | --- | --- |")
foreach ($Row in $Rows) {
  $Result = if ($Row.Passed) { "pass" } else { "fail" }
  $Failure = if ($Row.Failure.Length -gt 0) { $Row.Failure.Replace("|", "\|") } else { "-" }
  $Label = if ($Row.FailureLabel.Length -gt 0) { $Row.FailureLabel.Replace("|", "\|") } else { "-" }
  $Lines.Add("| $($Row.Factor) | $Result | $($Row.WorstMemberRatio) | $Failure | $Label | $($Row.Report) | $($Row.RunLog) |")
}
$Lines.Add("")
$Lines.Add("A pass is smoke evidence only. A fail records a concrete budget counterexample")
$Lines.Add("from the seed log and rules out using that member factor as the current proof target.")

$Lines | Set-Content -LiteralPath $Summary -Encoding utf8
Write-Host "== Wrote member-factor sweep report to $OutDirPath =="
