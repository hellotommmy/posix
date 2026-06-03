param(
  [string]$Ks = "3,5,8",
  [int]$MaxN = 30,
  [int]$Step = 1,
  [string]$Lengths = "",
  [string]$Metrics = "strongTree,cubicTree,sharedShapeStatePool,langContPruneShapeStatePool",
  [string]$SeqMode = "unary-cover-no-reassoc",
  [string]$OutDir = "agent_hunt_pipeline/reports/ch7_size_grid",
  [switch]$LogY,
  [int]$TimeoutSeconds = 600
)

$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$Repo = Resolve-Path (Join-Path $ScriptDir "..\..")
$Repo = $Repo.Path
$IsabelleHome = if ($env:ISABELLE_HOME) { $env:ISABELLE_HOME } else { "C:\Users\Chengsong\Isabelle2025-2" }
$Bash = Join-Path $IsabelleHome "contrib\cygwin\bin\bash.exe"

function Convert-ToCygwinPath([string]$Path) {
  $Full = (Resolve-Path -LiteralPath $Path).Path
  $Drive = $Full.Substring(0, 1).ToLowerInvariant()
  $Rest = $Full.Substring(2).Replace("\", "/")
  return "/cygdrive/$Drive$Rest"
}

if (-not (Test-Path -LiteralPath $Bash)) {
  throw "Cannot find Isabelle bundled bash at $Bash. Set ISABELLE_HOME if Isabelle moved."
}

if ($Step -le 0) {
  throw "Step must be positive."
}

Set-Location -LiteralPath $Repo

$OutDirPath = Join-Path $Repo $OutDir
New-Item -ItemType Directory -Force -Path $OutDirPath | Out-Null

if ($Lengths.Trim().Length -eq 0) {
  $LengthList = (0..$MaxN | Where-Object { ($_ % $Step) -eq 0 }) -join ","
} else {
  $LengthList = $Lengths
}

$CsvRel = (Join-Path $OutDir "ch7_size_grid.csv").Replace("\", "/")
$IsabelleCyg = Convert-ToCygwinPath $IsabelleHome
$RepoCyg = Convert-ToCygwinPath $Repo
$Isabelle = "$IsabelleCyg/bin/isabelle"

Write-Host "== Chapter 7 size grid: ks=$Ks lengths=$LengthList metrics=$Metrics seq=$SeqMode out=$CsvRel =="
& $Bash -lc "cd '$RepoCyg' && timeout ${TimeoutSeconds}s env POSIX_SMOKE_SEQ_MODE='$SeqMode' POSIX_SMOKE_CH7_SIZE_CSV='$CsvRel' POSIX_SMOKE_CH7_SIZE_KS='$Ks' POSIX_SMOKE_CH7_SIZE_LENGTHS='$LengthList' POSIX_SMOKE_CH7_SIZE_METRICS='$Metrics' '$Isabelle' scala agent_hunt_pipeline/scala/PosixCubicSmoke.scala"
if ($LASTEXITCODE -ne 0) {
  if ($LASTEXITCODE -eq 124) {
    throw "Chapter 7 size-grid Scala run timed out after $TimeoutSeconds seconds"
  }
  throw "Chapter 7 size-grid Scala run failed with exit code $LASTEXITCODE"
}

$CsvAbs = Join-Path $Repo $CsvRel
$PlotArgs = @(
  "agent_hunt_pipeline/scripts/plot_ch7_size_grid.py",
  "--csv", $CsvAbs,
  "--out-dir", $OutDirPath,
  "--title-prefix", "Chapter 7 derivative size"
)
if ($LogY) {
  $PlotArgs += "--log-y"
}

python @PlotArgs
if ($LASTEXITCODE -ne 0) {
  throw "Chapter 7 SVG plotting failed with exit code $LASTEXITCODE"
}

Write-Host "== Wrote Chapter 7 size grid to $OutDirPath =="
