param(
  [int]$Depth = 2,
  [int]$InputLength = 3,
  [int]$MaxRegexes = 100000,
  [int]$RandomCases = 0,
  [int]$RandomDepth = 5,
  [int]$RandomInputLength = 6,
  [long]$Seed = 20260602,
  [string]$SeqMode = "full",
  [int]$TimeoutSeconds = 120
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

$RepoCyg = Convert-ToCygwinPath $Repo
$IsabelleCyg = Convert-ToCygwinPath $IsabelleHome
$Isabelle = "$IsabelleCyg/bin/isabelle"

Set-Location -LiteralPath $Repo

Write-Host "== Scala cubic smoke: depth=$Depth input=$InputLength random=$RandomCases/$RandomDepth seed=$Seed seq=$SeqMode =="
& $Bash -lc "cd '$RepoCyg' && timeout ${TimeoutSeconds}s env POSIX_SMOKE_DEPTH=$Depth POSIX_SMOKE_INPUT=$InputLength POSIX_SMOKE_MAX_REGEXES=$MaxRegexes POSIX_SMOKE_RANDOM_CASES=$RandomCases POSIX_SMOKE_RANDOM_DEPTH=$RandomDepth POSIX_SMOKE_RANDOM_INPUT=$RandomInputLength POSIX_SMOKE_SEED=$Seed POSIX_SMOKE_SEQ_MODE='$SeqMode' '$Isabelle' scala agent_hunt_pipeline/scala/PosixCubicSmoke.scala"
if ($LASTEXITCODE -ne 0) {
  if ($LASTEXITCODE -eq 124) {
    throw "Scala cubic smoke timed out after $TimeoutSeconds seconds"
  }
  throw "Scala cubic smoke failed with exit code $LASTEXITCODE"
}
