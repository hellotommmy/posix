param(
  [int]$Depth = 2,
  [int]$InputLength = 3,
  [int]$MaxRegexes = 100000,
  [int]$RandomCases = 0,
  [int]$RandomDepth = 5,
  [int]$RandomInputLength = 6,
  [long]$Seed = 20260602,
  [string]$SeqMode = "full",
  [int]$Ch7K = 5,
  [string]$Ch7Lengths = "4,8,12,16,20",
  [int]$Ch7TreeThreshold = 1000,
  [int]$Ch7DagThreshold = 0,
  [int]$Ch7ShapeThreshold = 0,
  [switch]$SharedNoReassoc,
  [switch]$TraceStrong,
  [switch]$CheckStrong,
  [switch]$CheckStrongDeferred,
  [switch]$CheckStrongDeferredMemo,
  [switch]$TraceStrongSafe,
  [switch]$CheckStrongSafe,
  [switch]$TraceStrongRecon,
  [switch]$TraceStrongCore,
  [switch]$TraceStrongCoreLoop,
  [switch]$CheckStrongCoreCert,
  [switch]$CheckStrongCoreLoop,
  [switch]$FindStrongDirectCE,
  [switch]$FindStrongCoreCE,
  [switch]$FindRawInjectCE,
  [switch]$CheckStrongCoreHand,
  [switch]$SkipLegacyCubic,
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

$SharedNoReassocFlag = if ($SharedNoReassoc) { 1 } else { 0 }
$TraceStrongFlag = if ($TraceStrong) { 1 } else { 0 }
$CheckStrongFlag = if ($CheckStrong) { 1 } else { 0 }
$CheckStrongDeferredFlag = if ($CheckStrongDeferred) { 1 } else { 0 }
$CheckStrongDeferredMemoFlag = if ($CheckStrongDeferredMemo) { 1 } else { 0 }
$TraceStrongSafeFlag = if ($TraceStrongSafe) { 1 } else { 0 }
$CheckStrongSafeFlag = if ($CheckStrongSafe) { 1 } else { 0 }
$TraceStrongReconFlag = if ($TraceStrongRecon) { 1 } else { 0 }
$TraceStrongCoreFlag = if ($TraceStrongCore) { 1 } else { 0 }
$TraceStrongCoreLoopFlag = if ($TraceStrongCoreLoop) { 1 } else { 0 }
$CheckStrongCoreCertFlag = if ($CheckStrongCoreCert) { 1 } else { 0 }
$CheckStrongCoreLoopFlag = if ($CheckStrongCoreLoop) { 1 } else { 0 }
$FindStrongDirectCEFlag = if ($FindStrongDirectCE) { 1 } else { 0 }
$FindStrongCoreCEFlag = if ($FindStrongCoreCE) { 1 } else { 0 }
$FindRawInjectCEFlag = if ($FindRawInjectCE) { 1 } else { 0 }
$CheckStrongCoreHandFlag = if ($CheckStrongCoreHand) { 1 } else { 0 }
$SkipLegacyCubicFlag = if ($SkipLegacyCubic) { 1 } else { 0 }

Write-Host "== Scala cubic smoke: depth=$Depth input=$InputLength random=$RandomCases/$RandomDepth seed=$Seed seq=$SeqMode shared=$SharedNoReassocFlag skipLegacy=$SkipLegacyCubicFlag strong=$TraceStrongFlag checkStrong=$CheckStrongFlag checkStrongDeferred=$CheckStrongDeferredFlag checkStrongDeferredMemo=$CheckStrongDeferredMemoFlag strongSafe=$TraceStrongSafeFlag checkStrongSafe=$CheckStrongSafeFlag strongRecon=$TraceStrongReconFlag strongCore=$TraceStrongCoreFlag strongCoreLoopTrace=$TraceStrongCoreLoopFlag strongCoreCert=$CheckStrongCoreCertFlag strongCoreLoop=$CheckStrongCoreLoopFlag findStrongDirectCE=$FindStrongDirectCEFlag findCoreCE=$FindStrongCoreCEFlag findRawInjectCE=$FindRawInjectCEFlag handCore=$CheckStrongCoreHandFlag ch7=$Ch7K/$Ch7Lengths tree=$Ch7TreeThreshold dag=$Ch7DagThreshold shape=$Ch7ShapeThreshold =="
& $Bash -lc "cd '$RepoCyg' && timeout ${TimeoutSeconds}s env POSIX_SMOKE_DEPTH=$Depth POSIX_SMOKE_INPUT=$InputLength POSIX_SMOKE_MAX_REGEXES=$MaxRegexes POSIX_SMOKE_RANDOM_CASES=$RandomCases POSIX_SMOKE_RANDOM_DEPTH=$RandomDepth POSIX_SMOKE_RANDOM_INPUT=$RandomInputLength POSIX_SMOKE_SEED=$Seed POSIX_SMOKE_SEQ_MODE='$SeqMode' POSIX_SMOKE_SHARED_NO_REASSOC=$SharedNoReassocFlag POSIX_SMOKE_SKIP_LEGACY_CUBIC=$SkipLegacyCubicFlag POSIX_SMOKE_TRACE_STRONG=$TraceStrongFlag POSIX_SMOKE_CHECK_STRONG=$CheckStrongFlag POSIX_SMOKE_CHECK_STRONG_DEFERRED=$CheckStrongDeferredFlag POSIX_SMOKE_CHECK_STRONG_DEFERRED_MEMO=$CheckStrongDeferredMemoFlag POSIX_SMOKE_TRACE_STRONG_SAFE=$TraceStrongSafeFlag POSIX_SMOKE_CHECK_STRONG_SAFE=$CheckStrongSafeFlag POSIX_SMOKE_TRACE_STRONG_RECON=$TraceStrongReconFlag POSIX_SMOKE_TRACE_STRONG_CORE=$TraceStrongCoreFlag POSIX_SMOKE_TRACE_STRONG_CORE_LOOP=$TraceStrongCoreLoopFlag POSIX_SMOKE_CHECK_STRONG_CORE_CERT=$CheckStrongCoreCertFlag POSIX_SMOKE_CHECK_STRONG_CORE_LOOP=$CheckStrongCoreLoopFlag POSIX_SMOKE_FIND_STRONG_DIRECT_CE=$FindStrongDirectCEFlag POSIX_SMOKE_FIND_STRONG_CORE_CE=$FindStrongCoreCEFlag POSIX_SMOKE_FIND_RAW_INJECT_CE=$FindRawInjectCEFlag POSIX_SMOKE_CHECK_STRONG_CORE_HAND=$CheckStrongCoreHandFlag POSIX_SMOKE_CH7_K=$Ch7K POSIX_SMOKE_CH7_LENGTHS='$Ch7Lengths' POSIX_SMOKE_CH7_TREE_THRESHOLD=$Ch7TreeThreshold POSIX_SMOKE_CH7_DAG_THRESHOLD=$Ch7DagThreshold POSIX_SMOKE_CH7_SHAPE_THRESHOLD=$Ch7ShapeThreshold '$Isabelle' scala agent_hunt_pipeline/scala/PosixCubicSmoke.scala"
if ($LASTEXITCODE -ne 0) {
  if ($LASTEXITCODE -eq 124) {
    throw "Scala cubic smoke timed out after $TimeoutSeconds seconds"
  }
  throw "Scala cubic smoke failed with exit code $LASTEXITCODE"
}
