param(
  [switch]$SkipFetch,
  [switch]$PilotOnly,
  [switch]$NoCertificate,
  [switch]$SkipScalaSmoke,
  [ValidateSet("admin", "steward", "worker")]
  [string]$Role = "admin",
  [int]$BuildLockTimeoutSeconds = 7200,
  [int]$SessionTimeoutSeconds = 120,
  [int]$ScalaSmokeDepth = 2,
  [int]$ScalaSmokeInputLength = 3,
  [int]$ScalaSmokeMaxRegexes = 100000,
  [int]$ScalaSmokeRandomCases = 0,
  [int]$ScalaSmokeRandomDepth = 5,
  [int]$ScalaSmokeRandomInputLength = 6,
  [long]$ScalaSmokeSeed = 20260602,
  [string]$ScalaSmokeSeqMode = "full",
  [int]$ScalaSmokeCh7K = 5,
  [string]$ScalaSmokeCh7Lengths = "4,8,12,16,20",
  [int]$ScalaSmokeCh7TreeThreshold = 1000,
  [int]$ScalaSmokeCh7DagThreshold = 0,
  [int]$ScalaSmokeCh7ShapeThreshold = 0,
  [switch]$ScalaSmokeSharedNoReassoc,
  [switch]$ScalaSmokeCheckStrong,
  [switch]$ScalaSmokeCheckStrongDeferred,
  [switch]$ScalaSmokeCheckStrongDeferredMemo,
  [switch]$ScalaSmokeCheckStrongSafe,
  [switch]$ScalaSmokeTraceStrongRecon,
  [switch]$ScalaSmokeTraceStrongCore,
  [switch]$ScalaSmokeTraceStrongCoreLoop,
  [switch]$ScalaSmokeCheckStrongCoreCert,
  [switch]$ScalaSmokeCheckStrongCoreLoop,
  [switch]$ScalaSmokeFindStrongDirectCE,
  [switch]$ScalaSmokeFindStrongCoreCE,
  [switch]$ScalaSmokeFindRawInjectCE,
  [switch]$ScalaSmokeCheckStrongCoreHand,
  [switch]$ScalaSmokeSkipLegacyCubic
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
$BuildMutexName = "Global\AIPV2026Notes_POSIX_BackRef_Isabelle_Build"
$BuildMutex = $null
$BuildLockTaken = $false

Set-Location -LiteralPath $Repo

if (-not $SkipFetch) {
  git fetch --all --prune
}

git status --short --branch

python agent_hunt_pipeline/scripts/backref_no_cheat_guard.py --root $Repo
python agent_hunt_pipeline/scripts/backref_bounty_guard.py --file BACKREF_BOUNTIES.md
python agent_hunt_pipeline/scripts/backref_role_guard.py --role $Role

$Sessions = @()
if (-not $PilotOnly) {
  $Sessions += @{ Name = "Posix"; Args = "-v -d . Posix" }
}
$Sessions += @{ Name = "BackRefPilot"; Args = "-v -d pilot BackRefPilot" }

try {
  Write-Host "== Waiting for Isabelle build lock: $BuildMutexName =="
  $BuildMutex = [System.Threading.Mutex]::new($false, $BuildMutexName)
  $BuildLockTaken = $BuildMutex.WaitOne([TimeSpan]::FromSeconds($BuildLockTimeoutSeconds))
  if (-not $BuildLockTaken) {
    throw "Timed out waiting for Isabelle build lock after $BuildLockTimeoutSeconds seconds"
  }
  Write-Host "== Acquired Isabelle build lock =="

  if (-not $PilotOnly -and -not $SkipScalaSmoke) {
    $SharedNoReassocFlag = if ($ScalaSmokeSharedNoReassoc) { 1 } else { 0 }
    $CheckStrongFlag = if ($ScalaSmokeCheckStrong) { 1 } else { 0 }
    $CheckStrongDeferredFlag = if ($ScalaSmokeCheckStrongDeferred) { 1 } else { 0 }
    $CheckStrongDeferredMemoFlag = if ($ScalaSmokeCheckStrongDeferredMemo) { 1 } else { 0 }
    $CheckStrongSafeFlag = if ($ScalaSmokeCheckStrongSafe) { 1 } else { 0 }
    $TraceStrongReconFlag = if ($ScalaSmokeTraceStrongRecon) { 1 } else { 0 }
    $TraceStrongCoreFlag = if ($ScalaSmokeTraceStrongCore) { 1 } else { 0 }
    $TraceStrongCoreLoopFlag = if ($ScalaSmokeTraceStrongCoreLoop) { 1 } else { 0 }
    $CheckStrongCoreCertFlag = if ($ScalaSmokeCheckStrongCoreCert) { 1 } else { 0 }
    $CheckStrongCoreLoopFlag = if ($ScalaSmokeCheckStrongCoreLoop) { 1 } else { 0 }
    $FindStrongDirectCEFlag = if ($ScalaSmokeFindStrongDirectCE) { 1 } else { 0 }
    $FindStrongCoreCEFlag = if ($ScalaSmokeFindStrongCoreCE) { 1 } else { 0 }
    $FindRawInjectCEFlag = if ($ScalaSmokeFindRawInjectCE) { 1 } else { 0 }
    $CheckStrongCoreHandFlag = if ($ScalaSmokeCheckStrongCoreHand) { 1 } else { 0 }
    $SkipLegacyCubicFlag = if ($ScalaSmokeSkipLegacyCubic) { 1 } else { 0 }
    Write-Host "== Scala cubic smoke: depth=$ScalaSmokeDepth input=$ScalaSmokeInputLength random=$ScalaSmokeRandomCases/$ScalaSmokeRandomDepth seed=$ScalaSmokeSeed seq=$ScalaSmokeSeqMode shared=$SharedNoReassocFlag skipLegacy=$SkipLegacyCubicFlag checkStrong=$CheckStrongFlag checkStrongDeferred=$CheckStrongDeferredFlag checkStrongDeferredMemo=$CheckStrongDeferredMemoFlag checkStrongSafe=$CheckStrongSafeFlag strongRecon=$TraceStrongReconFlag strongCore=$TraceStrongCoreFlag strongCoreLoopTrace=$TraceStrongCoreLoopFlag strongCoreCert=$CheckStrongCoreCertFlag strongCoreLoop=$CheckStrongCoreLoopFlag findStrongDirectCE=$FindStrongDirectCEFlag findCoreCE=$FindStrongCoreCEFlag findRawInjectCE=$FindRawInjectCEFlag handCore=$CheckStrongCoreHandFlag ch7=$ScalaSmokeCh7K/$ScalaSmokeCh7Lengths tree=$ScalaSmokeCh7TreeThreshold dag=$ScalaSmokeCh7DagThreshold shape=$ScalaSmokeCh7ShapeThreshold =="
    & $Bash -lc "cd '$RepoCyg' && timeout ${SessionTimeoutSeconds}s env POSIX_SMOKE_DEPTH=$ScalaSmokeDepth POSIX_SMOKE_INPUT=$ScalaSmokeInputLength POSIX_SMOKE_MAX_REGEXES=$ScalaSmokeMaxRegexes POSIX_SMOKE_RANDOM_CASES=$ScalaSmokeRandomCases POSIX_SMOKE_RANDOM_DEPTH=$ScalaSmokeRandomDepth POSIX_SMOKE_RANDOM_INPUT=$ScalaSmokeRandomInputLength POSIX_SMOKE_SEED=$ScalaSmokeSeed POSIX_SMOKE_SEQ_MODE='$ScalaSmokeSeqMode' POSIX_SMOKE_SHARED_NO_REASSOC=$SharedNoReassocFlag POSIX_SMOKE_SKIP_LEGACY_CUBIC=$SkipLegacyCubicFlag POSIX_SMOKE_CHECK_STRONG=$CheckStrongFlag POSIX_SMOKE_CHECK_STRONG_DEFERRED=$CheckStrongDeferredFlag POSIX_SMOKE_CHECK_STRONG_DEFERRED_MEMO=$CheckStrongDeferredMemoFlag POSIX_SMOKE_CHECK_STRONG_SAFE=$CheckStrongSafeFlag POSIX_SMOKE_TRACE_STRONG_RECON=$TraceStrongReconFlag POSIX_SMOKE_TRACE_STRONG_CORE=$TraceStrongCoreFlag POSIX_SMOKE_TRACE_STRONG_CORE_LOOP=$TraceStrongCoreLoopFlag POSIX_SMOKE_CHECK_STRONG_CORE_CERT=$CheckStrongCoreCertFlag POSIX_SMOKE_CHECK_STRONG_CORE_LOOP=$CheckStrongCoreLoopFlag POSIX_SMOKE_FIND_STRONG_DIRECT_CE=$FindStrongDirectCEFlag POSIX_SMOKE_FIND_STRONG_CORE_CE=$FindStrongCoreCEFlag POSIX_SMOKE_FIND_RAW_INJECT_CE=$FindRawInjectCEFlag POSIX_SMOKE_CHECK_STRONG_CORE_HAND=$CheckStrongCoreHandFlag POSIX_SMOKE_CH7_K=$ScalaSmokeCh7K POSIX_SMOKE_CH7_LENGTHS='$ScalaSmokeCh7Lengths' POSIX_SMOKE_CH7_TREE_THRESHOLD=$ScalaSmokeCh7TreeThreshold POSIX_SMOKE_CH7_DAG_THRESHOLD=$ScalaSmokeCh7DagThreshold POSIX_SMOKE_CH7_SHAPE_THRESHOLD=$ScalaSmokeCh7ShapeThreshold '$Isabelle' scala agent_hunt_pipeline/scala/PosixCubicSmoke.scala"
    if ($LASTEXITCODE -ne 0) {
      if ($LASTEXITCODE -eq 124) {
        throw "Scala cubic smoke timed out after $SessionTimeoutSeconds seconds"
      }
      throw "Scala cubic smoke failed with exit code $LASTEXITCODE"
    }
  }

  foreach ($Session in $Sessions) {
    Write-Host "== Isabelle build: $($Session.Name) =="
    & $Bash -lc "cd '$RepoCyg' && timeout ${SessionTimeoutSeconds}s '$Isabelle' build $($Session.Args)"
    if ($LASTEXITCODE -ne 0) {
      if ($LASTEXITCODE -eq 124) {
        throw "Isabelle build timed out for $($Session.Name) after $SessionTimeoutSeconds seconds"
      }
      throw "Isabelle build failed for $($Session.Name) with exit code $LASTEXITCODE"
    }
  }
} finally {
  if ($BuildLockTaken -and $null -ne $BuildMutex) {
    $BuildMutex.ReleaseMutex()
    Write-Host "== Released Isabelle build lock =="
  }
  if ($null -ne $BuildMutex) {
    $BuildMutex.Dispose()
  }
}

if (-not $NoCertificate) {
  $Version = (& $Bash -lc "'$Isabelle' version") -join "`n"
  $Out = "agent_hunt_pipeline/certificates/local_ci_certificate.json"
  $CertArgs = @(
    "agent_hunt_pipeline/scripts/write_ci_certificate.py",
    "--root", $Repo,
    "--out", $Out,
    "--ci-name", "local-powershell",
    "--isabelle-version", $Version
  )
  foreach ($Session in $Sessions) {
    $CertArgs += @("--session", $Session.Name)
  }
  python @CertArgs
}
