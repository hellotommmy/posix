param(
  [switch]$SkipFetch,
  [switch]$PilotOnly,
  [switch]$NoCertificate,
  [ValidateSet("admin", "steward", "worker")]
  [string]$Role = "admin",
  [int]$BuildLockTimeoutSeconds = 7200,
  [int]$SessionTimeoutSeconds = 120
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
