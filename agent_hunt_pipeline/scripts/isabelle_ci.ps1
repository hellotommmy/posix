param(
  [switch]$SkipFetch,
  [switch]$PilotOnly,
  [switch]$NoCertificate,
  [ValidateSet("admin", "steward", "worker")]
  [string]$Role = "admin"
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

foreach ($Session in $Sessions) {
  Write-Host "== Isabelle build: $($Session.Name) =="
  & $Bash -lc "cd '$RepoCyg' && '$Isabelle' build $($Session.Args)"
  if ($LASTEXITCODE -ne 0) {
    throw "Isabelle build failed for $($Session.Name) with exit code $LASTEXITCODE"
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
