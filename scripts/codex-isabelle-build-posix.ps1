param(
  [int]$TimeoutSeconds = 300,
  [int]$BuildLockTimeoutSeconds = 1800
)

$ErrorActionPreference = 'Stop'

$Repo = Split-Path -Parent $PSScriptRoot
$IsabelleHome = 'C:\Users\Chengsong\Isabelle2025-2'
$Bash = Join-Path $IsabelleHome 'contrib\cygwin\bin\bash.exe'

function Convert-ToCygPath([string]$Path) {
  $Full = (Resolve-Path -LiteralPath $Path).Path
  $Drive = $Full.Substring(0, 1).ToLowerInvariant()
  $Rest = $Full.Substring(2).Replace('\', '/')
  "/cygdrive/$Drive$Rest"
}

$RepoCyg = Convert-ToCygPath $Repo
$IsabelleCyg = Convert-ToCygPath $IsabelleHome
$BoundedTimeout = [Math]::Max(1, $TimeoutSeconds)
$BoundedBuildLockTimeout = [Math]::Max(1, $BuildLockTimeoutSeconds)
$BuildCommand = "cd '$RepoCyg' && timeout ${BoundedTimeout}s '$IsabelleCyg/bin/isabelle' build -v -d . Posix"
$BuildMutexName = 'Global\AIPV2026Notes_POSIX_BackRef_Isabelle_Build'
$BuildMutex = $null
$BuildLockTaken = $false
$ExitCode = 1

try {
  Write-Host "Waiting for Isabelle build lock: $BuildMutexName"
  $BuildMutex = [System.Threading.Mutex]::new($false, $BuildMutexName)
  try {
    $BuildLockTaken = $BuildMutex.WaitOne([TimeSpan]::FromSeconds($BoundedBuildLockTimeout))
  } catch [System.Threading.AbandonedMutexException] {
    Write-Host 'Acquired abandoned Isabelle build lock.'
    $BuildLockTaken = $true
  }

  if (-not $BuildLockTaken) {
    throw "Timed out waiting for Isabelle build lock after $BoundedBuildLockTimeout seconds"
  }

  Write-Host 'Acquired Isabelle build lock.'
  & $Bash -lc $BuildCommand
  $ExitCode = $LASTEXITCODE
} finally {
  if ($BuildLockTaken -and $null -ne $BuildMutex) {
    $BuildMutex.ReleaseMutex()
    Write-Host 'Released Isabelle build lock.'
  }
  if ($null -ne $BuildMutex) {
    $BuildMutex.Dispose()
  }
}

exit $ExitCode
