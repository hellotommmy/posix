param(
  # Session to build. Default = the fast active leaf (loads the Posix_Base heap image;
  # recompiles only AntimirovFactoredTransition + AntimirovNormalFrontier, ~47s).
  #   -Session Posix_Antimirov : the cubic-bound lane (default)
  #   -Session Posix_Base       : (re)build the frozen base heap image (rarely; auto -b)
  [string]$Session = 'Posix_Antimirov',
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

# Base sessions persist a heap image (-b) so leaf sessions load them without
# re-elaboration. Leaf/active sessions do not need -b.
$HeapFlag = ''
if ($Session -like '*_Base') { $HeapFlag = '-b ' }

$BuildCommand = "cd '$RepoCyg' && timeout ${BoundedTimeout}s '$IsabelleCyg/bin/isabelle' build ${HeapFlag}-v -d . $Session"

# Per-session mutex: same-session builds serialize (heap-safe); different
# sessions/lanes build concurrently.
$BuildMutexName = "Global\AIPV2026Notes_POSIX_BackRef_Isabelle_Build_$Session"
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

  Write-Host "Acquired Isabelle build lock for session: $Session"
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
