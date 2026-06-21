<#
  Isolated build for the Route-2 / N-route lane.

  The norm lane uses a PRIVATE Isabelle store (USER_HOME=norm-home) so its build of
  the base session never collides with the primary route's shared Posix_Base
  (two worktrees writing the same session name into one store => SQLITE_CONSTRAINT,
  the documented hazard). Pure/HOL load from the read-only distribution heaps;
  HOL-Library + Posix_Base live in the private store (seed once by copying the shared
  heaps, then cached). Run from anywhere:

      cubic\Normalized\build-norm.ps1            # builds Posix_Norm
      cubic\Normalized\build-norm.ps1 -Session Posix_NormBase
#>
param([string]$Session = 'Posix_Norm', [int]$TimeoutSeconds = 360)
$ErrorActionPreference = 'Stop'

# worktree root = two levels up from this script (cubic/Normalized/)
$Repo = Split-Path -Parent (Split-Path -Parent $PSScriptRoot)
$IsabelleHome = 'C:\Users\Chengsong\Isabelle2025-2'
$Bash = Join-Path $IsabelleHome 'contrib\cygwin\bin\bash.exe'
$PrivateHome = 'C:\Users\Chengsong\Documents\norm-home-codex'

function Convert-ToCygPath([string]$Path) {
  $Full = (Resolve-Path -LiteralPath $Path).Path
  $Drive = $Full.Substring(0, 1).ToLowerInvariant()
  "/cygdrive/$Drive$($Full.Substring(2).Replace('\','/'))"
}

$RepoCyg = Convert-ToCygPath $Repo
$HomeCyg = Convert-ToCygPath $PrivateHome
$IsaCyg  = Convert-ToCygPath $IsabelleHome
$cmd = "export USER_HOME='$HomeCyg'; cd '$RepoCyg' && timeout ${TimeoutSeconds}s '$IsaCyg/bin/isabelle' build -d . $Session"
& $Bash -lc $cmd
exit $LASTEXITCODE
