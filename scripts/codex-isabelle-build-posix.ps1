param(
  [int]$TimeoutSeconds = 300
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
$BuildCommand = "cd '$RepoCyg' && timeout ${BoundedTimeout}s '$IsabelleCyg/bin/isabelle' build -v -d . Posix"

& $Bash -lc $BuildCommand
exit $LASTEXITCODE
