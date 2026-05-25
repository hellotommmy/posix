param(
  [switch]$SkipFetch,
  [switch]$PilotOnly,
  [switch]$NoCertificate,
  [ValidateSet("admin", "steward", "worker")]
  [string]$Role = "admin"
)

$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$Ci = Join-Path $ScriptDir "isabelle_ci.ps1"

$Args = @("-ExecutionPolicy", "Bypass", "-File", $Ci, "-Role", $Role)
if ($SkipFetch) { $Args += "-SkipFetch" }
if ($PilotOnly) { $Args += "-PilotOnly" }
if ($NoCertificate) { $Args += "-NoCertificate" }

powershell @Args
