param(
  [int]$Depth = 2,
  [int]$InputLength = 3,
  [int]$MaxRegexes = 100000,
  [int]$RandomCases = 2000,
  [int]$RandomDepth = 7,
  [int]$RandomInputLength = 8,
  [long]$Seed = 20260602,
  [string]$Ch7Lengths = "4,8,12,16,20,24,28,32,40,48,64,80",
  [double]$FinalActiveRowDagFactor = 3.0,
  [double]$FinalActiveComponentUnionFactor = 3.0,
  [double]$FinalActiveDecompBoundFactor = 3.0,
  [int]$FinalActiveTop = 5,
  [int]$TimeoutSeconds = 300
)

$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$Smoke = Join-Path $ScriptDir "scala_cubic_smoke.ps1"

& $Smoke `
  -Route strong-memo `
  -Depth $Depth `
  -InputLength $InputLength `
  -MaxRegexes $MaxRegexes `
  -RandomCases $RandomCases `
  -RandomDepth $RandomDepth `
  -RandomInputLength $RandomInputLength `
  -Seed $Seed `
  -Ch7K 5 `
  -Ch7Lengths $Ch7Lengths `
  -Ch7TreeThreshold 0 `
  -StrongFinalActiveRowDagUniverseFactor $FinalActiveRowDagFactor `
  -StrongFinalActiveComponentUnionFactor $FinalActiveComponentUnionFactor `
  -StrongFinalActiveDecompBoundFactor $FinalActiveDecompBoundFactor `
  -StrongFinalActiveTop $FinalActiveTop `
  -TimeoutSeconds $TimeoutSeconds
