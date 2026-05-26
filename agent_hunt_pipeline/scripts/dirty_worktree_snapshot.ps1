<#
.SYNOPSIS
  Save non-invasive snapshots of a dirty git worktree.

.DESCRIPTION
  This is a safety net for fragile GUI agent sessions. It never stages,
  commits, stashes, resets, checks out, pulls, pushes, or edits the target
  repository. When the target worktree is dirty, it writes a timestamped
  snapshot containing git status, a binary diff, recent HEAD, and copies of
  changed files into an ignored run directory.

.EXAMPLE
  powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/dirty_worktree_snapshot.ps1 -Once

.EXAMPLE
  powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/dirty_worktree_snapshot.ps1 -Background -PollSeconds 60
#>

param(
    [string]$RepoPath = "C:\Users\Chengsong\Documents\AIPV2026Notes\posix-opus",
    [string]$SnapshotDir = "",
    [string]$Label = "opus",
    [int]$PollSeconds = 60,
    [int]$MinIntervalSeconds = 120,
    [switch]$NoCopyFiles,
    [switch]$Once,
    [switch]$Background
)

$ErrorActionPreference = "Stop"

if ($Background) {
    $argsList = @(
        "-NoProfile", "-ExecutionPolicy", "Bypass",
        "-File", $PSCommandPath,
        "-RepoPath", $RepoPath,
        "-Label", $Label,
        "-PollSeconds", "$PollSeconds",
        "-MinIntervalSeconds", "$MinIntervalSeconds"
    )
    if ($SnapshotDir) { $argsList += @("-SnapshotDir", $SnapshotDir) }
    if ($NoCopyFiles) { $argsList += "-NoCopyFiles" }
    if ($Once) { $argsList += "-Once" }
    Start-Process -FilePath "powershell" -ArgumentList $argsList -WindowStyle Hidden | Out-Null
    Write-Host "Started dirty worktree snapshot watcher for $RepoPath"
    return
}

$script:Repo = (Resolve-Path -LiteralPath $RepoPath).Path
if (-not (Test-Path -LiteralPath (Join-Path $script:Repo ".git"))) {
    throw "RepoPath is not a git repository: $script:Repo"
}

if (-not $SnapshotDir) {
    $SnapshotDir = Join-Path $script:Repo "agent_hunt_pipeline\run\dirty_snapshots"
}
$script:SnapshotRoot = $SnapshotDir
New-Item -ItemType Directory -Path $script:SnapshotRoot -Force | Out-Null
$script:LogPath = Join-Path $script:SnapshotRoot "snapshot_watch.log"

function Write-SnapLog([string]$Message) {
    $line = "[$(Get-Date -Format "yyyy-MM-ddTHH:mm:ssK")] $Message"
    Write-Host $line
    Add-Content -LiteralPath $script:LogPath -Value $line -Encoding UTF8
}

function Invoke-GitLines {
    param([Parameter(ValueFromRemainingArguments = $true)][string[]]$GitArgs)
    $output = & git -C $script:Repo @GitArgs
    if ($LASTEXITCODE -ne 0) {
        throw "git $($GitArgs -join ' ') failed with exit code $LASTEXITCODE"
    }
    return @($output)
}

function Get-UntrackedMetadata {
    $items = Invoke-GitLines "ls-files" "-o" "--exclude-standard"
    $rows = foreach ($rel in $items) {
        $path = Join-Path $script:Repo $rel
        if (Test-Path -LiteralPath $path -PathType Leaf) {
            $item = Get-Item -LiteralPath $path
            "$rel|$($item.Length)|$($item.LastWriteTimeUtc.Ticks)"
        }
    }
    return @($rows)
}

function Get-DirtyFingerprint {
    $status = Invoke-GitLines "status" "--porcelain=v1"
    if ($status.Count -eq 0) {
        return $null
    }

    $diff = Invoke-GitLines "diff" "--binary" "--no-ext-diff" "HEAD" "--"
    $untracked = Get-UntrackedMetadata
    $combined = ($status + $diff + $untracked) -join "`n"
    $bytes = [System.Text.Encoding]::UTF8.GetBytes($combined)
    $sha = [System.Security.Cryptography.SHA256]::Create()
    try {
        return ([BitConverter]::ToString($sha.ComputeHash($bytes)) -replace "-", "").ToLowerInvariant()
    } finally {
        $sha.Dispose()
    }
}

function Copy-ChangedFiles([string]$DestinationRoot) {
    $tracked = Invoke-GitLines "diff" "--name-only" "HEAD" "--"
    $untracked = Invoke-GitLines "ls-files" "-o" "--exclude-standard"
    $paths = @($tracked + $untracked | Where-Object { $_ } | Sort-Object -Unique)
    foreach ($rel in $paths) {
        $src = Join-Path $script:Repo $rel
        if (-not (Test-Path -LiteralPath $src -PathType Leaf)) {
            continue
        }
        $dest = Join-Path $DestinationRoot $rel
        $destParent = Split-Path -Parent $dest
        New-Item -ItemType Directory -Path $destParent -Force | Out-Null
        Copy-Item -LiteralPath $src -Destination $dest -Force
    }
}

function Save-DirtySnapshot([string]$Fingerprint) {
    $branch = (Invoke-GitLines "branch" "--show-current" | Select-Object -First 1)
    $head = (Invoke-GitLines "rev-parse" "--short" "HEAD" | Select-Object -First 1)
    $timestamp = Get-Date -Format "yyyyMMdd_HHmmss"
    $dirName = "$timestamp-$Label-$branch-$head-$($Fingerprint.Substring(0, 12))" -replace '[\\/:*?"<>|]', '_'
    $snapshot = Join-Path $script:SnapshotRoot $dirName
    New-Item -ItemType Directory -Path $snapshot -Force | Out-Null

    Invoke-GitLines "status" "--short" "--branch" |
        Set-Content -LiteralPath (Join-Path $snapshot "status.txt") -Encoding UTF8
    Invoke-GitLines "log" "--oneline" "--decorate" "-5" |
        Set-Content -LiteralPath (Join-Path $snapshot "head.txt") -Encoding UTF8
    Invoke-GitLines "diff" "--stat" "HEAD" "--" |
        Set-Content -LiteralPath (Join-Path $snapshot "diffstat.txt") -Encoding UTF8

    $patch = Join-Path $snapshot "diff.patch"
    & git -C $script:Repo diff --binary --no-ext-diff --output="$patch" HEAD --
    if ($LASTEXITCODE -ne 0) {
        throw "git diff --output failed with exit code $LASTEXITCODE"
    }

    if (-not $NoCopyFiles) {
        Copy-ChangedFiles (Join-Path $snapshot "files")
    }

    [pscustomobject]@{
        time = (Get-Date).ToString("o")
        repo = $script:Repo
        branch = $branch
        head = $head
        fingerprint = $Fingerprint
        copiedFiles = -not $NoCopyFiles
    } | ConvertTo-Json |
        Set-Content -LiteralPath (Join-Path $snapshot "metadata.json") -Encoding UTF8

    Write-SnapLog "SNAPSHOT $snapshot"
}

$lastFingerprint = ""
$lastSnapshotTime = [DateTime]::MinValue
Write-SnapLog "Watcher boot: repo=$script:Repo; snapshots=$script:SnapshotRoot; poll=${PollSeconds}s"

while ($true) {
    $fingerprint = Get-DirtyFingerprint
    if (-not $fingerprint) {
        Write-SnapLog "clean worktree"
    } elseif ($fingerprint -eq $lastFingerprint -and ((Get-Date) - $lastSnapshotTime).TotalSeconds -lt $MinIntervalSeconds) {
        Write-SnapLog "dirty unchanged; snapshot suppressed"
    } else {
        Save-DirtySnapshot $fingerprint
        $lastFingerprint = $fingerprint
        $lastSnapshotTime = Get-Date
    }

    if ($Once) {
        break
    }
    Start-Sleep -Seconds $PollSeconds
}
