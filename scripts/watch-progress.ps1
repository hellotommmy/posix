# watch-progress.ps1 - one-shot digest of what the agents did recently.
# Usage:  powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\watch-progress.ps1 [-Hours 3]
# Prints: live workers, commit cadence, new checked lemmas, new PROGRESS
# entries, and uncommitted worktree state. Read this instead of agent UIs.

param([double]$Hours = 3)

$repo = Split-Path $PSScriptRoot -Parent
Set-Location $repo
$since = (Get-Date).AddHours(-$Hours).ToString('yyyy-MM-dd HH:mm:ss')

Write-Host "=== Agent activity digest for the last $Hours h (since $since) ===" -ForegroundColor Cyan

Write-Host "`n--- 1. Live proof workers" -ForegroundColor Yellow
& powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $PSScriptRoot 'codex-proof-workers.ps1') -Action Check

Write-Host "`n--- 2. Commits (newest first)" -ForegroundColor Yellow
$commits = git log --pretty=format:"%h|%ad|%s" --date=format:"%H:%M" --since="$since" 2>$null
if (-not $commits) {
    Write-Host "  (none in window - check a longer -Hours or whether agents stalled)"
} else {
    $commits | ForEach-Object {
        $p = $_ -split '\|', 3
        Write-Host ("  {0}  {1}  {2}" -f $p[1], $p[0], $p[2])
    }
    Write-Host ("  total: {0} commits" -f @($commits).Count)
}

$base = git rev-list -1 --before="$since" HEAD 2>$null
if ($base) {
    Write-Host "`n--- 3. Files changed in window" -ForegroundColor Yellow
    git diff --stat "$base..HEAD" | Select-Object -Last 12 | ForEach-Object { "  $_" }

    Write-Host "`n--- 4. New checked lemmas/theorems landed" -ForegroundColor Yellow
    $lemmas = git diff "$base..HEAD" -- '*.thy' | Select-String '^\+\s*(lemma|theorem)\s+([A-Za-z0-9_]+)' |
        ForEach-Object { $_.Matches[0].Groups[2].Value } | Select-Object -Unique
    if ($lemmas) { $lemmas | ForEach-Object { "  $_" } } else { Write-Host "  (none)" }

    Write-Host "`n--- 5. New PROGRESS entries (plain-language log)" -ForegroundColor Yellow
    $entries = git diff "$base..HEAD" -- PROGRESS_BACKREF.md | Select-String '^\+## ' |
        ForEach-Object { $_.Line.Substring(1) }
    if ($entries) { $entries | ForEach-Object { "  $_" } } else { Write-Host "  (none)" }
} else {
    Write-Host "`n  (no commit older than the window - showing nothing for sections 3-5)"
}

Write-Host "`n--- 6. Uncommitted worktree state (agents' in-flight edits)" -ForegroundColor Yellow
$st = git status --short
if ($st) { $st | ForEach-Object { "  $_" } } else { Write-Host "  clean" }

Write-Host "`nDetails: 'git show <hash>' for exact line diffs; PROGRESS_BACKREF.md tail for the narrative." -ForegroundColor Cyan
