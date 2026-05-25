#!/usr/bin/env python3
"""Check changed files against a coarse POSIX backref agent role."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


WORKER_ALLOWED = {
    "BackRefValues.thy",
    "PROGRESS_BACKREF.md",
    "BACKREF_BOUNTIES.md",
}

WORKER_PREFIXES = (
    "agent_hunt_pipeline/scripts/",
)

STEWARD_BLOCKED = {
    "Blexer.thy",
    "BlexerSimp.thy",
    "FBound.thy",
    "GeneralRegexBound.thy",
    "ClosedForms.thy",
    "ClosedFormsBounds.thy",
}


def changed_files() -> list[str]:
    proc = subprocess.run(
        ["git", "status", "--short"],
        text=True,
        check=True,
        stdout=subprocess.PIPE,
    )
    files: list[str] = []
    for line in proc.stdout.splitlines():
        if not line:
            continue
        path = line[3:].strip()
        if " -> " in path:
            path = path.split(" -> ", 1)[1]
        files.append(path.replace("\\", "/"))
    return files


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--role", choices=["worker", "steward", "admin"], required=True)
    args = parser.parse_args()

    files = changed_files()
    errors: list[str] = []

    if args.role == "worker":
        for path in files:
            if path in WORKER_ALLOWED:
                continue
            if any(path.startswith(prefix) for prefix in WORKER_PREFIXES):
                continue
            errors.append(f"worker may not edit {path}")

    if args.role == "steward":
        for path in files:
            if Path(path).name in STEWARD_BLOCKED:
                errors.append(f"steward must not edit blocked file {path}")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    print(f"OK: role {args.role} permits {len(files)} changed files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

