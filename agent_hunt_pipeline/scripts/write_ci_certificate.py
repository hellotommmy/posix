#!/usr/bin/env python3
"""Write an audit receipt after the local/remote Isabelle CI has passed."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path


INTERESTING_SUFFIXES = {".thy", ".md", ".py", ".ps1", ".sh", ".yml", ".yaml"}
INTERESTING_NAMES = {"ROOT", ".gitignore"}


def run(root: Path, args: list[str]) -> str:
    proc = subprocess.run(
        ["git", "-C", str(root), *args],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return proc.stdout.strip()


def git_list(root: Path, args: list[str]) -> list[str]:
    out = run(root, args)
    return [line for line in out.splitlines() if line]


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def include_file(path: str) -> bool:
    p = Path(path)
    return p.name in INTERESTING_NAMES or p.suffix in INTERESTING_SUFFIXES


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=".")
    parser.add_argument("--out", required=True)
    parser.add_argument("--session", action="append", default=[])
    parser.add_argument("--ci-name", default="local")
    parser.add_argument("--isabelle-version", default="")
    parser.add_argument("--isabelle-version-file")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    out_path = Path(args.out)
    if not out_path.is_absolute():
        out_path = root / out_path

    tracked = git_list(root, ["ls-files"])
    untracked = git_list(root, ["ls-files", "--others", "--exclude-standard"])
    files = sorted(path for path in {*tracked, *untracked} if include_file(path))

    version = args.isabelle_version
    if args.isabelle_version_file:
        version_file = Path(args.isabelle_version_file)
        if not version_file.is_absolute():
            version_file = root / version_file
        if version_file.exists():
            version = version_file.read_text(encoding="utf-8").strip()

    dirty = bool(run(root, ["status", "--porcelain"]))
    data = {
        "kind": "posix-backref-isabelle-ci-certificate",
        "ci_name": args.ci_name,
        "generated_utc": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "repo": str(root),
        "branch": run(root, ["rev-parse", "--abbrev-ref", "HEAD"]),
        "head": run(root, ["rev-parse", "HEAD"]),
        "dirty_worktree": dirty,
        "isabelle_version": version,
        "sessions": args.session,
        "status": "passed",
        "inputs": [
            {"path": path, "sha256": sha256(root / path)}
            for path in files
            if (root / path).is_file()
        ],
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"Wrote CI certificate: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
