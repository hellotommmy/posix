#!/usr/bin/env python3
"""Enforce immutability of frozen definition and theorem statements.

Compares current Isabelle theory files against a frozen snapshot directory.
Frozen statements (definitions, lemmas, theorems, etc.) must not be modified
or deleted. Proof bodies may change freely. New content after frozen content
is allowed.

This implements the Agent Hunt paper's statement immutability mechanism:
agents cannot change existing definitions/theorem statements to game the
bounty system.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


STATEMENT_RE = re.compile(
    r"^(lemma|theorem|corollary|proposition|definition|fun|primrec|"
    r"abbreviation|inductive|datatype|type_synonym)\b"
)

PROOF_END_RE = re.compile(r"^\s*(done|qed|by\b|oops|sorry)\b")


def extract_statements(text: str) -> dict[str, str]:
    """Extract named statement blocks (header only, not proof body)."""
    statements: dict[str, str] = {}
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        m = STATEMENT_RE.match(line)
        if m:
            keyword = m.group(1)
            block_lines = [lines[i]]
            name_match = re.search(
                rf"{re.escape(keyword)}\s+(\w+)", line
            )
            name = name_match.group(1) if name_match else f"_anon_{i}"

            j = i + 1
            if keyword in ("lemma", "theorem", "corollary", "proposition"):
                while j < len(lines):
                    stripped = lines[j].strip()
                    block_lines.append(lines[j])
                    if stripped.startswith('"') or stripped.startswith('\\"'):
                        if stripped.endswith('"') or stripped.endswith('\\"'):
                            break
                    if PROOF_END_RE.match(stripped):
                        block_lines.pop()
                        break
                    if stripped == "" and j > i + 1:
                        break
                    j += 1
            elif keyword in ("fun", "primrec", "definition", "abbreviation"):
                while j < len(lines):
                    stripped = lines[j].strip()
                    if stripped == "" or STATEMENT_RE.match(stripped):
                        break
                    block_lines.append(lines[j])
                    j += 1
            elif keyword in ("inductive", "datatype", "type_synonym"):
                while j < len(lines):
                    stripped = lines[j].strip()
                    if stripped == "" or STATEMENT_RE.match(stripped):
                        break
                    block_lines.append(lines[j])
                    j += 1

            statement_text = "\n".join(block_lines).rstrip()
            statements[name] = statement_text
            i = j
        else:
            i += 1
    return statements


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Check frozen Isabelle statements for immutability."
    )
    parser.add_argument(
        "--snapshot-dir",
        default="agent_hunt_pipeline/snapshots",
        help="Directory containing frozen .thy snapshots",
    )
    parser.add_argument(
        "--files",
        nargs="*",
        default=["BackRefLang.thy", "BackRefValues.thy"],
        help="Theory files to check against snapshots",
    )
    parser.add_argument(
        "--create-snapshot",
        action="store_true",
        help="Create frozen snapshots from current theory files",
    )
    args = parser.parse_args()

    snapshot_dir = Path(args.snapshot_dir)
    errors: list[str] = []

    if args.create_snapshot:
        snapshot_dir.mkdir(parents=True, exist_ok=True)
        for filename in args.files:
            src = Path(filename)
            if src.exists():
                dst = snapshot_dir / filename
                dst.write_text(src.read_text(encoding="utf-8"), encoding="utf-8")
                print(f"Snapshot created: {dst}")
            else:
                print(f"SKIP: {filename} does not exist")
        return 0

    if not snapshot_dir.exists():
        print(f"SKIP: snapshot directory {snapshot_dir} does not exist yet")
        print("Create snapshots with: backref_statement_guard.py --create-snapshot")
        return 0

    for filename in args.files:
        current_path = Path(filename)
        snapshot_path = snapshot_dir / filename
        if not snapshot_path.exists():
            continue
        if not current_path.exists():
            errors.append(f"{filename}: file deleted but snapshot exists")
            continue

        frozen = extract_statements(snapshot_path.read_text(encoding="utf-8"))
        current = extract_statements(current_path.read_text(encoding="utf-8"))

        for name, frozen_text in frozen.items():
            if name not in current:
                errors.append(f"{filename}: frozen statement {name!r} was deleted")
            elif current[name] != frozen_text:
                errors.append(f"{filename}: frozen statement {name!r} was modified")

    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    checked = sum(1 for f in args.files if (snapshot_dir / f).exists())
    print(f"OK: {checked} frozen theory files checked, no statement modifications")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
