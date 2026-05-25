#!/usr/bin/env python3
"""Idle re-prompt helper for long-running CLI agents.

Modes:
- tmux mode captures a pane and sends a prompt when unchanged.
- cwd mode snapshots repository/directory state and prints or sends a prompt
  when unchanged across two checks.

Use --once --dry-run to test without sending anything to an agent.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


def run(cmd: list[str], cwd: Path | None = None) -> str:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return proc.stdout


def prompt_text(path: Path) -> str:
    return " ".join(path.read_text(encoding="utf-8").split())


def tmux_capture(target: str) -> str:
    return run(["tmux", "capture-pane", "-t", target, "-p", "-S", "-200"])


def cwd_snapshot(cwd: Path) -> str:
    parts: list[str] = []
    if (cwd / ".git").exists():
        parts.append(run(["git", "status", "--short", "--branch"], cwd=cwd))
        parts.append(run(["git", "rev-parse", "HEAD"], cwd=cwd))
    else:
        for path in sorted(cwd.rglob("*")):
            if path.is_file():
                try:
                    stat = path.stat()
                except OSError:
                    continue
                rel = path.relative_to(cwd).as_posix()
                parts.append(f"{rel}\t{stat.st_size}\t{int(stat.st_mtime)}")
    return "\n".join(parts)


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def send_tmux(target: str, prompt: str) -> None:
    subprocess.run(["tmux", "send-keys", "-t", target, prompt], check=True)
    time.sleep(2)
    subprocess.run(["tmux", "send-keys", "-t", target, "Enter"], check=True)


def load_state(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    return json.loads(path.read_text(encoding="utf-8"))


def save_state(path: Path, state: dict[str, str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(state, indent=2, sort_keys=True), encoding="utf-8")


def once(args: argparse.Namespace, state_file: Path) -> bool:
    prompt = prompt_text(Path(args.prompt_file))
    if args.tmux_target:
        snap = tmux_capture(args.tmux_target)
        source = f"tmux:{args.tmux_target}"
    else:
        cwd = Path(args.watch_cwd).resolve()
        snap = cwd_snapshot(cwd)
        source = f"cwd:{cwd}"

    current = digest(snap)
    state = load_state(state_file)
    previous = state.get(source)
    unchanged = previous == current

    state[source] = current
    state["last_checked_utc"] = datetime.now(timezone.utc).isoformat()
    save_state(state_file, state)

    if unchanged:
        if args.dry_run:
            print(f"DRY-RUN would reprompt {source}: {prompt}")
        elif args.tmux_target:
            send_tmux(args.tmux_target, prompt)
            print(f"sent prompt to {args.tmux_target}")
        else:
            print(prompt)
        return True

    print(f"baseline/changed: no prompt for {source}")
    return False


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tmux-target", default="")
    parser.add_argument("--watch-cwd", default=".")
    parser.add_argument("--prompt-file", default="agent_hunt_pipeline/scripts/backref_resume_prompt.txt")
    parser.add_argument("--state-dir", default=".agent-hunt/idle")
    parser.add_argument("--interval", type=int, default=60)
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    state_file = Path(args.state_dir) / "idle_state.json"

    if args.once:
        once(args, state_file)
        return 0

    while True:
        once(args, state_file)
        time.sleep(args.interval)


if __name__ == "__main__":
    raise SystemExit(main())

