# Project Agent Entry Point

STANDING SELF-SYNC (do this BEFORE every proof step, every turn — not just at
session start): `git pull --rebase --autostash`, then re-read `STEER.md` (the
short live orders board). If it conflicts with your current plan, STEER.md wins
— switch immediately. This is how the Secretary redirects you without
interrupting; you are responsible for picking up the latest orders yourself.

Read in this order; do not bulk-read anything else.

0. `STEER.md` — the current order for your lane (tiny; re-read every turn).
1. `MAINLINE.md` — single-source charter: current target theorem, proof
   state, checked facts, dead routes, distilled rules, session checklist.
   It overrides route statements in any older document.
2. The LAST ~200 lines of `PROGRESS_BACKREF.md` — live state, supervisor
   instructions, inter-agent coordination. Never load the whole file.
3. `agent_hunt_pipeline/projects/posix-backref/CLAUDE.md` — the binding
   work rules (prohibitions, performance budget, bounty/guard mechanics).
4. `DOC_INDEX.md` — catalog of every other document; use it to look up
   details on demand instead of reading historical files whole.

Also relevant: `AGENTS.md` (short rule digest), `BACKREF_BOUNTIES.md` (when
locking/claiming bounties). Reusable pipeline materials live under
`agent_hunt_pipeline/`.
