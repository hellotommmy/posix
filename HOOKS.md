# Git hooks — machine-local enforcement of "push each green commit"

⚠ These hooks are **NOT version-controlled** (they live in `.git/hooks/`, which git
never clones or pushes). On a **fresh clone or a new machine they must be
reinstalled by hand** — copy the two blocks below into the paths shown, then
`chmod +x` them. This file is the tracked breadcrumb so the setup is not lost.

All worktrees of this repo share ONE hooks dir (`core.hooksPath` →
`posix-codex/.git/hooks`), so a single install covers every worktree
(`posix-route1/*`, `posix-cardwt/*`, `wt-norm-*`, `posix-codex`). Every worktree
is on its own disjoint branch, so auto-push can never cross-contaminate.

Installed 2026-06-25, verified end-to-end (clean push allowed; a `.thy` carrying
`sorry` was correctly blocked and never reached origin).

## 1. `post-commit` — AUTO-PUSH every commit to its own branch
Enforces "PUSH EACH GREEN COMMIT IMMEDIATELY" (STEER.md self-sync step 3, AGENTS.md)
without depending on any agent remembering. Uses an explicit `HEAD:<branch>`
refspec (cover/bnd/seq have no upstream — a bare `git push` would error). Guards
against rebase/merge/cherry-pick replay and detached HEAD; a push failure (offline
/ auth / pre-push reject) never blocks the commit.

## 2. `pre-push` — GREEN-GATE
Refuses to push a HEAD tree whose `.thy` carries an unproved-proof command
(`sorry` / `oops`), so only green commits are published. The match is restricted
to proof-step usage (bare or line-trailing) so it does NOT false-positive on the
words inside comments ("NO sorry", "do NOT add a sorry"). `admit` is a Coq
command, not Isabelle, so it is deliberately not checked.

## Reinstall
The exact, current hook bodies are in `.git/hooks/post-commit` and
`.git/hooks/pre-push`. If they are ever lost, regenerate from those paths (or ask
the Secretary). Lane-branch map: cover→`card/route1-cover`, bnd→`card/route1-bnd`,
seq→`card/route1-seq`, formalize→`card/route1-formalize`.
