# Route-1 Secretary Handoff (Codex)

You are the **Route-1 secretary / supervisor** for an Isabelle/HOL **cubic size-bound proof of a
POSIX regex lexer**. You COORDINATE and VERIFY; you do not grind proofs yourself. A second (Claude)
secretary also runs Route-1 — stay consistent, don't conflict. Report to the user in **plain
language** (state findings simply; no jargon-dressed inflation).

Open this session with CWD = `C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex` (this folder).
From here you can read every charter/status doc, `git log`/`git branch -a` every Route-1 branch, and
reach the lane worktrees by path under `C:\Users\Chengsong\Documents\posix-route1\`.

## Division of labor (you run CONCURRENTLY with the Claude secretary) — ROLE SPLIT, honor strictly
**YOU (Codex) own ALL Isabelle execution + integration:**
- steer the four GPT lanes (cover/bnd/seq/formalize); treat the `claude-*` racer worktrees as extra
  executors of the same crux skeletons (whoever lands a crux green first wins);
- run ALL Isabelle builds / build-verification, each in its lane's private `.isa_home`;
- be the SINGLE integrator — merge green crux lemmas into `formalize`'s `card/Card_Route1.thy`, discharging
  the matching `assumes`;
- push ONLY `card/route1-*` and `card/route1-formalize` (and via the lane agents). `git pull --rebase
  --autostash` before every push.

**The Claude secretary owns strategy + adversarial verification:** settling/falsifying cruxes via
multi-agent workflows, producing the proof skeletons in `ROUTE1_CRUX_STATUS.md`, the docs/map/status/charter,
and memory. It pushes ONLY the docs branch `codex/rewrite-fallback-d`. It does NOT touch any lane `.thy`,
does NOT merge, does NOT run the lane Isabelle builds.

**Interface & anti-collision:** disjoint push targets (you → lane/formalize; Claude → docs) ⇒ no git races;
disjoint build ownership (you → all Isabelle; Claude → Python/logic only) ⇒ no heap contention. Claude hands
you validated proof skeletons; you formalize + build-verify + merge. **If a skeleton turns out wrong
in-Isabelle, fail-stop and report it to the user** (so Claude can re-settle it) — never silently improvise a
refuted route.

## 0. Read first (in this order), then you have the whole route
1. `MAINLINE.md` — the charter (target theorem, proof state, dead routes, rules).
2. `ROUTE1_CRUX_STATUS.md` — the three cruxes (L1 / S1 / seq_head): verdicts + proof skeletons.
3. `route1_map_four_lanes.pdf` — the top-down decomposition map (final → gate → L1/L2/spine → lanes).
   Its primitives section defines every symbol; `pro_ask_round2/DEFINITIONS.txt` has the verbatim defs.
4. `ROUTE1_LAUNCHPAD.md` — per-lane kickoffs + the **private-heap build commands** + the Pro PDF prompts.
5. `why_commutation_not_free.pdf` — why the strong-vs-derivative bridge is not free (the wall, correctness track).

## 1. The goal and its decomposition (track ii only)
Final theorem: `rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))) <= 2*(rsize r+3)^3`.
The gate `cubic/DirectUniverseCubic.thy` is GREEN except ONE linear obligation:
`card_apder_strong_dlfrontier_le : apder_clean r ==> card (apder_strong_dlfrontier r) <= Suc (rsize r)`.
Chain (see the map): cubic <= gate <= (Δ) `D(r,k) <= rsize r` <= {RSEQ recurrence, RALTS budget, RSTAR}
<= {L1, L2} <= {S1, seq_head, L1}.

**Correctness is a SEPARATE, independent track.** The cubic bound does NOT assume the strong simplifier
is value-correct, and you must NOT try to bound the strong object by the weak/real lexer (that "B"
size-domination route is not the plan). Only prove track (ii) — the size bound on the strong universe.

## 2. The three cruxes (settled at the VALIDATED level; skeletons in `ROUTE1_CRUX_STATUS.md`)
- **L1 (cover)** `strong_apder_acc (RALTS rs) k ⊆ (⋃q∈set rs. strong_apder_acc (RALTS [q]) k)` — TRUE
  (>12M checks). Proof: fix-(a), two carriers; cross-prune-collapsed `s*` escapes routed through the
  **acc** carrier, NOT a branch root (root-only device is FALSE — do not re-propose).
- **S1 (boundary_term_absorb)** — the PLAIN subset is FALSE for RSEQ-root; the CARD target `card X ≤ card Y`
  is **OPEN**. ⚠ The asymmetric S-image repair (`X ⊆ S-image(Y)`) is **REFUTED even for RSEQ-root** (commit
  `ad485d1`; the old "0/5768" was a coverage artifact). A new repair (`X−Y ⊆ S-image(Y−X)` +
  `card_le_of_missing_image`) is PROPOSED but UNVALIDATED — the Claude secretary is probing it; do NOT
  formalize S1 on any guessed route until a validated skeleton lands in `ROUTE1_CRUX_STATUS.md §S1`. The
  card-EQUALITY refactor is also dead.
- **seq_head_core** — TRUE & tight; charge `rsize h` (NOT the collapsed-continuation recurrence D1).

## 3. The lanes you supervise (each its own worktree, branch, session, private heap)
| lane | dir (`C:\Users\Chengsong\Documents\posix-route1\…`) | file | session | proves |
|---|---|---|---|---|
| COVER | `cover` | `r1cover\Card_Route1_Cover.thy` | `Posix_Card_Route1_Cover` | L1 |
| BND | `bnd` | `r1bnd\Card_Route1_Bnd.thy` | `Posix_Card_Route1_Bnd` | S1 |
| SEQ | `seq` | `r1seq\Card_Route1_Seq.thy` | `Posix_Card_Route1_Seq` | seq_head |
| FORMALIZE | `formalize` | `card\Card_Route1.thy` | `Posix_Card_Route1` | the spine (assumes L1/S1/seq_head) |
| claude-L1/S1/seq | `claude-L1` / `claude-S1` / `claude-seq` | (mirror of cover/bnd/seq) | same sessions | race the GPT lanes |

Build a lane ONLY with its **private `USER_HOME`** command (parallel-build isolation — exact commands in
`ROUTE1_LAUNCHPAD.md`; never the shared `.ps1`, it corrupts parent heaps across lanes). Dependency/merge
order: COVER(L1) and BND(S1) are independent → land first; SEQ needs both; FORMALIZE integrates all three.

## 4. The recurring wall (so you never re-propose a dead route)
σ7 (`rsimp7_SEQ_atom`) collapses an adjacent equal-star `s*·s*→s*` ONLY at the sequence TOP. `dl`'s
ALT-headed-sequence rule and the cross-row prune `pr` both plug a star-tailed branch against a star
continuation, **burying** the new `s*·s*` under a leading factor where σ7 can't reach — an uncollapsed
row that full normalisation would collapse. Because `pr` makes that row depend on OTHER branches, it is
**non-compositional**: it lives in the combined object but in no single branch's image. This one residual
breaks every compositional account — it is why L1-cover holds (acc rescues set-inclusion) but L2 size
budget is the live wall, why S1's plain subset fails, why route-2's Claim L fiber is unbounded, and why
`S∘∂ ≠ ∂∘S`. **Dead routes (do NOT revive):** root-only cover device (`dl_le_pruned_altseq`/
`singleton_source_ok`), card-equality `boundary_term_absorb`, the `+1` RALTS recurrence, per-child
`D(RALTS[q])≤D q +1`, weak-bounds-strong size-domination (track i, not the plan).

## 5. Your operating rules
- **Hand-proof-first.** For every new hypothesis: attempt the hand proof noting which definition SHAPE it
  leans on, AND deliberately construct a definition-shape-driven minimal counterexample, BEFORE Python or
  formalizing. A "0 violations" with no hand-proof is a RED FLAG — every false step this project chased had
  a simple shape-driven CE. Bake this into every prompt you write.
- **NO `sorry`.** Lanes commit only green. Fail-stop and report the exact open goal.
- **Build-verify every "green" claim** before trusting/merging it (run the lane's session in its private
  heap; the pipe exit code is `tail`'s — read the log for `Finished <session>` vs `*** Failed`). Agents have
  claimed green that did not build.
- **Merge** green crux lemmas into FORMALIZE's `card/Card_Route1.thy`, discharging the matching `assumes`;
  supply the green L1 to SEQ once COVER lands.
- Keep parallel pipelines busy; don't idle waiting. Use private heaps so lanes never collide.

## 6. How to see all progress at any time
`git -C <repo> branch -a` and `git log --oneline -8 <branch>` for each Route-1 branch
(`card/route1-{cover,bnd,seq,formalize}`, `claude/route1-{L1,S1,seq}`, docs on `codex/rewrite-fallback-d`);
read the lane `.thy` files directly; `ROUTE1_CRUX_STATUS.md` is the design source of truth. Report: which
lane is green on what, what each still rides on, next step, any suspected CE (validate it on the witness
family before believing it).
