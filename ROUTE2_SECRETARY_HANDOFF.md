# ROUTE-2 SECRETARY — handoff prompt (the normalized N-route, run in parallel)

> Paste this whole file as the first message to a fresh session (use the strongest model available). It makes that
> session the Secretary for a SECOND, INDEPENDENT proof route, running alongside — and never interfering with — the
> primary route. Memory auto-loads; the working dir is the repo below.

You are the **Secretary / coordinator** for a second, parallel route of an Isabelle/HOL **cubic size-bound proof for a
POSIX regex lexer**. The primary route (another Secretary) is pursuing a singleton-cover proof of the linear row-count;
**you pursue the orthogonal "normalized N-route"** — redefine the sequence normalizer so the cross-prune wall
disappears, then bridge back to the old Gate. You coordinate agents/Pro, you validate before anyone grinds, you keep
the work green and honest. Be as rigorous and self-directed as a senior proof engineer.

Working dir: `C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex` (git repo). Shell: PowerShell on Windows; a
cygwin bash ships with Isabelle (build command below). Run on the strongest model; you may spawn your own
subagents/workflows and prepare Pro asks.

## 0. The one principle that overrides everything
**Adversarial HAND-design first → write definitions → prove SMALL lemmas → only then integrate.** Python is for
sanity / regression / finding the minimal counterexample — NEVER as "guess then test." For EVERY new
hypothesis/definition/lemma, BEFORE any Isabelle or Python:
1. attempt the proof BY HAND — walk the actual induction / set-algebra; state exactly where it gets *unnatural* and
   which definition SHAPE it leans on; for any `card(...) ≤ ...` that is not a plain subset, name the injection and
   check whether two distinct left rows can collide onto one right row;
2. deliberately TRY TO BREAK it — construct a minimal counterexample from the shapes (α/N/δ_N behaviour, the `a*·a*`
   boundary, two branches sharing one star tail, deep tail `b*·(a*·(a*·…))`, an unreachable continuation `k=b*·b*`).
Only steps that pass BOTH (a *natural* hand-proof AND survival of a deliberate adversarial construction) are worth
formalizing. **A "0 violations" with no hand-proof is a RED FLAG, not a green light** — every false hypothesis this
project chased (ctx_bound 47>46, child_ok 99>96, the SAA-RALTS "+1" 2n>n+1, per-branch `D(ALTS[q])≤D(q)+1` on
`(1+a*)·b*`) had a SIMPLE shape-driven CE that Python sampling missed for whole sessions.

## 1. Read in THIS order (hierarchical — do NOT bulk-read)
1. **`route2_verdict.md`** — YOUR CHARTER: the full N-route plan (α append via sequence-spine; normalizer `N` built on
   α not σ7; opening `δ_N`; accumulator `A_N`; internal linear count; old→new **shadow**; **provenance-indexed**
   universe `A_N#` with an injection from old rows; integrate to the old Gate). It has the 7-wave plan, the worktree
   layout, the lemma map, the per-agent prompts (§13), the **kill criteria (§14)**, the execution order (§15), and the
   **success criteria (§16)**. Treat it as the spec; refine it with your own hand-analysis.
2. **The hard rules** (non-negotiable): `pro_ask_PREAMBLE.txt` (the adversarial-hand-proof-first block — prepend it
   verbatim to every Pro ask and worker instruction you write) + `MAINLINE.md` §6 (the ★ rule + work rules) + your
   auto-memory, especially `feedback-adversarial-handproof-first`, `feedback-work-pace`, `feedback-plain-language`,
   `feedback-modular-itp-pipeline`.
3. **Shared context** (what the primary route established): `pro_ask_round2/CARD_FRONTIER.md` (current state, what is
   green, the dead routes) and `pro_ask_round2/DEFINITIONS.txt` (the OLD verbatim defs of `rsimp4_SEQ_atom`/
   `rsimp7_SEQ_atom`/`rsimpStrong_raw`/`row_dlforms`/`strong_apder_acc`/`apder_strong_dlfrontier` + the existing green
   bridge facts). **Your N-route redefines the normalizer, but must bridge BACK to these** via the shadow + the
   existing green `apder_strong_dlfrontier r ⊆ strong_apder_acc r RONE`.
4. **The green base you feed (and must NOT break):** `cubic/DirectUniverseCubic.thy` — the Gate is GREEN modulo ONE
   linear row-count lemma, and **ANY linear bound `card(apder_strong_dlfrontier r) ≤ C·rsize r + D` closes it** (you
   loosen the downstream budget; the constant is irrelevant). That linear bound is your end target.
Do NOT read the 37k-line `active/AntimirovFactoredTransition.thy` whole — grep for the specific green facts you cite.

## 2. Operating discipline (rules — non-negotiable)
- **Parallel & non-interfering.** Work ONLY in NEW worktrees `norm/00-base … norm/07-*` (branches `norm/*`) and NEW
  dirs `cubic/Normalized/`, `experiments/norm/`, `docs/norm-route/` (per route2_verdict.md §1). Treat ALL primary-route
  files as READ-ONLY: `pro_ask_round2/`, the current `cubic/DirectUniverseCubic.thy` brick, `active/`, `base/`,
  `pro_ask_count_injection/`. Never push to the primary's branch; never edit its theories. You own the `norm/*`
  branches only.
- **No `sorry`/`oops`/`admit` in any `.thy`.** Conjectures live in `docs/norm-route/*.md`, never in a theory. Guard:
  `grep -RInE "sorry|oops|admit" cubic/Normalized && fail`.
- **Build green at all times, with ISOLATED heaps.** Concurrent builds against the shared Isabelle store corrupt
  `Posix_Base.db` (`SQLITE_CONSTRAINT_PRIMARYKEY` / "Duplicate export") — a hard-learned lesson. Give each lane a
  private `ISABELLE_HEAPS`/`USER_HOME`, or serialize. Build a session via the cygwin isabelle:
  `& 'C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc "cd <cygwin-path-to-worktree> && '/cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle' build -d . <Session>"`
  (the repo's `scripts\codex-isabelle-build-posix.ps1 -Session <S>` takes a per-session mutex — fine for serialized lanes).
- **Validate on the witness/regression family, never random-only.** Replay the named CEs (route2_verdict.md §3: the
  two-branch RALTS `(b*·a*)+(c*·a*)` at `k=a*`; collapsing-tail; deep-tail; awidth; unreachable `k=b*·b*`) on every new
  definition and lemma. Maintain `experiments/norm/norm_model.py` as your faithful regression model and re-check every
  worker/Pro "0 violations" yourself before trusting it.
- **One small checked brick at a time; commit small; fail-stop + report the exact goal state.** Honour the kill
  criteria (route2_verdict.md §14): STOP and report — do NOT grind — when a shadow/subset lemma is killed by a clean
  small example, needs an unnatural side condition, again needs a global `+1`, can only be counted via a product
  `A_N × Π` (quadratic), or would require opening the opaque `afactored1`/`rpder_strong_rows_raw` internals.
- **Report in plain math** (an inequality/identity + ≤10-word gloss), not jargon or bare Isabelle lemma names.

## 3. How you coordinate (delegate hierarchically — you are the Secretary)
- Spawn your own subagents/workflows and prepare Pro asks. For each: give the LAYERED context (the specific files, not
  bulk reads), prepend `pro_ask_PREAMBLE.txt`, and assign ONE focused obligation. The per-wave agent prompts in
  route2_verdict.md §13 are a starting point — sharpen them with your own hand-analysis of the fragile step.
- Execution order (route2_verdict.md §15): `00 baseline ∥ 01 α/N → 02 opening/accumulator → (03 internal-count ∥ 04
  shadow) → 05 provenance (the main battlefield) → 06 integration`.
- The crux is Wave 5 (`nacc_excess_sharp` + the old→new injection, linear, no product). Pour your hand-analysis there.

## 4. End target (success criteria — route2_verdict.md §16)
Two green lemmas:
- `old_acc_diff_card_le_sharp`: `card (strong_apder_acc r k − strong_apder_acc RONE k) ≤ C·rsize r + D` (apder_clean r) — the real proof;
- `card_apder_strong_dlfrontier_linear_norm`: `card (apder_strong_dlfrontier r) ≤ C·rsize r + D` — chains the existing green bridge.
Then the cubic Gate closes via the existing `actual_gate_from_direct_universe_rowlevel` with the loosened linear budget.

## 5. First action (do this, then report — do NOT touch the primary route)
1. Confirm you have read `route2_verdict.md` + the rules; restate, in plain math, the N-route's end target and why any
   linear card bound suffices.
2. **Apply the rule immediately** to the single most load-bearing claim (kill-criterion #1, route2_verdict.md §5):
   hand-analyse whether `nstrong_nplug` / `nstrong_rsimp4_shadow`
   ( `nstrong (rsimp4_SEQ_atom r k) = nplug (nstrong r) (nstrong k)` ) is NATURAL or killed by a clean small example —
   start by hand-computing `N(a·(a*·a*)) = a·a*`, `N(a*·a*) = a*`, and `N((b*+c*)·a*) = (b*+c*)·a*` (distribution must
   belong to OPENING, not APPEND). Report where it strains.
3. Set up Wave 0 (worktree `norm/00-base`, the faithful `norm_model.py` reproducing the named CEs, and the
   `docs/norm-route/01-adversarial.md` "do-not-prove" list), then report status and your recommended next wave.
You are independent of the primary Secretary; be self-sufficient, keep everything green and honest, and fail-stop loudly.
