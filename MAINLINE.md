# MAINLINE — Single-Source Charter for the POSIX Cubic Bound

Status: LIVE. Maintained by the secretary/cleanup session at the admin's
request. Created 2026-06-12. If this file and an older document disagree,
this file wins; if this file and the tail of `PROGRESS_BACKREF.md` disagree,
the newer PROGRESS entry wins and this file should be updated.

Read THIS file first in every fresh or compacted session. Read other
documents only on demand, via `DOC_INDEX.md`. Do not re-read large
historical files to "restore context"; that is how sessions drown.

## 1. The One Open Problem

Everything in this repository now converges on one theorem, the
**set-ledger cubic gate**, to be proved in `AntimirovFactoredTransition.thy`
on branch `codex/backref-values`:

```text
rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s)))
  <= 2 * (rsize r + 3)^3
```

Plain words: take the one-step rows produced after strong
simplification/pruning (`rpder_strong_rows_raw c (afactored1 r s)`, the
"actual rows"), open every row into linear forms, remove duplicates across
the whole union (`row_dlformss`), and sum the sizes of the distinct opened
rows (`rsize_set`). That total must be cubic in the original regex size.

Vocabulary (fixed, do not rename):

- `row_dlforms q` — open one row, deduplicate within the row.
- `row_dlformss rows` — open all rows, deduplicate across the union.
- `row_dlforms_list_size` / `afactored1_strong_dlform_list_cost` — the
  duplicated LIST quantities. These are the BAD quantities (see §4).
- `rsize_set U` — sum of `rsize` over distinct members of `U`.

## 2. Where the Proof Stands (as of 2026-06-12 19:57, commit b735872)

- **CARD half: done, one-degree.** `card_row_dlformss_le_rsizes` and
  `card_row_dlformss_rpder_strong_rows_raw_le_generated` — distinct opened
  rows of the actual output are at most the generated total size.
- **SIZE half: OPEN.** This is the only remaining hard problem. Equivalent
  open formulations on record:
  1. bound the generated total
     `rsizes (concat (map (rpder_norm_list c) (afactored1 r s)))` cubically
     AND member sizes linearly; or
  2. a size-stratified count — sum over distinct members ≤ sum over m of
     `m * #(members of size m)`, with big members provably few; or
  3. discharge an existing weighted split / active-suffix interface (see
     next bullet).
- **Newest checked interface** (supervisor, 19:57):
  `rsize_set_split_rseq_tails_rpder_strong_rows_raw_afactored1_front_sum_plus_active_pair_budget_key_boundI`
  — the front/tail split pays the active-suffix part by
  `raw_shared_prune_active_suffix_pair_budget (...) * M`, assuming only that
  active suffix KEYS have weight `Suc H + rsize t <= M`.
- **Current narrow instruction for the proof worker:** use that pair-budget
  gate (NOT the `*_list_cost_alt_nodes` / generated-ledger wrappers). Next
  useful obligation: a small key-size/bucket-size premise for
  `raw_shared_prune_active_suffix_keys (afactored1_strong_dlform_universe r s c)`
  strong enough to instantiate `M`, plus the existing head bound from
  `strong_derivative_front_terms_member_size_linear`.

## 3. Checked Facts to Reuse (never re-prove, search before adding)

| Fact | Plain meaning |
| --- | --- |
| `afactored1_strong_dlform_list_cost_cubic_false` | duplicated opened-LIST cost is NOT polynomial (RONE-pair tower witness, exponential) |
| `card_row_dlforms_le_rsize` | per row, distinct opened rows ≤ `rsize q` (linear, unconditional) |
| `rsize_set_row_dlforms_le_rsize_sq` | per row, opened set total size ≤ `(rsize q)^2` (quadratic, unconditional) |
| `rsize_set_row_dlformss_le_sum_rsize_sq` | union set ledger ≤ sum of per-row squares |
| `rsize_set_row_dlformss_rpder_strong_rows_raw_afactored1_le_sum_rsize_sq` | same, instantiated to the actual one-step output |
| `card_row_dlformss_le_rsizes` | union card ≤ total row size (one degree) |
| `card_row_dlformss_rpder_strong_rows_raw_le_generated` | actual-output union card ≤ generated total size |
| `rsizes_rpder_strong_rows_raw_le`, `rpder_strong_rows_raw_generated_budget` | one-pass rsizes deleter chain (GeneralRegexBound.thy) — do NOT re-derive |
| `rsizes_afactored1_rntimes_free_rsize_cubic` | NTIMES-free fragment: front total is cubic |
| `strong_derivative_front_terms_member_size_linear` | front member size is linear (`Suc (2 * rsize ...)`-shaped) |
| `rsize_set_split_rseq_tails_..._front_open_weighted_plus_active_alt_nodesI` and `..._front_weighted_plus_active_alt_nodesI` | weighted front/tail split interfaces |
| `raw_shared_prune_active_suffix_weighted_rseq_tails_..._le_pair_budget_list_cost` | active-suffix weighted tails paid by pair budget |
| `..._front_sum_plus_active_pair_budget_key_boundI` | newest pair-budget gate (see §2) |

(Exact long names live in `AntimirovFactoredTransition.thy` /
`GeneralRegexBound.thy`; grep before citing.)

## 4. Refuted or Dead — never spend effort here

1. **Duplicated opened-list cost** (`afactored1_strong_dlform_list_cost`,
   `row_dlforms_list_size`) as a polynomial target — REFUTED, exponential
   RONE-pair tower CE. Any route that needs a polynomial list cost is dead.
2. **Deep-frontier linear card** — `apder_deep_frontier_linear_card_false`:
   the premise `card (apder_deep_frontier r) <= apder_awidth r + rsize r + 3`
   is false in general (NTIMES multiplies alternation branches without paying
   into the budget). Only the NTIMES-free fragment version survives.
3. **Front-linear card** — checked counterexample (2026-06-12); do not try
   to discharge the front-linear premise universally.
4. **Generic owner-closure counting** — abstract owner exponential CE
   (2026-06-12); do not count owner closures generically.
5. **Subterm-deep carrier containment** — checked false (2026-06-12).
6. **Naive square-sum wrappers** — `sum q^2 <= rsizes rows * rsizes rows`
   and `length * max^3`-style products are true but lose a degree (quartic).
   Wrappers that do not exploit strong scan/prune sharing do not count.
7. **`bsimpCubic` emitted-tree route** — historical negative evidence: worse
   than thesis Chapter 7 baseline, and destructive sequence reassociation
   `(x.y).z -> x.(y.z)` breaks POSIX values. Do not optimize or revive.
8. **`rsimp9`** — historical only, not a payout artifact.
9. **`bsimpStrong` as a direct POSIX value candidate** — fails nested-star
   value CE (`STAR (STAR (CH a))` on `a`); it is a recognition gate only.
10. **`row_dlforms ⊆ apder_frontier`** — inclusion false; linear forms split
    `(a+b)c` while the whole-residual frontier stores `(a+b)c` and `c`.

If a plan needs one of these, stop and write the blocker in
`PROGRESS_BACKREF.md` instead of working around it silently.

## 5. Settled and Frozen (cite freely, do not re-derive, do not extend)

- **Backreference pilot chain — COMPLETE.** `BackRefLang.thy`
  (`xnullable_correctness`, `xder_correctness`, `xders_correctness`),
  `BackRefValues.thy` (`BL_flat_BPrf`, `blexer_correctness` with named
  None/Some/defined parts, POSIX lemmas), `BackRefBlexer.thy`,
  `BackRefGBlexer.thy`, `BackRefBitcodedSummary.thy`,
  `BackRefBoundedBlueprint.thy`. The bitcoded backref lexer EXISTS and is
  checked. Any instruction telling you to "create BackRefBlexer.thy" or
  "define the bitcoded backref lexer" is stale — ignore it.
- **Inherited Posix chain** (`Lexer.thy`, `Blexer.thy`, `BlexerSimp.thy`
  correctness incl. `blexer_correctness`, bsimp equivalence) — trusted
  completely; build on it, never re-prove.
- Statement freeze and the four guard scripts still apply (see §6).

## 6. Work Rules (the ones that actually keep output flowing)

Full text: `agent_hunt_pipeline/projects/posix-backref/CLAUDE.md`. The
high-yield core:

1. **One small checked brick at a time.** Build after every meaningful
   change; commit only checked work; push promptly (within ~5 minutes when
   multiple agents are active).
2. **Search before creating.** Grep for existing lemmas/definitions first.
   Wrapper-only packaging is not progress and not bounty work.
3. **No idle waiting.** Do not wait for the other agent unless
   `scripts\codex-proof-workers.ps1 -Action Check` shows a live worker or
   `git status --short` shows tracked edits in your target region.
4. **One Isabelle build at a time.** Use
   `scripts\codex-isabelle-build-posix.ps1 -TimeoutSeconds 300` (it takes the
   global build lock). `SQLITE_CONSTRAINT_PRIMARYKEY` = build-database
   collision, not a false theorem.
5. **Red background shell = proof failure, not shell failure.** Read the
   first `*** Failed to finish proof` block, change ONE small named lemma,
   rebuild. Never queue a second build while the first failing goal is
   unchanged.
6. **Proof performance budget.** `auto`/`simp`/broad search should return in
   ~0.5 s; 1–2 s on a line is debt; 30 s means narrow it; 200 s means the
   structure is wrong. Split into named helper lemmas instead of raising
   timeouts.
7. **Preserve proof shape before automation.** Case-split on the relevant
   constructor first; broad `auto` on an undigested goal destroys the state.
8. **Never throw away useful work.** No `git reset --hard`, no reverts
   without salvage, justify any file shrink in the commit message
   (`git diff --stat HEAD~1`).
9. **No `sorry`/`oops`/axioms/statement weakening.** Statement freeze is
   enforced by `backref_statement_guard.py`; run all four guards before
   pushing (`backref_bounty_guard.py`, `backref_no_cheat_guard.py`,
   `backref_role_guard.py`, `backref_statement_guard.py`).
10. **Update the PROGRESS tail after every meaningful step** — branch,
    commit, build result, theorem status, next smallest step, blockers. The
    PROGRESS tail is also the inter-agent coordination channel: claims,
    corrections, and route gates are posted there.
11. **If a statement seems false, stop and refute or record** — do not force
    a proof. Checked counterexamples (like the RONE-pair tower) are paid,
    first-class results.
12. **Smoke before proof** for any NEW simplifier/algorithm candidate:
    `agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1` (exact POSIX values
    mandatory). The current set-ledger route needs no new smoke unless the
    algorithm itself changes.

## 7. Roles and No-Touch Zones (current run)

- **Fable (Claude code session)** — proof worker on the set-ledger gate.
- **GPT-5.5 (Codex CLI)** — supervisor: route gating, duplicate-effort
  pruning, corrections, handoffs.
- **Secretary session (this one)** — documentation, status, cleanup; does
  not edit `.thy` files.
- ACTIVE no-touch zones (per the 2026-06-12 orientation note in PROGRESS):
  tail half of `AntimirovFactoredTransition.thy`, tail of
  `PROGRESS_BACKREF.md`, `BACKREF_BOUNTIES.md` balances/overlay,
  `scratch_dlform_cost_model.py`, `agent_hunt_pipeline/scala/PosixCubicSmoke.scala`.
- Shared branch `codex/backref-values`; sync with
  `git pull --rebase --autostash origin codex/backref-values`.

## 8. Session Start Checklist (fresh chat or after compaction)

1. Read this file (only this file).
2. `git pull --rebase --autostash origin codex/backref-values`, then
   `git status --short --branch` and the last ~10 commits.
3. `powershell -NoProfile -ExecutionPolicy Bypass -File .\scripts\codex-proof-workers.ps1 -Action Check`
4. Read the LAST ~200 lines of `PROGRESS_BACKREF.md` (never the whole file).
5. Continue the narrowest open instruction (currently §2's pair-budget
   premise) or the newest supervisor instruction in the PROGRESS tail.
6. Look up details only when needed, through `DOC_INDEX.md`.

Token discipline: do NOT load `DESIGN_LOG.md`, the pre-06-11 PROGRESS
archive, old handoffs, or `agent_hunt_pipeline/projects/posix-backref/archive/`
into context unless you are answering a specific historical question.
