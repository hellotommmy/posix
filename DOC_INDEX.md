# DOC_INDEX — Catalog of Every Document in This Repository

Maintained by the secretary session; created 2026-06-12. Status tags:

- **LIVE** — current truth; safe to act on.
- **RULES** — operating rules; still binding.
- **SETTLED** — finished, checked, frozen; cite it, never redo it.
- **HISTORICAL** — superseded route record; consult only to look up exact
  theorem names, counterexamples, or provenance. Never take next-step
  instructions from a HISTORICAL document.
- **SCRATCH** — another agent's working file; do not edit or move.

Reading order for a fresh session: `MAINLINE.md` → last ~200 lines of
`PROGRESS_BACKREF.md` → (only if needed) this index to find details.

## 1. Live mainline

| Doc | Status | What it is |
| --- | --- | --- |
| `MAINLINE.md` | LIVE | Single-source charter: live theorem, proof state, checked-facts table, dead routes, distilled rules, session checklist. Overrides older route statements. |
| `PROGRESS_BACKREF.md` | LIVE | Append-only progress log AND the inter-agent coordination channel (claims, corrections, supervisor gates). Read the tail, append at the bottom. Pre-06-11 head archived (see §5). |
| `agent_hunt_pipeline/projects/posix-backref/NEXT_CHAT_FABLE_SUPERVISION_HANDOFF_2026_06_12.md` | LIVE | Compact supervisor handoff for the current set-ledger run: build discipline, checked facts, what not to do. |
| `GATE_BRIDGE_GAP.md` | LIVE | The one remaining open gap to close the cubic gate (2026-06-13): bridging the cubic static front to the DEDUPED opened-row ledger. A design point (square-sum is quintic, the list is exponential; the bound must come from suffix-sharing). |
| `GPT_PRO_GATE_BRIDGE_VERDICT.md` | LIVE | GPT Pro's design for the gate-bridge (2026-06-14): the opened-boundary / suffix-edge invariant (the opened analog of the D-law telescoping) + the `open_pot` potential + a 9-lemma execution stack. The route to close the gate — sample-check the potential bound at depth≥5 before Isabelle. |
| `MATHPROBLEM_ROWCOUNT.md` | LIVE | Self-contained statement of the D law (Antimirov row-count linearity). The clean-domain zw2 instance is now PROVEN (`D_law_clean`, 7e62648, via the T+S route) — top banner records this; the body is now the dead-ends/CE/route reference. Still includes the falsified strengthenings with CEs. |
| `GPT_PRO_DLAW_VERDICT.md` | LIVE | GPT Pro's design verdict on the D law (2026-06-13): the T+S telescoping boundary invariant that dissolves the SEQ overlap, the exact-E0 gap it found, four bridge lemmas, and per-constructor discharge. ROUTE NOW COMPLETE/CHECKED (`T_and_S` + `D_law_clean`, 7e62648). The recommended D-law architecture — sample-check at depth≥5 before Isabelle. |
| `CUBIC_OPEN_PROBLEM.tex` / `.pdf` | LIVE | 6-page self-contained mathematical statement of the set-ledger cubic gate: definitions, conjecture, checked facts, refutations, acceptance criteria, notation dictionary. |
| `cubic_progress.tex` / `.pdf` | LIVE | Incrementally-compiled ledger of checked progress, maintained by the Fable+Codex proof agents (every "checked" entry names a green Isabelle lemma). Detailed running record of the proof campaign; complements MAINLINE §2 (which is the distilled summary). Build artifacts (`.aux/.log/.out/.toc`) are gitignored. |
| `STATUS_MATH.tex` / `.pdf` | LIVE | ONE-PAGE plain-math roadmap of the whole proof in pure notation (✓ PROVEN / → CURRENT / ○ LATER), each line with a plain-English gloss and minimal jargon. The "you are here" map for the admin. Secretary keeps it current; move the `[→ CURRENT]` marker when a milestone lands and recompile. |
| `SUPER_LINEAR_PATTERNS.md` | LIVE | Companion fuzzer corpus: every machine-verified blow-up regex family and every conjecture-killing counterexample, with deception data (how many samples it fooled before dying). For stress-testing the linearity claims of NFA-based regex engines. Append-only — see the 2026-06-13 admin directive. |
| `BACKREF_BOUNTIES.md` | LIVE | Bounty board + ledger, parsed by `backref_bounty_guard.py` — never restructure. 14 open bounties; 2026-06-12 adds a 20,000 cubic overlay (12k final theorem / 5k major bridge / 3k checked negative). Note: BR-039/BR-040 prose still describes the superseded strong-memo route; the artifact lists remain valid checked infrastructure. Known bookkeeping flag: paid 74,970 vs balances 73,950 (gap 1,020), admin to reconcile. |
| `CLAUDE.md` (root) | LIVE | Two-line pointer into the rules and charter. |
| `RESTART_PROMPTS.md` | LIVE | Copy-paste handoff prompts for restarting each agent (Codex / Fable / Secretary): role, goal, lane, coordination mode, rules. Use when reopening stopped agents. |

## 2. Rules and operations (binding)

| Doc | Status | What it is |
| --- | --- | --- |
| `agent_hunt_pipeline/projects/posix-backref/CLAUDE.md` | RULES | The authoritative work rules: prohibitions, never-throw-away-work, proof performance budget, bounty/lock mechanics, statement freeze, git discipline, guards, stop conditions. Route narrative now lives in MAINLINE.md / archive. |
| `AGENTS.md` | RULES | Short cross-agent rule digest (applies to Codex and Claude alike). |
| `agent_hunt_pipeline/projects/posix-backref/AGENT_ROLES.md` | RULES | Admin / worker / merge-steward role definitions and write scopes. Named agent table is pilot-era; current roles: Fable = proof worker, GPT-5.5 Codex = supervisor, secretary = docs. |
| `agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md` | RULES | Full bounty mechanics: pool, 10% lock deposits, max 10 locks, 24 h expiry, lock-or-lose, sub-bounties, wrapper-only work not payable. |
| `agent_hunt_pipeline/projects/posix-backref/BRANCHING_AND_RUN_MODE.md` | RULES | Shared-branch model (`codex/backref-values`), pull --rebase --autostash, quarantine-branch exception. |
| `agent_hunt_pipeline/projects/posix-backref/DUAL_AGENT_COORDINATION.md` | RULES (part) | File leases, single-builder Isabelle mutex, performance budget. The concrete BR-015/BR-022 assignments inside are pilot-era. |
| `agent_hunt_pipeline/README.md` | RULES | Map of the reusable pipeline scaffolding (scripts/, templates/, hooks). |
| Guard scripts (`agent_hunt_pipeline/scripts/backref_*_guard.py`) | RULES | Run all four before pushing: bounty, no-cheat, role, statement. |
| Build wrappers (`scripts/codex-isabelle-build-posix.ps1`, `scripts/codex-proof-workers.ps1`, `agent_hunt_pipeline/scripts/isabelle_ci.ps1`) | RULES | The only sanctioned ways to build/check; they take the global build lock. |

## 3. Settled formal results (frozen; cite freely)

| Doc / file | Status | What it is |
| --- | --- | --- |
| `BackRefLang.thy`, `BackRefValues.thy`, `BackRefBlexer.thy`, `BackRefGBlexer.thy`, `BackRefBitcodedSummary.thy`, `BackRefBoundedBlueprint.thy`, `BackRefLang4Values.thy` | SETTLED | The complete backref pilot chain (BR-001..BR-022 paid). Top theorems listed in MAINLINE.md §5. Zero `sorry` repo-wide. |
| `RegLangs.thy`, `PosixSpec.thy`, `Lexer.thy`, `Blexer.thy`, `BlexerSimp.thy`, `BasicIdentities.thy`, `ClosedForms.thy`, `ClosedFormsBounds.thy` | SETTLED | Inherited original Posix development incl. `blexer_correctness`, `main_blexer_simp`, `blexersimp_correctness`. Trust completely; edits need admin approval. |
| `GeneralRegexBound.thy` | LIVE+SETTLED | Active infrastructure for the cubic work (deleter chains, active-suffix closures, pair budgets) plus settled older interfaces. |
| `AntimirovFactoredTransition.thy` | LIVE | The active workbench: set-ledger gate, RONE-pair CE block, per-row set bounds, union card account, split/pair-budget interfaces. Tail half = no-touch zone for non-proof agents. |
| `FBound.thy`, `AntimirovNormalFrontier.thy` | SETTLED | Checked contracts of earlier route generations (deferred-memo budgets, final-active row-DAG contracts, normal-frontier stage-one theorems). Valid theorems, no longer the mainline. |
| `backref_formalization_blueprint.md` (parent folder) | SETTLED | The original 6-stage backref theorem ladder — fully executed. |

## 4. Historical route record (for lookups only)

| Doc | Status | What to find there |
| --- | --- | --- |
| `agent_hunt_pipeline/projects/posix-backref/FABLE_CUBIC_HANDOFF_2026_06_11.md` | HISTORICAL | Newest-first 06-11/06-12 supervisor override trail. Top blocks duplicate the live gate; middle layers = same-day superseded subroutes; bottom = ops reference. Superseded as entry point by the 06-12 supervision handoff. |
| `agent_hunt_pipeline/projects/posix-backref/NEXT_CHAT_CUBIC_HANDOFF_2026_06_05.md` | HISTORICAL | Best pre-06-09 inventory of frontier-route theorems/CEs (whole-residual frontier, dlform universes, dcanon). Both of its recommended targets were later refuted. |
| `agent_hunt_pipeline/projects/posix-backref/DESIGN_LOG.md` | HISTORICAL | Append-only design log through 06-05: bridge-owner/row-DAG program, CE inventory, route debates. |
| `CUBIC_BOUND_PROOF_WRITEUP_2026_06_06.md` | HISTORICAL | Mathematical writeup of the 06-06..06-08 proof state (accumulator contracts, normal-canonical route). Statements settled; spine superseded. |
| `agent_hunt_pipeline/projects/posix-backref/CERTIFIED_STRONG_CORE.md` | HISTORICAL | Spec of the certified-core / strong-deferred-memo value-reconstruction route; records the CEs that killed direct decode and local certificates. The span/deferred POSIX theorems it lists are settled and remain valid. |
| `agent_hunt_pipeline/projects/posix-backref/archive/PROGRESS_BACKREF_ARCHIVE_2026-05-25_to_2026-06-10.md` | HISTORICAL | Verbatim pre-06-11 progress log (12,649 lines): pilot completion, rsimp9 revocation, strong-memo generation, frontier generation. |
| `agent_hunt_pipeline/projects/posix-backref/archive/CLAUDE_CUBIC_ROUTE_HISTORY_2026-06-04.md` | HISTORICAL | Verbatim route narrative excised from the rules file: strong-memo switch, scout scripts, factor sweeps, shared-DAG diagnostics, still-reusable FBound/GeneralRegexBound interface names. |
| `agent_hunt_pipeline/projects/posix-backref/archive/CLAUDE_PILOT_ROADMAP_COMPLETED.md` | HISTORICAL | Verbatim four-phase pilot roadmap (completed). |
| `agent_hunt_pipeline/projects/posix-backref/SESSION_BRIEF.md` | HISTORICAL | Pilot-era brief with a cubic-run override header; superseded by MAINLINE.md. |

## 5. Retired agent/ops configurations

| Doc | Status | Note |
| --- | --- | --- |
| `CURSOR_OPUS_COLLEAGUE.md`, `CURSOR_OPUS_SHARED_BRANCH_GUIDE.md` | HISTORICAL | Cursor/Opus bootstrap — Opus is retired. |
| `SLEEP_RUNBOOK.md`, `agent_hunt_pipeline/WINDOWS_RUNBOOK.md` | HISTORICAL | Overnight tmux/watchdog runbooks for the pilot-era agent pair; tmux/idle-watch mechanics reusable. |
| `agent_hunt_pipeline/references/agent_hunt_rule_search.md` | HISTORICAL | Provenance note on the public Agent Hunt rules. |
| `agent_hunt_pipeline/scripts/*_resume_prompt.txt`, `loop-config.json` | RULES | Refreshed 2026-06-12 to point at MAINLINE.md. Old copies of these prompts caused the post-compaction stale-instruction loop. |

## 6. Parent-folder documents (`C:\Users\Chengsong\Documents\AIPV2026Notes`)

| Doc | Status | Note |
| --- | --- | --- |
| `backref_agent_hunt_handoff.md` | HISTORICAL | First pilot handoff (May 2026); plan completed. Contains the original Cygwin build command. |
| `backref_agent_hunt_ops_and_prompts.md` | HISTORICAL | Multi-agent ops runbook + prompt templates from the pilot phase. One prompt forbids editing `GeneralRegexBound.thy` — obsolete; do not treat as binding. |
| `backref_formalization_blueprint.md` | SETTLED | Original theorem ladder; executed. |
| `agent_hunt_setup_study.md` | RULES (background) | Study of the Agent Hunt / 130k-lines methodology this workflow copies. |
| `AIPV2026_2026-05-19_notes_enriched.md` | unrelated | Personal conference notes; not project material. |
| `fable_cubic_handoff.txt` | HISTORICAL | The admin's short restart prompt for the supervisor session. |

## 7. Scratch and generated artifacts

| Path | Status | Note |
| --- | --- | --- |
| `agent_hunt_pipeline/projects/posix-backref/fable_partial.md` | SCRATCH | Fable's untracked scratchpad on an UNRELATED extremal-set-theory problem (holds unrecorded informal results; salvage suggestion logged in PROGRESS 2026-06-12). Not POSIX material. |
| `scratch_dlform_cost_model.py` | SCRATCH (active tool) | Python mirror of the one-step cost pipeline, used for numeric probes. Do not delete. |
| `agent_hunt_pipeline/scala/PosixCubicSmoke.scala` | LIVE tool | The executable smoke harness; required gate for any NEW simplifier candidate. |
| `agent_hunt_pipeline/reports/**` | generated | Smoke/scout/plot outputs (Chapter 7 grids, factor sweeps, scouts). Regenerate with the scripts; do not hand-edit. |
| `agent_hunt_pipeline/snapshots/*.thy` | frozen snapshots | Statement-guard reference copies, not mainline theories. |
| `agent_hunt_pipeline/logs/` | gitignored | Watcher/build logs. A stale 96 MB idle-watch log was deleted 2026-06-12. |
| `pilot/`, `backRef.sc` | SETTLED | Pilot session ROOT and the Scala reference implementation the bitcoded backref lexer was formalized from. |
