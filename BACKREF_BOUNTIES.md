# Backreference Pilot Bounties

This is the competitive-collaborative bounty board for the POSIX backreference
formalization pilot. It follows the Agent Hunt bounty mechanics: agents compete
for theorem bounties but are incentivized to collaborate.

Amounts are in simulated USD. A payout is valid only when the named artifact
exists, the guards pass, and the required Isabelle CI session succeeds.

Admin policy update: wrapper-only theorem packages do not count as bounty
deliverables. Summary/cases/iff/same/retrieve-equality facts may remain as API
convenience lemmas, but future bounty claims must introduce a new semantic or
algorithmic layer, or a nontrivial proof bridge needed by later work.

See `agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md` for the
full rules including locking, sub-bounties, effort estimates, and statement
immutability.

## Pool

| Category | Amount |
| --- | ---: |
| Total pool | 150,000 |
| Allocated (active + completed) | 149,090 |
| Collected (paid out) | 74,970 |
| Reserved (unallocated) | 910 |

## Agent Balances

| Agent | Role | Balance | Notes |
| --- | --- | ---: | --- |
| Codex | Admin/Worker | 67,750 | Completed BR-001 through BR-004, BR-006 through BR-010, BR-015 through BR-022, BR-032, BR-035 |
| Opus | Worker | 6,200 | Completed BR-005, BR-011, BR-012, BR-013, BR-014; BR-015 lock released when Cursor was retired |
| MergeSteward | Steward | 0 | Integration role |
| Alice | Worker | 0 | Optional future worker |
| Bob | Worker | 0 | Optional future worker |

## Active

| ID | Task | Bounty | Est. Lines | Difficulty | Est. USD | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |
| BR-023 | Original-file migration TODO audit | 120 | 30 | 3 | 120 | OPEN | - | RegLangs.thy;PosixSpec.thy;Lexer.thy;LexerSimp.thy;Blexer.thy;BlexerSimp.thy;BasicIdentities.thy;GeneralRegexBound.thy;ClosedForms.thy;ClosedFormsBounds.thy;FBound.thy | AdminReview | Small planning bounty only; no theorem payout until admin approves direct original-file implementation |
| BR-024 | Migrate backref4 language semantics into original RegLangs | 1,400 | 120 | 8 | 1,400 | OPEN | - | RegLangs.thy:backref_lang4,nullable_correctness,der_correctness,ders_correctness | Isabelle:Posix | Direct `rexp/L/nullable/der/ders` extension with BACKREF4/HALF/RESIDUE; no brexp/gbrexp wrappers |
| BR-025 | Migrate backref values and POSIX rules into original PosixSpec | 1,800 | 180 | 9 | 1,800 | OPEN | - | PosixSpec.thy:L_flat_Prf,LV_finite,Posix_determ,Posix_LV | Isabelle:Posix | Direct `val/flat/Prf/LV/Posix` extension; no bval/bval4/gbval wrappers |
| BR-026 | Migrate backref injection and lexer correctness into original Lexer | 1,400 | 140 | 9 | 1,400 | OPEN | - | Lexer.thy:Prf_injval,Posix_injval,lexer_correctness,Prf_flex | Isabelle:Posix | Direct `mkeps/injval/lexer/flex` extension after BR-024/025 |
| BR-027 | Migrate backref bitcoded lexer into original Blexer | 1,800 | 170 | 9 | 1,800 | OPEN | - | Blexer.thy:erase_bder,retrieve_code,bmkeps_retrieve,bder_retrieve,MAIN_decode,blexer_correctness | Isabelle:Posix | Direct `bit/arexp/code/decode/retrieve/bder/blexer` extension; no bbit/barexp/gabexp wrappers |
| BR-028 | Preserve aggressive original BlexerSimp for backrefs | 1,400 | 140 | 9 | 1,400 | OPEN | - | BlexerSimp.thy:rewrites_to_bsimp,rewrite_preserves_bder,central,main_blexer_simp,blexersimp_correctness | Isabelle:Posix | Must use original rewrite-system route; weak structural simplifier or wrapper equality does not count |
| BR-029 | Add backref closed-form families in original closed-form machinery | 1,200 | 160 | 9 | 1,200 | OPEN | - | BasicIdentities.thy;ClosedForms.thy:backref4_closed_form,half_closed_form,residue_closed_form | Isabelle:Posix | Decide rexp vs temporary rrexp, then add real BACKREF4/HALF/RESIDUE closed-form coverage |
| BR-030 | Close original bounds after backref migration | 1,000 | 120 | 8 | 1,000 | OPEN | - | GeneralRegexBound.thy;ClosedFormsBounds.thy;FBound.thy:finite_size_n,rders_simp_bounded,annotated_size_bound | Isabelle:Posix | Final boundedness through original theorem chain; BackRefBoundedBlueprint wrappers do not count |
| BR-031 | Cubic non-backref size-bound blueprint | 5,000 | 120 | 8 | 5,000 | OPEN | - | PROGRESS_BACKREF.md;BasicIdentities.thy;ClosedFormsBounds.thy;FBound.thy | AdminReview | State the cubic target, fragment invariant, and Antimirov-style frontier plan; no theorem payout for wrapper-only restatements |
| BR-033 | Prove partial-derivative universe cubic bound | 12,000 | 300 | 10 | 12,000 | OPEN | - | GeneralRegexBound.thy:partial_derivative_path_universe,partial_derivative_live_row_universe,rfrontier_path_continuation_subset_path_universe,partial_derivative_live_row_universe_subset_path,rsizes_distinct_live_row_universe_cubic,rsizes_rpders_norm17_rows_live_row_universe_cubic,raw_live_row_universe_not_closed_under_norm7 | Isabelle:Posix | Replace `card(sizeNregex N)` reasoning with a finite universe generated from subterms/continuations of the original non-backref regex; corrected live-row accounting is checked and inherits the path-universe cubic bound; remaining work is the normalized-root live-row one-step closure for `rpder_norm7_list` |
| BR-034 | Transfer cubic bound to annotated lexer states | 8,000 | 260 | 10 | 8,000 | OPEN | - | FBound.thy:asize_bp_der_norm_cubic,RL_rerase_bders_pder_norm,rpders_norm1_rows_rerase,annotated_size_bound_cubic_nonbackref | Isabelle:Posix | Final non-backref theorem for normalized row-list `bpders_norm1_rows`/future production `bsimp`; backref constructors explicitly excluded from the fragment |
| BR-038 | Cubic smoke and counterexample suite | 6,000 | 120 | 8 | 6,000 | OPEN | - | agent_hunt_pipeline/scala/PosixCubicSmoke.scala;agent_hunt_pipeline/scripts/scala_cubic_smoke.ps1;FBound.thy:thesis_cubic_smoke_A_shared_suffix,thesis_cubic_smoke_B_ch7_three_star,thesis_cubic_counterexample_C,thesis_cubic_counterexample_D,thesis_cubic_counterexample_E,thesis_cubic_counterexample_F,thesis_cubic_counterexample_G,thesis_cubic_counterexample_H | ScalaSmoke+Isabelle:Posix | Build a smoke suite before any new cubic proof attempt. Scala owns broad grids/enumeration and exact POSIX value comparisons; Isabelle owns compact proof-facing sanity facts. A is `(a+b)c + (a+d)c`; B is the thesis Chapter 7 three-star family. No proof bounty may depend on a simplifier that fails this suite. |
| BR-039 | Define smoke-tested cubic simplifier candidate | 25,000 | 260 | 10 | 25,000 | OPEN | - | GeneralRegexBound.thy:rsimpCubic,rders_simpCubic;BlexerSimp.thy:bsimpCubic,bders_simpCubic;FBound.thy:thesis_cubic_smoke_suite_bsimpCubic;agent_hunt_pipeline/scala/PosixCubicSmoke.scala | ScalaSmoke+Isabelle:Posix | Define a new candidate, not `rsimp9`, that passes BR-038 smoke tests including exact POSIX value preservation, shared-suffix pruning, and the three-star family under explicit size thresholds. Existing `rsimp9` lemmas may be mined only as technical ideas, not as bounty artifacts or proof targets. |
| BR-040 | Post-smoke cubic proof interface | 8,000 | 180 | 9 | 8,000 | OPEN | - | GeneralRegexBound.thy:rsimpCubic_size_le,RL_rsimpCubic,rsizes_rpders_cubic_rows_smoke_universe_boundI;FBound.thy:L_bsimpCubic,RL_rerase_bsimpCubic,RL_rerase_bders_simpCubic | Isabelle:Posix | Only after BR-038 and BR-039: state the first proof interface for the smoke-tested simplifier. This is not a final cubic theorem; it must not mention `rsimp9` as the candidate simplifier. |

## Retired / Revoked

| ID | Task | Former Bounty | Status | Date | Reason |
| --- | --- | ---: | --- | --- | --- |
| BR-036 | Close rsimp8/rsimp9 live-row cubic closure | 15,000 | DROPPED | 2026-06-02 | Revoked by admin: proof-first `rsimp9` route failed the smoke-test discipline and must not pay out. Existing lemmas remain historical technical evidence only. |
| BR-037 | Transfer root-safe cubic theorem to annotated lexer | 10,000 | DROPPED | 2026-06-02 | Revoked by admin: old root-safe transfer route is retired until a new simplifier passes A/B/C/D/E/F smoke tests. |

## Open Artifact Notes

- Strong prune exact-erasure caveat: `FBound.thy` now has the checked
  counterexample `rerase_bsimpStrong_prune_pair_not_exact`. It shows that
  annotated `bsimpStrong_prune_pair` does not syntactically erase to
  `rsimpStrong_prune_pair`, because the annotated side keeps bit/value-carrying
  row syntax while the skeleton side normalizes duplicate/nested pruned rows
  internally. Future BR-039/BR-040 work must not rely on a naive exact
  `map rerase` bridge for strong pruning; it needs a language/coverage
  universe argument or a checked shared-row reconstruction layer.
- Original-entry strong-row cubic interface: `FBound.thy` now has
  `strong_deferred_original_row_cubic_universe_interface`. It states the
  current checked contract from an original `legacy_rexp r`: a finite erased
  row universe with one-step `bpder_strong_rows` closure and card/member-size
  bounds gives a product bound for
  `bpders_strong1_rows (intern r) s`, while preserving the nullable-row iff
  unique deferred POSIX value gate and the `rxsize` alignment of `intern`.
  This is BR-040 infrastructure only. It does not pay until the actual cubic
  row universe construction/closure theorem is checked.
- Strong-tree route clarification: the currently viable way to preserve the
  `bsimpStrong` tree plateau while getting exact POSIX values is the
  deferred/span-memo route. `StrongFullCert` is retained as a CE-mining tool,
  but the `bba` greedy-sequence CE shows that local final-state
  `Val => Option[Val]` reconstruction is not enough by itself. The optional
  `-CheckStrongDeferredMemo` smoke now includes the known CE grid and must
  remain green before any BR-039/BR-040 claim can use this route.
- Strong cubic frontier reporting: optional `-StrongCubicTop` /
  `-ScalaSmokeStrongCubicTop` reports multiple high-ratio size-pressure
  witnesses for the strong-deferred CEGAR loop. The report also includes a
  distinct-regex frontier so repeated inputs for one regex do not hide other
  structural pressure families. This is diagnostic tooling only; it does not
  by itself satisfy BR-039 or BR-040.
- Checked original-value bridge: `FBound.thy` now has
  `rexp_span_posix` and the root bridge
  `bnullable_bders_simpStrong_intern_iff_rexp_span_posix_root`, plus a
  uniqueness theorem for the root span POSIX entry. This is useful BR-040
  proof infrastructure only; it does not pay until constructor-level
  reconstruction correctness is checked.
- Strong-deferred reconstruction package: `FBound.thy` now also has
  `strong_deferred_reconstruction_budget`, packaging the nullable gate,
  unique deferred value, bounded POSIX value table, and bounded split-probe
  table for the current span/memo route. This is BR-040 infrastructure only;
  the regex-size cubic tree/share bound remains open.
- Original non-backref fragment bridge: `RegLangs.thy` now has `legacy_rexp`,
  and `FBound.thy` has `legacy_rerase_intern`,
  `legacy_rexp_rerase_bders_simpStrong_intern`, and
  `strong_deferred_original_legacy_budget`. Future original-file cubic
  statements can use the premise `legacy_rexp r` directly. This is BR-040
  infrastructure only and does not count as a bounty payout.
- Deferred span fragment closure: `FBound.thy` now also proves that
  `rexp_subterms`, span states, split probes, POSIX span entries, and POSIX
  span states all remain `legacy_rexp` when the root is `legacy_rexp`.
  `strong_deferred_original_legacy_budget` includes this closure for the value
  and split-probe tables. This supports BR-040 but remains infrastructure, not
  a payout.
- Strong row gate bridge: `FBound.thy` now connects
  `bpders_strong1_rows (intern r) s` to the current deferred-value route:
  under `legacy_rexp r`, existence of a nullable strong row is equivalent to
  existence of the unique `strong_deferred_span_value r s`. The same checkpoint
  adds `asize_intern` and `rsize_rerase_intern`, aligning annotated/skeleton
  size with original `rxsize`. This supports the Antimirov row-universe cubic
  route but remains infrastructure, not a payout.
- Checked original split probes: `FBound.thy` now also has
  `rexp_span_split_probes`, `rexp_span_all_split_probes`, their cardinality
  bounds, and one-directional original POSIX constructor rules for `ONE`, `CH`,
  `ALT`, `SEQ`, `STAR`, and `NTIMES`. This supports the current CEGAR route:
  keep the `bsimpStrong` tree as the nullable gate, mine local-certificate CEs,
  and prove exact values through bounded original-root span reconstruction.
  It is still infrastructure, not a BR-039/BR-040 payout.
- Countdown universe fix: original `rexp_subterms` is now reconstruction-aware
  for `NTIMES`, containing every countdown state `NTIMES r k` with `k <= n`.
  This is required for span reconstruction of counted repetitions; plain
  syntactic subterms are too weak. `rexp_span_posix_ALT1E`,
  `rexp_span_posix_ALT2E`, and `rexp_span_posix_SEQE` are checked inversion
  infrastructure only.
- StrongFull known-CE guard: optional smoke gate `-CheckStrongFullKnownCE`
  checks that the minimal greedy-boundary case still blocks local
  `StrongFullCert` reconstruction while `StrongDeferredMemo` matches baseline.
  This prevents accidental payout or proof work on the old local-certificate
  route. It is a diagnostic guard only.
- Checked span constructor support now includes alternatives, unit/empty,
  nonempty star, and counted-repetition intro rules:
  `rspan_accepts_RALTSI`, `rspan_accepts_RONE_emptyI`,
  `rspan_accepts_RSTAR_stepI`, `rspan_accepts_RNTIMES_zeroI`, and
  `rspan_accepts_RNTIMES_SucI`. These are infrastructure only, not a payout
  until an actual POSIX reconstruction relation is checked.
- Admin revocation note: all later mentions of `BR-036`, `BR-037`, `rsimp9`,
  `norm19`, or `path9` in these notes are historical diagnostics only. They are
  not active bounty targets, cannot be locked, and cannot be collected. New
  cubic work must pass the BR-038 smoke suite before any proof-oriented bounty
  can be attempted.
- BR-038/BR-039 now have a stronger Scala-gated smoke checkpoint, still not a
  payout: `PosixCubicSmoke.scala` checks exact POSIX value preservation on
  bounded generated regexes/inputs and the Chapter 7 `k=5` family at derivative
  lengths `4`, `8`, `12`, `16`, and `20` under the same `bsimpCubic`
  candidate. The broad grid belongs in Scala, not in Isabelle `eval` lemmas.
  `thesis_cubic_counterexample_G` and `thesis_cubic_counterexample_H` check
  that `bsimpCubic` is not merely a `bsimpStrong` wrapper because it cleans
  counted repetitions (`ANTIMES`) that `bsimpStrong` leaves untouched. The
  erased-language bridges `L_bsimpCubic`, `RL_rerase_bsimpCubic`, and
  `RL_rerase_bders_simpCubic` are checked support facts only; the full cubic
  theorem and POSIX/bitcode-preserving route remain open.
- BR-039/BR-040 payout is explicitly blocked by the optional deterministic
  random smoke diagnostic until repaired. With seed `20260602`, random case
  `99` finds a POSIX value mismatch for
  `STAR (ALT ONE (STAR (STAR (STAR (STAR (STAR (CH a)))))))` on input `aaa`.
  Default CI keeps random smoke off to preserve a green integration branch, but
  any proof/bounty attempt must run it and resolve this class of bitstream
  mismatch first.
- New diagnostic localization: the value mismatch is tied to destructive
  sequence reassociation in `bsimpCubic_ASEQ_atom`. Mode `no-reassoc` passes
  the tested random value smoke but fails the Chapter 7 threshold; mode
  `full` passes the threshold but fails random value smoke; mode
  `reassoc-nonnullable-left` still fails random value smoke. Therefore BR-039
  cannot pay for a simplifier that emits reassociated sequence syntax unless it
  also supplies a checked bitcode/value reconstruction theorem.
- New route evidence: the Scala harness now reports exact DAG and shape-DAG
  sizes for Chapter 7. Value-safe `no-reassoc` has large tree size but compact
  shared structure (`k=8`, length `32`: tree `18643`, exact DAG `547`,
  shape DAG `312`). This supports a future hash-consed row-universe or delayed
  linear-form bounty route, but it is not itself a payout because BR-039 still
  asks for a smoke-tested candidate with an explicit POSIX-value story.
- Stronger route evidence: diagnostic mode `expanded-keyed-no-reassoc` indexes
  virtual expanded rows such as `a.c` and `b.c` from `(a+b).c` for pruning while
  keeping the emitted syntax `no-reassoc` shaped. It passes the current
  exhaustive depth `2`/input `3` smoke (`84,300` pairs) and deterministic random
  smoke (`2,000` cases, seed `20260602`). On Chapter 7 `k=8`, length `128`, it
  improves plain `no-reassoc` final sizes from tree/exact-DAG/shape-DAG
  `48077/1721/718` to `34581/1465/462`, with a slightly larger shared pool
  `11170 -> 11810`. This is a promising BR-039 design lead, not a payout.
- Thesis Figure 7.6 `k=5` caveat: `bsimpStrong` remains the route that gives
  hundreds-scale ordinary tree size (`n=16` is `820`, matching checked Isabelle
  facts). `expanded-keyed-no-reassoc` at `n=30` still has ordinary tree size
  `3849`, despite compact exact DAG/shape-DAG `276/132`. Therefore no bounty may
  describe this diagnostic as a tree-level reproduction of thesis
  `strongBlexer`; any payout must either recover a value-safe tree simplifier or
  state and prove a shared-representation reconstruction theorem.
- New optional smoke gate `-CheckStrong` blocks a naive tree-level
  `strongBlexer` payout: current `bsimpStrong` fails exact POSIX value
  preservation on `STAR (STAR (CH a))` with input `a`, because nested-star value
  structure is collapsed. This is an expected diagnostic failure, not a default
  CI failure. BR-039 may not use `bsimpStrong` as-is without a checked
  value-reconstruction theorem or a repaired value-safe strong simplifier.
- CE-driven safe-output diagnostic: `bsimpStrongSafe` repairs the first wave of
  value counterexamples by disabling nested-star collapse, nonempty right-unit
  deletion, star absorption, and sequence reassociation in the emitted regex.
  It passes exact POSIX smoke through random depth `5`/input `6`, seed
  `20260602`, but does not preserve the thesis tree-size plateau (`k=5,n=30`
  tree `5133`). It is therefore route evidence only. A payable tree-level
  strong candidate must keep the small `bsimpStrong` regex and add checked
  value transformers/reconstruction for those rewrites, or find a different
  value-safe pruning rule with comparable size.
- CE-driven strong-reconstruction sketch: `scala_cubic_smoke.ps1
  -TraceStrongRecon` now checks local transformer equations for the first
  strong CE witnesses while retaining the actual small `bsimpStrong` output.
  It also checks annotated-value local certificate laws for those rewrite
  classes over small input grids. This is positive route evidence, not a bounty
  claim; payout still requires a compositional derivative-time certificate or
  theorem.
- Strong core certificate prototype: `scala_cubic_smoke.ps1
  -CheckStrongCoreCert` checks the sequence/star core certificate on derivative
  expressions. Current smoke covers `84,300` exhaustive derivative expressions
  plus `3,000` deterministic random expressions with seed `20260602`.
  Alternation flatten/distinct is now included. This is still not a payout
  artifact because the Isabelle proof-facing story remains open.
- Certified-core size trace before row pruning was k=5,n=30 at `2342` versus
  thesis `bsimpStrong` at `958`; this identified row pruning as the next target.
- Certified row-pruning prototype: the direct shared-suffix pattern is now
  certificate-smoked in the surrounding `AALTs` context. The new k=5,n=30
  certified-core size is `678`, with `84,300` exhaustive derivative-expression
  checks and `3,000` deterministic random checks passing.
- Derivative-loop certificate smoke: `scala_cubic_smoke.ps1
  -CheckStrongCoreLoop` now composes `bder`, `bsimpStrongCoreCert`, `injectA`,
  and the accumulated continuation across the whole input. It matches
  `baselineValue` on `84,300` exhaustive pairs and `3,000` deterministic random
  cases. This upgrades the route from local certificates to whole-lexer Scala
  evidence, but Isabelle proof-facing invariants are still required before
  payout.
- Full strong-tree certificate diagnostic: `scala_cubic_smoke.ps1
  -CheckStrongFullLoop -FindStrongFullCE -TraceStrongFullLoop` keeps the
  `bsimpStrong`-scale tree and currently passes exhaustive depth `2`/input `3`
  plus `10,000` deterministic random cases at depth `6`/input `7`. It also
  reproduces the Chapter 7 `k=5` plateau with max state `721`. This does not
  pay BR-039: depth `7`/input `8`, seed `20260602`, case `622` shrinks to
  `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`, where the current
  certificate gives the final `a` to the right star instead of the left POSIX
  greedy star. This CE must be repaired or bypassed by a checked span/memo
  reconstruction theorem before any full-strong candidate can pay out.
- Checked span-universe support: `GeneralRegexBound.thy` now contains
  `rspan_states`, `rspan_split_probes`, and subset/cardinality bounds matching
  the Scala memo reconstruction accounting (`rsize(r) * (|s|+1)^2` states and
  `rsize(r) * (|s|+1)^3` split probes). This is proof infrastructure for
  BR-040-style reconstruction interfaces, not a payout by itself: the actual
  POSIX reconstruction relation still needs to prove that its memo table and
  split probes are subsets of these universes and agree with the existing
  POSIX value relation.
- Checked memo-table specifications: `rspan_accepts` and
  `rspan_all_split_probes` now give concrete table targets for the span route,
  with checked subset/cardinality bounds inherited from the universes. This is
  stronger than raw universe accounting, but still not a bounty payout until a
  reconstruction correctness relation is proved.
- Checked span algebra: `rslice_append`, `rspan_accepts_root_iff`,
  `rspan_accepts_RSEQI`, and `rspan_accepts_RSTAR_emptyI` now provide the first
  constructor rules for the memo-table correctness proof. These are
  infrastructure only; missing constructor/extraction rules and POSIX value
  reconstruction still block payout.
- Proof-facing bridge: `CERTIFIED_STRONG_CORE.md` records the intended
  `cert_recon` relation, loop invariant, certificate constructors, and
  loop-size trace. This is planning evidence, not payout.
- BR-036/BR-037 route correction: a proof based only on `rsimp9`/`bsimp9`
  does not address the thesis Chapter 7 three-star evil family
  `STAR (STAR (ALTs [a*, (aa)*, ...]))`. That family is designed to require
  shared-suffix row pruning such as `(a + b).c + (a + d).c ->
  (a + b).c + d.c`. Future payout for the cubic-bound tranche must therefore
  close the strong-row route (`rsimpStrong`/`bsimpStrong`,
  `rpder_strong_rows`/`bpder_strong_rows`) or prove an equivalent pruning
  theorem. The existing `rsimp9`/path9 material remains useful scaffold for
  tail/countdown normalization and diagnostics, but an `rsimp9`-only closure is
  not sufficient for this bounty.
- BR-036 now has explicit checked regression sanity lemmas for the thesis
  cubic-bound examples: `thesis_cubic_evil3_aaa_norm19_rows_cubic` for the
  Chapter 6 evil shape `(a* + (aa)* + (aaa)*)*` after `aaa`, with
  `thesis_cubic_small_alt3_aaa_norm19_rows_cubic` retained only as a cheap
  contrast for the non-starred variant, and
  `thesis_cubic_ntimes_countdown_norm9_no_zero_counter` plus
  `thesis_cubic_ntimes_countdown_norm19_rows_cubic` for the `(a){3}`
  countdown. These confirm the candidate route on the motivating examples but
  do not settle BR-036. The thesis Chapter 7 stronger simplification/pruning
  idea is not yet a checked production simplifier and remains a design gap.
- BR-036/BR-037 now have checked negative/diagnostic evidence in `FBound.thy`
  for the Chapter 7 example: `thesis_ch7_evil5_bders_simp_size_16` records
  production `bders_simp` size `14876` on `a^16`, while
  `thesis_ch7_evil5_bders_simp8_size_16` records `1308` for the root-safe
  `bsimp8` variant and `thesis_ch7_evil5_bpders_norm17_row_size_16` records
  `645` for the row-list route. The checked overlap-prune facts
  `thesis_ch7_bsimp_misses_overlap_prune`,
  `thesis_ch7_overlap_pruned_smaller`, and
  `thesis_ch7_overlap_pruned_same_language` show why a real
  `bsimpStrong`/`prune` design is still needed: current `bsimp` leaves the
  `(a + b + d).c + (a + c + e).c` overlap untouched, while the pruned erasure
  is language-equivalent and smaller. This is not a bounty payout.
- BR-037 has a first checked executable prototype, not a payout:
  `bsimpStrong`, `bsimpStrong_prune_rows`, and
  `bders_simpStrong` now live in `BlexerSimp.thy` on the original `arexp`
  datatype. The generic lemma `L_prune_eq1_against_AALTs` checks the
  erasure-language basis for deleting later alternatives covered by earlier
  alternatives under `eq1`. The concrete Chapter 7 facts
  `thesis_ch7_bsimpStrong_prunes_overlap`,
  `thesis_ch7_bsimpStrong_overlap_smaller`, and
  `thesis_ch7_bsimpStrong_overlap_same_language` show that the prototype
  performs the missing `(a + b + d).c + (a + c + e).c` prune. Remaining
  bounty requirements: POSIX/bitcode preservation, derivative-size regression
  on the full evil family, and integration without weakening existing lexer
  theorems.
- BR-037 now has the first full evil-family size regression for that prototype:
  `thesis_ch7_evil5_bders_simpStrong_lt_simp8_size_16` and
  `thesis_ch7_evil5_bders_simpStrong_size_16_under_825` show
  `bders_simpStrong` below `825` on `k=5, a^16`, while
  `thesis_ch7_evil5_bders_simpStrong_size_16_not_under_812` gives a checked
  lower-bound sanity check. This confirms the Chapter 7 prune is active beyond
  the toy overlap, but it is still only progress:
  row-list normalization remains smaller (`645`), and no general cubic theorem
  or POSIX/bitcode preservation theorem has been awarded.
- BR-037 also has the checked erasure-language theorem `L_bsimpStrong`,
  proving the executable prototype preserves the language after erasure. This
  is still only a support theorem: a bounty payout needs the POSIX/bitcode
  preservation route and production integration, not erased-language safety
  alone.
- BR-036 now also has the checked norm9-specific scaffold
  `rpath9_atom_frontier_acc`, `rpath9_atom_frontiers`,
  `partial_derivative_path9_atom_frontier_universe`,
  `finite_rpath9_atom_frontier_acc`, `finite_rpath9_atom_frontiers`,
  `finite_partial_derivative_path9_atom_frontier_universe`, and
  `path9_atom_frontier_avoids_old_atom_explosion`. The raw-tail bridge
  `rpath9_tail`, `rsize_rpath9_tail_le`,
  `rfrontier_rpath9_tail_member_size_le`,
  `rfrontier_rsimp7_SEQ_atom_rsimp9_rpath9_tail_member_size_le`, and
  `rfrontier_rpath9_tail_RSEQ_member_size_le` is also checked; it is progress
  toward the remaining linear member-size premise, not a payout claim. The
  generic frontier helper `rfrontier_rsimp7_SEQ_atom_rsimp9_member_size_le`
  and the `RCHAR` raw-tail base cases
  `rpath9_atom_frontier_acc_RCHAR_rpath9_tail_member_size_le` and
  `rpath9_atom_frontier_acc_RCHAR_rpath9_tail_RSEQ_member_size_le` are
  checked as the first leaves for that induction. The carried-constructor
  raw-tail handoffs
  `rpath9_atom_frontier_acc_RSEQ_rpath9_tail_member_sizeI`,
  `rpath9_atom_frontier_acc_RSTAR_rpath9_tail_member_sizeI`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_rpath9_tail_member_sizeI` are also
  checked. The top-level raw-tail member-size interfaces
  `rpath9_atom_frontiers_RSEQ_member_size_rpath9_tailI`,
  `rpath9_atom_frontiers_RSTAR_member_size_rpath9_tailI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_size_rpath9_tailI` are also
  checked, exposing the `RSEQ ... RONE` outer frontier cases through
  `rpath9_tail`. The checked counterexample
  `rpath9_tail_prefix_continuation_bound_counterexample` rules out using a
  continuation-only budget for long prefixes; the checked parent-budget
  interfaces
  `rpath9_atom_frontiers_RSEQ_member_size_rpath9_tail_parentI`,
  `rpath9_atom_frontiers_RSTAR_member_size_rpath9_tail_parentI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_size_rpath9_tail_parentI`
  are the intended next interface for the remaining linear member-size proof.
  The checked counterexamples
  `path9_frontiers_not_subset_norm9_frontier_universe` and
  `path9_frontiers_not_subset_original_frontier_universe` rule out reusing the
  old frontier universe as a direct superset of path9 frontiers.
  The checked budget layer
  `rpath9_member_budget`, `rpath9_member_budget_list`,
  `rpath9_atom_frontier_acc_rpath9_tail_member_budget`, and
  `rpath9_atom_frontiers_member_budget` now packages the accumulator
  member-size recursion, but
  `rpath9_member_budget_nested_star_not_linear` shows this raw budget is too
  coarse for the final linear bound. The tighter checked layer
  `rpath9_tight_member_budget`, `rpath9_tight_member_budget_list`,
  `rpath9_tight_member_budget_le_member_budget`,
  `rpath9_atom_frontier_acc_rpath9_tail_tight_member_budget`,
  `rpath9_atom_frontiers_tight_member_budget`, and
  `rpath9_tight_member_budget_nested_star_linear_sanity` is the current route
  for the remaining linear member-size premise. The checked
  `rpath9_tight_member_budget_nested_star_less_raw` witness records that the
  tight budget strictly improves the raw budget on the nested-star obstruction.
  The checked splitter layer
  `rpath9_tail_RSEQ_size_le`,
  `rpath9_tight_member_budget_list_boundI`,
  `rpath9_tight_member_budget_RALTS_boundI`,
  `rpath9_tight_member_budget_RSEQ_boundI`,
  `rpath9_tight_member_budget_RSTAR_boundI`, and
  `rpath9_tight_member_budget_RNTIMES_nonzero_boundI` is progress toward that
  premise only; it isolates the constructor obligations for the required
  root-owned/carried-continuation induction and is not a BR-036 payout claim.
  The one-step closure interface now also includes
  `rpder_norm9_path9_atom_frontier_step_RALTS_selfI` and
  `rpder_norm9_path9_atom_frontier_step_RSEQ_selfI`; the latter packages the
  nullable right-child lift and leaves only the left carried-continuation
  bridge as the explicit `RSEQ` blocker.
  The first checked slice of that blocker is now
  `rder_path_continuations_acc_RCHAR_left_path9_stable`, with checked stable
  right-tail constructor leaves
  `rder_path_continuations_acc_RCHAR_left_path9_RZERO`,
  `rder_path_continuations_acc_RCHAR_left_path9_RONE`,
  `rder_path_continuations_acc_RCHAR_left_path9_RCHAR`,
  `rder_path_continuations_acc_RCHAR_left_path9_RSTAR`, and
  `rder_path_continuations_acc_RCHAR_left_path9_RNTIMES`. These facts expose
  the exact norm-tail stability assumptions needed for `RALTS` and nested
  `RSEQ`; they are progress evidence only and do not close BR-036.
  The carried-continuation splitter layer now also includes
  `rder_path_continuations_acc_RCHAR_frontierI`,
  `rder_path_continuations_acc_RALTS_carriedI`,
  `rder_path_continuations_acc_RSEQ_carriedI`,
  `rder_path_continuations_acc_RSTAR_carriedI`, and
  `rder_path_continuations_acc_RNTIMES_carriedI`. These are
  universe-parametric scaffold facts for the path9 one-step closure and are
  not a payout claim.
  The first checked one-step leaves built on this layer are
  `rpder_norm9_path9_atom_frontier_step_RSEQ_RCHAR_stable` with
  `RZERO`/`RONE`/`RCHAR`/`RSTAR`/`RNTIMES` right-tail instances, plus
  `rpder_norm9_path9_atom_frontier_step_RSTAR_RCHAR` and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_RCHAR`. These close the
  character-body base leaves for the path9 induction; the general
  `RALTS`/nested-`RSEQ` cases remain open.
  The
  checked accounting
  interface adds
  `partial_derivative_path9_atom_frontier_universe_card_le`,
  `partial_derivative_path9_atom_frontier_universe_member_size_boundI`,
  `partial_derivative_path9_atom_frontier_universe_member_size_linearI`, and
  `rsizes_distinct_path9_atom_frontier_universe_cubicI`. This is progress
  evidence, not a payout claim. The newer tight-budget bridge
  `rpath9_atom_frontiers_tight_member_budget_linearI`,
  `partial_derivative_path9_atom_frontier_universe_member_size_tight_budgetI`,
  and `rsizes_rpders_norm19_rows_rsimp9_path9_tight_budget_cubicI` reduces
  the remaining member-size premise to the single top-level tight-budget
  inequality, while preserving the separate one-step `rpder_norm9_list`
  closure obligation for the smaller universe. The first checked
  closure-plumbing facts are
  `rsubterms_rsimp_ALTs_member`, `set_rflts_singleton_map_member`,
  `rflts_singleton_rsimp9_path9_atom_frontier`,
  `rflts_map_rsimp9_path9_atom_subsetI`,
  `rflts_rsimp9_alt_child_path9_atom_subset`, and
  `rpder_norm9_path9_atom_frontier_step_RZERO/RONE/RCHAR`. The checked
  `RALTS`/`rsimp_ALTs` layer adds `set_rflts_map_member_exists`,
  `set_rflts_map_memberE`, `rflts_map_rsimp9_alt_path9_atom_subset`,
  `rflts_map_rsimp9_rsimp_ALTs_path9_atom_subset`,
  `rpath9_atom_frontiers_alt_child_subset`,
  `rpath9_atom_frontiers_alt_child_universe`,
  `rpder_norm9_path9_atom_frontier_step_RALTS_parentI`, and
  `rpder_norm9_path9_atom_frontier_step_rsimp_ALTs_parentI`. The carried
  constructor parent-inclusion facts are
  `rpath9_atom_frontiers_universe`,
  `rpath9_atom_frontiers_seq_left_subset`,
  `rpath9_atom_frontiers_seq_left_universe`,
  `rpath9_atom_frontiers_seq_right_subset`,
  `rpath9_atom_frontiers_seq_right_universe`,
  `rpath9_atom_frontiers_star_body_subset`,
  `rpath9_atom_frontiers_star_body_universe`,
  `rpath9_atom_frontiers_ntimes_body_subset`, and
  `rpath9_atom_frontiers_ntimes_body_universe`. The checked parent-target
  derivative splitters are
  `rpder_norm9_path9_atom_frontier_step_RSEQ_parentI`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_parentI`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_parentI`. The direct carried
  variants
  `rpder_norm9_path9_atom_frontier_step_RSEQ_directI`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_directI`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_directI` are also checked;
  they reduce the remaining carried branch work to singleton
  `set (rflts [rsimp9 p])` obligations. The nullable
  sequence right-branch lift is also checked:
  `rnullable_rsimp9`,
  `rsubterms_rsimp9_RSEQ_right_nullable_universe`,
  `partial_derivative_path9_atom_frontier_universe_RSEQ_right_nullable_subset`,
  and `rpder_norm9_path9_atom_frontier_step_RSEQ_parent_childI`.
  The normalized-alternative child lifts are checked:
  `partial_derivative_path9_atom_frontier_universe_RALTS_flat_child_subset`,
  `rsubterms_nonalt_flattened_subterms`,
  `rsubterms_rsimp9_alt_child_nonalt_path9_atom_subset`,
  `partial_derivative_path9_atom_frontier_universe_RALTS_nonalt_child_member`,
  `rpder_norm9_path9_atom_frontier_step_RALTS_childI`, and
  `rpder_norm9_path9_atom_frontier_step_rsimp_ALTs_childI`.
  The first direct accounting split for `rpath9_atom_frontiers` is checked:
  `plus2_square_plus_plus3_square_le`,
  `sum_list_rsize_plus2_square_le_rsizes_plus3_square`,
  `card_rpath9_atom_frontier_acc_list_le`,
  `card_rpath9_atom_frontiers_RALTS_le`, and
  `card_rpath9_atom_frontiers_RALTS_quadraticI`. The matching `RALTS`
  member-size split is checked as
  `rpath9_atom_frontiers_RALTS_member_sizeI`.
  The base accounting facts for `RZERO`, `RONE`, `RCHAR`, and zero-count
  `RNTIMES` are checked via
  `card_rpath9_atom_frontiers_RZERO_quadratic`,
  `card_rpath9_atom_frontiers_RONE_quadratic`,
  `card_rpath9_atom_frontiers_RCHAR_quadratic`,
  `rpath9_atom_frontiers_RZERO_member_size`,
  `rpath9_atom_frontiers_RONE_member_size`,
  `rpath9_atom_frontiers_RCHAR_member_size`,
  `card_rpath9_atom_frontiers_RNTIMES_zero_quadratic`, and
  `rpath9_atom_frontiers_RNTIMES_zero_member_size`.
  The next carried-continuation accounting helpers are also checked:
  `rfrontier_member_size_le_rsize`, `card_rfrontier_rsimp7_SEQ_atom_le`, and
  `rfrontier_rsimp7_SEQ_atom_member_size_le`.
  The first path9 accounting constructor splitters are checked:
  `card_rpath9_atom_frontiers_RSEQ_le`,
  `card_rpath9_atom_frontiers_RSTAR_le`,
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_le`,
  `rpath9_atom_frontiers_RSEQ_member_sizeI`,
  `rpath9_atom_frontiers_RSTAR_member_sizeI`, and
  `rpath9_atom_frontiers_RNTIMES_nonzero_member_sizeI`.
  The conditional quadratic constructor layer is checked:
  `seq_component_product_plus_child_square_le`,
  `component_product_le_square`,
  `card_rpath9_atom_frontiers_RSEQ_quadraticI`,
  `card_rpath9_atom_frontiers_RSTAR_quadraticI`, and
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_quadraticI`; the remaining
  cardinality obligation is the carried collector product bound.
  Tail-normalization frontier bounds are checked:
  `rsize_rsimp4_SEQ_atom_RONE_le`,
  `rsize_rsimp7_SEQ_atom_RONE_le`,
  `rsize_rsimp7_SEQ_atom_rsimp9_RONE_le`,
  `card_rfrontier_rsimp7_SEQ_atom_RONE_le`,
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RONE_le`,
  `rfrontier_rsimp7_SEQ_atom_RONE_member_size_le`, and
  `rfrontier_rsimp7_SEQ_atom_rsimp9_RONE_member_size_le`.
  The carried-collector base cases are checked:
  `card_rpath9_atom_frontier_acc_RZERO_product`,
  `card_rpath9_atom_frontier_acc_RONE_product`,
  `card_rpath9_atom_frontier_acc_RCHAR_le`,
  `rpath9_atom_frontier_acc_RCHAR_member_size_le`,
  `card_rpath9_atom_frontier_acc_RCHAR_rsimp9_RONE_product`, and
  `rpath9_atom_frontier_acc_RCHAR_rsimp9_RONE_member_size`.
  The carried-collector constructor splitters are checked:
  `sum_list_map_rsize_mult_right`,
  `card_rpath9_atom_frontier_acc_RALTS_productI`,
  `rpath9_atom_frontier_acc_RALTS_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RSEQ_le`,
  `rpath9_atom_frontier_acc_RSEQ_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RSTAR_le`,
  `rpath9_atom_frontier_acc_RSTAR_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_le`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_member_sizeI`.
  The product-introduction layer is also checked:
  `card_rpath9_atom_frontier_acc_RSEQ_productI`,
  `card_rpath9_atom_frontier_acc_RSTAR_productI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_productI`,
  `card_rpath9_atom_frontier_acc_RBACKREF4_productI`,
  `rpath9_atom_frontier_acc_RBACKREF4_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RHALF_productI`,
  `rpath9_atom_frontier_acc_RHALF_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RRESIDUE_product`, and
  `rpath9_atom_frontier_acc_RRESIDUE_member_size`.
  The normalized nested-tail budget facts are checked:
  `rsize_rsimp7_SEQ_atom_rsimp9_nested_RONE_le`,
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_nested_RONE_le`, and
  `rfrontier_rsimp7_SEQ_atom_rsimp9_nested_RONE_member_size_le`.
  The corresponding `RCHAR` accumulator instances are checked:
  `card_rpath9_atom_frontier_acc_RCHAR_rsimp9_nested_RONE_product` and
  `rpath9_atom_frontier_acc_RCHAR_rsimp9_nested_RONE_member_size`.
  The `RSEQ` normalized-tail handoff is checked:
  `card_rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_productI` and
  `rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_member_sizeI`.
  The `RSTAR`/`RNTIMES` normalized-tail handoffs are checked:
  `card_rpath9_atom_frontier_acc_RSTAR_rsimp9_RONE_productI`,
  `rpath9_atom_frontier_acc_RSTAR_rsimp9_RONE_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_productI`, and
  `rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_member_sizeI`.
  The budget-compatible variants are checked:
  `card_rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_balanced_productI`,
  `rpath9_atom_frontier_acc_RSEQ_rsimp9_RONE_balanced_member_sizeI`,
  `card_rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_outer_productI`,
  and `rpath9_atom_frontier_acc_RNTIMES_nonzero_rsimp9_RONE_outer_member_sizeI`.
  The top-level path9 frontier cardinality bound is now checked:
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RSTAR_le`,
  `card_rfrontier_rsimp7_SEQ_atom_rsimp9_RNTIMES_le`,
  `sum_list_rsize_times_rsize_plus_le`, `seq_frontier_acc_card_arith`,
  `card_rpath9_atom_frontier_acc_le_size_frontier`, and
  `card_rpath9_atom_frontiers_quadratic`. The relaxed top-level interfaces
  `card_rpath9_atom_frontiers_RSEQ_quadratic_seq_RONEI`,
  `card_rpath9_atom_frontiers_RSTAR_quadratic_seq_RONEI`, and
  `card_rpath9_atom_frontiers_RNTIMES_nonzero_quadratic_seq_RONEI` are also
  checked. Remaining BR-036 proof debt is linear member-size for the path9
  frontier universe and one-step `rpder_norm9_list` closure.
  The cubic interface now consumes the checked card theorem directly via
  `rsizes_distinct_path9_atom_frontier_universe_cubic_member_sizeI`,
  `rsizes_rpders_norm19_rows_path9_atom_frontier_universe_cubic`, and
  `rsizes_rpders_norm19_rows_rsimp9_path9_atom_frontier_cubicI`; future work
  only needs the linear member-size premise and the one-step path9 closure.
  The current left-continuation bridge has a checked stable-tail helper layer:
  `rsimp4_SEQ_atom_RONE_stable_rsimp7_SEQ_atom`,
  `rsimp4_SEQ_atom_RONE_stable_rsimp_ALTs`, and
  `rsimp4_SEQ_atom_RONE_stable_rdistinct`. These do not collect BR-036, but
  they are the next modular interface for closing `RALTS`/nested-`RSEQ`
  carried-tail cases without broad slow automation.
  The stable-tail left bridge now also has a checked `RALTS`-of-`RCHAR`
  package: `rpath9_atom_frontiers_seq_alt_left_subset`,
  `rpath9_atom_frontiers_seq_alt_left_universe`,
  `rder_path_continuations_acc_RALTS_RCHARs_left_path9_stable`, and
  `rpder_norm9_path9_atom_frontier_step_RSEQ_RALTS_RCHARs_stable` with
  `RZERO`/`RONE`/`RCHAR`/`RSTAR`/`RNTIMES` right-tail instances. This is
  checked progress toward one-step closure, not a BR-036 payout claim.
  The same character-alternative body shape is now checked for `RSTAR` and
  `RNTIMES` via
  `rder_path_continuations_acc_RALTS_RCHARs_root_path9_RSTAR`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_RALTS_RCHARs`,
  `rder_path_continuations_acc_RALTS_RCHARs_root_path9_RNTIMES`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_RALTS_RCHARs`. The counted
  proof explicitly splits the zero-predecessor case, where `RONE` is admitted
  by the universe rather than by a body-frontier inclusion.
  The normalized alternative shape is also bridged by
  `rpder_norm9_path9_atom_frontier_step_RSEQ_rsimp_ALTs_RCHARs_stable`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_rsimp_ALTs_RCHARs`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_rsimp_ALTs_RCHARs`, which
  split `rsimp_ALTs` into empty, singleton-character, and genuine-`RALTS`
  cases. This is still only checked progress toward BR-036.
  Character-only alternatives now survive the literal `rsimp9 (RALTS rs)`
  normalizer path via `rflts_RCHARs_eq`, `RCHARs_rflts`,
  `RCHARs_rflts_map_rsimp9`, `RCHARs_rdistinct`, and
  `RCHARs_rdistinct_rflts_map_rsimp9`. The direct closure packages
  `rpder_norm9_path9_atom_frontier_step_RSEQ_rsimp9_RALTS_RCHARs_stable`,
  `rpder_norm9_path9_atom_frontier_step_RSTAR_rsimp9_RALTS_RCHARs`, and
  `rpder_norm9_path9_atom_frontier_step_RNTIMES_rsimp9_RALTS_RCHARs` are
  checked for that exact normalized shape.

## Completed

| ID | Task | Bounty | Est. Lines | Difficulty | Est. USD | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |
| BR-001 | Language nullable/derivative pilot | 200 | 80 | 6 | 200 | DONE | Codex | BackRefLang.thy:BL_BBACKREF_empty,xnullable_correctness,xder_correctness,xders_correctness | Isabelle:BackRefPilot | PR #1, merged |
| BR-002 | Value/Prf/flat correspondence pilot | 160 | 60 | 6 | 160 | DONE | Codex | BackRefValues.thy:BL_flat_BPrf | Isabelle:BackRefPilot | `BackRefValues.thy`, build passes |
| BR-003 | Add `bmkeps` for pilot nullable values | 80 | 20 | 4 | 80 | DONE | Codex | BackRefValues.thy:bmkeps | Isabelle:BackRefPilot | `bmkeps` in `BackRefValues.thy` |
| BR-004 | Prove `bmkeps` flat/prf correctness | 120 | 30 | 5 | 120 | DONE | Codex | BackRefValues.thy:bmkeps_flat,bmkeps_BPrf | Isabelle:BackRefPilot | `bmkeps_flat`, `bmkeps_BPrf` |
| BR-005 | Draft `binjval` statement blueprint | 500 | 30 | 5 | 500 | DONE | Opus | BackRefValues.thy:binjval | Isabelle:BackRefPilot | Commit `b9da0e1` |
| BR-006 | Add guard scripts for bounty/role checks | 60 | 10 | 3 | 60 | DONE | Codex | agent_hunt_pipeline/scripts/backref_bounty_guard.py;agent_hunt_pipeline/scripts/backref_role_guard.py | LocalGuards | `backref_bounty_guard.py`, `backref_role_guard.py` |
| BR-007 | Generalized four-language backreference blueprint | 160 | 20 | 5 | 160 | DONE | Codex | BackRefLang.thy:backref_lang4,backref_lang_as_backref_lang4 | Isabelle:BackRefPilot | `backref_lang4`, `backref_lang_as_backref_lang4` |
| BR-008 | Draft derivative story for generalized `backref_lang4` | 800 | 60 | 6 | 800 | DONE | Codex | BackRefLang.thy:backref_lang4I,Der_backref_lang4 | Isabelle:BackRefPilot | Derivative splits prefix, capture-with-accumulator, and post-capture tail |
| BR-009 | Local and GitHub Isabelle CI with anti-cheat gate | 260 | 15 | 4 | 260 | DONE | Codex | agent_hunt_pipeline/scripts/isabelle_ci.ps1;agent_hunt_pipeline/scripts/backref_no_cheat_guard.py;agent_hunt_pipeline/scripts/write_ci_certificate.py;.github/workflows/isabelle.yml | Isabelle:Posix+BackRefPilot | CI certificate only after both sessions pass |
| BR-010 | Reproduce recurring tmux prompt loop | 90 | 10 | 3 | 90 | DONE | Codex | agent_hunt_pipeline/scripts/backref_idle_watch.sh;agent_hunt_pipeline/scripts/test_tmux_recurring_prompt.sh;agent_hunt_pipeline/WINDOWS_RUNBOOK.md | WSL:tmux-recurring-test | Same paper prompt injected repeatedly |
| BR-011 | Prove `bflat (binjval r c v) = c # bflat v` | 1,000 | 40 | 6 | 1,000 | DONE | Opus | BackRefValues.thy:binjval_flat | Isabelle:BackRefPilot | Commit `6dc8e03` |
| BR-012 | Prove `BPrf (binjval r c v) r` when `BPrf v (xder c r)` | 1,200 | 50 | 7 | 1,200 | DONE | Opus | BackRefValues.thy:binjval_BPrf | Isabelle:BackRefPilot | Commit `6dc8e03` |
| BR-013 | Define and prove `blexer` for pilot `brexp` | 1,500 | 80 | 7 | 1,500 | DONE | Opus | BackRefValues.thy:blexer,blexer_BPrf,blexer_flat,blexer_correct_None,blexer_correct_Some | Isabelle:BackRefPilot | Commit `2e8c45a` |
| BR-014 | Prove `blexer` correctness for pilot `brexp` | 2,000 | 100 | 8 | 2,000 | DONE | Opus | BackRefValues.thy:blexer_correctness,BPosix_binjval,blexer_POSIX,blexer_POSIX_iff | Isabelle:BackRefPilot | Cursor proof lane, Codex stabilization/build verification |
| BR-015 | POSIX value ordering for backreferences | 2,500 | 120 | 8 | 2,500 | DONE | Codex | BackRefValues.thy:BPosix_determ | Isabelle:BackRefPilot | Codex-B lane; uses `BSEQ_split_unique`, nullable empty-value uniqueness, and `BPosix_BBACKREF_value_unique` |
| BR-016 | Generalized `backref_lang4` value pilot | 1,500 | 70 | 7 | 1,500 | DONE | Codex | BackRefLang4Values.thy:bval4,bflat4,BPrf4,backref_lang4_flat_BPrf4,backref_lang_flat_BPrf4_special | Isabelle:BackRefPilot | Explicit value-evidence blueprint before datatype migration |
| BR-017 | Bitcoded backreference lexer definition | 2,500 | 100 | 8 | 2,500 | DONE | Codex | BackRefBlexer.thy:bbit,barexp,berase,bfuse,baintern,bbnullable,bbmkeps,bbder,bblexer | Isabelle:BackRefPilot | Separate pilot file; erase/nullable/derivative checks included |
| BR-018 | Bitcoded backreference lexer correctness | 3,000 | 150 | 9 | 3,000 | DONE | Codex | BackRefBlexer.thy:bbder_bretrieve,bblexer_blexer_retrieve | Isabelle:BackRefPilot | Derivative retrieval transport plus bitcoded output matches `bretrieve (baintern r)` of `blexer` value |
| BR-019 | Bounded fragment theorem for backreferences | 4,000 | 200 | 9 | 4,000 | DONE | Codex | BackRefBoundedBlueprint.thy:BL_bound_BBACKREF_derivative_family_card_bound,GBL_bound_GBACKREF4_derivative_family_card_bound | Isabelle:BackRefPilot | Constructor-specific bounded-fragment derivative families land in finite bounded-string universes with explicit cardinal bounds |
| BR-020 | Simplification rules for backreference lexer | 2,000 | 90 | 7 | 2,000 | DONE | Codex | BackRefBlexer.thy:bbsimp,bblexer_simp_correctness,bblexer_step_simp_correctness | Isabelle:BackRefPilot | Post-derivative and per-step simplified loops preserve `bblexer` |
| BR-021 | Cursor/Opus loop startup kit | 140 | 15 | 4 | 140 | DONE | Codex | .cursor/hooks/posix_loop.ps1;.cursor/hooks/posix_loop.sh;agent_hunt_pipeline/projects/posix-backref/loop-config.cursor-opus.json;agent_hunt_pipeline/projects/posix-backref/SLEEP_RUNBOOK.md | CursorHook:posix-loop | Supplemental robust hook and sleep runbook |
| BR-022 | Bounded-fragment statement blueprint | 1,200 | 60 | 7 | 1,200 | DONE | Codex | BackRefBoundedBlueprint.thy:bounded_GBACKREF4_finite_derivative_languages | Isabelle:BackRefPilot | Semantic bounded-language blueprint for finite derivative-language families; no production bounds or closed forms touched |
| BR-032 | Define stronger cubic-bound simplifier | 25,000 | 260 | 10 | 25,000 | DONE | Codex | BasicIdentities.thy:rsimp7_SEQ_atom,rsimp7_SEQ,rsimp7,RL_rsimp7;BlexerSimp.thy:bsimp7_ASEQ_atom,bsimp7_ASEQ,bsimp7,bpder_norm7_list,bp_der_norm7,bpder_norm7_rows;GeneralRegexBound.thy:rpder_norm7_list,rpd_der_norm7,rpder_norm7_rows,rpders_norm17_rows,RLS_rpders_norm17_rows,RL_rders_pder_norm7;FBound.thy:bsimp7_rerase,bp_der_norm7_rerase,rpders_norm17_rows_rerase,RL_rerase_bders_pder_norm7 | Isabelle:Posix | Checked `rsimp7`/`bsimp7` adds prefix star absorption `r*.(r*.k)=r*.k` over Antimirov row lists; final repeated-row cubic closure remains BR-033 |
| BR-035 | Define root-safe cubic simplifier | 25,000 | 260 | 10 | 25,000 | DONE | Codex | BasicIdentities.thy:rsimp8,rders_simp8,RL_rsimp8,RL_rders_simp8;BlexerSimp.thy:bsimp8,bders_simp8;FBound.thy:bsimp8_rerase,rders_simp8_size,RL_rerase_bders_simp8;GeneralRegexBound.thy:rsize_rsimp8_le,rsizes_rpders_norm17_rows_rsimp8_live_row_cubicI | Isabelle:Posix | New 50k cubic tranche: checked root normalizer preserves language and erasure while avoiding `rsimp7` root-size blow-up; conditional cubic interface is w.r.t. original `rsize r` |

## Effort Estimate Key

Every bounty must include an effort estimate before it can be locked:

- **Est. Lines**: approximate lines of a textbook proof for this result.
- **Difficulty**: formalization difficulty on a 1-10 scale (1 = trivial, 10 = research-level).
- **Est. USD**: approximate cost assuming $100/hour of expert Isabelle work.

Estimates assume all previous results in the dependency chain are already proved.

## Locks

| Lock ID | Task ID | Agent | Deposit | Branch | Expires UTC | Status |
| --- | --- | --- | ---: | --- | --- | --- |
| - | - | - | 0 | - | - | RELEASED |
| L-OPUS-015 | BR-015 | Opus | 250 | codex/backref-values | 2026-05-27T07:38:41Z | RELEASED |
| L-CODEX-B-015 | BR-015 | Codex | 250 | codex/backref-values | 2026-05-27T15:44:00Z | COLLECTED |
| L-CODEX-A-022 | BR-022 | Codex | 120 | codex/backref-values | 2026-05-27T15:44:01Z | COLLECTED |
| L-CODEX-017 | BR-017 | Codex | 250 | codex/backref-values | 2026-05-27T09:35:51Z | COLLECTED |
| L-CODEX-A-019 | BR-019 | Codex | 400 | codex/backref-values | 2026-05-27T18:46:17Z | COLLECTED |

## Lock Rules

- Lock deposit: 10% of bounty, rounded up.
- Maximum **10** active locks per agent.
- Locks expire after **24 hours**.
- Push locks immediately if multiple agents are active.
- Lock-or-lose: if someone else proves a locked theorem, bounty goes to locker.
- A lock does not authorize statement changes.
- Admin can clear stale locks.
- Expired lock deposit is forfeited (not refunded).

## Ledger

| Time UTC | Agent | Action | Task ID | Amount | Balance After | Notes |
| --- | --- | --- | --- | ---: | ---: | --- |
| 2026-05-22T14:00:00Z | Codex | COLLECT | BR-001 | 200 | 200 | Language nullable/derivative pilot merged in PR #1 |
| 2026-05-22T14:20:00Z | Codex | COLLECT | BR-002 | 160 | 360 | Value/Prf/flat correspondence |
| 2026-05-22T14:28:00Z | Codex | COLLECT | BR-003 | 80 | 440 | `bmkeps` definition |
| 2026-05-22T14:28:00Z | Codex | COLLECT | BR-004 | 120 | 560 | `bmkeps` flat and Prf correctness |
| 2026-05-25T16:24:31Z | Opus | COLLECT | BR-005 | 500 | 500 | `binjval` definition |
| 2026-05-24T02:58:00Z | Codex | COLLECT | BR-006 | 60 | 620 | Bounty and role guard scripts |
| 2026-05-24T02:58:00Z | Codex | COLLECT | BR-007 | 160 | 780 | Generalized `backref_lang4` blueprint |
| 2026-05-25T03:40:00Z | Codex | COLLECT | BR-009 | 260 | 1,040 | Local and remote Isabelle CI gates |
| 2026-05-25T04:22:00Z | Codex | COLLECT | BR-010 | 90 | 1,130 | Recurring tmux prompt reproduction |
| 2026-05-25T15:24:00Z | Codex | COLLECT | BR-021 | 140 | 1,270 | Cursor/Opus loop startup kit |
| 2026-05-25T23:24:27Z | Opus | COLLECT | BR-011 | 1,000 | 1,500 | `binjval_flat` |
| 2026-05-25T23:24:27Z | Opus | COLLECT | BR-012 | 1,200 | 2,700 | `binjval_BPrf` |
| 2026-05-25T23:37:17Z | Opus | COLLECT | BR-013 | 1,500 | 4,200 | pilot `blexer` definition and language correctness |
| 2026-05-26T03:58:00Z | Opus | COLLECT | BR-014 | 2,000 | 6,200 | `blexer_correctness`, `BPosix_binjval`, `blexer_POSIX`, `blexer_POSIX_iff`; Codex stabilized build |
| 2026-05-26T07:38:41Z | Opus | LOCK | BR-015 | 250 | 5,950 | Lock L-OPUS-015 for POSIX value ordering / `BPosix_determ` |
| 2026-05-26T09:15:17Z | Codex | COLLECT | BR-008 | 800 | 2,070 | `backref_lang4I`, `Der_backref_lang4`; BackRefPilot passed |
| 2026-05-26T09:35:51Z | Codex | LOCK | BR-017 | 250 | 1,820 | Lock L-CODEX-017 for bitcoded backreference lexer definitions |
| 2026-05-26T09:42:18Z | Codex | COLLECT | BR-017 | 2,500 | 4,320 | `BackRefBlexer.thy` definitions plus erase/nullable/derivative checks; BackRefPilot passed |
| 2026-05-26T10:57:17Z | Codex | COLLECT | BR-018 | 3,000 | 7,320 | `bbder_bretrieve`, `bblexer_blexer_retrieve`; BackRefPilot passed |
| 2026-05-26T11:46:37Z | Codex | COLLECT | BR-020 | 2,000 | 9,320 | `bblexer_simp_correctness` and per-step `bblexer_step_simp_correctness`; BackRefPilot passed |
| 2026-05-26T11:57:08Z | Codex | COLLECT | BR-016 | 1,500 | 10,820 | `backref_lang4_flat_BPrf4`; BackRefPilot passed |
| 2026-05-26T15:43:53Z | Opus | RELEASE | BR-015 | 250 | 6,200 | Cursor/Opus retired because reconnect stalls made overnight work unreliable |
| 2026-05-26T15:44:00Z | Codex | LOCK | BR-015 | 250 | 10,570 | Codex-B takes over POSIX value ordering |
| 2026-05-26T15:44:01Z | Codex | LOCK | BR-022 | 120 | 10,450 | Codex-A takes non-conflicting bounded-fragment statement blueprint lane |
| 2026-05-26T16:06:05Z | Codex | COLLECT | BR-022 | 1,200 | 11,650 | `BackRefBoundedBlueprint.thy` semantic bounded-language finite derivative blueprint; BackRefPilot passed |
| 2026-05-26T18:16:47Z | Codex | COLLECT | BR-015 | 2,500 | 14,150 | `BackRefValues.thy:BPosix_determ`; BackRefPilot passed |
| 2026-05-26T18:46:17Z | Codex | LOCK | BR-019 | 400 | 13,750 | Codex-A locks bounded-fragment theorem packaging |
| 2026-05-26T18:46:18Z | Codex | COLLECT | BR-019 | 4,000 | 17,750 | `BackRefBoundedBlueprint.thy` constructor-specific derivative-family universe/card bounds; BackRefPilot passed |
| 2026-05-31T02:35:36Z | Codex | COLLECT | BR-032 | 25,000 | 42,750 | `rsimp7`/`bsimp7` prefix-star absorption definitions plus norm7 row drivers and erasure/language transfer; Posix and BackRefPilot passed |
| 2026-05-31T03:57:03Z | Codex | COLLECT | BR-035 | 25,000 | 67,750 | `rsimp8`/`bsimp8` root-safe simplifier, erasure/language bridge, size non-increase, and original-size conditional cubic interface; Posix and BackRefPilot passed |

## Sub-Bounty Rules

An agent may offer a sub-bounty from their own balance to request help:

1. Create a new task in Active with `Sub-bounty of BR-XXX` in Notes.
2. Record a `SUB_OFFER` ledger entry deducting from the offering agent.
3. Sub-bounty follows normal completion and guard rules.
4. Cancellation: `SUB_CANCEL` entry refunds the offering agent.

## Early-Finish Bonus

If the entire allocated bounty board is completed before the admin-set
deadline, 10% of the remaining unallocated pool is distributed equally among
agents who completed at least one bounty.

Run the full local CI before collecting or pushing:

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin
```
