# CLAUDE.md cubic route history (2026-06-03/04 generation), archived 2026-06-12

Verbatim text excised from agent_hunt_pipeline/projects/posix-backref/CLAUDE.md
by the secretary session. It documents the strong-memo / deferred-memo /
shared-DAG / certified-core route generation: route switches, scout scripts,
factor sweeps, plateau diagnostics, and the still-reusable FBound.thy /
GeneralRegexBound.thy interface names of that generation. The live route is in
MAINLINE.md at the repository root. Nothing below was edited.

---
The current default route is `strong-memo`: `bsimpStrong` is used only as a
small recognition tree, and exact POSIX values are reconstructed from the
original regex via span/memo tables. Language preservation alone is not enough
for a cubic candidate.

Default CI runs the bounded exhaustive `strong-memo` smoke plus the Chapter 7
memo trace. Before any cubic proof or bounty attempt, also run deterministic
deeper random smoke, for example
`scala_cubic_smoke.ps1 -Route strong-memo -RandomCases 2000 -RandomDepth 5 -RandomInputLength 6`.
If random smoke finds a POSIX value mismatch, the candidate is diagnostic only
until the simplifier or value-reconstruction story is repaired.

Before theorem work on a new cubic simplifier, refresh the Chapter 7
derivative-size plots:
`powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\ch7_derivative_size_compare.ps1`.
The report
`agent_hunt_pipeline/reports/ch7_derivative_size_compare/index.html` overlays
the thesis `strongTree` baseline, the deferred `strongMemoTree` route, and the
candidate/current emitted tree size by `k` and input length `n`. A simplifier
that is visibly worse than thesis Chapter 7 on this grid is a diagnostic only,
not a proof or bounty candidate.
Current graphs show that emitted-tree `bsimpCubic` is not the main route; keep
it as historical/negative evidence unless a future variant both matches the
thesis baseline and preserves POSIX values.
As of 2026-06-03, do not assign proof work to rescuing `bsimpCubic`; assign
testing and proof work to the memo strong tree route: POSIX value
reconstruction over the original regex plus a cubic shared/memo universe for
the `bsimpStrong` recognition states.
Treat this as a hard route switch, not a naming preference. A candidate that
only makes the emitted derivative tree small but cannot produce exact POSIX
values is not a cubic-bound candidate for this project. The active target is:
keep `bders_simpStrong` as the small recognition tree, reconstruct exact POSIX
values from the original regex via span/memo tables, then prove the
final-active rows, pair-budget, and row member-size bounds needed by
`FBound.thy:strong_deferred_original_final_active_budget_contract_with_member_bound`.
Do not silently replace the memo strong tree by the partial-derivative row
list. The optional row-list/factoring bridge has a dedicated shrinker,
`scala_cubic_smoke.ps1 -FindStrongRowsBridgeCE`, and currently still shrinks a
depth-6 random failure to
`SEQ(SEQ(STAR(SEQ(STAR(ALT(SEQ(CH(a),CH(b)),CH(a))),CH(a))),CH(a)),CH(b))`
on input `a`. The tempting root
`bsimpStrong (AALTs [] (bpdersStrong1Rows (intern r) s))` is not structurally
the Brzozowski strong derivative on that case. Any new row-list theorem route
must remove this smoke counterexample first.
For the shared-prune universe, prefer the active-suffix proof contract:
`FBound.thy:strong_deferred_original_raw_row_norm_active_suffix_memo_cubic_interface`
and `GeneralRegexBound.thy:raw_shared_prune_active_suffix_closure`. This
counts only real `RSEQ (RALTS rows) k` shared-suffix rows and avoids the broad
`None` bucket from the older same-suffix closure. The remaining proof burden is
active suffix-key count, active bucket size, and ordinary universe member-size
bound.
Use
`powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\ch7_deferred_memo_grid.ps1`
from the repository root to refresh the current deferred-memo plots. If the
PowerShell current directory is elsewhere, use the absolute script path:
`powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\Chengsong\Documents\AIPV2026Notes\posix-codex\agent_hunt_pipeline\scripts\ch7_deferred_memo_grid.ps1`.
The report includes
`strongMemoActiveRows`, `strongMemoActiveKeys`,
`strongMemoActiveMaxBucket`, `strongMemoActivePairBudget`, and the
active owner decomposition metrics `strongMemoActiveAltNodes`,
`strongMemoActivePayloadRoots`, `strongMemoActivePayloadDag`,
`strongMemoActiveKeyDag`, `strongMemoActiveComponentUnion`,
`strongMemoActiveDecompBound`, and `strongMemoActiveRowDagUniverse`; inspect
these before changing the proof universe. The `DecompBound` metric is the one
aligned with the Isabelle decomposition bound; the `ComponentUnion` metric is
only observational and need not cover the full row-DAG universe.
The `n=200` long-tail grid shows `strongMemoTree` is still promising, but the
unquotiented cumulative active prefix pool keeps growing for `k=8`. Treat
active-prefix metrics as diagnostics, not as the final root-owned cubic
universe unless a quotient/periodic/indexed bound is added.
The same report now includes final-state metrics
`strongMemoFinalActiveRows`, `strongMemoFinalActiveKeys`,
`strongMemoFinalActiveMaxBucket`, `strongMemoFinalActiveMaxRowSize`,
`strongMemoFinalActivePairBudget`, `strongMemoFinalActiveAltNodes`,
`strongMemoFinalActivePayloadRoots`, `strongMemoFinalActivePayloadDag`,
`strongMemoFinalActiveKeyDag`, `strongMemoFinalActiveComponentUnion`,
`strongMemoFinalActiveDecompBound`, and
`strongMemoFinalActiveRowDagUniverse`.
Prefer these when reasoning about the size of the final derivative tree; on
the current `k=5,8,10,12,n<=200` grid they stay tiny while the prefix pool
grows.
The current route is smoke-first memo-strong: `bders_simpStrong` is a
recognition gate, exact POSIX values come from original-regex span memoization,
and the size object is the final-active row-DAG owner table. Do not spend new
proof effort on `bsimpCubic` emitted-tree bounds unless a future implementation
first beats the memo-strong owner traces and passes exact POSIX value smoke.
On the proof side, use
`FBound.thy:card_strong_deferred_final_active_suffix_row_dag_universe_decomp_linearI`
as the component-to-owner bridge: it reduces the remaining row-DAG linear
target to linear bounds for final-active rows, payload-DAG universe, and
suffix-key-DAG universe.
Before trying to prove the final-active route, run the dedicated budget scout:
`powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\strong_memo_final_active_scout.ps1`.
It keeps exact POSIX value smoke enabled and checks optional linear rows and
member-size gates plus a quadratic pair-budget gate for the final derivative
state. A failing run prints a greedy-shrunk counterexample. A passing run is
smoke evidence only; it does not authorize a bounty claim without the
corresponding checked Isabelle theorem. The default scout now matches the
proof-facing exact-DAG/decomposition target: `RowsFactor=1.0`,
`PairFactor=1.0`, `MemberFactor=0.0`, `MemberDagFactor=2.0`,
`MemberShapeDagFactor=2.0`, `RowDagUniverseFactor=3.0`, and
`DecompBoundFactor=3.0`. Raw member-tree factors `1.0`, `2.0`, and `4.0`
are known too strong and should be treated as negative evidence for the wrong
metric, not as counterexamples to the memo/hash-consed route. The current
default three-seed scout passes on seeds `20260602,20260603,20260604`, `5000`
random cases each at depth `6`, input length `8`; worst exact-DAG/shape-DAG
ratio is `1.266667`.
Do not use a scout run that omits `strongMemoFinalActiveDecompBound` as
evidence for BR-040: the Isabelle bridge
`card_strong_deferred_final_active_suffix_row_dag_universe_decomp_linearI`
needs the row/payload/key decomposition, not just a visually small tree.
The named Isabelle metric is
`FBound.thy:strong_deferred_final_active_suffix_decomp_bound`; the preferred
final handoff is
`FBound.thy:strong_deferred_memo_lexer_final_active_decomp_linear_contract`.
Use that theorem when the proof has component bounds for final rows,
payload-DAG universe, and suffix-key-DAG universe.
If you want to probe the whole final memo-strong exact-DAG metric, use
`scala_cubic_smoke.ps1 -FindStrongMemoDagBudgetCE -StrongMemoDagFactor K`.
This is a diagnostic only. Recent smoke shows `K=2` is already false, shrinking
to `STAR(NTIMES(STAR(CH(b)),2))` on input `bb` while preserving exact POSIX
values. Do not turn this into a bounty target unless the intended theorem is
explicitly about the whole final DAG; the proof-facing target remains the
final-active row-DAG universe.
Use
`powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\strong_memo_final_active_factor_sweep.ps1`
to compare member factors without overwriting the main scout report. The
legacy raw-member sweep report shows factors `4` and `6` fail on seed
`20260602`, case `4784`, while `8` passes the three-seed `5000`-case grid.
A deeper sweep under
`agent_hunt_pipeline/reports/strong_memo_final_active_factor_sweep_deep/`
checks factors `8,10,12` on seeds
`20260602,20260603,20260604,20260605,20260606`, `10000` random cases each,
depth `7`, input length `10`. All pass, with worst member ratio `6.809524`.
This is historical raw-member evidence only. The active exact-DAG scout uses
`K = 2` as the current smoke-backed DAG/shape-DAG constant, and it is still
only a proof hypothesis until Isabelle derives it from the original regex
structure.
On the Isabelle side, the current handoff theorem for this route is
`FBound.thy:strong_deferred_original_final_active_max_row_dag_metrics_contract`.
It mirrors the Scala final-active row metrics: assume final row count `R` and
`strong_deferred_final_active_suffix_max_row_dag r s <= M`, then obtain exact
POSIX reconstruction, pair budget `R * R`, row-DAG universe size `R * M`, and
the span/split memo budgets. To obtain the desired cubic theorem, prove
original-regex-owned bounds for these two quantities, for example
`R <= C * rxsize r` and `M <= K * rxsize r`.
If the proof naturally constructs a row-DAG universe instead of the scalar
maximum, use
`FBound.thy:strong_deferred_original_final_active_row_dag_universe_metrics_contract`:
a bound on
`card (strong_deferred_final_active_suffix_row_dag_universe r s)` implies the
same `finalMaxRowDag` bound via the checked raw/strong bridge.
Prefer the single-universe theorem
`FBound.thy:strong_deferred_original_final_active_single_row_dag_universe_contract`
when possible. It needs only
`card (strong_deferred_final_active_suffix_row_dag_universe r s) <= D` and
then supplies final rows `<= D`, pair budget `<= D * D`, `finalMaxRowDag <= D`,
row-member exact-DAG `<= D`, and exact POSIX reconstruction.
For a factored proof, use
`FBound.thy:card_strong_deferred_final_active_suffix_row_dag_universe_le_rows_times_max`:
`card rowDagUniverse <= card finalRows * finalMaxRowDag`. This is often the
cleanest split if row count and max-row-DAG require different invariants.
For final-active proof work, prefer the syntax-facing lemmas
`raw_final_active_suffix_rows_iff`, `raw_final_active_suffix_keys_iff`, and
`raw_final_active_suffix_bucket_iff`, plus their lifted
`strong_deferred_final_active_suffix_*` versions. They characterize the active
objects as concrete `RSEQ (RALTS rows) k` subterms of the final strong tree,
which is the right shape for a structural proof.
On the Isabelle side, prefer
`GeneralRegexBound.thy:card_raw_shared_prune_active_suffix_closure_member_pair_budget_bound`
when possible: it uses the aggregate active pair-budget directly and is sharper
than only bounding active key count and max bucket size.
If a base cardinality bound is also available, use
`GeneralRegexBound.thy:card_raw_shared_prune_active_suffix_closure_member_pair_budget_card_bound`
to get the direct `C + P * M` closure-cardinality shape. Keep
`raw_shared_prune_active_suffix_pair_budget_bucket_bound` only as a fallback
sanity bridge back to the old `S * K * K` estimate.
For iterative or least-universe arguments, use the checked monotonicity facts
`raw_shared_prune_active_suffix_closure_mono` and
`raw_shared_prune_active_suffix_pair_budget_mono` instead of unfolding the
active definitions again.

For the current deferred-memo route, use
`FBound.thy:strong_deferred_memo_budget` as the checked accounting interface:
it packages the unique deferred-value gate, the quadratic combined
accept/value span-state budget, and the cubic split-probe budget. Do not
re-prove those bounds ad hoc in later files.
When starting from the non-backref fragment, prefer
`FBound.thy:strong_deferred_original_memo_budget`; it adds the legacy-subterm
closure facts needed by downstream original-file bound statements.
For the current leading conditional theorem, use
`FBound.thy:strong_deferred_original_raw_row_norm_closed_memo_cubic_interface`.
It combines the raw strong-row cubic-universe premises with the deferred POSIX
memo/reconstruction budget and keeps the old theorem numbering for the earlier
row-only interfaces untouched.

Do not count destructive sequence reassociation as a POSIX-value-preserving
output simplification. The Scala diagnostic mode localized a current
`bsimpCubic` gap to `(x.y).z -> x.(y.z)`: full reassociation controls the
Chapter 7 size trace but fails deterministic random value smoke, while
`no-reassoc` preserves tested values but grows beyond the threshold. Even the
tempting restriction "only reassociate when the left factor is non-nullable"
failed random value smoke. Reassociation may be used as a comparison key,
proof-only normalization, or generalized-value transfer route, but production
`bsimpCubic` needs a checked bitcode/value reconstruction theorem before it can
emit reassociated syntax.

The newest promising route is shared representation rather than destructive
syntax change. The Scala harness reports tree size, exact DAG size, and
shape-DAG size for Chapter 7 traces. Value-safe `no-reassoc` fails the old
tree threshold but has much smaller DAG measures, suggesting a hash-consed
row universe or delayed linear-form representation. Use those diagnostics to
guide design, but do not claim a tree-size theorem or bounty from DAG evidence
alone; the shared representation and POSIX-value reconstruction must be stated
and checked.

There are two shared smoke routes. `scala_cubic_smoke.ps1 -SharedNoReassoc`
retains the historical post-step hash-cons diagnostic, and the shared
diagnostic follows the current `-SeqMode`. The newer
`scala_cubic_smoke.ps1 -SharedDirectDag` route runs derivative and
simplification directly on hash-consed node IDs. Both expand the final root
back to ordinary `arexp` only to check exact decoded POSIX values. Passing
direct-DAG smoke is stronger evidence for a future shared-row algorithm, but
it is still not a theorem. The direct report distinguishes final reachable DAG
size, prefix `statePool`, and raw total allocation pool; proof work should
target the prefix reachable state/row universe, while raw dead temporaries
need either garbage-free construction, garbage collection, or separate
accounting. Use `-SharedDirectCompareTree` when validating direct-DAG changes:
it checks every prefix derivative root for exact syntactic equality against
the existing tree-step reference algorithm, so direct-DAG remains a
hash-consed execution form rather than an untracked new simplifier.
When steering the shared route, also enable the `statePool` cubic frontier:
`scala_cubic_smoke.ps1 -SharedStatePoolCubicFactor 1.0
-SharedStatePoolCubicTop 4`, or the corresponding
`isabelle_ci.ps1 -ScalaSmokeSharedStatePoolCubicFactor 1.0
-ScalaSmokeSharedStatePoolCubicTop 4`. This is not a theorem, but it is the
current regression gate for the proof-facing prefix-reachable universe idea.
Do not claim a cubic candidate is improving unless the top-ratio witnesses are
stable or better under this gate.
For constant-state claims, short Chapter 7 traces are not enough. Run a
long-tail plateau check, normally with
`-SharedPlateauMaxLength <N> -SharedPlateauStep 4 -SharedPlateauMetric
shapeStatePool`, and keep increasing `<N>` until the chosen metric first
fails to strictly increase. If the run times out or runs out of memory before
that happens, record the last sampled point and the failure mode; do not turn
that into a plateau claim. Use `-SharedPlateauProgress` (or
`-ScalaSmokeSharedPlateauProgress`) on long runs so OOM/timeout leaves a
checked high-water boundary. The proof-side raw route is erased `rrexp`, so
`shapeStatePool` is the closest smoke metric; exact `statePool` also
distinguishes bit annotations and may continue growing after the erased/shape
universe stabilizes. Current evidence: direct `expanded-keyed-no-reassoc`
has `k=5` first stopping at `n=124`, but `k=8` remains strictly increasing
through `n=500`. The experimental `unary-cover-no-reassoc` mode also stops on
`k=5` (`shapeStatePool 337 -> 337` at `n=124`) but fails the larger `k=8`
tail: it is still strictly increasing at `n=624` (`shapeStatePool=2568`)
before the current direct-DAG dedup runs out of heap. Therefore neither route
is a completed constant-universe argument.
Two narrower diagnostics are also negative. `unaryModShapeStatePool`, which
identifies `a^m . (a^p)*` rows modulo `p`, gives only `2552` instead of
`2568` at Chapter 7 `k=8,n=624` and is still strictly increasing.
`unaryPruneShapeStatePool`, which locally drops simple later unary ALT children
covered by earlier unary children, matches the modulo metric through the
checked `k=8,n=160` prefix. Do not spend more bounty effort on these shallow
variants as standalone candidates. The next meaningful route is
continuation-aware row-set coverage: prove or smoke a mechanism where an
earlier row block with continuation `c` covers a later same-continuation row
block when the later row language is included in the POSIX-prior earlier row
set.
The first diagnostic version of this route is `contPruneShapeStatePool`. It
decomposes left-associated sequence branches into `(row-set, continuation)`
pairs and improves the smaller Chapter 7 roots (`k=3` stops at `n=12`, `k=5`
stops at `n=68`), but it still fails `k=8`: the metric is strictly increasing
through `n=624` with value `2552`, matching the unary-modulo metric. Treat this
as evidence that the continuation key itself needs a stronger quotient or an
indexed linear-form representation; do not treat `contPruneShapeStatePool` as
a BR-039 candidate.

The strongest current diagnostic is `langContPruneShapeStatePool`, normally
run with `-SharedPlateauMetricOnly` /
`-ScalaSmokeSharedPlateauMetricOnly`. Metric-only mode intentionally skips
full-tree reconstruction and erases bit payloads inside the diagnostic
`DagStore`; it is for long-tail shape/row-universe measurement only, not for
POSIX value preservation. Ordinary exact-value smoke remains mandatory and
bit-preserving. Current evidence is mixed: Chapter 7 `k=8`, sampled every 64
characters, first stops increasing at `n=960` (`885 -> 885`), but Chapter 7
`k=10`, sampled every 128 characters, timed out at `n=1664` with the metric
still strictly increasing (`1731`). Therefore this is not a BR-039 candidate
yet. It points toward a real periodic/indexed continuation-family universe,
or a reconstruction theorem that justifies the same quotient without
diagnostic-only erasure.

The `expanded-keyed-no-reassoc` diagnostic is the current smoke version of the
virtual-row accumulator idea. Its pruning key may index `a.c` and `b.c` when a
prior row has shape `(a+b).c`, but it still emits `no-reassoc` output syntax.
This is promising because it exposes Antimirov-style row coverage without
directly distributing POSIX value-carrying syntax. It remains smoke evidence
only until reconstruction/value theorems are stated and checked.

Do not try to shortcut strong-row bounds with a naive exact erasure theorem for
strong pruning. `FBound.thy` has the checked counterexample
`rerase_bsimpStrong_prune_pair_not_exact`: annotated
`bsimpStrong_prune_pair` keeps bit/value-carrying alternative syntax and relies
on outer `distinctWith/flts`, while skeleton `rsimpStrong_prune_pair`
normalizes the pruned row internally with `rdistinct/rflts`. Future row-universe
work must use language/coverage subset interfaces, or introduce an explicit
normalized/shared-row representation plus reconstruction theorem.

When an exact erased carrier is needed, use the raw strong skeleton bridge, not
the normalized skeleton shortcut. `GeneralRegexBound.thy` defines
`rsimpStrong_raw` and raw strong row derivatives, and `FBound.thy` proves
`rerase_bsimpStrong_raw` plus row-level `map_rerase` bridges. This raw layer
mirrors annotated delayed normalization and is suitable as the proof-facing
carrier before a separate shared-row/reconstruction theorem. It is not itself
a cubic simplifier bounty.

The preferred proof obligation after that bridge is raw-row closure. Use
`strong_deferred_original_raw_row_cubic_universe_interface` as the current
contract: prove a finite universe `U` is closed by
`rpder_strong_rows_raw`, with cubic card/member-size bounds, and the annotated
`bpders_strong1_rows (intern r) s` size bound plus deferred-value gate follows.
This keeps later universe construction away from annotated bit payloads.

For actual closure work, use the split interface
`strong_deferred_original_raw_row_norm_later_shared_cubic_universe_interface`.
It reduces raw one-step closure to three local obligations: row flattening
closure, `rsimpStrong_raw` closure over `rpder_norm_list`, and raw shared-suffix
pruning closure for
`rsimp7_SEQ_atom (rsimp_ALTs (rprune_eq_against lrs rrs)) k`. Do not unfold and
attack the full `rpder_strong_rows_raw` definition when these local hooks
suffice.

Prefer the newer closed-universe contract when possible:
`strong_deferred_original_raw_row_norm_closed_cubic_universe_interface`.
It replaces the arbitrary-left shared premise with
`raw_shared_prune_closed U`, meaning shared pruning is required only when both
the earlier and later row shapes already belong to `U`. This is the more
realistic target for a finite raw/shared universe.

Keep the measurement honest. On the thesis Figure 7.6 `k=5` family,
`bsimpStrong` gives the expected hundreds-scale ordinary tree trace; the
value-safe `expanded-keyed-no-reassoc` mode still has larger ordinary trees,
although its exact DAG/shape-DAG are compact. Do not treat shared-DAG evidence
as a tree-size reproduction of `strongBlexer` unless the candidate theorem is
explicitly about the shared representation and includes reconstruction.

Also keep the value story honest. The optional `scala_cubic_smoke.ps1
-CheckStrong` gate currently fails for `bsimpStrong` on `STAR (STAR (CH a))`
with input `a`, because the strong simplifier collapses nested-star bit/value
structure. A future tree-level strong route must repair that simplifier or add
a checked generalized-value reconstruction theorem before any POSIX/cubic
bounty can rely on it.

Keep the Chapter 7 size intuition visible. Use
`agent_hunt_pipeline/scripts/ch7_size_grid.ps1` to generate CSV and SVG plots
of simplified derivative size as `k` and input length `n` vary. The default
report goes to `agent_hunt_pipeline/reports/ch7_size_grid/` and compares
`strongTree` (the thesis-style `bsimpStrong` ordinary tree baseline),
`cubicTree` (current `bsimpCubic` ordinary tree size),
`sharedShapeStatePool`, and `langContPruneShapeStatePool`. Before claiming
that a new simplifier is at least as strong as thesis Chapter 7, regenerate
this report and compare ordinary tree sizes, not only shared/DAG metrics.
Current baseline: for `k=5,n=30`, `strongTree=958` while current
`cubicTree=3245`; for `k=8,n=30`, `strongTree=2747` while current
`cubicTree=7587`. The current tree simplifier is therefore not yet thesis-good.
The optional `langAtomicContPruneShapeStatePool` metric is deliberately not a
default plot metric because it collapses the all-unary Chapter 7 family too
coarsely and currently has no POSIX reconstruction meaning.

For the currently most promising tree-level route, also plot the deferred
memo reconstruction metrics:
`ch7_size_grid.ps1 -Metrics
"strongMemoTree,strongMemoStates,strongMemoSplitProbes,strongMemoSpanBound,strongMemoSplitBound"
-OutDir agent_hunt_pipeline/reports/ch7_deferred_memo_grid`.
This uses thesis-strength `bsimpStrong` as the derivative/nullability gate and
recovers exact POSIX values from the original regex via span/memo
reconstruction. Current evidence is encouraging: on the Chapter 7 grid
`k=1..8,n=0..30`, `strongMemoTree` matches `strongTree`; at `k=5,n=30` it is
`958`, and at `k=8,n=30` it is `2747`. The same grid has
`strongMemoStates=1703` and `strongMemoSplitProbes=6011` for both k=5 and k=8.
Run `scala_cubic_smoke.ps1 -SkipLegacyCubic -CheckStrongDeferredMemo` before
proof work on this route; it must pass exact POSIX value comparison, known CEs,
and memo universe bounds. This route is still not a bounty payout until the
Isabelle reconstruction and cubic tree/share theorem are checked.

The CE-driven `bsimpStrongSafe` diagnostic is useful but not the destination.
It disables nested-star collapse, nonempty right-unit deletion, star absorption,
and sequence reassociation in output syntax; this passes deeper exact-value
Scala smoke but loses the Figure 7.6 tree-size plateau. The next tree-level
route should keep the small strong regex and carry local value transformers for
those rewrites, then prove reconstruction to the original `val`.

Use `scala_cubic_smoke.ps1 -TraceStrongRecon` to check the current executable
sketch for that route. It verifies the first CE witnesses with local
reconstruction equations while keeping the actual `bsimpStrong` small output.
It also runs annotated-value local certificate laws for the rewrite rules that
caused those CEs. Treat it as route evidence only; a bounty candidate still
needs a compositional derivative-time certificate or theorem.

Use `scala_cubic_smoke.ps1 -CheckStrongCoreCert` to check the current
compositional certificate prototype for the sequence/star core of
`bsimpStrong`. The prototype returns a simplified regex plus a value
transformer for derivative-expression epsilon values. It now includes
alternation flatten/distinct certificates, but deliberately does not certify
Antimirov row pruning yet, so do not treat it as BR-039 completion.

Use `scala_cubic_smoke.ps1 -TraceStrongCore` to compare the certified core size
against thesis `bsimpStrong`. The current gap on Chapter 7 points to
shared-suffix row pruning as the next certificate target.

Certified row pruning is contextual to the surrounding `AALTs`: a deleted later
row is justified by an earlier row with the same suffix and POSIX priority.
Never state this as a standalone equivalence of the later row. After the first
prototype, Chapter 7 k=5,n=30 certified core is `678`, below thesis
`bsimpStrong` at `958`; the remaining semantic gap is stating and checking the
proof-facing invariant.

Use `scala_cubic_smoke.ps1 -CheckStrongCoreLoop` for the current whole-input
certificate smoke. It composes `bder`, `bsimpStrongCoreCert`, `injectA`, and an
accumulated continuation to reconstruct the original POSIX value. This is the
main executable gate for the certified-core route.

Use `scala_cubic_smoke.ps1 -CheckStrongFullLoop -FindStrongFullCE` as a CE
miner for the user's preferred "keep the `bsimpStrong` tree" idea. Do not
promote this local-certificate route to a proof target while it still fails the
greedy sequence CE
`SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`.

The current positive version of "keep the `bsimpStrong` tree and still get the
right answer" is `scala_cubic_smoke.ps1 -CheckStrongDeferredMemo`: `bdersStrong`
is only the small nullable acceptance certificate, and exact POSIX values are
reconstructed from original `(regex, input)` spans. This gate now includes the
known nested-star and greedy-sequence CEs, so keep it green before trying any
Isabelle proof route based on the strong tree plateau.

After the 2026-06-03 derivative-size graphs, do not optimize the old
emitted-tree `bsimpCubic` route. The proof-facing route is now the final
active strong tree bridge: `raw_final_active_suffix_rows` on the erased final
tree and `strong_deferred_final_active_suffix_rows` on
`bders_simpStrong (intern r) s`. Future proof work should bound these
final-active rows/pair-budgets, or introduce an indexed quotient for prefix
rows, while preserving the checked deferred POSIX reconstruction theorem.

When measuring this route on the Chapter 7 family, use
`scala_cubic_smoke.ps1 -TraceStrongDeferredMemo` with explicit tree/DAG/shape
thresholds. This trace is a guard, not just a report: it checks reconstructed
value flatness, memo span/split universe bounds, and the selected size
thresholds. Do not run the old baseline derivative lexer on the full Chapter 7
trace; that path is heap-explosive and recreates the old growth problem. Exact
baseline POSIX value equality belongs in the bounded exhaustive/random and
known-CE smoke grids. Treat either a small tree with a bad value or a correct
value with an exploding tree as the next counterexample to repair before proof
work.

For regex-size budget pressure, add `-Ch7StrongCubicFactor 1.0` (or the
corresponding `-ScalaSmokeCh7StrongCubicFactor 1.0` in full CI). This enforces
`asize(final strong tree) <= factor * rsize(root)^3` on the Chapter 7 grid.
Keep this distinct from the fixed thesis-regression tree threshold: the former
tests the shape of a cubic claim, while the latter checks that the k=5 example
stays in the Figure 7.6 scale.

Also run the general budget gate with `-StrongCubicFactor 1.0` (or
`-ScalaSmokeStrongCubicFactor 1.0`). This applies the same cubic-shaped size
budget to the exhaustive, known-CE, and random `StrongDeferredMemo` smoke
cases. A candidate that only passes the Chapter 7 family but fails this general
grid should be treated as a fresh CE, not as a proof target.

Read the "worst strong cubic ratio" summaries printed by these smoke runs.
They deliberately ignore `rsize < 5` examples in the summary, while still
checking them for budget failure. Use the reported witness as the next thing to
shrink, explain, or turn into a compact regression when tightening constants
or modifying the simplifier.

For a broader CEGAR signal, add `-StrongCubicTop 3` to
`scala_cubic_smoke.ps1` or `-ScalaSmokeStrongCubicTop 3` to
`isabelle_ci.ps1`. This reports several high-ratio frontier witnesses while
still checking every generated case against the budget. The top-N list is a
diagnostic steering tool only; it does not justify a bounty or theorem claim.
When top-N is greater than one, the smoke also prints a distinct-regex
frontier. Prefer that structurally deduplicated list when choosing the next
compact regression or counterexample family; use the raw list when analyzing
how one regex behaves across several inputs.

When a tightened constant is suspected to fail, run
`scala_cubic_smoke.ps1 -SkipLegacyCubic -FindStrongCubicBudgetCE
-StrongCubicFactor <factor> ...`. The finder searches random cases and greedily
shrinks the first budget violation. It tracks visited `(regex,input)` pairs to
avoid same-size replacement loops; if it reports a tiny witness, that usually
means the factor is too small as a universal finite-size constant, not that the
asymptotic route failed.
For a reproducible multi-seed budget scout, run
`agent_hunt_pipeline/scripts/strong_memo_budget_scout.ps1`. It keeps exact
POSIX `strong-memo` smoke enabled, runs `-FindStrongCubicBudgetCE`, and writes
`agent_hunt_pipeline/reports/strong_memo_budget_scout/summary.md` plus per-seed
logs. Use this before proposing a concrete final-tree or indexed-universe
bound, and record any new budget CE in `PROGRESS_BACKREF.md`.

Use `-StrongCubicMinRegexSize <n>` to focus the report/finder on larger
frontiers. The budget checks still cover all regexes, but the worst-witness
summary and CE search ignore smaller regexes, and the CE shrinker preserves
that floor. This is the right knob when small constants are drowning out the
larger Antimirov/Chapter-7-style structure.

Before proof work, read
`agent_hunt_pipeline/projects/posix-backref/CERTIFIED_STRONG_CORE.md`. It is
the current proof-facing spec for replacing Scala closures with an Isabelle
relation and loop invariant.

