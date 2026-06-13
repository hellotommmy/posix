# SUPER_LINEAR_PATTERNS — Fuzzer Corpus from a Machine-Verified POSIX Lexer Proof

A companion deliverable of the POSIX cubic-bound project. Every entry is a
regex (or regex family) that either **provably blows up** a derivative-based
matcher's state, or was the **counterexample that killed a conjecture** during
the cubic-bound proof. Both kinds are valuable fuzzer input for stress-testing
the *linearity* claims of NFA/derivative-based regex engines (RE2, PCRE2-JIT,
Java, Python `re`, JavaScript `RegExp`, Rust `regex`, Go `regexp`, ...).

**Why these are unusually good fuzzer seeds.** Each carries a
machine-verified pedigree: we know *exactly* what it breaks, and — for the
conjecture-killers — *how many test samples it passed before dying*. The
patterns that fooled hundreds of thousands of samples before a deep probe
caught them are precisely the inputs that other people's test suites also
miss. The tortuous cubic-bound proof itself is evidence that strict
linear-time matching is implausible once **bounded repetition `r{n}`** and
**POSIX submatch/value semantics** are in play.

## How to read an entry

- **rrexp**: the canonical form, in the project's erased-skeleton notation:
  `RZERO=∅`, `RONE=ε`, `RCHAR c=c`, `RSEQ=·` (concatenation),
  `RALTS [..]=alternation`, `RSTAR=*`, `RNTIMES r n=r{n}` (exactly n).
- **PCRE**: a translation into standard regex syntax for direct use against
  other engines. `ε` is written `()`; `∅` (the empty language) has no literal
  PCRE equivalent and is noted where it matters (it is a proof artifact —
  replace with a never-matching class `[^\s\S]` or drop the branch when
  fuzzing real engines).
- **killed / blows up**: the conjecture or simplifier it refuted, plus the
  checked Isabelle lemma name (these are *proved*, not conjectured).
- **deception**: how many samples / what sampling depth it survived before
  being caught — the headline fuzzing value.
- **mechanism**: the structural reason in one or two sentences.

Standing rule (admin, 2026-06-13): **append, never prune.** A dead conjecture
makes the CE a *better* fuzzer seed, not a worse one. Add new finds here in the
same cycle you record them in the `PROGRESS_BACKREF.md` tail. See
`MATHPROBLEM_ROWCOUNT.md`, `CUBIC_OPEN_PROBLEM.tex`, and the PROGRESS tail for
the surrounding proof context.

---

# Part A — Provable blow-up families (true super-polynomial / tight growth)

These are *theorems*: the derivative-row count or list ledger grows
faster than any candidate polynomial budget. These are the cannonballs — feed
them to another engine at increasing depth/length and watch match time or
memory.

## A1. RONE-pair tower — exponential derivative-row list

- **rrexp**: parameter = depth `n`.
  ```
  payload(a,b) = RSEQ (RALTS [RONE, RCHAR a]) (RALTS [RONE, RCHAR b])
  tower 0      = RSEQ (RCHAR k) (RCHAR l)
  tower (n+1)  = RSEQ (RALTS [RONE, payload(a,b)]) (tower n)
  fire on:     RSEQ (RCHAR g) (tower n)     -- then derive on the guard char g
  ```
- **PCRE** (depth n, distinct letters a,b,k,l,g): the per-level block is
  `(?:()|(?:()|a)(?:()|b))` and the whole input is
  `g(?:()|(?:()|a)(?:()|b)){n}kl`. Drive the matcher with the single
  character `"g"` (or any prefix), then longer strings.
- **blows up**: the *deduplicated-by-list* per-character transition cost is
  **not even cubic** — `afactored1_strong_dlform_list_cost_cubic_false`
  (`AntimirovFactoredTransition.thy:27961`). Row count obeys
  `len(n+1) = 2·len(n) + 2`, closed form `len(n) = 3·2ⁿ − 2`, while regex size
  is only `10n + 3`.
- **deception**: a size/length trap, not a sampling trap. The list length
  stays under the cubic ceiling `2·(10n+9)³` for every small `n` you would try
  by hand; the *minimal* crossover is **depth 24** (`rsize = 245`, ceiling
  `2·248³ = 30,517,504`, list cost `3·2²⁴ − 2 = 50,331,646`). A test suite
  that stops at depth ~15 sees nothing.
- **mechanism**: every `(ε|payload)` alternative offers a fully-collapsing
  ε-path that, after one derivative, reassociates to the **same** tail row;
  the non-deduplicated list keeps one copy per ε-path, doubling per level.
  (Set-level dedup merges them back to *quadratic* — so an engine that
  hash-conses states survives; one that materializes the row list does not.)

## A2. Duplicate-RONE row-group tower — list ledger not even quadratic

- **rrexp**: `step k = RSEQ (RALTS [RONE,RONE,RONE,RONE]) k`;
  `q = step⁵ (RCHAR a)` (five nested 4-way ε-groups over one `a`).
- **PCRE**: `(?:()|()|()|()){5}` applied around `a`, i.e.
  `(?:()|()|()|())(?:()|()|()|())(?:()|()|()|())(?:()|()|()|())(?:()|()|()|())a`.
- **blows up**: refutes a *quadratic* bound on the deep row-dlform ledger —
  `duplicate_RONE_row_group_deep_nf_quadratic_list_bound_false`
  (`AntimirovFactoredTransition.thy:4946`): `row_dlforms_list_size q = 1024`,
  `rsize q = 31`, and `1024 > 31² = 961`.
- **deception**: closed-form, no sampling. Minimal companion to A1 showing the
  list ledger is not even quadratic — normal-form + tail-normal-form do **not**
  stop it.
- **mechanism**: four ε-branches per layer each re-expose the same shared tail
  without consuming input, multiplying forms by 4 per layer (`4⁵ = 1024`) while
  size grows only +6 per layer.

## A3. NTIMES deep-frontier alt-spread — bounded repetition multiplies branches

- **rrexp**:
  ```
  SS  = [RSTAR RONE, RSTAR RZERO, RNTIMES RONE 0, RNTIMES RZERO 0,
         RSTAR (RSTAR RONE), RSTAR (RSTAR RZERO), RNTIMES RONE 1, RNTIMES RZERO 1]
  X   = RSEQ (RCHAR a) (RALTS SS)
  cex = RNTIMES X 6
  ```
- **PCRE** (the proof uses ∅/ε branches that don't all have engine analogues;
  the *fuzzing-relevant skeleton* is `(?:a(?:...8 nullable star/rep branches...)){0,6}` —
  the point is **8 alternatives × an `{n}` counter**). A practical engine seed:
  `(?:a(?:b*|(?:b{0})|(?:c*)|(?:c{0})|d*|(?:d{0})|e*|f*)){6}`.
- **blows up**: the deep frontier is **not linear-card** —
  `apder_deep_frontier_linear_card_false`
  (`AntimirovFactoredTransition.thy:9649`): card `= 49` vs budget
  `awidth(6) + rsize(30) + 3 = 39`.
- **mechanism**: `r{6}` spawns a residual count `m ∈ {0..5}`, each carrying the
  whole 8-way alternation, so rows multiply `8×6 = 48` (+root) while `{n}` pays
  its count only *additively* in size. **This is the canonical "bounded
  repetition is the blow-up vector" witness** — exactly the construct standard
  Thompson-NFA engines special-case and frequently get wrong.

## A4. NTIMES star-reentry front — `{n}` under a Kleene star

- **rrexp**: `r = RSEQ (RSTAR (RCHAR a)) (RNTIMES X 8)` with `X` as in A3;
  fixed input `"aaaaaaaa"`.
- **PCRE**: `a*(?:a(?:b*|c*|d*|e*|...8 branches...)){8}` on input `aaaaaaaa`.
- **blows up**: refutes the front-level linear-card premise —
  `adlform_front_linear_card_false`
  (`AntimirovFactoredTransition.thy:9773`): card `≥ 64` (8 alternatives × 8
  residual counts) vs budget `47`.
- **mechanism**: the `a*` prefix re-enters the counted repetition on every
  input character, so the front simultaneously carries rows for many residual
  counts `i` at once; `8×8 = 64` distinct front rows. **`(prefix)*(...){n}` is
  a real-world ReDoS shape** — this is the formal version.

## A5. Chapter-7 three-layer nested-star — the thesis growth benchmark

- **rrexp** (parameter `k`):
  `RSTAR (RSTAR (RALTS [RSTAR(a), RSTAR(aa), RSTAR(aaa), ..., RSTAR(a^k)]))`,
  i.e. `((a* + (aa)* + (aaa)* + … + (aᵏ)*)*)*`, run over alphabet `{a}` with
  input `aⁿ`.
- **PCRE**: `(?:(?:a)*|(?:aa)*|(?:aaa)*|...|(?:a{k})*)**` — note the double
  star; on a run of `a`s. (`k` default 5 and 8; lengths 4,8,12,16,20,32.)
- **blows up**: the canonical simplifier stress family. Value-safe `no-reassoc`
  keeps POSIX values but the emitted tree explodes (k=8,len32: tree **18643**
  vs exact-DAG 547). This is the family the live cubic gate must tame.
- **deception**: under destructive `full` reassociation it *looks* bounded
  (plateau 413→820 across 84,300 exhaustive pairs) — until the value bug in
  B5b surfaced. Tree-size compactness was not evidence of a sound simplifier.
- **mechanism**: three stacked stars over a fan of `(aⁿ)*` create exponentially
  many ways to chunk a run of `a`s; repeated derivatives spawn many
  shared-suffix rows, and the outer two stars add zero-width re-entry. **The
  classic catastrophic-backtracking / superlinear-NFA family.**

## A6. Least-owner-closure subset explosion — exponential owner/DAG count

- **rrexp**: parameter `m`. Atoms `atomf i = RSTAR^(i+1) RONE` (`i+1` nested
  stars over `ε`). Seeds:
  ```
  ras = [atomf 0, ..., atomf (m-1)]
  L   = RSEQ (RALTS (ras @ [atomf m, atomf (m+1), atomf (m+2)])) (atomf (m+3))
  E i = RSEQ (RALTS [atomf i, atomf (m+2)]) (atomf (m+3))
  U   = insert L { E i | i < m }            -- card U <= m+1
  ```
- **PCRE**: each `atomf i` is `i+1` nested empty-stars, e.g.
  `(?:(?:(?:())*)*)*`; the active ingredient is the alternation-under-a-shared
  suffix `(alt)·k` that the pairwise suffix-pruner "owns". (A proof artifact
  over ε-atoms — the fuzzing-relevant shape is *many same-suffix alternation
  rows feeding an all-pairs pruner*.)
- **blows up**: the abstract least-owner closure of `U` contains one distinct
  row for every **nonempty** subset `S ⊆ {0..m-1}` — `card = 2^m − 1` — from
  only `card U ≤ m+1` seeds. Any owner/DAG cardinality bound polynomial in
  `card U` and member sizes alone is therefore false —
  `raw_shared_prune_active_suffix_owner_exponential`
  (`AntimirovFactoredTransition.thy:20928`).
- **deception**: closed-form, no sampling. It looks polynomial for tiny `m`;
  the `2^m` only dominates once `m` is past hand-enumeration size.
- **mechanism**: from `m+1` same-key rows, iterated pairwise suffix pruning can
  reach a distinct surviving row for every nonempty subset of the prunable
  alternatives. This is *why* the cubic proof uses the order-respecting
  one-pass pruning object and never the all-pairs owner closure — an engine
  that materializes owner/DAG closures over shared suffixes inherits this
  `2^m` blow-up.

---

# Part B — Conjecture-killer counterexamples (the deceptive ones)

These refuted *plausible inequalities* we tried to prove. Their fuzzing value
is the **deception datum**: each looked true across large directed/random
sample campaigns. They are the "looks linear, isn't" boundary cases — the most
likely to slip past a real engine's regression suite.

## B1. Depth-5 nested-zero-width-star — killed the zwidth row-count law AND J*

- **rrexp**: `r = RSEQ (RCHAR b) (RALTS [RSTAR(RSTAR(RCHAR a)), RSTAR(RSTAR(RCHAR b)), RCHAR b])`,
  continuation `k = RONE`. Witness: `card(acc r k − frontier k) = 5 > zwidth r = 4`.
- **PCRE**: `b(?:(?:a*)*|(?:b*)*|b)` — the `(x*)*` nested stars are the active
  ingredient.
- **killed**: the original max-1 `zwidth` D law
  (`card (acc r k − rfrontier k) ≤ apder_zwidth r`) **and** the J\* joint
  inclusion-exclusion invariant — *the same CE killed both*. Forced the
  corrected weight `apder_zw2` (star = `Suc`, not `max 1`).
- **deception**: ⭐ the headline. Passed the zwidth-D campaign at **~200,000**
  cumulative normal-form samples (depth ≤ 4) **and** the J\* candidate at
  **95,510** samples (55,351 nontrivially-active) — *zero violations* — before
  a directed depth-5 run (285k samples) caught it. **Lesson now standing: this
  problem requires depth ≥ 5 sampling; shallow sampling validated FALSE laws
  twice.**
- **mechanism**: a nested zero-consuming star `(a*)*` contributes both itself
  as a frontier point *and* its unrolled re-entry row, so each star *layer*
  needs its own derivative slot; max-1 zwidth charges one slot for the whole
  star, undercounting by the nesting depth.

## B2. Equality-tight char-over-double-star — killed three unary discounts

- **rrexp**: `r = RSEQ (RCHAR a) (RALTS [RCHAR a, RSTAR(RSTAR(RCHAR a))])`,
  `k = RONE`. `card(acc − {RONE}) = 3 = zwidth r = 3` (equality, no slack).
- **PCRE**: `a(?:a|(?:a*)*)`.
- **killed**: the D⁺ subset-discount, the intersect-discount, **and** the
  list-length (no-dedup) route — falsified strengthenings #1, #2, #7 of nine.
- **deception**: survived **113,751** samples before this single CE appeared.
- **mechanism**: at `k=ε` the single-char leaf (budget 1) must pay the whole
  2-point frontier of the alternation; the books balance *only* by
  inclusion-exclusion (the sibling accumulators share the point `a`). Any unary
  subset/intersect discount overdraws an already-tight equality account.

## B3. Bare zero-width star families — killed the membership companions & awidth

- **rrexp / PCRE**:
  - `RSTAR RONE` = `()*` — zwidth = 1 but accumulator empty ⇒ 43% violation of
    the zwidth membership companion.
  - `RSTAR (RCHAR a)` = `a*` — awidth = 1 but the accumulator is a single
    *rewritten* row not containing the raw continuation frontier ⇒ 22%
    violation of the awidth membership companion.
  - `r = RSEQ (RCHAR b) (RALTS [RCHAR a, RSTAR RONE, RSTAR(RSTAR RONE)])` =
    `b(?:a|()*|(?:()*)*)` — killed the all-letters `awidth` row-count law
    (zero-width stars score 0 but occupy real rows).
- **killed**: both membership-absorption companions; the non-additive
  `card(acc) ≤ awidth` law (failed at 47,298 samples, 13 violations).
- **mechanism**: zero-width stars have positive width-floor but produce no
  letter-consuming row, *or* a rewritten re-entry row — any "the frontier row
  is already in the accumulator" absorption story is structurally wrong.

## B4. Potential/reserve forms 9a & 9b — killed the last two strengthenings

- **rrexp**: dominated by the same nested zero-width-star family as B1
  (e.g. `RSEQ (RCHAR b) (RALTS [RSTAR(RSTAR(RCHAR a)), RSTAR(RSTAR(RCHAR b)), RCHAR b])`,
  `k=RONE`, card 5).
- **PCRE**: `b(?:(?:a*)*|(?:b*)*|b)` (same as B1).
- **killed**: strengthening 9a (acc-diff + unproduced-frontier reserve, ~10%
  violation) and 9b (`card((acc ∪ frontier r) − frontier k) ≤ zwidth r + 1`,
  witness `5 > 3+1`) — bringing the dead-strengthening tally to **nine**.
- **mechanism**: a single additive `+1` (or a reserve term) still prices each
  star as one slot; nested zero-consuming stars overrun by the nesting depth,
  one constant higher.

## B5. Value-semantics counterexamples (POSIX parse-tree, not size)

These break *correctness*, not size — but they are excellent fuzzer seeds for
any engine claiming to return **POSIX-correct submatches/captures**.

- **B5a. Minimal nested-star value CE**: `RSTAR (RSTAR (RCHAR a))` = `(?:a*)*`
  on input `"a"`. The strong simplifier returns the wrong POSIX value
  structure (loses the outer `Stars` nesting). Checked by the `-CheckStrong`
  gate (`PosixCubicSmoke.scala:7638`). **Deception**: minimal (depth 2, 1
  char) — all recognition/size checks pass; only exact decoded-value
  comparison catches it. *Fuzz idea*: compare an engine's capture tree on
  `(?:a*)*` against the POSIX spec for input `a`.
- **B5b. Reassociation value bug**:
  `RSTAR (RALTS [RONE, RSTAR(RSTAR(RSTAR(RSTAR(RSTAR(RCHAR a)))))])` =
  `(?:()|(?:(?:(?:(?:a*)*)*)*)*)*` on input `"aaa"`. Destructive sequence
  reassociation `(x·y)·z → x·(y·z)` is **not** POSIX-value-preserving.
  Recorded `DESIGN_LOG.md:2215`, `BACKREF_BOUNTIES.md:964`. **Deception**: ⭐
  passed the *entire exhaustive* bounded enumeration (depth-2/input-3 value
  smoke) and only surfaced under deterministic random smoke at **seed 20260602,
  case 99** (depth 5 / input 6). The single hardest-to-find value bug in the
  project.

## B6. Zero-count NTIMES alternation — killed unrestricted raw zw2 D

- **rrexp**:
  ```
  r = RSEQ (RCHAR c)
        (RALTS [RNTIMES (RCHAR a) 0, RNTIMES (RCHAR b) 0])
  k = RONE
  ```
- **PCRE**: `c(?:a{0}|b{0})`. For real-engine fuzzing, preserve the explicit
  `{0}` branches instead of simplifying them away.
- **killed**: the unrestricted corrected `apder_zw2` D law
  `card (apder_term_frontier_acc r k - rfrontier k) <= apder_zw2 r`.
  Checked lemma:
  `apder_zw2_D_law_rntimes_zero_alt_false`
  (`AntimirovFactoredTransition.thy`), with row count `2` and budget `1`.
- **deception**: the raw zw2 repair had passed the reported **295,551** deep
  samples; this was caught only by a directed supervisor audit of
  `RNTIMES _ 0` continuations.
- **mechanism**: `RNTIMES x 0` has no accumulator rows and contributes zero
  `zw2` budget, but it remains a distinct syntactic frontier atom. A preceding
  character imports every zero-count alternative through a single character
  slot, so two `{0}` alternatives already overdraw the unrestricted budget.

## B7. Empty alternative continuation — killed global carry-measure strengthening

- **rrexp**:
  ```
  r = RALTS []
  k = RCHAR a
  ```
- **PCRE**: the empty alternative block represents the empty language; as a
  fuzz seed, keep an explicit unsatisfiable alternation node before sequencing
  it with a non-empty continuation.
- **killed**: the global simultaneous carry invariant at arbitrary
  continuations,
  `card(acc r k - F(k)) + card(F(sigma4 r k) - F(k) - acc r k) <= zw2 r`.
  Checked lemma:
  `apder_zw2_global_carry_empty_alt_false`
  (`AntimirovFactoredTransition.thy`), with D-count `0`, carry-count `1`,
  and budget `0`.
- **deception**: the original D law is not refuted by this shape; only the
  stronger carry-measure scaffold fails.  That makes it easy to overfit a SEQ
  proof skeleton to a false helper while the live D samples stay green.
- **mechanism**: `RALTS []` has no accumulator rows and zero `zw2`, but
  `sigma4 (RALTS []) k` at a non-`RONE` continuation is a syntactic sequence
  row with a singleton frontier outside `F(k)`.

## B8. Character over two-character alternation — killed global left-two-bucket

- **rrexp**:
  ```
  left = RCHAR c
  r2 = RALTS [RCHAR a, RCHAR b]
  k = RONE
  ```
- **PCRE**: `c(?:a|b)` as the surrounding SEQ shape.
- **killed**: treating the new SEQ left-two-bucket premise as a global
  induction invariant for the left child alone,
  `card(acc left (sigma4 r2 k) - F(sigma4 r2 k)) +
   card((acc left (sigma4 r2 k) INT F(sigma4 r2 k)) - F(k) - acc r2 k)
   <= zw2 left`.
  Checked lemma:
  `apder_zw2_left_two_bucket_RCHAR_alt_false`
  (`AntimirovFactoredTransition.thy`), with outside-middle count `0`,
  middle-overlap count `2`, and left budget `1`.
- **mechanism**: a character-left SEQ imports the entire right alternation
  frontier.  The live D law is still balanced by the right alternation budget,
  but charging that middle-overlap bucket only to the left character overdraws
  immediately.

## B9. Sequence with dead tail — killed "opened rows ⊆ frontier" inclusion

- **rrexp**: `p = RSEQ (RCHAR a) RZERO` = `a·∅`, opened against continuation
  `RONE`.
- **PCRE**: `a` immediately followed by the empty language (`a(?!)`, or
  `a[^\s\S]`); a proof artifact — keep an explicit never-matching tail when
  fuzzing real engines.
- **killed**: the plausible inclusion
  `row_lforms p ⊆ rfrontier (rsimp7_SEQ_atom p RONE)` — i.e. "every linear form
  opened out of a row already lives in that row's frontier." Checked false:
  `row_lforms_rsimp7_SEQ_atom_RONE_subset_false`
  (`AntimirovFactoredTransition.thy:15578`).
- **deception**: closed-form, minimal. The general intuition (MAINLINE §4
  item 10) is sharper than this minimal witness: the opener splits `(a+b)·c`
  into the linear forms `a·c`, `b·c`, while the whole-residual frontier stores
  `(a+b)·c` and `c` — so the opened set and the frontier are genuinely
  *incomparable*, not nested either way.
- **mechanism**: opening distributes a leading alternation over the shared
  suffix; the frontier keeps the un-distributed residual. Any proof step (or
  engine state-sharing scheme) that treats opened linear forms as a subset of
  the frontier is unsound.

## B10. Singleton-alt under a star — killed the opened-boundary carrier bridge

- **rrexp**: `r = RSTAR (RALTS [RCHAR a])` = `(a)*` with a one-element
  alternation under the star; the escaping row is `bad = RSTAR (RCHAR a)`.
- **PCRE**: `(?:a)*` — a redundant single-branch alternation wrapped in a star.
  For fuzzing a simplifier, keep the singleton `(?:...)` un-flattened in the
  input so the pre/post-simplification mismatch is exercised.
- **killed**: the strong-carrier-preservation bridge of the GPT Pro
  opened-boundary gate route —
  `rsimpStrong_dlform_closure (set (afactored1 r u)) ⊆
   odfront RONE ∪ opened_boundary_forms r RONE`. Checked false:
  `rsimpStrong_dlform_closure_opened_boundary_carrier_false`
  (`AntimirovFactoredTransition.thy`). Isabelle proves `apder_clean r` and
  `bad ∈ rsimpStrong_dlform_closure (set (afactored1 r []))` yet
  `bad ∉ odfront RONE ∪ opened_boundary_forms r RONE`.
- **deception**: closed-form, minimal — but it killed an entire *checked-stack*
  route. The opened-boundary 9-lemma stack (inclusions, `open_pot` potential,
  carrier) all went green at the `apder_clean`/`afactored1` level before this CE
  showed the final bridge to the STRONG-pruned object is unsound on the clean
  fragment. A worked, self-consistent invariant can still fail at the one place
  the strong simplifier rewrites structure.
- **mechanism**: strong simplification collapses the singleton `RALTS [RCHAR a]`
  under the star (`RSTAR (RALTS [RCHAR a]) → RSTAR (RCHAR a)`) *after* the opened
  carrier was computed for the unsimplified root, so a strong-simplified row
  escapes the carrier built pre-simplification. Any "compute the carrier on the
  raw form, then simplify" pipeline inherits this gap.

---

# Suggested fuzzer use

1. **Linearity stress (Part A)**: for each family, sweep the depth/length
   parameter and measure match time and peak memory on the target engine. A
   linear-time claim should show linear scaling; A1/A3/A4 are designed to break
   that, A5 is the classic catastrophic family.
2. **Differential value testing (B5)**: run the target engine's submatch/capture
   output against a POSIX reference on B5a/B5b. These were caught only by exact
   value comparison, never by recognition or size.
3. **Boundary mining (B1–B4)**: these are "looks linear, isn't" shapes built
   from `(x*)*` and `(...){n}`. Use them as *seeds* for a mutation fuzzer —
   their deception data shows the live boundary is around nesting depth ≥ 5,
   so mutate toward deeper nesting and counted repetition.

The recurring villains are **nested zero-width stars `(x*)*`** and **bounded
repetition `r{n}` under iteration**. Any engine that special-cases `{n}` by
unrolling, or that flattens `(x*)*`, is where these will bite.
