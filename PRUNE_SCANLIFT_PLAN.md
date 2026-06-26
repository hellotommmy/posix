# PRUNE SCAN-LIFT PLAN — the shared hard core (Pro, 2026-06-25)

**The real hard core is NOT the cubic gate, NOT RALTS_diff — it is one shared lemma: PRUNE BRANCH-LIST / SPINE
PRESERVATION.** Crack it and O1/L1 cover AND O2/S1 injection both loosen. The project keeps stalling because workers
keep adding helpers AROUND the `rsimpStrong_prune_rows_raw` wall without abstracting it into one correct intermediate
theorem. **Pair-level prune facts are essentially DONE (in `card/route1-cover`); the missing piece is the FOLD/SCAN
LIFT** over `rsimpStrong_prune_against_rows_raw`. Stop adding isolated row helpers; concentrate on the scan-lift.

## 🔴 STATUS UPDATE (Secretary, 2026-06-26) — the scan-lift is PROVED but ORPHANED; O1 stalls on the GLUE, not the lift
The scan-lift this plan asks for is DONE and GREEN: `row_dlforms_prune_against_rows_shared_tail_subset_later_or_credit`
(`card/route1-cover` @ df74132, `r1cover/Card_Route1_Cover.thy:1159`, 0 sorry). **But it is referenced NOWHERE downstream
(orphaned), and it is CREDIT-PARAMETRIC**: its collapsed-star branch is carried as two undischarged hypotheses
`one_credit` (:1168) / `star_credit` (:1176) — when `rsimp_ALTs (rprune_eq_against lrs rows)` collapses to `RONE` / `RSTAR s`
(the a*·a* residual), that residual's opening must land in the credit set `C`. So the wall is RELOCATED into these premises.
Both halves of the proof exist but were NEVER connected:
 - (A) the scan-lift (:1159) + a full credit machine: `singleton_saa_key_credit` (:2499); bases RZERO/RONE/RCHAR/… (:3233-3255);
   `tagged_rdistinct_preserves_…`/`tagged_rflts_preserves_…` (:3536/:3626); per-pair shared-RSTAR credits (:2513-2640).
 - (B) the GREEN conditional bridges `cover_root_from_tagged_invariant` (:3764), `…_if_tagged_inv` (:3843), `…_if_root_split` (:3883);
   the final `strong_apder_acc_RALTS_singleton_cover` is STILL only a TARGET comment (:3934).
**THE ONE MISSING LEMMA = the glue** (e.g. `cover_root_split_from_scan_lift`): instantiate :1159 with
`C := rsimpStrong_dlform_closure (apder_term_frontier_acc …)` (the per-branch term/ACC carrier), discharge `one_credit`/`star_credit`
from the credit bases above, and so prove the premise of `…_if_root_split` (or `tagged_inv`) → chain the green bridge → `singleton_cover`.
The alignment to pin is `tagged_Strong_ALTs_rows rs` ↔ the `(seen, later)` accumulator of `rsimpStrong_prune_against_rows_raw`; the lift's
two disjuncts map onto root_split's two targets ("subset-later" → branch ROOT, "credit C" → branch TERM/ACC). **This is finishable
formalization — the discovery is done, the cover worker just stopped after landing the lift. Pro: please target this single glue lemma.**

## Why the brittle syntactic equality is the wrong target
Do NOT chase `S(s4 t k) = RSEQ(RALTS ps') kX` / `S(s4(RALTS[t])k) = RSEQ(RALTS ps') kY` directly. It is too
syntactic and breaks on `[]`, singleton, `a*·a*` collapse, and inner `RSEQ(RALTS ...)` exposure: after a prune leaves
a singleton, `rsimp_ALTs [p] = p` EXPOSES the branch's next inner `RSEQ(RALTS …)`, so further prune happens on a
DEEPER suffix/tail class. "Same top branch list is preserved" is too coarse — it changes layer inside the spine.
So the ghost view must be **spine-recursive**, not top-level-only.

## The fix: a ghost prune-VIEW, not the final syntax
Track what the prune scan does on each EXPOSED altseq class, not the final `S(...)` syntax. Key observation:
`rsimpStrong_prune_pair_raw` only looks at rows with the SAME exact tail `k`; only earlier rows of shape
`RSEQ (RALTS lrs) k` can prune a later `RSEQ (RALTS rrs) k`; all other seen rows are INERT for that tail class —
but must then handle the singleton-exposed next layer.

### Block 1 — shared ghost definitions (put in a shared place, not a local proof)
```isabelle
fun altseq_view :: "rrexp ⇒ (rrexp list × rrexp) option" where
  "altseq_view (RSEQ (RALTS ps) k) = Some (ps, k)"
| "altseq_view _ = None"

fun same_tail_heads :: "rrexp ⇒ rrexp ⇒ rrexp list" where
  "same_tail_heads k (RSEQ (RALTS ps) k') = (if k' = k then ps else [])"
| "same_tail_heads k _ = []"

definition seen_heads_at :: "rrexp ⇒ rrexp list ⇒ rrexp list" where
  "seen_heads_at k seen = concat (map (same_tail_heads k) seen)"

definition is_altseq_at :: "rrexp ⇒ rrexp ⇒ bool" where
  "is_altseq_at k r ⟷ (∃ps. r = RSEQ (RALTS ps) k)"
```

### Block 1 — hygiene lemmas (definition-level; do NOT touch the big regex structure)
```isabelle
lemma rprune_eq_against_append:
  "rprune_eq_against xs (rprune_eq_against ys zs) = rprune_eq_against (xs @ ys) zs"
  by (induct zs) auto

lemma prune_pair_raw_inert_if_not_same_tail:           (* the key hygiene fact *)
  assumes "¬ is_altseq_at k earlier"
  shows   "rsimpStrong_prune_pair_raw earlier (RSEQ (RALTS ps) k) = RSEQ (RALTS ps) k"
  using assms by (cases earlier; simp add: is_altseq_at_def rsimpStrong_prune_pair_raw_def)
```
(Use `is_altseq_at` not `same_tail_heads=[]`: the latter is also true for a genuine same-tail with `lrs=[]`.)

## Block 2 — pair-level is DONE (already in Card_Route1_Cover.thy)
`card/route1-cover` already has the pair-level row-domination facts:
- shared `RSEQ` tail:    `row_dlforms (rsimp7_SEQ_atom (rsimpStrong_prune_pair_raw e l) K) ⊆ row_dlforms (rsimp7_SEQ_atom l K)`
- shared `nonstar` tail:  same subset shape.
- shared `RSTAR` tail:    NOT subset-later but `pruned opens ⊆ later opens ∪ C` (C = star-escape credit / singleton ACC carrier) — `..._subset_later_or_credit`.
**So the hard core is NOT pair-level. It is the scan/fold lift of these.**

## Block 3 — the scan-lift theorem (THE missing piece)
Do NOT prove a giant `strong_apder_acc_RALTS_singleton_cover` directly. Prove this intermediate first:
```isabelle
lemma row_dlforms_prune_against_rows_shared_tail_subset_later_or_credit:
  assumes seen_ok:  "∀e∈set seen. inert_for_tail tail e ∨ (∃lrs. e = RSEQ (RALTS lrs) tail ∧ heads_ok lrs)"
  assumes later:    "later = RSEQ (RALTS rrs) tail"
  assumes rrs_ok:   "heads_ok rrs"   and tail_ok: "tail_case_ok tail"   and K_nf: "rtail_nf K"
  assumes credit_ok:"star_escape_credit_ok tail rrs K C"
  shows "row_dlforms (rsimp7_SEQ_atom (rsimpStrong_prune_against_rows_raw seen later) K)
           ⊆ row_dlforms (rsimp7_SEQ_atom later K) ∪ C"
```
First do the THREE concrete tails (don't pre-abstract the predicates):
`row_dlforms_prune_against_rows_shared_RSEQ_tail_subset_later` / `..._shared_nonstar_tail_subset_later` /
`..._shared_RSTAR_tail_subset_later_or_credit`.

**Proof (induct `seen` arbitrary: `later rrs`):**
```
Nil:               simp
Cons e es:         split whether e has the same tail.
  not same tail:   prune_pair_raw_inert_if_not_same_tail; use IH.
  same tail:       use the existing PAIR lemma to relate one-step-pruned later to later ∪ C;
                   then split the shape of (rprune_eq_against lrs rrs):
                     []           : later becomes RZERO; future scan inert / opens empty.
                     singleton [p]: later becomes rsimp7_SEQ_atom p tail — this may EXPOSE an inner altseq,
                                    so DO NOT force the same top tail; discharge by the row_dlforms-level pair
                                    lemma + suffix lemma, NOT by syntactic branch-list equality.
                     length ≥ 2   : later stays RSEQ (RALTS ps') tail; IH applies with ps' and set ps' ⊆ set rrs.
```
This single induction IS the hard core. Cover's latest commits (star/nonstar/tagged scan suffix) are exactly at this layer — they just have not been folded into this one theorem.

## Using it for O1/L1 — close `tagged_inv` directly
```
For every tagged branch (q,t):
  row from pruned parent root carrier ⊆ row from corresponding singleton branch root ∪ star_escape_credit
  star_escape_credit ⊆ strong_apder_acc (RALTS [q]) k
i.e. B1 surviving branch → singleton ROOT carrier;  B2 collapsed-star escape → singleton TERM/ACC carrier.
```
⇒ discharge `tagged_inv` / `root_split` ⇒ `strong_apder_acc_RALTS_singleton_cover`. Cover already has the
star-escape-credit / singleton-carrier helpers — fold-lift them, do NOT open a new route.

## Using it for O2/S1 — existence BEFORE inj_on
BND already has `card_le_of_card_diff_le` + `bnd_profile/key/counts/lift_compatible`. Do NOT formalize `f = least y`
first. Prove structural relation lemmas in this order:
```isabelle
definition bnd_seam_lift :: "rrexp ⇒ rrexp ⇒ bool" where
  "bnd_seam_lift kX kY ⟷ bnd_key kX = bnd_key kY ∧ list_all2 (≤) (bnd_counts kX) (bnd_counts kY)"

definition one_pos_le :: "nat list ⇒ nat list ⇒ bool" where
  "one_pos_le xs ys ⟷ list_all2 (≤) xs ys ∧ card {i. i < length xs ∧ xs ! i ≠ ys ! i} ≤ 1"

lemma bnd_lift_compatible_rsimp7_same_head:                 (* the O2 core localisation *)
  assumes "bnd_seam_lift kX kY"  "rtail_nf p"
  shows   "bnd_lift_compatible (rsimp7_SEQ_atom p kX) (rsimp7_SEQ_atom p kY)"

lemma bnd_lift_compatible_rsimp7_same_head_one_pos:         (* σ7 changes exactly ONE adjacent-equal-star seam run *)
  assumes "bnd_seam_lift kX kY"  "rtail_nf p"
  shows   "bnd_key (rsimp7_SEQ_atom p kX) = bnd_key (rsimp7_SEQ_atom p kY)"
    and   "one_pos_le (bnd_counts (rsimp7_SEQ_atom p kX)) (bnd_counts (rsimp7_SEQ_atom p kY))"
```
Then D_nonempty as a SCAN-LIFT corollary (existence, not a global f):
```isabelle
lemma boundary_missing_has_root_lift_from_prune_scan:
  assumes "x ∈ boundary_excess t k - root_excess t k"
          "legacy_rrexp t" "rntimes_free t" "apder_nf t" "apder_nf k"
  shows   "∃y∈root_excess t k - boundary_excess t k. bnd_lift_compatible x y"
(* x ∈ boundary ⇒ row of pruned strong root of S(s4 t k); scan-lift ⇒ x in lazy singleton root side OR a
   star-credit escape; x∉root_excess ⇒ collapsed/escape ⇒ seam-lift builds y with same key + ≥ counts; y∉boundary
   because the boundary side already σ7-collapsed exactly that seam. *)
```
Then D_chain as COMPARABILITY (not uniqueness-first):
```isabelle
lemma bnd_candidates_same_key_chain:
  assumes "x ∈ boundary_excess t k - root_excess t k"
          "y1 ∈ root_excess t k - boundary_excess t k"  "y2 ∈ root_excess t k - boundary_excess t k"
          "bnd_lift_compatible x y1"  "bnd_lift_compatible x y2"
  shows   "list_all2 (≤) (bnd_counts y1) (bnd_counts y2) ∨ list_all2 (≤) (bnd_counts y2) (bnd_counts y1)"
```
⚠ Varying run is the branch-JUNCTION run at ARBITRARY interior index (NOT leading — that wording is FALSE). Then a
finite chain + least candidate defines `f` ⇒ `card(X−Y) ≤ card(Y−X)` ⇒ `card_le_of_card_diff_le` ⇒ S1.

## Shortest executable path
```
1. COVER: fold-lift the existing pair lemmas through rsimpStrong_prune_against_rows_raw
          → row_dlforms_prune_against_rows_shared_tail_subset_later_or_credit.
2. COVER: use that scan theorem to close tagged_inv/root_split → strong_apder_acc_RALTS_singleton_cover (O1 done).
3. BND:   stop the missing-image route permanently; prove bnd_lift_compatible_rsimp7_same_head (+ one_pos_le).
4. BND:   use COVER's scan theorem to prove D_nonempty; then D_chain/comparability; then least-candidate injection
          → card(boundary_excess − root_excess) ≤ card(root_excess − boundary_excess) (O2 done).
5. SEQ:   keep the combined/clean theorem, consuming L1 + S1 (NOT the dead bare head_core).
6. FORMALIZE: replace the ideal seq interface with the combined/clean singleton_bound assembler + the domain bridge
          apder_clean r ⟹ legacy_rrexp r ∧ rntimes_free r ∧ apder_nf r.
```

## Per-agent short instructions (Pro)
**COVER:** your next target is NOT another isolated helper — it is the scan-lift
`row_dlforms_prune_against_rows_shared_tail_subset_later_or_credit`. Induct over
`rsimpStrong_prune_against_rows_raw seen later`, using the existing pair lemmas (shared RSEQ / nonstar / RSTAR
tail). Report ONLY the exact remaining induction case: tail = RSTAR/RSEQ/nonstar × pruned head list = []/singleton/length≥2.

**BND:** do NOT extend `boundary_missing_*` or any S-image premise. Next prove the local seam lemmas
`bnd_lift_compatible_rsimp7_same_head` then strengthen to `one_pos_le` on counts. Only AFTER that attempt D_nonempty
(as the scan-lift corollary), then D_chain comparability, then the least-candidate injection.

**FORMALIZE:** do NOT wait for the (false) old `seq_head_core_le_rsize`. Prepare the `singleton_bound` assembler
consuming L1_cover + boundary_term_absorb + the combined_RSEQ_clean theorem, plus the domain bridge
`apder_clean r ⟹ legacy_rrexp r ∧ rntimes_free r ∧ apder_nf r`.

## Bottom line
Not a fake problem; but stop saying "advancing". The hard core is precisely: **lift the pair-level prune facts to
scan/spine-level preservation.** The repo already has the pair-level bricks; cover's latest commits are at this layer
but have not formed the fold-lift theorem; bnd's injection scaffold is landed but D_nonempty/D_chain CANNOT be forced
without the scan/spine theorem. More scattered constructor helpers = spinning; concentrating on the scan-lift = real
convergence.

---

## 2026-06-25 ADVERSARIAL RECONCILIATION (workflow w03gpr3c2) — the nut is TRUE-PROVABLE, de-risked
An independent adversarial workflow (faithful model via the ACTUAL `rflts∘rdistinct∘rsimpStrong_prune_rows` chain)
found **NO counterexample across ~3.6M cases** (incl. all a*·a* / shared-(s*·s*)-tail / deep-nest / SEQ-root threaded).
**Verdict: TRUE-PROVABLE.** It converges with Pro's plan and adds two cleaner routes + the precise remaining gap.

**WHY the wall does NOT bite (clean structural reason): the cross-prune is CONTINUATION-FREE.** For clean
`t = RSEQ (RALTS bs) tl`: `S(s4 t k) = σ7(S(RALTS bs), S(s4 tl k))`; the ENTIRE prune lives inside
`H := S(RALTS bs) = strongALTs(rflts(map S bs))`, which has ZERO dependency on the continuation. So `H` (and every
`k1=k2` inter-branch deletion) is computed IDENTICALLY in the threaded opening (X) and the separated opening (Y).
Firing-level trace: 51384 fires in X == 51384 in Y, deleted sets identical across 390668 cases incl. 41480 GENUINE
inter-branch deletions — the wall is exercised, not vacuous, and still preserved. ⇒ `ps_X = ps_Y = head_branches H`
automatically (genuine ALTS-headed form). When the prune collapses `H` to a singleton/non-ALT (`rsimp_ALTs[p]=p`
exposing an inner altseq — Pro's "brittle" case) that is the OTHER shape, handled by the whole-row `bnd_key/counts`
lift, NOT branch-list equality. So Pro's "no UNIFORM syntactic E1/E2" and this "`ps_X=ps_Y` for genuine ALTS-head" are
CONSISTENT — split by shape.
- LAYER A `head_prune_continuation_free`: `S(s4 (RSEQ(RALTS bs) tl) k) = σ7 (S(RALTS bs)) (S(s4 tl k))` (NO induction
  on the cross-prune accumulator — Layer A confines it inside S(RALTS bs)).
- LAYER B `σ7_RALTS_head`: `H=RALTS hs ∧ cont≠RZERO ⟹ head_branches(σ7 H cont) = hs` (σ7=σ4 since H not RSTAR-headed).

**Cleaner route-around for O2 — RA1/RA2 CANCELLATION (0 viol / 269k random + 682k EXHAUSTIVE size≤8):** the
cross-prune-SYNTHESIZED rows land ONLY in X∩Y (collapse matches on BOTH sides) ⇒ they CANCEL in the diffs ⇒ **O2
reduces to PER-BRANCH S1 over non-ALT branches, never touching the global cross-prune:**
```
RA1:  root_excess t k − boundary_excess t k  ⊆  (⋃_q single_root(q,k)) − strong_apder_acc RONE k
RA2:  boundary_excess t k − root_excess t k   ⊆  ⋃_q boundary_excess(q,k)
   + per-branch base (q non-ALT): card(Xq−Yq) ≤ card(Yq−Xq)  AND the full injection   (0 viol / 298k)
⇒ the matching partner of a genuine X−Y row is ALWAYS a per-branch root row, NEVER a cross-prune-synthesized one (0/209k).
```
⚠ CORRECTION: `single_root(RALTS bs,k) ≠ ⋃_q single_root(q,k)` (for t=RALTS the cross-prune fires ACROSS t's branches;
the earlier "Y==Yb 0/74.5k" was a generator-coverage artifact). Distribute via RA1/RA2 (cancellation), not naive per-branch =.

**THE ONE REMAINING GAP (shared by all routes): the E3 seam lemma** — `counts(kX) ≤ counts(kY)` at the junction StarRun
(at ARBITRARY INTERIOR depth) needs an explicit σ4/σ7 induction with the split "junction star = continuation's leading
star (σ7 collapse fires) vs not (σ4 leaves RSEQ)" — the SAME distinction that bit three earlier S1 statements. 0-viol on
every sweep but VALIDATE the interior-depth seam induction explicitly before formalizing.
(Files: %TEMP%\prune\{prune_adv_*.py, prune_fire_decision.py, prune_setlevel_*.py, _routearound_lemma.py}.)

---

## 2026-06-25 E3 SEAM LEMMA — HAND-PROVED, the LAST gap CLOSED (workflow w84vcc7v5)
Both parts HAND-PROVED (high confidence), 0 CE across millions incl. interior junctions, the collapse boundary, and
degenerate. **The validated seam skeleton below is what BND formalizes.** ⚠ The first hand-prover shipped a proof whose
STEP 1 and STEP 3 are literally FALSE (true lemma, wrong mechanism — the recurring trap); the corrected proof and the
two mandatory corrections are below. Use THIS, not the brittle version.

**THE single load-bearing definitional choice:** pin `kY = rsimp4_SEQ_atom (S tl) (S k)` (the NORMALIZED separated
continuation). With RAW k the lemma is **FALSE** (key-level CE, ~42% of random). Both X and Y continuations go through S.

**Corrected proof of E3a** (`apder_nf tl`, `apder_nf k`; `kX = S(rsimp4_SEQ_atom tl k)`, `kY = rsimp4_SEQ_atom (S tl) (S k)`):
- **CLAIM A** (the regime-restricted STEP 1 — NOT the unconditional one): `apder_nf r ⟹ S r has NO internal
  equal-star run`. (Reason: apder_nf forbids a SEQ left-factor, so σ4 never re-associates an interior `s*·s*` into
  existence. The unconditional "S removes ALL internal equal-star runs" is FALSE — CE `tl=(b·b*)·b*` ⇒ `S tl = b·(b*·b*)`.)
- **STEP 2** `raw_spine (rsimp4_SEQ_atom x y) = bnd_spine x @ bnd_spine y` (σ4 is a pure non-collapsing spine concat).
- ⇒ **CLAIM B**: `kY`'s spine has AT MOST ONE adjacent-equal-star pair, at the seam = (last factor of `S tl`) | (first
  factor of `S k`), only when their star bodies coincide. `kX` collapses that seam (count −1) iff its left factor is RSTAR.
- ⇒ `bnd_key kX = bnd_key kY`, `list_all2 (≤) (bnd_counts kX) (bnd_counts kY)`, at most ONE differing index ⇒ `one_pos_le`.
  Single-position delta is **EXACTLY +1** (never +2 — the digest's +2 used un-normalized spines), junction at ARBITRARY INTERIOR depth.
- **⚠ DELETE STEP 3** (`kX = S(kY)`): it is FALSE (CE `tl=RALTS[a**·b**], k=b*` ⇒ `kX=a*·(b*·b*) ≠ a*·b* = S(kY)`) and UNUSED.
- 3-case seam split: (i) interior/unequal stars or non-star x_m ⇒ σ7=σ4 plug ⇒ cX=cY; (ii) equal stars, x_m's left
  neighbour RSTAR ⇒ σ7 fires, one run −1; (iii) equal stars but left neighbour non-star ⇒ σ7 degrades to σ4 ⇒ cX=cY.

**E3b** (prior proof CORRECT, verified): σ7's collapse-guard is decided by key-visible head data, so `bnd_key kX = bnd_key kY`
⇒ the collapse fires identically on both sides (asymmetric collapse structurally impossible, 0/500k). Collapse case
(`σ7 p k = k`) ⇒ goal is the hypothesis; plug case (`σ7 p k = σ4 p k`) ⇒ symmetric prepend of p.

**Isabelle lemma shapes to hand BND:**
```isabelle
definition bnd_seam_lift kX kY ≡ bnd_key kX = bnd_key kY ∧ list_all2 (≤) (bnd_counts kX) (bnd_counts kY)
definition one_pos_le xs ys ≡ list_all2 (≤) xs ys ∧ card {i. i < length xs ∧ xs!i ≠ ys!i} ≤ 1

lemma S_apder_nf_no_internal_equal_star_run:   "apder_nf r ⟹ ¬ has_internal_equal_star_run (bnd_spine (S r))"  -- CLAIM A (NOT unconditional)
lemma raw_spine_sigma4_append: "x≠RZERO ⟹ x≠RONE ⟹ bnd_spine (rsimp4_SEQ_atom x y) = bnd_spine x @ bnd_spine y"
lemma E3a_continuation_seam:                    -- pin kY normalized; do NOT use kX=S kY
  assumes "apder_nf tl" "apder_nf k"
  defines "kX ≡ S (rsimp4_SEQ_atom tl k)" and "kY ≡ rsimp4_SEQ_atom (S tl) (S k)"
  shows "bnd_seam_lift kX kY ∧ one_pos_le (bnd_counts kX) (bnd_counts kY)"
lemma bnd_lift_compatible_rsimp7_same_head_one_pos:   -- E3b
  assumes "bnd_seam_lift kX kY" "one_pos_le (bnd_counts kX) (bnd_counts kY)" "rtail_nf p"
  shows "bnd_key (rsimp7_SEQ_atom p kX) = bnd_key (rsimp7_SEQ_atom p kY)"
    and "one_pos_le (bnd_counts (rsimp7_SEQ_atom p kX)) (bnd_counts (rsimp7_SEQ_atom p kY))"
```
Supporting bridge: `bnd_profile_eq_rle_spine` (bnd_key = RLE shape of spine; bnd_counts = run-lengths). E3b helper
`bnd_key_eq_imp_same_head_guard` (σ7 collapse-guard agrees when keys agree). NO induction on the cross-prune accumulator.

**⇒ S1 chain is now validated end-to-end:** E3a + E3b ⇒ D_nonempty (existence) + D_chain (comparability) ⇒ least-candidate
injection ⇒ `card(X−Y)≤card(Y−X)` ⇒ `card_le_of_card_diff_le` (GREEN) ⇒ S1. Remaining work = FORMALIZATION (BND), not discovery.
**Two mandatory corrections for the formalizer:** (1) CLAIM A is `apder_nf`-conditioned, the unconditional STEP 1 is false;
(2) DELETE STEP 3 (`kX=S kY` is false, unused). Scratch: %TEMP%\e3seam (read-only).
