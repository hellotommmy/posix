# LANE BOUNDARY — prove S1 + boundary_term_absorb

You are ONE lane of a parallel route-1 formalization (POSIX cubic size-bound, Isabelle/HOL). A Secretary supervises
and merges your green proof into the integration. **Prove your lemmas; build green; no `sorry`; fail-stop + report.**
Work only in `r1bnd/Card_Route1_Bnd.thy`.

## Read first
- `pro_ask_round2/DEFINITIONS.txt` (functions + green lemmas), `pro_ask_round2/verdict_G3.md` (the L2 proof + helpers).
  Green base `cubic/DirectUniverseCubic.thy` (do NOT modify).

## YOUR TARGETS (prove S1 first, then boundary_term_absorb via S1)
```isabelle
(* S1 — the clean, collision-free sufficient condition (validated 0/629,868) *)
lemma boundary_excess_le_root_excess:
  "card (strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
     <= card (single_root t k - strong_apder_acc RONE k)"

(* boundary_term_absorb — from S1 + disjointness of collapsed-boundary forms from term rows *)
lemma boundary_term_absorb:
  assumes "apder_nf t" "apder_nf k"
  shows
    "card ((strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
            \<union> (single_term t k - strong_apder_acc RONE k))
       <= card (strong_apder_acc (RALTS [t]) k - strong_apder_acc RONE k)"
```
where `single_root q k = rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom (RALTS [q]) k))`,
`single_term q k = rsimpStrong_dlform_closure (apder_term_frontier_acc q k)` (both defined in your file).

## ★ The proof-level steer (validated by the Secretary)
Prove `boundary_term_absorb` **VIA S1**, NOT a raw injection. Useful facts:
- the decomposition `strong_apder_acc (RALTS [t]) k = single_root t k \<union> single_term t k` (provable by unfolding
  `strong_apder_acc_def`/`rsimpStrong_dlform_closure_def`; `apder_term_frontier_acc (RALTS [t]) k = apder_term_frontier_acc t k`).
- so RHS `= card ((single_root t k \<union> single_term t k) - B k)`, and the LHS shares the `(single_term t k - B k)` term;
  after cancelling it, the content is exactly S1 (`boundary-excess <= root-excess`) plus that collapsed-boundary forms
  are disjoint from genuine term rows (0 coincidences measured).

  ⚠ STALE — see the 2026-06-21 correction below. Do NOT read S1 as "a single `card_mono`-style inequality"
  or a plain-subset route. The cardinal target (card X <= card Y) is OPEN; the proposed repair pays the
  common part by identity (where X - Y = {}) via `card_mono`, PLUS the missing rows X - Y via `card_image_le`
  on the S-image of Y - X (X - Y \<subseteq> S-image(Y - X)). So it is `card_mono` + `card_image_le`, NOT pure
  `card_mono`. (And the repair itself is still UNVALIDATED — falsification-probe before formalizing.)
  Canonical status: ROUTE1_CRUX_STATUS.md §S1.

### 2026-06-21 correction: cardinal-only repair, not full S-image

Do **not** record the following as a refutation of S1 or `boundary_term_absorb`: the cardinal S1 target is
still unrefuted here.  What has been Isabelle-refuted is only the stronger helper
`uniform_S_image_boundary_subset`:

```isabelle
strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k
  \<subseteq> rsimpStrong_raw ` (single_root t k - strong_apder_acc RONE k)
```

The checked witness is RSEQ-root:

```isabelle
t = RSEQ (RCHAR a) (RALTS [RSEQ (RCHAR a) (RSTAR (RCHAR a))])
k = RSTAR (RCHAR a)
bad =
  RSEQ (RCHAR a)
    (RSEQ (RCHAR a)
      (RSEQ (RSTAR (RCHAR a)) (RSTAR (RCHAR a))))
```

The temporary proof showed `bad` is in the boundary excess but not in the
`rsimpStrong_raw` image of the root excess.  Therefore do not spend more proof time on that image-subset
branch as stated; reconcile this RSEQ-root witness before reinstating any S-image/card_image_le steer.

Current repair target: use the cardinal-only missing-row form.  Write

```isabelle
X t k = strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k
Y t k = single_root t k - strong_apder_acc RONE k
```

First prove/use the finite-set card lemma:

```isabelle
finite X \<Longrightarrow> finite Y \<Longrightarrow> X - Y \<subseteq> f ` (Y - X) \<Longrightarrow> card X \<le> card Y
```

Then target only:

```isabelle
X t k - Y t k \<subseteq> rsimpStrong_raw ` (Y t k - X t k)
```

Do **not** try to prove `X t k \<subseteq> Y t k`, and do **not** try to prove
`X t k \<subseteq> rsimpStrong_raw ` Y t k`.  For non-RSEQ constructors, plain subset
may discharge `X-Y={}`; for RSEQ, prove only the missing-row image statement.

### 2026-06-22 update — missing-image route is ALSO DEAD; live route = definable injection
Both S-image routes are now DEAD:
- `X ⊆ S-image(Y)` — REFUTED (RSEQ-root, ad485d1).
- `X−Y ⊆ S-image(Y−X)` (the "missing-row" form above) — **ALSO REFUTED** (2026-06-22 probe): `S=rsimpStrong_raw`
  over-collapses (folds the whole trailing star-nest to ONE star), so the image premise is false on clean RSEQ-root.
  Clean CE: `t=(c+a·b*)·b*`, `k=b*·b*` (`a·(b*·b*)` ∈ X−Y but ∉ S(Y−X)). ⇒ do NOT formalize
  `boundary_excess_le_root_excess_if_missing` / `..._if_missing_with_term` with `f = rsimpStrong_raw`.

**LIVE route (VALIDATED, probe wwpa6b1ld):** prove the still-true `card(X−Y) ≤ card(Y−X)` via a DEFINABLE INJECTION
`f : (X−Y) ↪ (Y−X)` — the least-dominator star-run lift (NOT S, NOT a bijection):
`spine`→`profile` (positions = AtomPos | StarRun(body,runlen)); `key` = profile with all runlens reset to 1;
`counts` = tuple of runlens; `f x = the pointwise-LEAST y∈Y−X with key y = key x ∧ counts x ≤ counts y`.

**Next formalization (IN THIS ORDER):**
1. Land the generic `card_le_of_card_diff_le : finite X ⟹ finite Y ⟹ card(X−Y) ≤ card(Y−X) ⟹ card X ≤ card Y`
   (mechanical; sibling of the green `card_le_if_missing_in_image`) + the `profile`/`key`/`counts`/`lift_compatible` defs.
2. The `inj_on f (X−Y)` step **WAITS** for the Secretary's hand-proof of the two structural lemmas: `D_nonempty`
   (every X−Y row lifts to a present Y−X row) and `D_chain` (each key-class is a chain — the "exactly-one-position"
   lemma, from σ7 collapsing only a leading equal-adjacent star-run). **Do NOT formalize inj_on yet.**

**RULE: no Isabelle theory proof beyond the generic finite-set combinator may be landed unless it builds green.**
KEEP all existing GREEN bricks (`card_le_if_missing_in_image`, finiteness, the per-constructor subset/missing leaves);
do NOT extend the missing-image leaves to RSEQ-root. Canonical status: `ROUTE1_CRUX_STATUS.md §S1`.

## BUILD — ISOLATED HEAP (required; the other lanes build concurrently)
Do NOT use the shared `.ps1` build — it shares the heap store with the other lanes and WILL corrupt it. Use your OWN
private heap (first build ~2min; then seconds):
```
& 'C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc "export USER_HOME=/cygdrive/c/Users/Chengsong/Documents/posix-route1/bnd/.isa_home && export HOME=\$USER_HOME && cd /cygdrive/c/Users/Chengsong/Documents/posix-route1/bnd && '/cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle' build -d . Posix_Card_Route1_Bnd"
```
Exit 0 = green.

## Discipline / report
0 sorry. Grep `DEFINITIONS.txt §D`
for green names. If you suspect a lemma is FALSE, STOP + report the minimal `t`+`k`. Commit small on `card/route1-bnd`;
report the proof text + build result when green.
