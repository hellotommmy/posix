# OPEN_OBLIGATIONS.md — the single source of truth (route-1 final proof)

There are **exactly FOUR** open obligations. The final cubic theorem is blocked ONLY because these four
inputs are not yet unconditional Isabelle theorems with statements that MATCH the `formalize` interface.
The Gate and the conditional spine are DONE — `cubic_gate_unconditional_from_L1_D1_spine` exists and consumes
`L1_cover` + `singleton_bound`. "插座有了,电源没来。"

## DISCIPLINE (mandatory — no more "magui")
- Every worker report updates **exactly ONE** obligation below, in place. **No free-form "progress note".**
- A report MUST give the **exact missing subgoal / exact failing branch**, not "validated / advancing / N green
  helpers". "Green helper added" without naming which obligation's missing subgoal it closes is NOT a valid report.
- **Python "0 viol" is NOT a theorem-statement license.** Three statements already passed huge Python sweeps and
  were then Isabelle-REFUTED (S1 `X⊆S(Y)`, S1 `X−Y⊆S(Y−X)`, seq `head_core≤rsize h`). Hand-prove the structural
  invariant FIRST; only then formalize.
- **No Isabelle theory proof beyond a generic finite-set/order combinator may be landed unless it builds GREEN.**

---

## O1  L1_cover     (lane: COVER `card/route1-cover`)
```
exact theorem statement:
  strong_apder_acc (RALTS rs) k ⊆ (⋃ q ∈ set rs. strong_apder_acc (RALTS [q]) k)
  [Isabelle: strong_apder_acc_RALTS_singleton_cover ; still a TARGET comment, NOT landed]

current strongest theorem (@ card/route1-cover):
  CONDITIONAL bridges only — strong_apder_acc_RALTS_singleton_cover_if_tagged_inv,
  ..._if_tagged_saa_ok, ..._if_root_split  (L1 modulo `tagged_inv` / `tagged_saa_ok` / `root_split`).

missing subgoal:
  discharge `tagged_inv` (equivalently `root_split`). The HARD point is the cross-prune COLLAPSED-star row's
  branch routing: a row of row_dlforms(rsimp7_SEQ_atom t (S k)) for tagged branch (q,t) that, after σ7 collapse
  of an RSTAR tail, has NO root provenance — it must land in the singleton branch's ACC carrier, not a root one.
  (Validated truth + mechanism: ROUTE1_CRUX_STATUS.md §L1 / [[l1-singleton-cover-acc-part-rescue]].)
  ★ SHARED WITH O2: this branch-routing reduces to the SAME prune branch-list/origin-preservation lemma (S keeps the
  head-branch list across `rsimpStrong_prune_rows_acc_raw`). Crack that ONE prune lemma ⇒ BOTH O1 and O2 fall.
  ➤ RESOLUTION (Pro 2026-06-25, see PRUNE_SCANLIFT_PLAN.md): pair-level prune facts are DONE; the missing piece is the
  FOLD/SCAN LIFT `row_dlforms_prune_against_rows_shared_tail_subset_later_or_credit` (induct over
  rsimpStrong_prune_against_rows_raw, reusing the shared RSEQ/nonstar/RSTAR pair lemmas; report case tail×[]/singleton/≥2).
  Then close tagged_inv via B1 (surviving branch → singleton ROOT carrier) / B2 (collapsed-star escape → singleton ACC
  credit). STOP adding isolated row helpers — fold-lift the existing ones.
  ✅ DE-RISKED (workflow w03gpr3c2, TRUE-PROVABLE, 0 CE/~3.6M): the cross-prune is CONTINUATION-FREE (it lives inside
  H:=S(RALTS bs), computed identically in X and Y — firing-level identical). So for genuine ALTS-headed H, `ps_X=ps_Y`
  via `head_prune_continuation_free` (Layer A) + `σ7_RALTS_head` (Layer B); singleton/OTHER shape uses the whole-row
  chain lift. This is an ALTERNATIVE to the scan-lift (use whichever formalizes cleaner). ONE gap: the E3 interior-depth seam lemma.
```

## O2  S1_boundary  (lane: BND `card/route1-bnd`)
```
exact theorem statement:
  card (boundary_excess t k − root_excess t k) ≤ card (root_excess t k − boundary_excess t k)
  where boundary_excess t k = strong_apder_acc RONE (rsimp4_SEQ_atom t k) − strong_apder_acc RONE k
        root_excess     t k = single_root t k − strong_apder_acc RONE k
  [feeds card_le_of_card_diff_le ⇒ card X ≤ card Y ⇒ boundary_term_absorb (= S1)]
  DEAD routes (do NOT revive): X ⊆ S(Y) ; X−Y ⊆ S(Y−X) — both refuted (S=rsimpStrong_raw over-collapses).

current strongest theorem (@ card/route1-bnd):
  card_le_of_card_diff_le (generic, GREEN) + the injection scaffolding defs
  bnd_spine / bnd_profile / bnd_key / bnd_counts / bnd_lift_compatible. inj_on NOT proven.

missing subgoal (2026-06-23 hand-proof probe w0d8xekkc): D_nonempty + D_chain are BOTH TRUE (0 CE / ~11M incl.
ALL degenerate regimes) but BOTH are **GAP** — their proofs reduce to ONE shared open sub-lemma:
  ★ PRUNE BRANCH-LIST PRESERVATION (= the recurring a*·a* cross-prune wall; this ALSO blocks O1):
    (E1) S (rsimp4_SEQ_atom t k)           = RSEQ (RALTS ps') kX
    (E2) S (rsimp4_SEQ_atom (RALTS [t]) k) = RSEQ (RALTS ps') kY    -- SAME branch list ps'
    (E3) bnd_key (s7 p kY)=bnd_key (s7 p kX) ∧ counts(s7 p kX) ≤ counts(s7 p kY)  -- kX,kY differ ONLY at the seam
  i.e. S preserves the head-branch list across the set-level prune `rsimpStrong_prune_rows_acc_raw`. Strongly
  evidenced but NOT written equationally; the prune (DEFINITIONS.txt:131-156) is the hard nut. The injection does
  NOT avoid the wall — it RELOCATES it here. **⇒ the real O2 (and O1) blocker is this prune lemma.**
  ⚠ MECHANISM CORRECTION (the old "leading run only / count-index-0" wording is FALSE): D_chain's varying run is the
  BRANCH-JUNCTION run at ARBITRARY INTERIOR depth (a branch's trailing star meets the continuation's head star), NOT
  the leading run — ~64% of same-key collisions diff at an interior index (CE t=(b*+c**·b*+c**)·(b**·a*), k=a*·a*:
  diff at index 1). The CONCLUSION is unchanged: exactly ONE position varies ⇒ counts-comparable ⇒ each class is a
  CHAIN (size ≤2) ⇒ f inj_on. Then ⇒ card_inj_on_le ⇒ card(X−Y)≤card(Y−X) ⇒ card_le_of_card_diff_le (GREEN) ⇒ card X ≤ card Y.
  (NB the literal S1 with Y=root_excess is TRUE — the "rsize-4 CE" was a model-faithfulness error: SAA(t,k) with atf,
  not SAA(RONE, s4 t k) which has atf RONE = ∅.)
  ➤ RESOLUTION (Pro 2026-06-25, see PRUNE_SCANLIFT_PLAN.md): do NOT prove the brittle syntactic E1/E2 (it breaks on
  []/singleton/inner-RSEQ(RALTS) exposure). Use the COVER scan-lift theorem. BND order: prove
  `bnd_lift_compatible_rsimp7_same_head` (+ `one_pos_le`) → `boundary_missing_has_root_lift_from_prune_scan` (D_nonempty,
  a scan-lift corollary, EXISTENCE before inj_on) → `bnd_candidates_same_key_chain` (D_chain = COMPARABILITY) →
  least-candidate injection ⇒ card(X−Y)≤card(Y−X) ⇒ card_le_of_card_diff_le ⇒ S1. Pair-level is DONE; the fold-lift is the nut.
  ✅ DE-RISKED + CLEANER ROUTE (workflow w03gpr3c2, 0 viol / 269k+682k exhaustive): RA1/RA2 CANCELLATION — the
  cross-prune-synthesized rows land in X∩Y and CANCEL in the diff, so **O2 reduces to PER-BRANCH S1 over non-ALT
  branches, never touching the global cross-prune** (RA1: Y−X ⊆ (⋃_q single_root q k)−base; RA2: X−Y ⊆ ⋃_q boundary_excess q k;
  + per-branch base card(Xq−Yq)≤card(Yq−Xq)). ⚠ single_root does NOT distribute per-branch for t=RALTS (cross-prune fires
  across branches) — use RA1/RA2, not naive =. The matching partner of an X−Y row is ALWAYS a per-branch root row (0/209k).
  ONE gap: the E3 interior-depth seam lemma (the junction StarRun count, σ7-collapse-fires-or-not case split).
```

## O3  seq / D1     (lane: SEQ `card/route1-seq`)
```
⚠ old seq_head_core statement is FALSE (Isabelle counterexamples committed in card/route1-seq):
  apder_nf h ⟹ apder_nf t ⟹ apder_nf k ⟹ head_core(h,t,k) ≤ rsize h    -- FALSE
  seq_head_core_le_rsize_unrestricted_false : h=RONE gives rsize h < card(...)
  seq_head_core_le_rsize_nf_seq_false       : h=RALTS[RONE] (apder_nf(RSEQ h t) holds) gives card=3 > rsize h=2
  (the earlier "VALIDATED TRUE & tight" held only on the NON-degenerate clean regime; degenerate unit /
   singleton-ALT heads break the bare statement — Python sweep missed them.)

new theorem statement (the LIVE target — the COMBINED RSEQ budget on the clean domain):
  the per-row head_core is no longer the unit; charge the whole RSEQ. Target the shape already in the file:
  D1_singleton_le_rsize_from_combined_RSEQ_L1_clean   (combined head_core(r1,r2,k)+boundary(r2,k) ≤ rsize(RSEQ r1 r2)),
  on legacy_rrexp + rntimes_free + apder_nf (clean) assumptions.

current strongest theorem (@ card/route1-seq):
  required_seq_head_core_le_rsize_from_cases_clean, seq_head_core_le_rsize_from_L1_cases_clean,
  D1_singleton_le_rsize_from_seq_head_cases_boundary_L1_root_clean,
  D1_singleton_le_rsize_from_combined_RSEQ_L1_clean  (D1 singleton bound modulo {rone_diff, rseq_case, rstar_case,
  ralts_root_cover (=L1), boundary assumption (=S1), clean-domain assumptions}).

missing assumptions:
  unify the clean-domain predicate (legacy_rrexp ∧ rntimes_free ∧ apder_nf  vs  apder_clean) and discharge the
  case hypotheses; the `boundary assumption` = O2 (S1), `ralts_root_cover` = O1 (L1).
```

## O4  final assembly  (lane: FORMALIZE `card/route1-formalize`)
```
exact theorem consumed by formalize:
  singleton_bound : apder_nf q ⟹ apder_nf k ⟹ D1 q k ≤ rsize q
  consumed by card_apder_strong_dlfrontier_le_from_L1_D1_spine ⇒ cubic_gate_unconditional_from_L1_D1_spine
  (both present & GREEN, modulo L1_cover + singleton_bound).

current plug status:  ⚠ INTERFACE MISMATCH.
  D1_RSEQ_step_spine still consumes the IDEAL `seq_head_core_le_rsize` shape, which O3 has proven FALSE.
  TO FIX (theory work — FORMALIZE/Codex, build-green only): re-state singleton_bound to consume the seq lane's
  COMBINED/clean theorem (O3 new target), and bridge the domain by proving
  `apder_clean q ⟹ legacy_rrexp q ∧ rntimes_free q ∧ apder_nf q`. Until the domain predicates are unified, the
  inputs will not plug in.
```
