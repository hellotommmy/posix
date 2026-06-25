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

missing subgoal D_nonempty / D_chain (HAND-PROVE first, from rsimp4/rsimp7/prune — σ7 collapses ONLY the
leading equal-adjacent star-run):
  D_nonempty: ∀ x ∈ X−Y. ∃ y ∈ Y−X. lift_compatible x y   (every collapsed boundary row has a more-expanded
              root row to pay it — reinflate the leading collapsed star-run).
  D_chain:    within one key-class, two distinct X−Y rows differ in EXACTLY ONE star-run count position ⇒ the
              compatible set is a CHAIN ⇒ unique least element ⇒ f : X−Y ↪ Y−X is inj_on.
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

current plug status after FORMALIZE/Codex build-green edit (`Posix_Card_Route1`, private heap, EXIT 0):
  DONE: removed the formalize singleton adapter that consumed the refuted IDEAL `seq_head_core_le_rsize`
  shape.  Added the corrected assembler:
    singleton_bound_from_L1_BND_combined_RSEQ_clean_spine
      assumes L1_cover in the nested RALTS shape needed by the singleton induction,
      assumes boundary_term_absorb,
      assumes the seq combined clean theorem
        combined head-core(r1,r2,k) + boundary(r2,k) ≤ rsize (RSEQ r1 r2),
      and proves
        legacy_rrexp q ⟹ rntimes_free q ⟹ apder_nf q ⟹ apder_nf k ⟹ D1 q k ≤ rsize q.

  DONE: kept the corrected adapter:
    singleton_bound_from_combined_RSEQ_L1_clean_spine
      consumes the already-assembled clean-domain singleton theorem plus apder_clean q, apder_nf k,
      and shows D1 q k ≤ rsize q.

  DONE: domain bridge is GREEN:
    apder_clean_domain_spine :
      apder_clean q ⟹ legacy_rrexp q ∧ rntimes_free q ∧ apder_nf q.

current O4 plug status after FORMALIZE/Codex clean-wrapper edit (`Posix_Card_Route1`, private heap, EXIT 0):
  DONE: added the clean-domain RALTS budget hook
    card_strong_apder_acc_RALTS_diff_base_le_size_budget_from_D1_clean_spine
  carrying outer `apder_clean (RALTS rs)` into each branch singleton call via
    apder_clean_domain_spine :
      apder_clean q ⟹ legacy_rrexp q ∧ rntimes_free q ∧ apder_nf q.

  DONE: added the clean global count wrapper
    card_strong_apder_acc_diff_base_le_rsize_from_L1_D1_clean_spine :
      L1_cover ⟹
      (∀ q k. legacy_rrexp q ⟹ rntimes_free q ⟹ apder_nf q ⟹ apder_nf k ⟹ D1 q k ≤ rsize q) ⟹
      apder_clean r ⟹ apder_nf k ⟹ D r k ≤ rsize r.

  DONE: added the clean final target wrapper
    card_apder_strong_dlfrontier_le_from_L1_D1_clean_spine :
      L1_cover ⟹ singleton_bound ⟹ apder_clean r ⟹
      card (apder_strong_dlfrontier r) ≤ Suc (rsize r).

  DONE: added the clean cubic wrapper
    cubic_gate_unconditional_from_L1_D1_clean_spine :
      L1_cover ⟹ singleton_bound ⟹ apder_clean r ⟹
      rsize_set (row_dlformss (rpder_strong_rows_raw c (afactored1 r s))) ≤ 2 * (rsize r + 3)^3.

  EXACT OPEN POINT: supply the two assumptions to the new clean wrappers:
    - top-level `L1_cover`
        strong_apder_acc (RALTS rs) k ⊆ (⋃q∈set rs. strong_apder_acc (RALTS [q]) k)
    - clean-regime singleton/D1 bound
        legacy_rrexp q ⟹ rntimes_free q ⟹ apder_nf q ⟹ apder_nf k ⟹ D1 q k ≤ rsize q,
      produced by `singleton_bound_from_L1_BND_combined_RSEQ_clean_spine` from nested L1 + BND
      `boundary_term_absorb` + SEQ `combined_RSEQ_clean`.
  No old/refuted `seq_head_core_le_rsize` interface is used by the new clean final wrappers, and no L1/S1/seq
  proof was re-proved here.
```
