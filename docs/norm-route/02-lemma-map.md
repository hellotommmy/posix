# 02 — Lemma dependency map (N-route)

Arrows: `A → B` means "B is proved using A". `[Sn/m]` = Python evidence n viol / m
checked (from `norm_model.py`). `★` = the lone crux. No lemma here may carry `sorry`.

```
LIST LAYER (Wave 1A, NormalizedAppend.thy)
  norm_seq_idem            [implicit in T3]
  norm_seq_append_assoc    ────────────────┐
       │                                   │
       ▼                                   ▼
  nplug_assoc  [T3: 0/5,268,024] ★fragile (star-fold boundary)
       │
       ▼
NORMALIZER (Wave 1B, NormalizedStrong.thy)
  nstrong_idem            [T6: 0/8021]
  nstrong_rsimp4_shadow :  N(σ4 r k) = α(N r, N k)   [T2: 0/80210]   ← reduces to nplug_assoc
  rsize_nstrong_le,  rsize_nplug_le   (size lemmas, easy)
       │
       ├───────────────► OPENING (Wave 2A, NormalizedOpening.thy)
       │                   ndlforms_finite
       │                   OPEN-SHADOW :  x∈dl(S q) ⟹ N x ∈ δ_N(N q)   [T5_S: 0]
       │                        (RAW form  x∈dl(q) ⟹ … is FALSE — DNP-2, [T5_raw: 112])
       │                        uses  nstrong_rsimpStrong_shadow : N(S r)=N r  [T7: 0/8021]
       │
       └───────────────► ACCUMULATOR (Wave 2B, NormalizedAccumulator.thy)
                           nacc_RSEQ_subset    (telescope via nplug)
                           nacc_RALTS_subset   (clean union, NO +1 — DNP-3)
                           nacc_RSTAR_subset
                           nbase_sigma_subset
                                │
                                ▼
                  INTERNAL COUNT (Wave 3, NormalizedCount.thy)
                    card_nacc_diff_base_le :  card(A_N r k − B_N k) ≤ C·rsize r + D
                    (RSEQ telescope; RALTS Σ-subset no +1; RSTAR root+IH)
                                │
SHADOW (Wave 4, NormalizedShadow.thy)                                 │
  nstrong_rsimpStrong_shadow : N(S r)=N r        [T7]                 │
  nstrong_rsimp4_shadow      (from 1B)                                │
  old_term_acc_shadow        (constructor induction)                 │
  old_acc_shadow : x∈strong_apder_acc r k ⟹ N x ∈ nacc r (N k)       │
                                │                                     │
                                ▼                                     ▼
                  PROVENANCE (Wave 5, NormalizedProvenance.thy)  ★ THE CRUX
                    nacc_excess_sharp  (finite recursive debt; NO product — DNP-4)
                    card_nacc_excess_sharp_le : ≤ C·rsize r + D
                    old_acc_diff_inj_sharp :
                       strong_apder_acc r k − strong_apder_acc 1 k  ↪  A_N#(r, N k)
                       (injective; family r_n must give O(n) tags — DNP-5)
                                │
                                ▼
                  INTEGRATION (Wave 6, NormalizedGateBridge.thy)
                    old green bridge (EXISTS):
                       apder_strong_dlfrontier r ⊆ strong_apder_acc r RONE
                    card_apder_strong_dlfrontier_linear_norm :
                       card(apder_strong_dlfrontier r) ≤ C·rsize r + D
                                │
                                ▼
                  GATE (EXISTS, GREEN):
                    actual_gate_from_direct_universe_rowlevel
                       [loosen budget_suc_quad_le_cube from Suc(rsize r) to C·rsize r+D]
                    ⇒  cubic Gate closes.
```

## Green facts to CITE from the primary route (do NOT reprove)
- `apder_strong_dlfrontier_subset_strong_apder_acc_RONE` (the bridge)   `DirectUniverseCubic.thy:389`
- `per_row_size_le_quadratic`, `universe_le_cubic_rowlevel`,
  `actual_gate_from_direct_universe_rowlevel`, `budget_suc_quad_le_cube`  `DirectUniverseCubic.thy`
- `card_apder_rows_clean_le_rsize_plus_2`   `active:37190`
- `card_le_Suc_card_Diff_singleton`, `card_le_rsize_set`   `DirectUniverseCubic.thy:307,328`

## Kill criteria (STOP + report, do not grind) — route2_verdict §14
1. `nstrong_rsimp4_shadow` killed by a clean small example   → NOT triggered [T2]
2. OPEN-SHADOW (S-form) killed by a clean small example       → NOT triggered [T5_S]
3. `nacc_RSEQ_subset` needs an unnatural side condition
4. `nacc_RALTS_subset` needs a global `+1`                    (DNP-3)
5. `nacc_excess_sharp` countable only via product `A_N × Π`   (DNP-4)
6. family `q_i=b_i*·a*` forces `Ω(n²)` tags                   (DNP-5)
7. deep-tail forces tags > linear in syntax depth
8. main line needs `afactored1` / `rpder_strong_rows_raw` internals (DNP-6) → backup route
```
