# Route-1 — Crux Status (2026-06-20)

**Gate state.** `cubic/DirectUniverseCubic.thy` is GREEN (0 sorry) MODULO one linear row-count
lemma:

```
card_apder_strong_dlfrontier_le :
  apder_clean r ⟹ card (apder_strong_dlfrontier r) ≤ Suc (rsize r)
```

Any linear bound `C·rsize r + D` closes the gate. The singleton-cover design reduces this lemma
to THREE cruxes (L1 cover, S1 boundary-excess, seq_head_core). **All three are now SETTLED at the
`[VALIDATED]` level** — hand-proof + definition-shape counterexample + faithful-Python
confirmation, with proof skeletons in hand. They are **NOT yet Isabelle-green**; formalization is
in progress on the lanes. Tag everything below `[VALIDATED]`, never `[PROVED]`.

Settled by two adversarial workflows (3 agents each, hand-prove ∥ CE-hunt ∥ python-confirm).
Methodology rule: hand-proof first + deliberately constructed definition-shape CE; Python only
confirms. Faithful model + scratch validators in `pro_ask_round2/` (`scratch_l1_*.py`,
`secretary_validator.py`).

---

## L1 — singleton cover  `[VALIDATED, TRUE — high confidence]`

```
strong_apder_acc (RALTS rs) k  ⊆  (⋃ q ∈ set rs. strong_apder_acc (RALTS [q]) k)
```

TRUE across >12M faithful cases (0 viol), including the exact cross-prune wall family. The famous
"CE" `[(a+b)·a*, (a+1)·a*] @ k=a*` does **not** refute L1 (L1 holds there); it only refutes Pro's
dead root-only device `singleton_source_ok` / `dl_le_pruned_altseq` (false 295/78457).

**Proof = fix-(a), two definitional carriers of** `SAA = Cclos(rfrontier(s4 r k) ∪ acc r k)`,
`Cclos U = ⋃_{p∈U} row_dlforms(S p)` (per-element ⇒ splits over ∪/⋃):
- **Carrier I — acc/term (EXACT, no prune):** `acc(RALTS rs)k = ⋃_q acc(q,k)`, `acc(RALTS[q])k =
  acc(q,k)` ⇒ `Cclos` distributes ⇒ ⊆ ⋃_q SAA(RALTS[q],k). (0/283668)
- **Carrier II — root/rfrontier, case on k:** RZERO/RONE reuse the two green in-file lemmas;
  general k → carrier `row_dlforms(S(RSEQ(RALTS rs)k))`, split each y:
  - **(B1)** y has a surviving branch root-origin → that branch's root carrier (prune
    `rsimpStrong_prune_rows_acc_raw` is shrink-never-drop / first-occurrence:
    `rprune_eq_against` only drops covered head-alts, `rflts`/`rdistinct`).
  - **(B2 — the only hard case)** y is a cross-prune-collapsed `s*` with NO root origin → route to
    the **acc carrier** (NOT a branch root — that mis-attribution is the dead device): a branch
    ending `(..)·s*` has acc row `s*·s*`, `Cclos` opens `S(s*·s*)=s*={s*}`.
  - Escape characterization: `Crf(rs,k) \ ⋃_q Crf([q],k) ⊆ {RSTAR s} ⊆ ⋃_q acc-carrier`
    (0 non-star, 0 unrouted).

⚠ L1 is the COVER; it does NOT close the gate alone — the singleton-SIZE budget (where uncollapsed
`s*·s*` survivors bite) is L2, carried by the S1 + seq_head lanes.

---

## S1 — boundary-excess / `boundary_term_absorb`  `[card target OPEN — image repair REFUTED (ad485d1)]`

The **PLAIN subset** `A(RONE, s4 t k) ⊆ single_root t k ∪ B k` is **FALSE for RSEQ-root t**
(min CE t=`a·a*`, k=`a*`: LHS has the σ7-collapsed row `a·a*`, single_root has the uncollapsed
`a·(a*·a*)`; distinct rows, neither contains the other ⇒ `card_mono` cannot rescue — the a*·a*
σ7 depth-of-collapse mismatch). The **CARD inequality** that `boundary_term_absorb` actually needs
is the still-**OPEN / unrefuted** target (validated 0/14.7k, but validation alone is suspect here — see the refutation below):

```
card (strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k)
  ≤ card (single_root t k - strong_apder_acc RONE k)
```

The bnd lane's card-EQUALITY refactor was doomed (sets differ; and `card X = card B` ⇏
`card(X∪C)=card(B∪C)`).

⚠ **REFUTED & SUPERSEDED (commit `ad485d1`).** Notation: X = boundary excess =
`strong_apder_acc RONE (rsimp4_SEQ_atom t k) − strong_apder_acc RONE k`; Y = root excess =
`single_root t k − strong_apder_acc RONE k`; S = `rsimpStrong_raw`; write S-image(Z) for the Isabelle
image of Z under S. The card target `card X ≤ card Y` is still **OPEN / unrefuted**.

**REFUTED:** the S-image subset `X ⊆ S-image(Y)` is FALSE **even for RSEQ-root** (counterexample in
commit `ad485d1`). The earlier "0/5768 validated" was a coverage-gap artifact — same sampling trap as
route-2's M=1. So `card_image_le` via `X ⊆ S-image(Y)` is DEAD. Do NOT re-propose the asymmetric
RSEQ→S-image / non-SEQ→plain split.

**NEW PROPOSED REPAIR — NOT yet validated; the Secretary (Claude) is falsification-probing it. Do NOT
grind it into Isabelle until that probe confirms it (else it is the same "grind an unvalidated route"
mistake).**
```
X − Y  ⊆  S-image(Y − X)        -- the part of X missing from Y = S-image of the part of Y missing from X
card_le_of_missing_image :  finite X ⟹ finite Y ⟹ (X − Y) ⊆ S-image(Y − X) ⟹ card X ≤ card Y
   -- a surjection (Y − X) ↠ (X − Y) via S gives card(X−Y) ≤ card(Y−X), hence card X ≤ card Y
```

**BND theory state (ad485d1):** only 3 helpers landed — `finite_single_root`, `finite_single_term`,
`strong_apder_acc_singleton_decomp`. S1 and `boundary_term_absorb` are still comment targets, not landed.

**Original two-pronged fix below — DEAD, do not revive (record only):**
- RSEQ-root → **S-image subset** `A−B ⊆ rsimpStrong_raw \` (single_root−B)` (0/5768) + `card_image_le`.
  (The S-image FAILS for ALTS-root — S over-collapses, 96 viol — so it must NOT be used uniformly.)
- non-RSEQ (`rnonseq t`) → **plain subset** holds (0 viol), `(cases t; cases k; simp_all …)`;
  the ~100 leftover RZERO-root subgoals close via `rsimp4_SEQ_atom RZERO k = RZERO` +
  `rfrontier RZERO = {}` (both sides empty).
- `boundary_excess_le_root_excess` = `(cases t)`: RSEQ via image + `card_image_le`, others via
  plain subset + `card_mono`. `boundary_term_absorb` then consumes only the card form — sound.

---

## seq_head_core  `[VALIDATED, TRUE & tight]`

```
assumes apder_nf h, apder_nf t, apder_nf k
card ((single_root (RSEQ h t) k ∪ single_term h (rsimp4_SEQ_atom t k))
      - (strong_apder_acc RONE k ∪ strong_apder_acc RONE (rsimp4_SEQ_atom t k)))
  ≤ rsize h
```

TRUE and TIGHT (margin 0 at h=b*,t=a*,k=a*; 0 viol over ~14M exhaustive). MUST charge `rsize h`
(the head syntax pays for the frozen-tail / doubled rows; tail/k stars are a suffix-shared product
that does not inflate row count) — the recurrence `D1 h (s4 t k)` with the collapsed continuation
is the FALSE trap and is deliberately sidestepped.

**Fix** (the stuck RCHAR `by`): do NOT case-split `S(s4 t k)`. Helper first —
`single_root_RSEQ_RCHAR_card_le_one : card (single_root (RSEQ (RCHAR c) t) k) ≤ 1` (an RCHAR-headed
SEQ never distributes through `row_dlforms` ⇒ singleton). Then induction on h: RZERO/RONE trivial;
RCHAR via `single_term_RCHAR` (term part absorbed by `B(s4 t k)`) + the helper (discharge spurious
RNTIMES/RRESIDUE via `legacy_rrexp`/`rntimes_free`); RSEQ via reassociation + `boundary_term_absorb`
(the S1 card lemma) + in-file `single_term_RSEQ` (Suc node slack absorbs the extra row); RALTS via
the L1 cover; RSTAR via `star_single_root_eq_B` + `star_boundary_shift_le_one` + child IH.

---

## Net + dependency order

The singleton-cover design is **SOUND**; remaining work is Isabelle formalization, not math
discovery. Land order:
- **cover (L1)** and **bnd (S1)** are independent leaves → formalize in parallel first.
- **seq (seq_head_core)** depends on BOTH `boundary_term_absorb` (bnd) and the L1 cover.
- **formalize (spine + ASSEMBLER)** integrates all three via `assumes`, swapping in the real lemmas as the
  lanes land them; then assembles up to `card_apder_strong_dlfrontier_le` and `cubic_gate_unconditional`.

### ⚠ The easily-missed layer: the `singleton_bound` ASSEMBLER (FORMALIZE owns it — NOT a crux lane)
The three cruxes do NOT by themselves give the singleton size bound. There is a distinct ASSEMBLY layer:
```
singleton_bound :  apder_nf q ⟹ apder_nf k ⟹ D1 q k ≤ rsize q     (D1 q k = card (SAA (RALTS[q]) k − B k))
```
proved by **induction on q**, tying together:
```
  base cases (RZERO/RONE/RCHAR)
  + RSEQ step   D1 (RSEQ r1 r2) k ≤ rsize r1 + D1 r2 k     (D1_RSEQ_step_spine; uses boundary_term_absorb + seq_head_core)
  + RSTAR step  (D1_RSTAR_step_spine)
  + RALTS step  (rflts-flatten + the RALTS budget  D (RALTS rs) k ≤ Σ rsize,  which uses L1)
  ⇒ singleton_bound
```
The existing `D1_*_step_spine`s do **NOT** auto-produce `singleton_bound` — they must be tied by the q-induction.
**COVER / BND / SEQ each deliver ONLY their one crux lemma** (L1 / `boundary_term_absorb` / `seq_head_core`);
**none of them delivers `singleton_bound` or any `RALTS_diff`** — that assembly is FORMALIZE's. Then the global
`D r k ≤ rsize r` (induction on r) uses `singleton_bound` at the RALTS case, → (G) → cubic.
