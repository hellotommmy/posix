# Route-1 Launchpad (2026-06-20) — one-click chat kits

All three cruxes are SETTLED (validated + proof skeletons); see `ROUTE1_CRUX_STATUS.md`. This file
is the operational launchpad: for each chat, **open it with the listed working directory, then paste
the KICKOFF block**. Lanes build with a **private `USER_HOME`** (parallel-build isolation rule —
never the shared `.ps1`). Standing rules for every lane: hand-proof-first, **NO `sorry`**, build
green, fail-stop + report the exact open goal.

Dependency order: **cover (L1)** and **bnd (S1)** are independent — run first. **seq** needs both.
**formalize** integrates via `assumes`.

---

## ▶ Lane COVER — proves L1 (the singleton cover)

- **Open chat in dir:** `C:\Users\Chengsong\Documents\posix-route1\cover`
- **Theory file:** `r1cover\Card_Route1_Cover.thy`  · **Session:** `Posix_Card_Route1_Cover`
- **Build command:**
```
& 'C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc "export USER_HOME=/cygdrive/c/Users/Chengsong/Documents/posix-route1/cover/.isa_home && export HOME=\$USER_HOME && cd /cygdrive/c/Users/Chengsong/Documents/posix-route1/cover && '/cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle' build -d . Posix_Card_Route1_Cover"
```
- **KICKOFF (paste):**
```
You are the COVER lane. Working dir: posix-route1/cover, theory r1cover/Card_Route1_Cover.thy,
session Posix_Card_Route1_Cover. Read ROUTE_COVER.md for context. Rules: hand-proof-first, NO sorry,
build green with the private-USER_HOME command, fail-stop + report the exact open goal.

TARGET: strong_apder_acc_RALTS_singleton_cover :
  "strong_apder_acc (RALTS rs) k ⊆ (⋃q∈set rs. strong_apder_acc (RALTS [q]) k)"

L1 is TRUE (>12M faithful cases, 0 viol). Prove by fix-(a) over the TWO definitional carriers of
SAA = Cclos(rfrontier(s4 r k) ∪ acc r k), Cclos U = ⋃_{p∈U} row_dlforms(S p) (per-element ⇒ splits
over ∪/⋃ via UN_Un, SUP_le_iff). Do NOT use any root-only "single source row" device
(dl_le_pruned_altseq / singleton_source_ok) — it is FALSE here (295/78457).

CARRIER I — acc/term (EXACT, no prune; you already have this green):
  acc(RALTS rs)k = ⋃_q acc(q,k), acc(RALTS[q])k = acc(q,k) ⇒ Cclos distributes ⇒ ⊆ ⋃_q SAA(RALTS[q],k).

CARRIER II — root/rfrontier, CASE ON k:
  k=RZERO, k=RONE → reuse the two GREEN root lemmas already in the file.
  k∉{RZERO,RONE} → s4(RALTS rs)k = RSEQ(RALTS rs)k, rfrontier = {RSEQ(RALTS rs)k}; carrier =
    row_dlforms(S(RSEQ(RALTS rs)k)). Prove load-bearing lemma combined_root_in_union (validated
    0/138451): row_dlforms(S(RSEQ(RALTS rs)k)) ⊆ ⋃_q SAA(RALTS[q],k). Split each y:
      (B1) y has a SURVIVING branch root-origin → that branch's rfrontier carrier. Prune
           (rsimpStrong_prune_rows_acc_raw) is SHRINK-NEVER-DROP / first-occurrence: rprune_eq_against
           only DROPS already-covered head-alt branches, rflts drops RZERO/unnests, rdistinct keeps
           first; dl distributes over the pruned ALT head (row_dlforms.simps RALTS + RSEQ(RALTS ps)k =
           ⋃_p row_dlforms(rsimp7_SEQ_atom p k)).
      (B2 — THE STAR ESCAPE) y is a cross-prune-collapsed s* with NO surviving root-origin → route to
           the ACC CARRIER, NOT a branch root. Witness: some branch q ends in (..)·s*; acc(RALTS[q],k)
           contains s*·s*, and Cclos opens row_dlforms(S(s*·s*)) = row_dlforms(s*) = {s*} via
           rsimp7_SEQ_atom's s*·s*→s* collapse. Existence/witness proof, not rewrite.
  Escape characterization to state+use: Crf(rs,k) \ ⋃_q Crf([q],k) ⊆ {RSTAR s} ⊆ ⋃_q acc-carrier.

Tactics: membership-chasing (intro/elim on ⋃, set(rflts..), set(rdistinct..), rprune_eq_against_set)
+ explicit acc witness for B2. NOT auto, NOT equational rewriting. Your lane's job is the COVER only.
```

---

## ▶ Lane BND — proves S1 + boundary_term_absorb

- **Open chat in dir:** `C:\Users\Chengsong\Documents\posix-route1\bnd`
- **Theory file:** `r1bnd\Card_Route1_Bnd.thy`  · **Session:** `Posix_Card_Route1_Bnd`
- **Build command:**
```
& 'C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc "export USER_HOME=/cygdrive/c/Users/Chengsong/Documents/posix-route1/bnd/.isa_home && export HOME=\$USER_HOME && cd /cygdrive/c/Users/Chengsong/Documents/posix-route1/bnd && '/cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle' build -d . Posix_Card_Route1_Bnd"
```
- **KICKOFF (paste):**
```
You are the BND lane. Working dir: posix-route1/bnd, theory r1bnd/Card_Route1_Bnd.thy, session
Posix_Card_Route1_Bnd. Read ROUTE_BND.md for context. Rules: hand-proof-first, NO sorry, build green
with the private-USER_HOME command, fail-stop + report.

The PLAIN subset is FALSE for RSEQ-root t (min CE t=a·a*, k=a*: LHS has the σ7-COLLAPSED row a·a*,
single_root has the UNcollapsed a·(a*·a*); distinct rows, neither contains the other ⇒ card_mono
CANNOT rescue). ABANDON the card-EQUALITY refactor (sets differ; and card X=card B does NOT give
card(X∪C)=card(B∪C) — that `sub` step was invalid). The CARD form is TRUE (0/14.7k all ctors).
Prove it with an ASYMMETRIC two-pronged split:

lemma boundary_excess_RSEQ_subset_image:        (* RSEQ-root ONLY; validates 0/5768 *)
  assumes "is_RSEQ t"
  shows "strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k
           ⊆ rsimpStrong_raw ` (single_root t k - strong_apder_acc RONE k)"
  (* then card_image_le gives the card bound for the SEQ case.
     The S-IMAGE form FAILS for ALTS-root (S over-collapses, 96 viol) — do NOT use it uniformly. *)

lemma boundary_excess_nonseq_subset:             (* non-RSEQ; PLAIN subset HOLDS, 0 viol *)
  assumes "rnonseq t"
  shows "strong_apder_acc RONE (rsimp4_SEQ_atom t k) - strong_apder_acc RONE k
           ⊆ single_root t k - strong_apder_acc RONE k"
  by (cases t; cases k;
      simp_all add: strong_apder_acc_def single_root_def rsimpStrong_dlform_closure_def
                    rsimp7_SEQ_atom_def rsimpStrong_ALTs_raw_def
                    rsimp4_SEQ_atom.simps(1) rfrontier.simps Let_def
        split: rrexp.splits)
  (* the ~100 leftover RZERO-root × all-k subgoals close because rsimp4_SEQ_atom RZERO k = RZERO and
     rfrontier RZERO = {} make BOTH sides empty — adding rsimp4_SEQ_atom.simps(1)+rfrontier.simps
     discharges them. That is exactly what stalled the (induction t; cases k)(simp_all). *)

Then boundary_excess_le_root_excess = (cases t): RSEQ via the image lemma + card_image_le; all other
branches via boundary_excess_nonseq_subset + card_mono. boundary_term_absorb is then sound as
written — it consumes ONLY the card form S1. (If `is_RSEQ`/`rnonseq` predicates aren't in scope, use
the existing rnonseq from DEFINITIONS and a cases on the RSEQ constructor.)
```

---

## ▶ Lane SEQ — proves seq_head_core (depends on L1 + boundary_term_absorb)

- **Open chat in dir:** `C:\Users\Chengsong\Documents\posix-route1\seq`
- **Theory file:** `r1seq\Card_Route1_Seq.thy`  · **Session:** `Posix_Card_Route1_Seq`
- **Build command:**
```
& 'C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc "export USER_HOME=/cygdrive/c/Users/Chengsong/Documents/posix-route1/seq/.isa_home && export HOME=\$USER_HOME && cd /cygdrive/c/Users/Chengsong/Documents/posix-route1/seq && '/cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle' build -d . Posix_Card_Route1_Seq"
```
- **KICKOFF (paste):**
```
You are the SEQ lane. Working dir: posix-route1/seq, theory r1seq/Card_Route1_Seq.thy, session
Posix_Card_Route1_Seq. Read ROUTE_SEQ.md for context. Rules: hand-proof-first, NO sorry, build green
with the private-USER_HOME command, fail-stop + report.

TARGET seq_head_core_le_rsize is TRUE and TIGHT (0 viol / ~14M exhaustive, margin 0). Charge rsize h,
NOT D1 — D1 with the COLLAPSED continuation is the FALSE recurrence (the trap). Fix the stuck RCHAR
'by' (~line 96) by NOT case-splitting on S(s4 t k). Land this helper FIRST:

lemma single_root_RSEQ_RCHAR_card_le_one:
  "card (single_root (RSEQ (RCHAR c) t) k) ≤ 1"
  (* carrier = row_dlforms(rfrontier(rsimp4_SEQ_atom (RALTS [RSEQ (RCHAR c) t]) k)).
     (cases k): RZERO→rfrontier={} (card 0); RONE→{RSEQ (RCHAR c) t}; else→{RSEQ(RALTS[..])k}.
     S keeps an RCHAR-HEADED SEQ (rsimp7_SEQ_atom fires ONLY on RSTAR heads), so
     S(RSEQ (RCHAR c) t) = RSEQ (RCHAR c)(S t), non-ALTS-head; row_dlforms NEVER distributes through
     a non-RALTS head ⇒ bottoms at a singleton ⇒ card ≤ 1. *)

Then induction on h, arbitrary t k:
 - RZERO/RONE: single_term={}, single_root singleton/empty; by simp on defs.
 - RCHAR c (the stuck case): rewrite single_term (RCHAR c)(s4 t k) = strong_apder_acc RONE (s4 t k)
   via the in-file single_term_RCHAR simp → term part absorbed by the subtracted B(s4 t k); residual
   single_root(RSEQ (RCHAR c) t) k closed by card_mono on the helper above. DISCHARGE the spurious
   RNTIMES/RRESIDUE subgoals via legacy_rrexp/rntimes_free from apder_nf — they're unreachable on the
   clean fragment; do NOT leave them to auto (that's why the 'by' failed).
 - RSEQ h1 h2: reassociate s4(RSEQ h1 h2)c = s4 h1 (s4 h2 c); h1-core via IH (≤rsize h1) + h2 via
   boundary_term_absorb (≤rsize h2 — the BND-lane card lemma, AssUME it as an `assumes` until the
   Secretary supplies the green version) + in-file single_term_RSEQ; the Suc node slack absorbs the
   extra row (RSEQ-head worst margin −1, genuine).
 - RALTS rs: use the L1 singleton cover (ASSUME it as an `assumes` — the Cover lane delivers it) →
   distinct head-prefix per branch → Σ rsize branches < rsize(RALTS rs).
 - RSTAR r: star_single_root_eq_B (single_root(RSTAR r)k = B(s4(RSTAR r)k)) + star_boundary_shift_le_one
   (σ7 collapses only leading equal-star, +1) + child IH ≤ rsize r.

Report the two assumed dependencies explicitly (boundary_term_absorb from BND, L1 cover from COVER).
```

---

## ▶ Lane FORMALIZE — spine integration (assumes the 3 cruxes)

- **Open chat in dir:** `C:\Users\Chengsong\Documents\posix-route1\formalize`
- **Theory file:** `card\Card_Route1.thy`  · **Session:** `Posix_Card_Route1`  · branch is pushed.
- **Build command:**
```
& 'C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc "export USER_HOME=/cygdrive/c/Users/Chengsong/Documents/posix-route1/formalize/.isa_home && export HOME=\$USER_HOME && cd /cygdrive/c/Users/Chengsong/Documents/posix-route1/formalize && '/cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle' build -d . Posix_Card_Route1"
```
- **KICKOFF (paste):**
```
You are the FORMALIZE / spine lane. Working dir: posix-route1/formalize, theory card/Card_Route1.thy,
session Posix_Card_Route1. Read ROUTE1.md. Rules: hand-proof-first, NO sorry, build green with the
private-USER_HOME command, fail-stop + report.

All THREE hard cruxes are settled (validated, skeletons in hand) and are being formalized on the
cover/bnd/seq lanes. Your job is the SPINE: assemble the chain assuming the three as `assumes`, so
the moment a lane lands its green lemma the Secretary swaps it in. Build the spine with these exact
assumption shapes (match names/statements so swap-in is mechanical):

 (A) L1_cover:  strong_apder_acc (RALTS rs) k ⊆ (⋃q∈set rs. strong_apder_acc (RALTS [q]) k)
 (B) boundary_term_absorb (card form, S1) — the bnd-lane statement
 (C) seq_head_core_le_rsize — the seq-lane statement (charge rsize h)

Spine to land on top of (A)(B)(C):
 1. RSEQ recurrence  D1 (RSEQ r1 r2) k ≤ rsize r1 + D1 r2 k   (uses C + boundary_term_absorb)
 2. L2 singleton size  D1 q k ≤ rsize q   (induction on q; RSEQ via 1, RALTS via the budget step + A)
 3. RALTS budget step + global  card_strong_apder_acc_diff_base_le_rsize  (induction on r, arbitrary k;
    + the two RSTAR sub-lemmas: card_rho_RSTAR_diff_base_le_1 and the σ4(RSTAR)-singleton-frontier eq)
 4. target  card_apder_strong_dlfrontier_le  (bridge: card U ≤ Suc (rsize r))
 5. cubic_gate_unconditional.

Keep everything green at each step; where a step needs (A)/(B)/(C), cite the `assumes`. Report after
each build: which spine step is green, what assumption it still rides on, next step. Do NOT re-prove
(A)/(B)/(C) yourself — the parallel lanes own them.
```

---

## ▶ Pro — Route-1 progress PDF

Paste to Pro (it browses the PUBLIC repo https://github.com/hellotommmy/posix):

```
You are writing a rigorous technical progress report (LaTeX → PDF) on an in-progress Isabelle/HOL
proof. Repo is PUBLIC: https://github.com/hellotommmy/posix

Read these files (navigate the branch file trees on GitHub):
On branch  codex/rewrite-fallback-d :
  - ROUTE1_CRUX_STATUS.md               (LATEST status, 2026-06-20 — the three cruxes are settled
                                         at the [VALIDATED] level; use this as the current state)
  - MAINLINE.md                         (charter: target theorem, proof state, dead routes, rules)
  - pro_ask_round2/DESIGN.md            (the singleton-cover design: L1 / L2 / bridge)
  - pro_ask_round2/DEFINITIONS.txt      (verbatim Isabelle definitions — use for exact statements)
  - cubic/DirectUniverseCubic.thy       (the GREEN gate cubic_gate_* ; the SINGLE open lemma
                                         card_apder_strong_dlfrontier_le)
  - cubic/DirectUniverseCubic_L3.thy    (the L3 cubic interface)
  - DIRECT_UNIVERSE_CUBIC_ROUTE.md      (the route narrative)
On branch  card/route1-formalize :
  - ROUTE1.md                           (the exact lemma chain being landed)
  - card/Card_Route1.thy                (current formalization state of the spine)

GOAL: a self-contained LaTeX document (article, amsmath/amsthm), compiled to PDF, on Route-1
(the direct-universe cubic size bound for a POSIX regex lexer). Sections:
  1. Problem & target theorem (the cubic size bound; what closing it means).
  2. The gate — DirectUniverseCubic.thy is GREEN (0 sorry) MODULO exactly one linear row-count
     lemma  card_apder_strong_dlfrontier_le : apder_clean r ⟹
     card (apder_strong_dlfrontier r) ≤ Suc (rsize r). State precisely; any linear C·rsize r+D closes it.
  3. The singleton-cover design — L1 (SAA-level singleton cover), L2 (boundary_term_absorb via S1;
     seq_head_core), the RSEQ recurrence D1(SEQ r1 r2)k ≤ rsize r1 + D1 r2 k, the RALTS budget step,
     the global induction, the bridge to card ≤ rsize+1.
  4. Crux status (from ROUTE1_CRUX_STATUS.md) — L1 cover [VALIDATED TRUE], S1 (plain subset FALSE,
     card form TRUE via the asymmetric RSEQ-image / non-SEQ-plain split) [VALIDATED], seq_head_core
     [VALIDATED TRUE & tight]. Explain the cross-prune wall (σ7 collapses a leading a*·a*→a* but the
     set-level prune keeps uncollapsed (s*·s*) survivors) and how each crux handles it.
  5. Formalization status, per lemma — green vs in-progress on the lanes.
  6. Dead-ends ruled out (e.g. the false dl_le_pruned_altseq / root-only device).
  7. Next steps.

RIGOR (critical): state every theorem precisely, lifting exact statements from the .thy /
DEFINITIONS.txt. Tag each claim with exactly one of:
  [PROVED]    = machine-checked green in Isabelle (0 sorry),
  [VALIDATED] = numerically checked (Python) + proof skeleton in hand, but NOT machine-proved,
  [OPEN]      = conjectured / unproved.
The three cruxes are [VALIDATED], NOT [PROVED] — do not upgrade them. This project has a documented
history of mislabeling validated-but-unproved steps as proved; when in doubt, mark lower.

Deliverable: complete compilable LaTeX source + the PDF.
```

---

## ▶ Pro — Route-2 progress PDF

Paste to Pro (PUBLIC repo https://github.com/hellotommmy/posix):

```
You are writing a rigorous technical progress report (LaTeX → PDF) on an in-progress Isabelle/HOL
proof — a SECOND, parallel route to the same target as Route-1. Repo is PUBLIC:
https://github.com/hellotommmy/posix

Read these files (navigate the branch file trees on GitHub):
On branch  codex/rewrite-fallback-d :
  - route2_verdict.md                 (the N-route design: redefine the normalizer N on the
                                       associative append α; kill-criteria; Wave structure; the
                                       linchpin "Claim L")
  - ROUTE2_SECRETARY_HANDOFF.md       (route-2 plan, rules, coordination)
  - MAINLINE.md                       (shared charter & target theorem — for context)
On branch  norm/01-alpha :
  - cubic/Normalized/NormalizedAppend.thy   (Wave-1A capstone: nplug_assoc GREEN — the load-bearing
                                             step of kill-criterion #1; the normalizer N on assoc. append α)
On branch  norm/00-base :
  - active/AntimirovNormalFrontier.thy       (the normalized-frontier N-route theory)
  - active/AntimirovFactoredTransition.thy   (Wave-0/Wave-5 baseline)
  (the linchpin "Claim L" — robust on 2.8M+ checks, easy proof REFUTED — is described in
   route2_verdict.md; locate its statement within the N-route theory files above.)

GOAL: a self-contained LaTeX document (article, amsmath/amsthm), compiled to PDF, on Route-2
(the normalized N-route). Sections:
  1. Why a second route — what Route-2 changes vs Route-1 (the normalizer N on associative append α;
     how it aims to kill the cross-prune wall that blocks Route-1).
  2. The kill-criteria and the Wave plan — what each Wave must establish.
  3. Current status — nplug_assoc [PROVED, norm/01-alpha]; Claim L [VALIDATED on 2.8M+ but its easy
     proof REFUTED, norm/00-base]; the crux = Wave-5 no-product linear injection.
  4. The open crux(es) — state precisely and explain difficulty.
  5. Comparison to Route-1 — shared machinery vs divergence.
  6. Next steps.

RIGOR (critical): lift exact statements from the theory files / route2_verdict.md. Tag every claim
[PROVED] (green in Isabelle, 0 sorry) / [VALIDATED] (numerically checked, NOT proved) / [OPEN]. Do
NOT overclaim — mark validated-but-unproved as [VALIDATED], never [PROVED].

Deliverable: complete compilable LaTeX source + the PDF.
```
