# ⛔ RALTS GAP (2026-06-17) — the `strong_apder_acc` card route has a REAL gap at RALTS. PIVOT to Antimirov/AFP.

VALIDATED FALSE (963/36318 in-regime): the per-child distribution the `strong_apder_acc` route needs at RALTS,
  rows(rsimpStrong_raw(rsimp4_SEQ_atom(RALTS rs) k)) ⊆ rows(k) ∪ (⋃ q∈rs. rows(rsimp4_SEQ_atom q k)),
is FALSE — it is the `a*·a*` S-collapse wall. CE: RALTS = ((a·a*)+a), k = a*, leaks the row `a·(a*·a*)`:
the RALTS-combined strong opening keeps `a*·a*` UNcollapsed, but each child opened separately collapses it
to `a*`, so that row comes from NO single child. Hence the card lemma's RALTS diff-bridge — `card-a` build
RED @830 `x ∈ rows(rsimpStrong_raw(rsimp4_SEQ_atom(RALTS rs) k)) − strong_apder_acc RONE k ⇒ x ∈ ⋃_q
strong_apder_acc q k`; `card-2`'s `_modulo_RALTS` hypothesis — CANNOT be closed via per-child distribution.

The card BOUND `card (apder_strong_dlfrontier r) ≤ Suc (rsize r)` is STILL TRUE (validated 0 fails). It is the
PROOF METHOD that is broken at RALTS, not the bound.

✅ USE THE ANTIMIROV / AFP ROUTE (lane card-1): `card(apder_strong_dlfrontier r) ≤ linear` IS Antimirov's
proven LINEAR count of DISTINCT partial derivatives (AFP `Myhill-Nerode`; thesis Ch.7 §7.1.1 Property 9). It
bounds the count of distinct rows DIRECTLY — NO per-child distribution — so it SIDESTEPS the a*·a* collapse.
ALL card lanes: stop grinding the strong_apder_acc RALTS bridge; bound the count the Antimirov way.
