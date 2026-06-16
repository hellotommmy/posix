# WORKER-A — formalize the RSTAR cube-shell (Pro strategy VALIDATED, with one caveat)

Self-sync first: `git pull --rebase --autostash` in `posix-codex`, read `STEER.md`, then read
`gpt_pro_bundle/verdict_root.md` (the proof strategy) and `RSTAR_CUBE_SHELL_SKETCH.md` (the de-risk). No
`sorry`/`oops`. Claim each lemma in `PROGRESS_BACKREF.md` before editing. Build with
`scripts\codex-isabelle-build-posix.ps1` (the fast `Posix_Antimirov` leaf).

## The whole gate is one lemma away
All GREEN already (no sorry): the gate reduces via `actual_gate_bridge_from_strong_opened_live_potential` (@35221)
+ `rsize_set_strong_opened_live_row_universe_le_potential` (@35010) to the CUBE-SHELL invariant
`strong_opened_live_acc_potential r k ≤ (rsize r + rsize k)^3 − (rsize k)^3`, whose constructor steps are GREEN for
leaves/RALTS (@33665)/RSEQ (@33928). The ONLY open step is **RSTAR**. Prove it and the gate closes (clean fragment).

## Secretary-VALIDATED (so you can trust the targets)
- Pro's `pot_trace`/`event_cost` exactly computes the potential: `pot_trace_sound` checked 0/949 mismatches.
- The affine envelope `pot(RSTAR r) k ≤ M^3 + 3·M^2·rsize k` (M = rsize(RSTAR r)) is TRUE: 0 violations / 530+437
  incl. the witness family + RSTAR star-re-entry inflation.
- The two scalar bounds are TRUE: `A(r) ≤ M^3` and `B(r) ≤ 3·M^2` (0/437).

## ⚠ CAVEAT (validation-found — do NOT waste time here)
Pro's `rsimpStrong_self_star_absorb` / `..._absorb_open` lemma — `row_dlforms(S(σ(RSTAR r) k)) = row_dlforms(S k)`
— is **FALSE unrestricted** (483/508 fail). It holds **only when `k` is `r*`-prefixed** (0/615). Do NOT try to prove
the unrestricted form. Moreover the body `r` can never contain the anchor `RSTAR r` (a term can't contain itself),
so a *second* copy of `r*` never arises while unrolling the body — Pro's "`q = r`" absorption branch is essentially
vacuous. The real engine is:
- **slope (`trace_B ≤ 3M^2`):** in `pot(RSTAR r) k`, the continuation `k` always sits at the TAIL, behind the single
  `r*` anchor (`σ(RSTAR r) k = r*·k`, and every deeper continuation is `path·r*·k`). `k` at the tail adds rows
  LINEARLY to each opened ledger ⇒ slope is `O(M^2)`, no quadratic-in-`k` term. (Prove a tail-monotonicity/linearity
  lemma: `opn(σ sub (cont·k)) ≤ opn(σ sub cont) + (linear-in-rsize k)`, summed over the trace.)
- **intercept (`trace_A ≤ M^3`):** at `k = RONE`, the charged rows live in the STAR's own derivative universe; use
  the proven static facts `card_apder_rows_clean_le_rsize_plus_2` (@37190, ≤ M+2 rows) and
  `apder_rows_member_size_quadratic` (@31364, each row ≤ (M+2)^2) + the quadratic opening bound
  `rsize_set_row_dlforms_rsimpStrong_raw_quadratic` (@22761). Linear × quadratic = cubic.

## Order of work (land the SAFE skeleton first, then grind the crux)
1. **`pot_trace` + `pot_trace_sound`** (`pot r k = sum_list (map event_cost (pot_trace r k))`). Definitional — `induction r`
   + `sum_list` simp. Low risk. (Trace/event defs are in verdict_root.md §2; they match the `pot` recursion exactly.)
2. **The arithmetic skeleton (makes the whole gate conditional on just the envelope):**
   - `strong_opened_live_acc_potential_RSTAR_cube_shell` from an assumed
     `..._RSTAR_affine_envelope` (`pot(RSTAR r) k ≤ M^3+3M^2·rsize k`) by `nlinarith`
     (`M^3+3M^2 n ≤ (M+n)^3 − n^3`, leftover `3 M n^2 ≥ 0`).
   - Wire it into the cube-shell induction driver (leaves/RALTS/RSEQ are the existing green cases), specialise
     `k := RONE` → `pot r RONE ≤ 2(rsize r+3)^3`, feed @35010 + @35221. ⇒ the gate is GREEN modulo the envelope.
3. **HEAD term**: `opn(σ(RSTAR r) k) ≤` the top shell layer — direct analogue of the GREEN
   `strong_opened_live_acc_RALTS_root_shell_large` (@33427); copy it with `n := rsize r + rsize k`.
4. **THE CRUX — the two scalar lemmas** (`trace_A ≤ M^3`, `trace_B ≤ 3M^2`) ⇒ the affine envelope. Use the slope/
   intercept engines above (NOT the unrestricted absorption). This is the real proof content; if you hit a concrete
   wall, post the exact stuck goal in PROGRESS and the Secretary will sharpen it (or fire a Pro follow-up).

If a numeric sub-claim you invent needs checking, ask the Secretary to validate it on the witness family
(`witness_gen.py` / `scratch_cubeshell_*.py`) BEFORE you sink proof effort into it — two earlier targets were false
by sampling artifact. Do not edit the gate wrapper or the green reduction.
