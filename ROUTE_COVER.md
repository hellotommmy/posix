# LANE COVER — prove L1 (the SAA-level singleton cover)

You are ONE lane of a parallel route-1 formalization (POSIX cubic size-bound, Isabelle/HOL). A Secretary (separate
Claude session) supervises and merges your green proof into the integration. **Prove ONE lemma; build green; no
`sorry`; fail-stop + report.** Work only in `r1cover/Card_Route1_Cover.thy`.

## Read first (in this worktree)
- `pro_ask_round2/DEFINITIONS.txt` — every function + the GREEN lemmas you cite, verbatim.
- `pro_ask_round2/verdict_G2.md` — the cover analysis (and WHY the naive route fails).
- Green base (do NOT modify): `cubic/DirectUniverseCubic.thy`.

## YOUR TARGET
```isabelle
lemma strong_apder_acc_RALTS_singleton_cover:
  "strong_apder_acc (RALTS rs) k \<subseteq> (\<Union>q \<in> set rs. strong_apder_acc (RALTS [q]) k)"
```
(`strong_apder_acc r k = rsimpStrong_dlform_closure (rfrontier (rsimp4_SEQ_atom r k) \<union> apder_term_frontier_acc r k)`.)

## ★ The proof-level steer (validated by the Secretary — follow it)
Prove it at the **SAA level directly** (each opened parent row lies in SOME branch's FULL carrier
`strong_apder_acc (RALTS[q]) k`). **Do NOT use** verdict_G2's `dl_le_pruned_altseq` / `singleton_source_ok` route — it
is FALSE (it tracks only the branch ROOT-row opening; the σ7 `a*·a*`-collapse residual, e.g. a bare `a*`, is an ORPHAN
there; min CE `rs=[((a+b)·a*),((a+1)·a*)]`, pruned row `a*`, `k=a*`).
- **TERM part is easy** (distributes per-branch): `apder_term_frontier_acc (RALTS rs) k = (\<Union>q. apder_term_frontier_acc q k)`,
  so `rsimpStrong_dlform_closure (apder_term_frontier_acc (RALTS rs) k) \<subseteq> (\<Union>q. strong_apder_acc (RALTS[q]) k)` by `auto`/unfolding.
- **ROOT part is the work**: `rfrontier (rsimp4_SEQ_atom (RALTS rs) k)` — the single row `RSEQ (RALTS rs) k`,
  S-normalized (where the cross-row prune of `S(RALTS rs)` lives) then opened. Show each opened row lands in some
  singleton branch's carrier. The collapsed cross-prune residual is covered by a branch's TERM/continuation part
  (not its root) — that is exactly why the SAA-level (full carrier) cover holds where the root-only device fails.
  Handle `k ∈ {RZERO, RONE}` first (trivial), then general k.

## BUILD — ISOLATED HEAP (required; the other lanes build concurrently)
Do NOT use the shared `scripts\codex-isabelle-build-posix.ps1` — it shares the Isabelle heap store with the other
parallel lanes and WILL corrupt it (`Posix_Cubic FAILED ... parent saved state does not match`). Use your OWN private
heap. Run this exact command (first build ~2min builds the chain in your private store; then iterations are seconds):
```
& 'C:\Users\Chengsong\Isabelle2025-2\contrib\cygwin\bin\bash.exe' -lc "export USER_HOME=/cygdrive/c/Users/Chengsong/Documents/posix-route1/cover/.isa_home && export HOME=\$USER_HOME && cd /cygdrive/c/Users/Chengsong/Documents/posix-route1/cover && '/cygdrive/c/Users/Chengsong/Isabelle2025-2/bin/isabelle' build -d . Posix_Card_Route1_Cover"
```
Exit 0 = green.

## Discipline / report
0 sorry/oops/admit. Grep `DEFINITIONS.txt §D` to confirm
green names. If you suspect the lemma is FALSE, STOP and report the minimal `rs`+`k` (the Secretary re-validates on the
witness family). Commit small on `card/route1-cover`; when the lemma is green, report the full proof text + build result.
