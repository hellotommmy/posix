# Backreference Pilot Bounties

This is the competitive-collaborative bounty board for the POSIX backreference
formalization pilot. It follows the Agent Hunt bounty mechanics: agents compete
for theorem bounties but are incentivized to collaborate.

Amounts are in simulated USD. A payout is valid only when the named artifact
exists, the guards pass, and the required Isabelle CI session succeeds.

Admin policy update: wrapper-only theorem packages do not count as bounty
deliverables. Summary/cases/iff/same/retrieve-equality facts may remain as API
convenience lemmas, but future bounty claims must introduce a new semantic or
algorithmic layer, or a nontrivial proof bridge needed by later work.

See `agent_hunt_pipeline/projects/posix-backref/BOUNTY_PROTOCOL.md` for the
full rules including locking, sub-bounties, effort estimates, and statement
immutability.

## Pool

| Category | Amount |
| --- | ---: |
| Total pool | 150,000 |
| Allocated (active + completed) | 135,090 |
| Collected (paid out) | 74,970 |
| Reserved (unallocated) | 14,910 |

## Agent Balances

| Agent | Role | Balance | Notes |
| --- | --- | ---: | --- |
| Codex | Admin/Worker | 67,750 | Completed BR-001 through BR-004, BR-006 through BR-010, BR-015 through BR-022, BR-032, BR-035 |
| Opus | Worker | 6,200 | Completed BR-005, BR-011, BR-012, BR-013, BR-014; BR-015 lock released when Cursor was retired |
| MergeSteward | Steward | 0 | Integration role |
| Alice | Worker | 0 | Optional future worker |
| Bob | Worker | 0 | Optional future worker |

## Active

| ID | Task | Bounty | Est. Lines | Difficulty | Est. USD | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |
| BR-023 | Original-file migration TODO audit | 120 | 30 | 3 | 120 | OPEN | - | RegLangs.thy;PosixSpec.thy;Lexer.thy;LexerSimp.thy;Blexer.thy;BlexerSimp.thy;BasicIdentities.thy;GeneralRegexBound.thy;ClosedForms.thy;ClosedFormsBounds.thy;FBound.thy | AdminReview | Small planning bounty only; no theorem payout until admin approves direct original-file implementation |
| BR-024 | Migrate backref4 language semantics into original RegLangs | 1,400 | 120 | 8 | 1,400 | OPEN | - | RegLangs.thy:backref_lang4,nullable_correctness,der_correctness,ders_correctness | Isabelle:Posix | Direct `rexp/L/nullable/der/ders` extension with BACKREF4/HALF/RESIDUE; no brexp/gbrexp wrappers |
| BR-025 | Migrate backref values and POSIX rules into original PosixSpec | 1,800 | 180 | 9 | 1,800 | OPEN | - | PosixSpec.thy:L_flat_Prf,LV_finite,Posix_determ,Posix_LV | Isabelle:Posix | Direct `val/flat/Prf/LV/Posix` extension; no bval/bval4/gbval wrappers |
| BR-026 | Migrate backref injection and lexer correctness into original Lexer | 1,400 | 140 | 9 | 1,400 | OPEN | - | Lexer.thy:Prf_injval,Posix_injval,lexer_correctness,Prf_flex | Isabelle:Posix | Direct `mkeps/injval/lexer/flex` extension after BR-024/025 |
| BR-027 | Migrate backref bitcoded lexer into original Blexer | 1,800 | 170 | 9 | 1,800 | OPEN | - | Blexer.thy:erase_bder,retrieve_code,bmkeps_retrieve,bder_retrieve,MAIN_decode,blexer_correctness | Isabelle:Posix | Direct `bit/arexp/code/decode/retrieve/bder/blexer` extension; no bbit/barexp/gabexp wrappers |
| BR-028 | Preserve aggressive original BlexerSimp for backrefs | 1,400 | 140 | 9 | 1,400 | OPEN | - | BlexerSimp.thy:rewrites_to_bsimp,rewrite_preserves_bder,central,main_blexer_simp,blexersimp_correctness | Isabelle:Posix | Must use original rewrite-system route; weak structural simplifier or wrapper equality does not count |
| BR-029 | Add backref closed-form families in original closed-form machinery | 1,200 | 160 | 9 | 1,200 | OPEN | - | BasicIdentities.thy;ClosedForms.thy:backref4_closed_form,half_closed_form,residue_closed_form | Isabelle:Posix | Decide rexp vs temporary rrexp, then add real BACKREF4/HALF/RESIDUE closed-form coverage |
| BR-030 | Close original bounds after backref migration | 1,000 | 120 | 8 | 1,000 | OPEN | - | GeneralRegexBound.thy;ClosedFormsBounds.thy;FBound.thy:finite_size_n,rders_simp_bounded,annotated_size_bound | Isabelle:Posix | Final boundedness through original theorem chain; BackRefBoundedBlueprint wrappers do not count |
| BR-031 | Cubic non-backref size-bound blueprint | 5,000 | 120 | 8 | 5,000 | OPEN | - | PROGRESS_BACKREF.md;BasicIdentities.thy;ClosedFormsBounds.thy;FBound.thy | AdminReview | State the cubic target, fragment invariant, and Antimirov-style frontier plan; no theorem payout for wrapper-only restatements |
| BR-033 | Prove partial-derivative universe cubic bound | 12,000 | 300 | 10 | 12,000 | OPEN | - | GeneralRegexBound.thy:partial_derivative_path_universe,partial_derivative_live_row_universe,rfrontier_path_continuation_subset_path_universe,partial_derivative_live_row_universe_subset_path,rsizes_distinct_live_row_universe_cubic,rsizes_rpders_norm17_rows_live_row_universe_cubic,raw_live_row_universe_not_closed_under_norm7 | Isabelle:Posix | Replace `card(sizeNregex N)` reasoning with a finite universe generated from subterms/continuations of the original non-backref regex; corrected live-row accounting is checked and inherits the path-universe cubic bound; remaining work is the normalized-root live-row one-step closure for `rpder_norm7_list` |
| BR-034 | Transfer cubic bound to annotated lexer states | 8,000 | 260 | 10 | 8,000 | OPEN | - | FBound.thy:asize_bp_der_norm_cubic,RL_rerase_bders_pder_norm,rpders_norm1_rows_rerase,annotated_size_bound_cubic_nonbackref | Isabelle:Posix | Final non-backref theorem for normalized row-list `bpders_norm1_rows`/future production `bsimp`; backref constructors explicitly excluded from the fragment |
| BR-036 | Close rsimp8/rsimp9 live-row cubic closure | 15,000 | 320 | 10 | 15,000 | OPEN | - | GeneralRegexBound.thy:rsimp8_live_row_universe_not_closed,norm18_closes_rsimp8_live_row_obstruction,rsimp8_live_row_universe_RNTIMES_not_closed,norm18_live_row_NTIMES_body_normalized_sanity,rsimp9,RL_rsimp9,rsize_rsimp9_le,rpder_norm9_list,rpder_norm9_rows,rpders_norm19_rows,RLS_rpders_norm19_rows,rpders_norm19_rows_rflts_subsetI,rsizes_rpders_norm19_rows_rsimp9_live_row_cubicI,rsizes_rpders_norm19_rows_rsimp9_path_cubicI,rflts_singleton_rsimp9_path_universe,rflts_map_rsimp9_path_subsetI,rflts_map_rsimp9_rpder_list_path_universe_subsetI,rflts_map_rsimp9_rpder_list_norm_tail_path_universe_subsetI,rpder_norm9_path_universe_step_RSEQ_pathI,rpder_norm9_path_universe_step_RSTAR_pathI,rpder_norm9_path_universe_step_RNTIMES_pathI,rpder_norm9_live_row_step_RSEQ_path_directI,rpder_norm9_live_row_step_RSTAR_path_directI,rpder_norm9_live_row_step_RNTIMES_path_directI,norm19_closes_RNTIMES_countdown_sanity,norm19_RNTIMES_body_normalization_obstruction_persists,norm19_RNTIMES_body_normalization_obstruction_in_path_universe,rpder_norm8_list,rpder_norm8_rows,rpders_norm18_rows,RLS_rpders_norm18_rows,rsizes_rpders_norm18_rows_rsimp8_live_row_cubicI | Isabelle:Posix | Current `norm17` closure is refuted by `(((1+a).a))*`; checked `norm18 = map rsimp8` repairs that obstruction but the plain target is refuted for `RNTIMES` because `rsimp8` does not recurse under repetition bodies. The proof-level `rsimp9` prototype recursively normalizes `RNTIMES` bodies, collapses zero-count repetitions to `RONE`, preserves language, does not increase `rsize`, closes the simple countdown shape, has checked norm19 live-row and path-universe cubic hooks, and now has checked live-row plus path-universe carried splitters. The checked body-normalization obstruction escapes live-row but lands in path-universe, so the next payout target is path-universe one-step closure before annotated `bsimp` transfer; non-backref fragment only |
| BR-037 | Transfer root-safe cubic theorem to annotated lexer | 10,000 | 260 | 10 | 10,000 | OPEN | - | FBound.thy:bpders_norm17_rows_rsimp8_rerase,annotated_size_bound_rsimp8_cubic_nonbackref;BlexerSimp.thy:production_bsimp_cubic_fragment | Isabelle:Posix | Connect the checked root-safe cubic theorem to the annotated `bsimp`/partial-derivative lexer path without wrapper-only restatements; backrefs excluded |

## Completed

| ID | Task | Bounty | Est. Lines | Difficulty | Est. USD | Status | Owner | Artifact | Verifier | Notes |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- | --- | --- |
| BR-001 | Language nullable/derivative pilot | 200 | 80 | 6 | 200 | DONE | Codex | BackRefLang.thy:BL_BBACKREF_empty,xnullable_correctness,xder_correctness,xders_correctness | Isabelle:BackRefPilot | PR #1, merged |
| BR-002 | Value/Prf/flat correspondence pilot | 160 | 60 | 6 | 160 | DONE | Codex | BackRefValues.thy:BL_flat_BPrf | Isabelle:BackRefPilot | `BackRefValues.thy`, build passes |
| BR-003 | Add `bmkeps` for pilot nullable values | 80 | 20 | 4 | 80 | DONE | Codex | BackRefValues.thy:bmkeps | Isabelle:BackRefPilot | `bmkeps` in `BackRefValues.thy` |
| BR-004 | Prove `bmkeps` flat/prf correctness | 120 | 30 | 5 | 120 | DONE | Codex | BackRefValues.thy:bmkeps_flat,bmkeps_BPrf | Isabelle:BackRefPilot | `bmkeps_flat`, `bmkeps_BPrf` |
| BR-005 | Draft `binjval` statement blueprint | 500 | 30 | 5 | 500 | DONE | Opus | BackRefValues.thy:binjval | Isabelle:BackRefPilot | Commit `b9da0e1` |
| BR-006 | Add guard scripts for bounty/role checks | 60 | 10 | 3 | 60 | DONE | Codex | agent_hunt_pipeline/scripts/backref_bounty_guard.py;agent_hunt_pipeline/scripts/backref_role_guard.py | LocalGuards | `backref_bounty_guard.py`, `backref_role_guard.py` |
| BR-007 | Generalized four-language backreference blueprint | 160 | 20 | 5 | 160 | DONE | Codex | BackRefLang.thy:backref_lang4,backref_lang_as_backref_lang4 | Isabelle:BackRefPilot | `backref_lang4`, `backref_lang_as_backref_lang4` |
| BR-008 | Draft derivative story for generalized `backref_lang4` | 800 | 60 | 6 | 800 | DONE | Codex | BackRefLang.thy:backref_lang4I,Der_backref_lang4 | Isabelle:BackRefPilot | Derivative splits prefix, capture-with-accumulator, and post-capture tail |
| BR-009 | Local and GitHub Isabelle CI with anti-cheat gate | 260 | 15 | 4 | 260 | DONE | Codex | agent_hunt_pipeline/scripts/isabelle_ci.ps1;agent_hunt_pipeline/scripts/backref_no_cheat_guard.py;agent_hunt_pipeline/scripts/write_ci_certificate.py;.github/workflows/isabelle.yml | Isabelle:Posix+BackRefPilot | CI certificate only after both sessions pass |
| BR-010 | Reproduce recurring tmux prompt loop | 90 | 10 | 3 | 90 | DONE | Codex | agent_hunt_pipeline/scripts/backref_idle_watch.sh;agent_hunt_pipeline/scripts/test_tmux_recurring_prompt.sh;agent_hunt_pipeline/WINDOWS_RUNBOOK.md | WSL:tmux-recurring-test | Same paper prompt injected repeatedly |
| BR-011 | Prove `bflat (binjval r c v) = c # bflat v` | 1,000 | 40 | 6 | 1,000 | DONE | Opus | BackRefValues.thy:binjval_flat | Isabelle:BackRefPilot | Commit `6dc8e03` |
| BR-012 | Prove `BPrf (binjval r c v) r` when `BPrf v (xder c r)` | 1,200 | 50 | 7 | 1,200 | DONE | Opus | BackRefValues.thy:binjval_BPrf | Isabelle:BackRefPilot | Commit `6dc8e03` |
| BR-013 | Define and prove `blexer` for pilot `brexp` | 1,500 | 80 | 7 | 1,500 | DONE | Opus | BackRefValues.thy:blexer,blexer_BPrf,blexer_flat,blexer_correct_None,blexer_correct_Some | Isabelle:BackRefPilot | Commit `2e8c45a` |
| BR-014 | Prove `blexer` correctness for pilot `brexp` | 2,000 | 100 | 8 | 2,000 | DONE | Opus | BackRefValues.thy:blexer_correctness,BPosix_binjval,blexer_POSIX,blexer_POSIX_iff | Isabelle:BackRefPilot | Cursor proof lane, Codex stabilization/build verification |
| BR-015 | POSIX value ordering for backreferences | 2,500 | 120 | 8 | 2,500 | DONE | Codex | BackRefValues.thy:BPosix_determ | Isabelle:BackRefPilot | Codex-B lane; uses `BSEQ_split_unique`, nullable empty-value uniqueness, and `BPosix_BBACKREF_value_unique` |
| BR-016 | Generalized `backref_lang4` value pilot | 1,500 | 70 | 7 | 1,500 | DONE | Codex | BackRefLang4Values.thy:bval4,bflat4,BPrf4,backref_lang4_flat_BPrf4,backref_lang_flat_BPrf4_special | Isabelle:BackRefPilot | Explicit value-evidence blueprint before datatype migration |
| BR-017 | Bitcoded backreference lexer definition | 2,500 | 100 | 8 | 2,500 | DONE | Codex | BackRefBlexer.thy:bbit,barexp,berase,bfuse,baintern,bbnullable,bbmkeps,bbder,bblexer | Isabelle:BackRefPilot | Separate pilot file; erase/nullable/derivative checks included |
| BR-018 | Bitcoded backreference lexer correctness | 3,000 | 150 | 9 | 3,000 | DONE | Codex | BackRefBlexer.thy:bbder_bretrieve,bblexer_blexer_retrieve | Isabelle:BackRefPilot | Derivative retrieval transport plus bitcoded output matches `bretrieve (baintern r)` of `blexer` value |
| BR-019 | Bounded fragment theorem for backreferences | 4,000 | 200 | 9 | 4,000 | DONE | Codex | BackRefBoundedBlueprint.thy:BL_bound_BBACKREF_derivative_family_card_bound,GBL_bound_GBACKREF4_derivative_family_card_bound | Isabelle:BackRefPilot | Constructor-specific bounded-fragment derivative families land in finite bounded-string universes with explicit cardinal bounds |
| BR-020 | Simplification rules for backreference lexer | 2,000 | 90 | 7 | 2,000 | DONE | Codex | BackRefBlexer.thy:bbsimp,bblexer_simp_correctness,bblexer_step_simp_correctness | Isabelle:BackRefPilot | Post-derivative and per-step simplified loops preserve `bblexer` |
| BR-021 | Cursor/Opus loop startup kit | 140 | 15 | 4 | 140 | DONE | Codex | .cursor/hooks/posix_loop.ps1;.cursor/hooks/posix_loop.sh;agent_hunt_pipeline/projects/posix-backref/loop-config.cursor-opus.json;agent_hunt_pipeline/projects/posix-backref/SLEEP_RUNBOOK.md | CursorHook:posix-loop | Supplemental robust hook and sleep runbook |
| BR-022 | Bounded-fragment statement blueprint | 1,200 | 60 | 7 | 1,200 | DONE | Codex | BackRefBoundedBlueprint.thy:bounded_GBACKREF4_finite_derivative_languages | Isabelle:BackRefPilot | Semantic bounded-language blueprint for finite derivative-language families; no production bounds or closed forms touched |
| BR-032 | Define stronger cubic-bound simplifier | 25,000 | 260 | 10 | 25,000 | DONE | Codex | BasicIdentities.thy:rsimp7_SEQ_atom,rsimp7_SEQ,rsimp7,RL_rsimp7;BlexerSimp.thy:bsimp7_ASEQ_atom,bsimp7_ASEQ,bsimp7,bpder_norm7_list,bp_der_norm7,bpder_norm7_rows;GeneralRegexBound.thy:rpder_norm7_list,rpd_der_norm7,rpder_norm7_rows,rpders_norm17_rows,RLS_rpders_norm17_rows,RL_rders_pder_norm7;FBound.thy:bsimp7_rerase,bp_der_norm7_rerase,rpders_norm17_rows_rerase,RL_rerase_bders_pder_norm7 | Isabelle:Posix | Checked `rsimp7`/`bsimp7` adds prefix star absorption `r*.(r*.k)=r*.k` over Antimirov row lists; final repeated-row cubic closure remains BR-033 |
| BR-035 | Define root-safe cubic simplifier | 25,000 | 260 | 10 | 25,000 | DONE | Codex | BasicIdentities.thy:rsimp8,rders_simp8,RL_rsimp8,RL_rders_simp8;BlexerSimp.thy:bsimp8,bders_simp8;FBound.thy:bsimp8_rerase,rders_simp8_size,RL_rerase_bders_simp8;GeneralRegexBound.thy:rsize_rsimp8_le,rsizes_rpders_norm17_rows_rsimp8_live_row_cubicI | Isabelle:Posix | New 50k cubic tranche: checked root normalizer preserves language and erasure while avoiding `rsimp7` root-size blow-up; conditional cubic interface is w.r.t. original `rsize r` |

## Effort Estimate Key

Every bounty must include an effort estimate before it can be locked:

- **Est. Lines**: approximate lines of a textbook proof for this result.
- **Difficulty**: formalization difficulty on a 1-10 scale (1 = trivial, 10 = research-level).
- **Est. USD**: approximate cost assuming $100/hour of expert Isabelle work.

Estimates assume all previous results in the dependency chain are already proved.

## Locks

| Lock ID | Task ID | Agent | Deposit | Branch | Expires UTC | Status |
| --- | --- | --- | ---: | --- | --- | --- |
| - | - | - | 0 | - | - | RELEASED |
| L-OPUS-015 | BR-015 | Opus | 250 | codex/backref-values | 2026-05-27T07:38:41Z | RELEASED |
| L-CODEX-B-015 | BR-015 | Codex | 250 | codex/backref-values | 2026-05-27T15:44:00Z | COLLECTED |
| L-CODEX-A-022 | BR-022 | Codex | 120 | codex/backref-values | 2026-05-27T15:44:01Z | COLLECTED |
| L-CODEX-017 | BR-017 | Codex | 250 | codex/backref-values | 2026-05-27T09:35:51Z | COLLECTED |
| L-CODEX-A-019 | BR-019 | Codex | 400 | codex/backref-values | 2026-05-27T18:46:17Z | COLLECTED |

## Lock Rules

- Lock deposit: 10% of bounty, rounded up.
- Maximum **10** active locks per agent.
- Locks expire after **24 hours**.
- Push locks immediately if multiple agents are active.
- Lock-or-lose: if someone else proves a locked theorem, bounty goes to locker.
- A lock does not authorize statement changes.
- Admin can clear stale locks.
- Expired lock deposit is forfeited (not refunded).

## Ledger

| Time UTC | Agent | Action | Task ID | Amount | Balance After | Notes |
| --- | --- | --- | --- | ---: | ---: | --- |
| 2026-05-22T14:00:00Z | Codex | COLLECT | BR-001 | 200 | 200 | Language nullable/derivative pilot merged in PR #1 |
| 2026-05-22T14:20:00Z | Codex | COLLECT | BR-002 | 160 | 360 | Value/Prf/flat correspondence |
| 2026-05-22T14:28:00Z | Codex | COLLECT | BR-003 | 80 | 440 | `bmkeps` definition |
| 2026-05-22T14:28:00Z | Codex | COLLECT | BR-004 | 120 | 560 | `bmkeps` flat and Prf correctness |
| 2026-05-25T16:24:31Z | Opus | COLLECT | BR-005 | 500 | 500 | `binjval` definition |
| 2026-05-24T02:58:00Z | Codex | COLLECT | BR-006 | 60 | 620 | Bounty and role guard scripts |
| 2026-05-24T02:58:00Z | Codex | COLLECT | BR-007 | 160 | 780 | Generalized `backref_lang4` blueprint |
| 2026-05-25T03:40:00Z | Codex | COLLECT | BR-009 | 260 | 1,040 | Local and remote Isabelle CI gates |
| 2026-05-25T04:22:00Z | Codex | COLLECT | BR-010 | 90 | 1,130 | Recurring tmux prompt reproduction |
| 2026-05-25T15:24:00Z | Codex | COLLECT | BR-021 | 140 | 1,270 | Cursor/Opus loop startup kit |
| 2026-05-25T23:24:27Z | Opus | COLLECT | BR-011 | 1,000 | 1,500 | `binjval_flat` |
| 2026-05-25T23:24:27Z | Opus | COLLECT | BR-012 | 1,200 | 2,700 | `binjval_BPrf` |
| 2026-05-25T23:37:17Z | Opus | COLLECT | BR-013 | 1,500 | 4,200 | pilot `blexer` definition and language correctness |
| 2026-05-26T03:58:00Z | Opus | COLLECT | BR-014 | 2,000 | 6,200 | `blexer_correctness`, `BPosix_binjval`, `blexer_POSIX`, `blexer_POSIX_iff`; Codex stabilized build |
| 2026-05-26T07:38:41Z | Opus | LOCK | BR-015 | 250 | 5,950 | Lock L-OPUS-015 for POSIX value ordering / `BPosix_determ` |
| 2026-05-26T09:15:17Z | Codex | COLLECT | BR-008 | 800 | 2,070 | `backref_lang4I`, `Der_backref_lang4`; BackRefPilot passed |
| 2026-05-26T09:35:51Z | Codex | LOCK | BR-017 | 250 | 1,820 | Lock L-CODEX-017 for bitcoded backreference lexer definitions |
| 2026-05-26T09:42:18Z | Codex | COLLECT | BR-017 | 2,500 | 4,320 | `BackRefBlexer.thy` definitions plus erase/nullable/derivative checks; BackRefPilot passed |
| 2026-05-26T10:57:17Z | Codex | COLLECT | BR-018 | 3,000 | 7,320 | `bbder_bretrieve`, `bblexer_blexer_retrieve`; BackRefPilot passed |
| 2026-05-26T11:46:37Z | Codex | COLLECT | BR-020 | 2,000 | 9,320 | `bblexer_simp_correctness` and per-step `bblexer_step_simp_correctness`; BackRefPilot passed |
| 2026-05-26T11:57:08Z | Codex | COLLECT | BR-016 | 1,500 | 10,820 | `backref_lang4_flat_BPrf4`; BackRefPilot passed |
| 2026-05-26T15:43:53Z | Opus | RELEASE | BR-015 | 250 | 6,200 | Cursor/Opus retired because reconnect stalls made overnight work unreliable |
| 2026-05-26T15:44:00Z | Codex | LOCK | BR-015 | 250 | 10,570 | Codex-B takes over POSIX value ordering |
| 2026-05-26T15:44:01Z | Codex | LOCK | BR-022 | 120 | 10,450 | Codex-A takes non-conflicting bounded-fragment statement blueprint lane |
| 2026-05-26T16:06:05Z | Codex | COLLECT | BR-022 | 1,200 | 11,650 | `BackRefBoundedBlueprint.thy` semantic bounded-language finite derivative blueprint; BackRefPilot passed |
| 2026-05-26T18:16:47Z | Codex | COLLECT | BR-015 | 2,500 | 14,150 | `BackRefValues.thy:BPosix_determ`; BackRefPilot passed |
| 2026-05-26T18:46:17Z | Codex | LOCK | BR-019 | 400 | 13,750 | Codex-A locks bounded-fragment theorem packaging |
| 2026-05-26T18:46:18Z | Codex | COLLECT | BR-019 | 4,000 | 17,750 | `BackRefBoundedBlueprint.thy` constructor-specific derivative-family universe/card bounds; BackRefPilot passed |
| 2026-05-31T02:35:36Z | Codex | COLLECT | BR-032 | 25,000 | 42,750 | `rsimp7`/`bsimp7` prefix-star absorption definitions plus norm7 row drivers and erasure/language transfer; Posix and BackRefPilot passed |
| 2026-05-31T03:57:03Z | Codex | COLLECT | BR-035 | 25,000 | 67,750 | `rsimp8`/`bsimp8` root-safe simplifier, erasure/language bridge, size non-increase, and original-size conditional cubic interface; Posix and BackRefPilot passed |

## Sub-Bounty Rules

An agent may offer a sub-bounty from their own balance to request help:

1. Create a new task in Active with `Sub-bounty of BR-XXX` in Notes.
2. Record a `SUB_OFFER` ledger entry deducting from the offering agent.
3. Sub-bounty follows normal completion and guard rules.
4. Cancellation: `SUB_CANCEL` entry refunds the offering agent.

## Early-Finish Bonus

If the entire allocated bounty board is completed before the admin-set
deadline, 10% of the remaining unallocated pool is distributed equally among
agents who completed at least one bounty.

Run the full local CI before collecting or pushing:

```powershell
powershell -ExecutionPolicy Bypass -File agent_hunt_pipeline/scripts/isabelle_ci.ps1 -SkipFetch -Role admin
```
