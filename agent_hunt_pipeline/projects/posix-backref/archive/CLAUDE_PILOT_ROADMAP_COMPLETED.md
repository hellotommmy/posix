# CLAUDE.md backref pilot roadmap (COMPLETED), archived 2026-06-12

Verbatim text excised from agent_hunt_pipeline/projects/posix-backref/CLAUDE.md
by the secretary session. All four phases of this roadmap are complete and the
BR-001..BR-022 bounties are paid; the chain is checked and frozen (theorem
list in MAINLINE.md section 5). Kept for provenance only. Nothing below was
edited.

---
## Technical Roadmap

The work is organized into four phases. Each phase has a clear dependency on
the previous one. Agents should not jump ahead.

### Phase 1: Complete backref_lang (simple version)

The simple backreference `backref_lang A B cs` models `(r1)r2\1`, i.e. the
captured group `r1` is repeated verbatim, with `r2` as the middle expression
and no surrounding context beyond the capture.

**1a. Define `binjval` for brexp (BR-005)**

The injection value function reconstructs a value for the original regex from
a value for the character derivative. Follow the pattern of `injval` in
`Lexer.thy` but extended for `BBACKREF`, `BHALF`, `BRESIDUE`. The definition
must satisfy:

```isabelle
bflat (binjval r c v) = c # bflat v    (* when BPrf v (xder c r) *)
BPrf (binjval r c v) r                 (* when BPrf v (xder c r) *)
```

Study `xder` carefully: each `xder` case produces certain value shapes, and
`binjval` must invert them. For the `BBACKREF` nullable case, `xder` produces
an `BALT` with a `BBACKREF` branch and a `BHALF`/`BRESIDUE` branch; `binjval`
must unwrap accordingly.

**1b. Prove `bflat (binjval r c v) = c # bflat v` (BR-011)**

Induction on `r` with `c` and `v` universally quantified. Each case follows
from the `xder` definition and `BPrf` elimination. The backreference cases
will need careful case analysis matching the `xder` branching.

**1c. Prove `BPrf (binjval r c v) r` (BR-012)**

Same induction structure. This is the value-level correctness of injection.

**1d. Define bitcoded lexer for brexp**

This is recommended as the **primary implementation path** because the Scala
reference implementation (`backRef.sc`) already exists and is tested. The key
definitions to formalize from `backRef.sc`:

- Extend `arexp` datatype with `ABACKREF`, `AHALF`, `ARESIDUE` constructors
  (each carrying `bit list`).
- Extend `fuse`, `intern`, `erase`, `bnullable`, `bmkeps`, `bder`/`bder_simp`
  for the new constructors.
- The `bder` for `ABACKREF` follows the branching in `bder_bsimp_rev` from
  `backRef.sc`. Key insight: when the captured group is nullable, `bder`
  produces an `AALTS` with a `ABACKREF` branch (continuing to derive the
  capture) and a `AHALF` branch (transitioning to replay phase).
- `bmkeps` for `ABACKREF` emits a `Backbit(cs)` marker encoding the captured
  string.

Reference: `backRef.sc` lines 148-553 contain the full Scala implementation.

**Important**: the bitcoded lexer work should go into new sections of
`BackRefValues.thy` or a new theory file `BackRefBlexer.thy` (discuss with
admin). Do NOT modify `Blexer.thy` or `BlexerSimp.thy` during this phase.

**1e. Define `blexer` for brexp and prove correctness (BR-013, BR-014)**

Once `binjval` is defined, the lexer function follows mechanically:

```isabelle
blexer r [] = (if xnullable r then Some (bmkeps r) else None)
blexer r (c#s) = map_option (binjval r c) (blexer (xder c r) s)
```

Correctness: `blexer r s = lexer r s` (where `lexer` is the specification
lexer using `binjval`).

**1f. BlexerSimp for brexp: `blexer ≡ blexer_simp`**

Prove that the simplified bitcoded lexer produces the same result as the
unsimplified one for `brexp`. This requires extending `bsimp`, `bder_simp`,
and the `flts`/`distinctBy` simplification lemmas for the new constructors.
The proof follows `BlexerSimp.thy` structure.

**1g. (Optional, hard) ClosedFormsBounds for brexp (BR-019)**

The size of `xder`-derivatives for backreferences may not be bounded in the
same way as standard regex. This requires careful analysis and may reveal that
backreferences break the finite-derivative property. Record findings in
`PROGRESS_BACKREF.md` even if the result is negative.

### Phase 2: Generalized backref_lang4

The generalized `backref_lang4 L1 L2 L3 L4 cs` models `r1(r2)r3\1r4`, i.e.
the captured group `r2` appears between prefix context `r1` and suffix context
`r3`, then is replayed, followed by tail context `r4`.

**2a. Define new constructors**

Add `BBACKREF4`, `BHALF4`, `BRESIDUE4` (or extend existing constructors with
additional fields) to `brexp`. Define `BL`, `xnullable`, `xder` for them.

The current `backref_lang` is a special case:

```isabelle
backref_lang A B cs = backref_lang4 {[]} A B {[]} cs
```

**2b. Prove xnullable/xder correctness for new constructors**

Follow the same structure as `BackRefLang.thy`.

**2c. Define value/Prf/flat for new constructors**

Extend `bval`, `bflat`, `BPrf` for the generalized case.

**2d. Repeat Phase 1 steps for backref4**

Define `binjval`, prove flat/Prf correctness, define bitcoded lexer,
prove BlexerSimp equivalence -- all for the generalized constructors.

### Phase 3: injval definition (collaborative)

Defining `injval` for backreferences is the hardest open problem because the
derivative structure creates non-trivial value shapes. The recommended
approach:

1. Study the `xder` cases exhaustively and enumerate all possible output
   shapes for each constructor.
2. Define `binjval` case-by-case, matching each `xder` output shape.
3. Prove flat correctness first (easier), then Prf correctness.
4. If a case seems impossible, record the blocker -- it may indicate a
   semantic issue requiring admin intervention.

### Phase 4: Full integration

Once all pieces are in place:

1. Prove the full correctness chain: `lexer ≡ blexer ≡ blexer_simp` for
   `brexp` including all backreference constructors.
2. Integrate with the existing POSIX lexer story.
3. Address bounds questions.

### Concurrent Agent Task Division

When two agents work concurrently:

- **Agent A** (e.g., Opus): Work on `binjval` definition and correctness
  proofs (BR-005, BR-011, BR-012). This is the value-theoretic path.
- **Agent B** (e.g., GPT-5.5): Work on bitcoded lexer definitions for brexp,
  referencing `backRef.sc`. This is the implementation path. Use a new theory
  file `BackRefBlexer.thy` to avoid conflicts with Agent A's edits to
  `BackRefValues.thy`.

Both agents must pull/rebase frequently and push locks immediately.

## Dependency Awareness

The dependency direction is:

1. `RegLangs.thy`
2. `BackRefLang.thy`
3. `BackRefValues.thy` (value/Prf/flat + injval)
4. `BackRefBlexer.thy` (bitcoded lexer for brexp, new)
5. future BlexerSimp for brexp
6. future bounds or bounded-fragment theorems

Do not jump down this chain before the previous layer is checked.

