# Certified Strong-Core Route

Last updated: 2026-06-02

This note is the proof-facing bridge from the Scala smoke prototype toward an
Isabelle candidate for the non-backref cubic-size route. It records the semantic
object that should be proved, not a bounty claim.

## Candidate Objects

The historical direct-core candidate in
`agent_hunt_pipeline/scala/PosixCubicSmoke.scala` is:

- `bsimpStrongCoreCert r = (r', recon)` returns a simplified annotated regex and
  a reconstruction function from epsilon values of `r'` back to epsilon values
  of `r`.
- `strongCoreCertifiedValue r s` iterates over the input and composes:
  `bder`, `bsimpStrongCoreCert`, `injectA`, and the accumulated continuation.
- The final continuation maps the final simplified epsilon value back to the
  original POSIX value.

CE-driven smoke shows that this direct-core candidate is not strong enough for
nullable-star future derivatives.

The current positive candidate is the deferred/generalized route:

- `bdersStrong (intern r) s` is the small acceptance state.
- If that state is nullable, exact POSIX value reconstruction is deferred to a
  relation over the original regex and consumed string.
- The Scala reference implementation is `strongDeferredValue`.
- The Isabelle acceptance bridge is now checked in `FBound.thy`:
  `bnullable_bders_simpStrong_iff_Ders` and
  `bnullable_bders_simpStrong_iff_member`.
- The bridge to the original POSIX value relation is also checked:
  `bnullable_bders_simpStrong_intern_iff_Posix`,
  `bnullable_bders_simpStrong_intern_iff_lexer_defined`,
  `bnullable_bders_simpStrong_intern_obtain_lexer`, and
  `bnullable_bders_simpStrong_intern_unique_Posix`.
  The current theorem-level fallback says: when the small strong state is
  nullable, `lexer r s` supplies the unique original POSIX value.

The current positive Scala smoke gate is:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 `
  -SkipLegacyCubic `
  -CheckStrongDeferred `
  -RandomCases 50000 `
  -RandomDepth 7 `
  -RandomInputLength 8 `
  -Ch7TreeThreshold 1000000
```

It also passes the default exhaustive depth `2`, input length `3` grid with
`84,300` regex/input pairs.

The fallback-free memoized reconstruction smoke gate is:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 `
  -SkipLegacyCubic `
  -CheckStrongDeferredMemo `
  -RandomCases 10000 `
  -RandomDepth 6 `
  -RandomInputLength 7 `
  -Ch7TreeThreshold 1000000
```

`strongDeferredMemoValue` uses the same full `bdersStrong` nullable gate, then
calls `posixMemoValue` to reconstruct the original POSIX value from
`(r, s)` by span dynamic programming. This is now the preferred executable
prototype over `strongDeferredValue`, whose `baselineValue` fallback still runs
the derivative lexer.

The memoized reconstruction table-size trace is:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 `
  -SkipLegacyCubic `
  -TraceStrongDeferredMemo `
  -Ch7K 5 `
  -Ch7Lengths "0,4,8,12,16,20,24,30" `
  -Ch7TreeThreshold 1000000
```

Observed checkpoints:

- k=5, n=30: strong tree `958`, accepts states `1577`, value states `126`,
  split probes `6011`, span bound `44206`, split bound `1370386`.
- k=8, n=48: strong tree `2963`, accepts states `3818`, value states `198`,
  split probes `22145`, span bound `232897`, split bound `11411953`.

This suggests the reconstruction proof should talk about a span-indexed parser
universe, not about decoding ordinary values from the final simplified regex.
The current smoke enforces accepts/value states below
`rsize(r) * (|s| + 1)^2` and split probes below
`rsize(r) * (|s| + 1)^3`. These are intentionally about the value
reconstruction layer; the separate derivative-state proof still needs the
regex-size cubic frontier argument.

The first checked Isabelle support for this route is now in
`GeneralRegexBound.thy`:

- `rspan_states r s` and `finite_rspan_states`;
- `rspan_statesI` / `rspan_statesE`;
- `card_rspan_states_bound`;
- `card_subset_rspan_states_bound`;
- `rspan_split_probes r s` and `finite_rspan_split_probes`;
- `rspan_split_probesI` / `rspan_split_probesE`;
- `card_rspan_split_probes_bound`;
- `card_subset_rspan_split_probes_bound`.

The next proof-facing reconstruction relation should prove that its memo table
and split-probe set are subsets of these universes. This gives the same
accounting discipline as the Scala `posixMemoValue` smoke without committing
to direct value decoding from the simplified derivative state.

The next checked layer has also been started:

- `rslice s i j`;
- `rspan_accepts r s`, a language-membership specification for acceptance memo
  entries;
- `rspan_accepts_subset_rspan_states`;
- `card_rspan_accepts_bound`;
- `rspan_all_split_probes r s`, a legal-split specification for split probes;
- `rspan_all_split_probes_subset`;
- `card_rspan_all_split_probes_bound`.

Future reconstruction correctness can now be phrased against these table
specifications rather than against raw finite universes.

The table-correctness algebra has started as well:

- `rslice_0_length`;
- `rslice_same`;
- `length_rslice`;
- `rslice_append`;
- `rspan_accepts_iff`;
- `rspan_accepts_root_iff`;
- `rspan_all_split_probes_iff`;
- `rspan_accepts_RSEQI`;
- `rspan_accepts_RSTAR_emptyI`.

These facts are deliberately one-directional where that keeps the proof light:
they support constructing accepted table entries from legal split evidence.
The converse/extraction lemmas for longest-left POSIX reconstruction are still
future work.

The new CE-driven direct-decode guard is:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 `
  -SkipLegacyCubic `
  -FindStrongDirectCE `
  -RandomCases 5000 `
  -RandomDepth 6 `
  -RandomInputLength 7
```

It currently shrinks to `STAR(STAR(CH(b)))` on input `b`, which proves that
directly decoding ordinary values from the final `bsimpStrong` state is not the
right semantic object. This is intentional negative evidence for the deferred
route.

## Full Strong Tree Experiment

There is now a second experimental route, `StrongFullCert`, whose purpose is to
test the user's preferred goal: keep the `bsimpStrong` tree-size behavior and
recover exact POSIX values by certificate reconstruction.

Useful smoke commands:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 `
  -SkipLegacyCubic `
  -CheckStrongFullLoop `
  -FindStrongFullCE `
  -TraceStrongFullLoop `
  -RandomCases 10000 `
  -RandomDepth 6 `
  -RandomInputLength 7 `
  -Ch7K 5 `
  -Ch7Lengths "0,4,8,12,16,20,24,30"
```

Current positive evidence:

- exhaustive depth `2`, input length `3`: `84,300` pairs pass;
- random depth `6`, input length `7`, seed `20260602`: `10,000` cases pass;
- Chapter 7 `k=5` max full-certificate state is `721`.

Current negative evidence:

- random depth `7`, input length `8`, seed `20260602`, case `622` shrinks to
  `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on input `bba`;
- the exact POSIX value is
  `Seq(Stars [Left (Stars [b]), Right (Seq b a)], Stars [])`;
- the current full certificate returns
  `Seq(Stars [Left (Stars [b,b])], Stars [a])`.

This is a left-greedy sequence boundary CE: the right `STAR(a)` receives a
character that POSIX assigns to the left star. Therefore `StrongFullCert` is a
CE-mining and design tool, not a theorem target or bounty candidate yet.

## Isabelle Invariant Shape

The proof-facing relation should avoid Scala-style function closures. A useful
Isabelle shape is a relation, not a function:

```isabelle
cert_recon r r' v' v
```

Read this as: value `v'` decoded from the simplified regex `r'` reconstructs to
value `v` for the original regex `r`.

The expected one-step simplification theorem is:

```isabelle
bsimpStrongCoreCert r = (r', cert) ==>
  nullable r' ==>
  decode_eps r' (bmkeps r') = Some v' ==>
  cert_recon r r' v' v ==>
  decode_eps r (bmkeps r) = Some v
```

For the derivative loop, the key invariant should be:

```isabelle
loop_cert r0 s r k ==>
  nullable r ==>
  decode_eps r (bmkeps r) = Some v' ==>
  k v' = Some v ==>
  s \<in> lang r0 /\ posix_value r0 s v
```

The executable Scala `LoopValueCert(regex, recon)` is only route evidence for
this shape. CE-driven smoke now shows that local `Val => Option[Val]`
reconstruction is not enough when nullable expressions are simplified and then
used for future derivatives. Isabelle should therefore not commit to this
closure shape until the certificate relation carries enough history for
nullable-star segmentation, or until the simplifier is restricted to a fragment
where the derivative-state theorem is true.

## Certificate Constructors Needed

The current Scala prototype uses the following logical constructors:

- identity
- left/right/nested alternative choice reconstruction
- alternation flattening with original row index
- `distinctWith` row deletion under POSIX priority
- contextual shared-suffix row pruning in an outer `AALTs`
- sequence reassociation
- right unit deletion, including nonempty bit payload handling
- zero propagation
- nested-star collapse
- star absorption
- star-zero collapse
- derivative injection `injectA`
- loop-step composition

Important: shared-suffix pruning is contextual. A deleted later row is not a
standalone equivalent regex. It is justified only because an earlier outer
alternative with the same suffix has POSIX priority and captures the value.

## CE-Driven Status

The earlier full strong-core trace kept the desired small tree:

```text
46,438,618,612,612,632,579,678
```

That trace is now classified as unsafe for exact POSIX values. Counterexamples
show that future derivatives over the simplified state can change POSIX
segmentation even when a local reconstruction function repairs the current
epsilon value.

Important CEs:

- `SEQ(STAR(ALT(STAR(b), SEQ(b,a))), STAR(a))` on `bba`
- `STAR(STAR(ALT(SEQ(STAR(a), ONE), b)))` on `bab`
- deterministic random seed `20260602`, depth `6`, input length `7`, case
  `1355`, involving nullable `NTIMES(ONE,3)` and `STAR(STAR(ZERO))`

The current side-conditioned core avoids nullable unit deletion,
nullable-left reassociation, and nullable-body star absorption/collapse. It
passes the hand CE grid but still fails broader random exact-value smoke.

Its size trace is worse:

```text
k=5 lengths 0,4,8,12,16,20,24,30:
46,901,2241,2988,3305,3317,3443,3674

k=8 lengths 0,4,8,16,32:
97,2209,5789,12145,18473
```

Disabling AALTs pruning/dedup entirely caused an OOM on the k=5 trace, so the
size route still needs pruning. The open problem is to make pruning carry enough
history/payload to preserve future POSIX choices.

## Next Proof Tasks

1. Treat `strongDeferredValue` as the current positive route:
   `bdersStrong` supplies a small acceptance state, while exact POSIX values
   are reconstructed from the original regex and consumed string.
2. Continue from the checked language bridge for `bdersStrong`:
   `bnullable (bders_simpStrong r s)` agrees with `s \<in> RL (rerase r)`.
3. Refine the checked fallback bridge
   `bnullable_bders_simpStrong_intern_obtain_lexer` into an efficient
   proof-facing deferred reconstruction relation, for example
   `deferred_posix r s v`, rather than trying to decode ordinary POSIX values
   directly from the simplified derivative.
4. Keep comparing two implementation routes:
   - smart/certified pruning with payload/history keys;
   - generalized POSIX values that can reconstruct equivalent nullable-star
     segmentations.
5. Only after that relation is stable, connect the size trace to a
   proof-facing row-universe or cubic frontier argument.

Current positive Scala evidence for the deferred route:

- exhaustive depth `2`, input length `3`: `84,300` pairs pass;
- deterministic random depth `7`, input length `8`: `50,000` cases pass with
  seed `20260602`;
- Chapter 7 `bsimpStrong` traces remain thesis-scale:
  `k=5`, n=30 -> `958`; `k=8`, n=48 -> `2963`.
