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
2. Prove/check the language bridge for `bdersStrong` first:
   `nullable (bdersStrong (intern r) s)` should agree with `s \<in> lang r`.
3. Define a proof-facing deferred reconstruction relation, for example:
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
