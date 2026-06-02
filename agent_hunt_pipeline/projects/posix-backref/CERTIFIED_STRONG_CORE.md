# Certified Strong-Core Route

Last updated: 2026-06-02

This note is the proof-facing bridge from the Scala smoke prototype toward an
Isabelle candidate for the non-backref cubic-size route. It records the semantic
object that should be proved, not a bounty claim.

## Candidate Object

The executable candidate is the certified strong core currently implemented in
`agent_hunt_pipeline/scala/PosixCubicSmoke.scala`:

- `bsimpStrongCoreCert r = (r', recon)` returns a simplified annotated regex and
  a reconstruction function from epsilon values of `r'` back to epsilon values
  of `r`.
- `strongCoreCertifiedValue r s` iterates over the input and composes:
  `bder`, `bsimpStrongCoreCert`, `injectA`, and the accumulated continuation.
- The final continuation maps the final simplified epsilon value back to the
  original POSIX value.

The current Scala smoke gate is:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File agent_hunt_pipeline\scripts\scala_cubic_smoke.ps1 `
  -SeqMode expanded-keyed-no-reassoc `
  -CheckStrongCoreCert `
  -CheckStrongCoreLoop `
  -RandomCases 3000 `
  -RandomDepth 5 `
  -RandomInputLength 6 `
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

The executable Scala `LoopValueCert(regex, recon)` is evidence for this shape,
but Isabelle should replace `recon` with an inductive relation over certificate
constructors.

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

## Current Size Evidence

For the Chapter 7 k=5 family and lengths `0,4,8,12,16,20,24,30`, the certified
strong core trace is:

```text
46,438,618,612,612,632,579,678
```

This is below the thesis `bsimpStrong` trace at n=30 (`958`) and below the
previous uncertified/unsafe route's practical target on this smoke. It is
evidence that the certificate route can preserve the desired tree-size behavior.

The loop-level size summary on the same family is:

```text
n=0  final=46  maxRaw=46    maxCore=46
n=4  final=438 maxRaw=807   maxCore=438
n=8  final=618 maxRaw=1302  maxCore=618
n=12 final=612 maxRaw=1429  maxCore=721
n=16 final=612 maxRaw=1429  maxCore=721
n=20 final=632 maxRaw=1429  maxCore=721
n=24 final=579 maxRaw=1429  maxCore=721
n=30 final=678 maxRaw=1434  maxCore=721
```

This suggests the proof should bound every simplified loop state, not just the
final state. The raw derivative can be temporarily larger, but the certified
core quickly returns to a stable frontier.

## Next Proof Tasks

1. Define a small certificate datatype or inductive relation in Isabelle.
2. Define an Isabelle relation corresponding to `injectA`.
3. State and prove `cert_recon` soundness for each constructor.
4. State and prove the derivative-loop invariant using `injectA`.
5. Only after those pass, connect the size trace to a proof-facing row-universe
   or cubic frontier argument.
