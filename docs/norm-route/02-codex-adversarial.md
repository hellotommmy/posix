# 02-codex — Option 3 S-form opening shadow lane

## Plain target

Route 2 still needs a linear old-frontier count:

```text
card(apder_strong_dlfrontier r) <= C * rsize r + D
```

Any fixed linear `C,D` suffices because the existing green row-level gate already has a
quadratic per-row size bound; linear count times quadratic row size is cubic. A quadratic
count would make the gate quartic.

## Claim L status

Claim L, the proposed single-bit injection, is refuted. In the family

```text
r_1 = (a.b*) + a
r_d = (r_{d-1}.b*) + a
k = b*
```

the non-normal old rows in one `N`-fiber have multiplicity `d`. The single bit and any
fixed per-`N`-value tag collide. What survives is only the weaker observation that total
cardinality on this family is still linear; a per-occurrence/depth tag is not refuted.

## Chosen obligation

I am taking option 3: the route-agnostic S-form opening shadow

```text
x in row_dlforms(S q) ==> N x in ndlforms(N q)
```

where `S = rsimpStrong_raw` and `N = nstrong`.

## Hand-analysis before formalization

The natural induction is over the shape opened by `row_dlforms(S q)`. The fragile step is
not ordinary top-level alternation: it is the old plug inside `row_dlforms`, namely
`rsimp7_SEQ_atom`, which collapses only a leading `a* . a*`. To make the S-form shadow
natural, every old σ7 plug must become the normalized associative append after applying
`N`:

```text
N(rsimp7_SEQ_atom r k) = nplug(N r, N k)
```

The only non-fallback cases are exactly the two σ7 star triggers: `r*` with `r*`, and
`r*` with `r* . k`. Both reduce to the normalized-star absorb law for `nplug`.

## Break attempts

The raw shadow

```text
x in row_dlforms(q) ==> N x in ndlforms(N q)
```

is false: `q = 0*.(a+b)` leaves the raw old row whole while `N q = a+b` and `ndlforms`
splits it. This does not kill the S-form target because the old universe opens `S q`,
not raw `q`.

The usual `a* . a*` boundary is exactly handled by the proved σ7 shadow brick. The Claim L
family refutes bit provenance but does not touch this local σ7-to-α equality.

## Checked brick

Green in `NormalizedStrong.thy`:

```text
N(rsimp7_SEQ_atom r k) = nplug(N r, N k)
```

Plain gloss: strong plug normalizes like associative append.

Build:

```text
cubic/Normalized/build-norm.ps1 -Session Posix_Norm
```

Result: green.
