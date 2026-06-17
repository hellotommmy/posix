"""CANONICAL witness generator + falsity regression guard for the per-step drain budgets.

WHY THIS FILE EXISTS
--------------------
Two "machine-validated TRUE, 0-violation > 10^5 samples" claims were SAMPLING ARTIFACTS:

  (T1)  rsize_set(strong_child_drain p k) <= ctx_bound(drain_ctxs p) k        [the TIGHT ledger]
  (T2)  rsize_set(strong_child_drain p k) <= drain_child_budget p k           [the LOOSE budget = child_ok]

Both are FALSE in-regime (S p = p, S k = k, clean, depth>=5).  `rand_clean` essentially never
builds the killer structure, so flat 20k-40k gates reported 0 violations and the bounds were
believed true.  The killer is a nested-SEQ chain opened at a star continuation:

    SEQ(ALTS[pre,1], ... SEQ(ALTS[pre,1], SEQ(atom, star*)))   opened at  k = star*

each frame re-doubles  star* -> star*.star*, stacking uncollapsed S-shadow rows multiplicatively.

USE THIS MODULE in EVERY future sampling gate touching strong_child_drain / drain budgets.
A `rand_clean`-only gate is no longer acceptable (STEER.md methodology fix, 2026-06-16).

  from witness_gen import witness_family, mixed_samples, NAMED_CES, target_false, gate_report
  # gate_report(...) replaces the old homegrown "G2 must be 0" loop.

Named confirmed CEs (all in-regime, clean, S-fixed, depth>=5):
  CE2  rsize19 RALTS : 47 > ctx_bound 46  (drain_child_budget 60 holds)
  CE1  rsize18       : 64 > ctx_bound 60  (drain_child_budget 74 holds)
  CHILDOK rsize22    : 99 > ctx_bound AND 99 > drain_child_budget 96   (kills BOTH)

DECISION (2026-06-16): NEITHER T1 nor T2 is a viable cubic target.  drain_child_budget is NOT
proven (child_okD @32981 only *assumes* child_ok; child_ok is false in-regime).  The live route
is the cube-shell potential bound (STEER.md).  This module exists to make the dead targets
*stay* refuted and to stop any future gate from re-passing them falsely.
"""
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "agent_hunt_pipeline" / "scripts"))
sys.path.insert(0, str(ROOT))

import scratch_rowcount_check as b   # noqa: E402
import drain_rowcount_check as d     # noqa: E402

Z, O, C, SEQ, ALTS, STAR = b.Z, b.O, b.C, b.SEQ, b.ALTS, b.STAR
rsize = b.rsize
rsize_set = b.rsize_set
S = d.rsimpStrong_raw
scd = d.strong_child_drain
DCB = d.drain_child_budget           # open_pot p + zw2 p * (1 + rsize k)   (.thy 32386-32387)


# ---------------- drain_ctxs / ctx_bound (EXACT .thy transcription) ----------------
def raw_plug(h, k):
    return b.rsimp7(h, k)


def ctx_extend(q, hc):
    head, cost = hc
    return (raw_plug(head, q), cost + (1 + rsize(q)))


def drain_ctxs(r):
    t = r[0]
    if t in ('Z', 'O'):
        return []
    if t == 'C':
        return [(r, rsize(r))]
    if t == 'ALTS':
        out = []
        for q in r[1]:
            out.extend(drain_ctxs(q))
        return out
    if t == 'SEQ':
        p, q = r[1], r[2]
        out = [ctx_extend(q, hc) for hc in drain_ctxs(p)]
        out.extend(drain_ctxs(q))
        return out
    if t == 'STAR':
        p = r[1]
        out = [(r, rsize(r))]
        out.extend(ctx_extend(r, hc) for hc in drain_ctxs(p))
        return out
    raise ValueError(t)


def ctx_bound(Cs, k):
    return sum(c[1] for c in Cs) + len(Cs) * (1 + rsize(k))


def regime(q):
    return S(q) == q and b.nf(q)


def sr(r):
    t = r[0]
    if t == 'Z':
        return '0'
    if t == 'O':
        return '1'
    if t == 'C':
        return r[1]
    if t == 'SEQ':
        return f'({sr(r[1])}.{sr(r[2])})'
    if t == 'ALTS':
        return '(' + '+'.join(sr(q) for q in r[1]) + ')'
    if t == 'STAR':
        return sr(r[1]) + '*'
    return '?'


# ============================================================
# THE WITNESS FAMILY (the structure rand_clean never builds)
# nested SEQ(ALTS[pre,1], ... SEQ(atom, star*)) opened at star*.
# ============================================================
def witness_family(rng, maxd=7):
    st = rng.choice(['a', 'b', 'c'])
    K = S(STAR(C(st)))
    body = SEQ(rng.choice([C('a'), C('b'), C('c'), O]), STAR(C(st)))
    for _ in range(rng.randrange(1, 5)):
        pre = rng.choice([SEQ(ALTS([C('a'), O]), C('b')), ALTS([C('a'), O]),
                          C(rng.choice('abc')), SEQ(ALTS([O, C('a')]), C('c')),
                          STAR(C(rng.choice('abc')))])
        head = ALTS([pre, O]) if rng.random() < 0.5 else pre
        body = SEQ(head, body)
    cand = body if rng.random() < 0.5 else ALTS([body, C(rng.choice('abc'))])
    return S(cand), K


# ============================================================
# NAMED CONFIRMED COUNTEREXAMPLES (regression anchors)
# ============================================================
_CE2_p = ('ALTS', (('O',),
                   ('SEQ', ('ALTS', (('O',),
                                     ('SEQ', ('ALTS', (('O',), ('C', 'a'))), ('C', 'a')),
                                     ('SEQ', ('ALTS', (('C', 'c'), ('O',))), ('ALTS', (('C', 'c'), ('O',)))))),
                           ('STAR', ('C', 'c')))))
_CE2_k = ('STAR', ('C', 'c'))
_CE1_p = ('ALTS', (('SEQ', ('ALTS', (('SEQ', ('ALTS', (('C', 'a'), ('O',))), ('C', 'b')), ('O',))),
                           ('SEQ', ('ALTS', (('O',), ('C', 'a'))), ('SEQ', ('C', 'c'), ('STAR', ('C', 'b'))))),
                   ('C', 'c')))
_CE1_k = ('STAR', ('C', 'b'))
# CHILDOK rsize22 -- kills the LOOSER drain_child_budget too:
#   p = (((((a+1).b)+1).((((a+1).b)+1).(a.b*)))+c), k = b*  -> strong 99 > dcb 96
_L = ALTS([SEQ(ALTS([C('a'), O]), C('b')), O])
_CHILDOK_p = ALTS([SEQ(_L, SEQ(_L, SEQ(C('a'), STAR(C('b'))))), C('c')])
_CHILDOK_k = STAR(C('b'))

# Each entry: (tag, p, k, breaks_ctx_bound, breaks_drain_child_budget)
NAMED_CES = [
    ('CE2', _CE2_p, _CE2_k, True, False),
    ('CE1', _CE1_p, _CE1_k, True, False),
    ('CHILDOK_rsize22', _CHILDOK_p, _CHILDOK_k, True, True),
]


# ============================================================
# TARGET PREDICATES
# ============================================================
def target_false(target, p, k):
    """True iff the named per-step budget `target` is VIOLATED at (p,k) (in-regime caller)."""
    lhs = rsize_set(scd(p, k))
    if target == 'ctx_bound':
        return lhs > ctx_bound(drain_ctxs(p), k)
    if target == 'drain_child_budget':
        return lhs > DCB(p, k)
    raise ValueError(target)


def mixed_samples(rng, n, maxd=7, witness_frac=0.5):
    """Yield up to n in-regime (p,k) pairs; `witness_frac` from the witness family,
    the rest from plain rand_clean depth-5..maxd.  This is the MINIMUM acceptable
    generator for any strong_child_drain gate."""
    got = 0
    attempts = 0
    while got < n and attempts < n * 40:
        attempts += 1
        if rng.random() < witness_frac:
            p, k = witness_family(rng, maxd)
        else:
            p = S(b.rand_clean(rng.randrange(5, maxd + 1), rng))
            k = S(b.rand_clean(rng.randrange(0, maxd + 1), rng))
        if regime(p) and regime(k):
            yield p, k
            got += 1


def confirm_named_ces():
    """Assert every NAMED CE is in-regime and violates the targets it is supposed to.
    Returns a list of report dicts.  Raises AssertionError on any regression."""
    out = []
    for tag, p, k, breaks_ctx, breaks_dcb in NAMED_CES:
        p, k = S(p), S(k)
        assert regime(p) and regime(k), f"{tag}: not in regime"
        lhs = rsize_set(scd(p, k))
        cb = ctx_bound(drain_ctxs(p), k)
        dcb = DCB(p, k)
        assert (lhs > cb) == breaks_ctx, f"{tag}: ctx_bound regression lhs={lhs} cb={cb}"
        assert (lhs > dcb) == breaks_dcb, f"{tag}: drain_child_budget regression lhs={lhs} dcb={dcb}"
        out.append(dict(tag=tag, p=sr(p), k=sr(k), rsize_p=rsize(p),
                        strong=lhs, ctx_bound=cb, drain_child_budget=dcb,
                        breaks_ctx_bound=lhs > cb, breaks_drain_child_budget=lhs > dcb))
    return out


def gate_report(target, rng, n=20000, maxd=7, witness_frac=0.5, label="GATE"):
    """Drop-in replacement for a homegrown 'G2 must be 0' loop.  Returns
    (violations, tested).  Unlike the old gate it draws from the witness family,
    so for the DEAD targets (ctx_bound, drain_child_budget) it WILL report
    violations -- which is the correct, non-artifactual result.  Also folds in
    the NAMED_CES so the known killers are always present."""
    viol = 0
    tested = 0
    first_ce = None
    # named CEs first (deterministic anchors)
    for tag, p, k, _, _ in NAMED_CES:
        p, k = S(p), S(k)
        if not (regime(p) and regime(k)):
            continue
        tested += 1
        if target_false(target, p, k):
            viol += 1
            if first_ce is None:
                first_ce = (tag, sr(p), sr(k), rsize_set(scd(p, k)))
    for p, k in mixed_samples(rng, n, maxd, witness_frac):
        tested += 1
        if target_false(target, p, k):
            viol += 1
            if first_ce is None:
                first_ce = ('rand', sr(p), sr(k), rsize_set(scd(p, k)))
    print(f"[{label}] target '{target}': {viol}/{tested} violations "
          f"(witness_frac={witness_frac}).  "
          f"{'TARGET IS FALSE (expected)' if viol else 'NO violation found'}")
    if first_ce:
        print(f"        first CE: {first_ce[0]} p={first_ce[1]} k={first_ce[2]} strong={first_ce[3]}")
    return viol, tested


def main():
    print("witness_gen self-test\n=====================")
    print("Named CEs (regression anchors):")
    for r in confirm_named_ces():
        print(f"  {r['tag']:16s} rsize(p)={r['rsize_p']:2d}  strong={r['strong']:3d}  "
              f"ctx_bound={r['ctx_bound']:3d} (broken {r['breaks_ctx_bound']})  "
              f"drain_child_budget={r['drain_child_budget']:3d} (broken {r['breaks_drain_child_budget']})")
        print(f"                   p={r['p']}  k={r['k']}")
    print("  --> all named CEs reproduce; both per-step budget targets are FALSE in-regime.\n")
    rng = random.Random(20260616)
    gate_report('ctx_bound', rng, n=8000, label="self-test ctx_bound")
    gate_report('drain_child_budget', rng, n=8000, label="self-test drain_child_budget")


if __name__ == "__main__":
    main()
