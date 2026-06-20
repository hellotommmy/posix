"""
norm_model.py -- Wave-0 faithful regression model for the N-route (Route 2).

Purpose: a model that does NOT prove anything; it (1) implements the OLD Isabelle
definitions VERBATIM (sigma4, sigma7, rsimpStrong_raw incl. the cross-row prune,
row_dlforms, apder_*), (2) implements the NEW normalizer N (= nstrong), the new
associative append alpha (= nplug), and the new opening delta_N (= ndlforms),
and (3) replays the named counterexamples + runs the small-size EXHAUSTIVE
adversarial checks that confirm / refute the route's load-bearing claims.

Run:  python norm_model.py

Every definition cites its source line in pro_ask_round2/DEFINITIONS.txt.
Representation of rrexp (hashable, immutable -- regexes live in sets):
    ('0',)                ZERO
    ('1',)                ONE
    ('ch', c)             RCHAR c
    ('seq', r1, r2)       RSEQ r1 r2
    ('alt', (q1,...))     RALTS [q1,...]      (branches stored as a tuple)
    ('star', r)           RSTAR r
We stay on the clean fragment: no RNTIMES / backref / half / residue.
"""

import sys
import itertools

sys.setrecursionlimit(1_000_000)

# ----------------------------------------------------------------------------
# constructors / accessors
# ----------------------------------------------------------------------------
ZERO = ('0',)
ONE  = ('1',)
def CH(c):       return ('ch', c)
def SEQ(a, b):   return ('seq', a, b)
def ALT(qs):     return ('alt', tuple(qs))
def STAR(r):     return ('star', r)

def is_zero(r):  return r == ZERO
def is_one(r):   return r == ONE
def is_char(r):  return r[0] == 'ch'
def is_seq(r):   return r[0] == 'seq'
def is_alt(r):   return r[0] == 'alt'
def is_star(r):  return r[0] == 'star'

def pp(r):
    """human-readable regex"""
    t = r[0]
    if t == '0':    return '0'
    if t == '1':    return '1'
    if t == 'ch':   return r[1]
    if t == 'star':
        inner = pp(r[1])
        return (inner if len(inner) == 1 else f'({inner})') + '*'
    if t == 'seq':
        return f'{_wrap_seq(r[1])}.{_wrap_seq(r[2])}'
    if t == 'alt':
        return '(' + '+'.join(pp(q) for q in r[1]) + ')'
    return str(r)

def _wrap_seq(r):
    s = pp(r)
    if is_seq(r):   # right-nested seq prints fine; parenthesise alts/seq for clarity
        return f'({s})'
    return s

# ----------------------------------------------------------------------------
# rsize  (DEFINITIONS.txt A, base/BasicIdentities.thy:487)
# ----------------------------------------------------------------------------
def rsize(r):
    t = r[0]
    if t in ('0', '1', 'ch'):  return 1
    if t == 'alt':             return 1 + sum(rsize(q) for q in r[1])
    if t == 'seq':             return 1 + rsize(r[1]) + rsize(r[2])
    if t == 'star':            return 1 + rsize(r[1])
    raise ValueError(r)

# ============================================================================
# OLD DEFINITIONS  (verbatim from DEFINITIONS.txt)
# ============================================================================

# sigma4 -- rsimp4_SEQ_atom  (BasicIdentities.thy:287)  WEAK plug, no a*.a* collapse
def sigma4(r1, r2):
    if is_zero(r1):  return ZERO
    if is_one(r1):   return r2
    if is_seq(r1):   return sigma4(r1[1], sigma4(r1[2], r2))
    # r1 is CHAR / ALTS / STAR  (leaf for the spine)
    if is_zero(r2):  return ZERO
    if is_one(r2):   return r1
    return SEQ(r1, r2)

# sigma7 -- rsimp7_SEQ_atom  (BasicIdentities.thy:414) STRONG plug: sigma4 + top a*.a* collapse ONLY
def sigma7(r1, r2):
    if is_star(r1):
        if is_star(r2) and r1[1] == r2[1]:
            return STAR(r1[1])
        if is_seq(r2) and is_star(r2[1]) and r1[1] == r2[1][1]:
            return SEQ(STAR(r1[1]), r2[2])
    return sigma4(r1, r2)

# rflts  (BasicIdentities.thy:177)
def rflts(rs):
    out = []
    for r in rs:
        if is_zero(r):       continue
        elif is_alt(r):      out.extend(r[1])
        else:                out.append(r)
    return out

# rdistinct  (BasicIdentities.thy:83)
def rdistinct(rs, acc):
    out = []
    seen = set(acc)
    for x in rs:
        if x in seen:        continue
        out.append(x)
        seen.add(x)
    return out

# rsimp_ALTs  (BasicIdentities.thy:206)
def rsimp_ALTs(rs):
    if len(rs) == 0:  return ZERO
    if len(rs) == 1:  return rs[0]
    return ALT(rs)

# ---- the cross-row prune scan (GeneralRegexBound.thy:17015..18239) ----
def rprune_eq_against(covered, rs):
    cov = set(covered)
    return [r for r in rs if r not in cov]

def rsimpStrong_prune_pair_raw(earlier, later):
    # fires ONLY for (RSEQ (RALTS lrs) k1, RSEQ (RALTS rrs) k2) with k1==k2
    if (is_seq(earlier) and is_alt(earlier[1]) and
            is_seq(later) and is_alt(later[1]) and earlier[2] == later[2]):
        lrs = list(earlier[1][1]); rrs = list(later[1][1]); k2 = later[2]
        return sigma7(rsimp_ALTs(rprune_eq_against(lrs, rrs)), k2)
    return later

def rsimpStrong_prune_against_rows_raw(seen, r):
    for x in seen:
        r = rsimpStrong_prune_pair_raw(x, r)
    return r

def rsimpStrong_prune_rows_raw(rs):
    seen = []          # collects the PRUNED rows r' (not originals); fold order matters
    out = []
    for r in rs:
        rp = rsimpStrong_prune_against_rows_raw(seen, r)
        out.append(rp)
        seen = [rp] + seen   # acc = (r' # seen)
    return out

def rsimpStrong_ALTs_raw(rs):
    return rsimp_ALTs(rdistinct(rflts(rsimpStrong_prune_rows_raw(rs)), set()))

# rsimpStrong_raw -- S  (GeneralRegexBound.thy:18365)
def S(r):
    t = r[0]
    if t in ('0', '1', 'ch'):  return r
    if t == 'seq':             return sigma7(S(r[1]), S(r[2]))
    if t == 'alt':             return rsimpStrong_ALTs_raw(rflts([S(q) for q in r[1]]))
    if t == 'star':
        s = S(r[1])
        if is_zero(s) or is_one(s):  return ONE
        if is_star(s):               return s         # RSTAR s  (collapses STAR(STAR s))
        return STAR(s)
    raise ValueError(r)

# rfrontier  (GeneralRegexBound.thy:3862)
def rfrontier(r):
    if is_zero(r):  return frozenset()
    if is_alt(r):   return frozenset().union(*[rfrontier(q) for q in r[1]]) if r[1] else frozenset()
    return frozenset({r})

# row_dlforms -- dl  (AntimirovFactoredTransition.thy:4791)
def row_dlforms(r):
    if is_zero(r):   return frozenset()
    if is_alt(r):    return frozenset().union(*[row_dlforms(q) for q in r[1]]) if r[1] else frozenset()
    if is_seq(r) and is_alt(r[1]):
        ps = r[1][1]; k = r[2]
        return frozenset().union(*[row_dlforms(sigma7(p, k)) for p in ps]) if ps else frozenset()
    return rfrontier(r)

# ---- Antimirov structures (clean fragment) ----
def apder_terms(r):
    t = r[0]
    if t in ('0', '1'):  return frozenset()
    if t == 'ch':        return frozenset({ONE})
    if t == 'alt':       return frozenset().union(*[apder_terms(q) for q in r[1]]) if r[1] else frozenset()
    if t == 'seq':
        left = frozenset(sigma4(p, r[2]) for p in apder_terms(r[1]))
        return left | apder_terms(r[2])
    if t == 'star':
        return frozenset(sigma4(p, r) for p in apder_terms(r[1]))
    raise ValueError(r)

def apder_frontier(r):
    base = rfrontier(r)
    extra = frozenset().union(*[rfrontier(q) for q in apder_terms(r)]) if apder_terms(r) else frozenset()
    return base | extra

def apder_rows(r):
    return frozenset({r}) | apder_frontier(r)

def apder_strong_dlfrontier(r):          # U(r)
    rows = apder_rows(r)
    return frozenset().union(*[row_dlforms(S(q)) for q in rows]) if rows else frozenset()

# ============================================================================
# NEW DEFINITIONS  (route2_verdict.md waves 1A/1B/2A)
# ============================================================================

# fac / mk_seq -- the sequence spine
def fac(r):
    if is_seq(r):  return fac(r[1]) + fac(r[2])
    return [r]

def mk_seq(xs):
    if len(xs) == 0:  return ONE
    if len(xs) == 1:  return xs[0]
    return SEQ(xs[0], mk_seq(xs[1:]))

# norm_seq: (1) drop RONE; (2) any RZERO => [RZERO]; (3) fold adjacent identical stars
def norm_seq(xs):
    if any(is_zero(x) for x in xs):
        return [ZERO]
    ys = [x for x in xs if not is_one(x)]
    zs = []
    for x in ys:
        if zs and zs[-1] == x and is_star(x):
            continue                         # collapse adjacent identical star
        zs.append(x)
    return zs

# alpha -- nplug  (the associative normalized append)
def nplug(r, k):
    return mk_seq(norm_seq(fac(r) + fac(k)))

# ---- new alternation prune: copies old shape but RE-PLUGS via alpha (nplug), not sigma7 ----
def nprune_pair(earlier, later):
    if (is_seq(earlier) and is_alt(earlier[1]) and
            is_seq(later) and is_alt(later[1]) and earlier[2] == later[2]):
        lrs = list(earlier[1][1]); rrs = list(later[1][1]); k2 = later[2]
        return nplug(rsimp_ALTs(rprune_eq_against(lrs, rrs)), k2)
    return later

def nprune_against_rows(seen, r):
    for x in seen:
        r = nprune_pair(x, r)
    return r

def nprune_rows(rs):
    seen = []; out = []
    for r in rs:
        rp = nprune_against_rows(seen, r)
        out.append(rp)
        seen = [rp] + seen
    return out

def nalts(rs):
    return rsimp_ALTs(rdistinct(rflts(nprune_rows(rs)), set()))

# nstrong -- N
def N(r):
    t = r[0]
    if t in ('0', '1', 'ch'):  return r
    if t == 'seq':             return nplug(N(r[1]), N(r[2]))
    if t == 'star':
        s = N(r[1])
        if is_zero(s) or is_one(s):  return ONE
        if is_star(s):               return s            # N(r*) = s*  when N r = s*
        return STAR(s)
    if t == 'alt':             return nalts([N(q) for q in r[1]])
    raise ValueError(r)

# delta_N -- ndlforms  (the new opening; distribution uses alpha)
def ndlforms(r):
    if is_zero(r):   return frozenset()
    if is_alt(r):    return frozenset().union(*[ndlforms(q) for q in r[1]]) if r[1] else frozenset()
    if is_seq(r) and is_alt(r[1]):
        ps = r[1][1]; k = r[2]
        return frozenset().union(*[ndlforms(nplug(p, k)) for p in ps]) if ps else frozenset()
    return rfrontier(r)

# ============================================================================
# named regexes / counterexamples  (route2_verdict.md sec 3)
# ============================================================================
a, b, c, d = CH('a'), CH('b'), CH('c'), CH('d')
As, Bs, Cs = STAR(a), STAR(b), STAR(c)

CE1 = (ALT([ONE, SEQ(Bs, As)]), As)                       # 1 + (b*.a*),  k=a*
CE2 = (ALT([SEQ(Bs, As), SEQ(Cs, As)]), As)               # (b*a*)+(c*a*), k=a*
CE3 = (SEQ(ALT([ONE, SEQ(SEQ(a, ONE), As), a]), As), None)# (1+((a.1).a*)+a).a*  (collapsing tail-ish)
CE4 = (SEQ(d, SEQ(ALT([SEQ(Bs, As), SEQ(Cs, As)]), As)), None)  # d.(((b*a*)+(c*a*)).a*)
def deep_tail(n):                                          # b*.(a*.(a*...a*))
    r = As
    for _ in range(n): r = SEQ(As, r)
    return SEQ(Bs, r)
CE5 = (deep_tail(3), None)
CE6 = (ALT([ONE, STAR(ALT([Cs, ONE]))]), None)            # 1 + (c*+1)*
K_UNREACH = SEQ(Bs, Bs)                                    # k = b*.b*

# ============================================================================
# small-size clean-regex enumerator (for EXHAUSTIVE adversarial checks)
# ============================================================================
def nonalt(r):  return not is_alt(r)
def rnonseq(r): return not is_seq(r)

def apder_nf(r):
    t = r[0]
    if t in ('0', '1', 'ch'):  return True
    if t == 'alt':
        qs = r[1]
        return len(qs) >= 1 and all(apder_nf(q) and nonalt(q) and not is_zero(q) for q in qs)
    if t == 'seq':
        r1, r2 = r[1], r[2]
        return (apder_nf(r1) and apder_nf(r2) and rnonseq(r1)
                and not is_zero(r1) and not is_one(r1)
                and not is_zero(r2) and not is_one(r2))
    if t == 'star':
        return apder_nf(r[1])
    raise ValueError(r)

_ALPHABET = ('a', 'b')   # 2 chars keeps the exhaustive enum tractable; 'c' added for CEs

def gen_upto(maxsize, alphabet=_ALPHABET, max_alt_arity=3):
    """all rrexp with rsize in [1..maxsize], deduped, clean fragment constructors only."""
    by_size = {n: set() for n in range(1, maxsize + 1)}
    by_size[1] = {ZERO, ONE} | {CH(ch) for ch in alphabet}
    for n in range(2, maxsize + 1):
        bucket = by_size[n]
        # STAR r, rsize r = n-1
        for r in by_size[n - 1]:
            bucket.add(STAR(r))
        # SEQ r1 r2, rsize r1 + rsize r2 = n-1
        for s1 in range(1, n - 1):
            s2 = (n - 1) - s1
            if s2 < 1: continue
            for r1 in by_size[s1]:
                for r2 in by_size[s2]:
                    bucket.add(SEQ(r1, r2))
        # ALTS of 2..max_alt_arity branches, 1 + sum rsize = n
        budget = n - 1
        for arity in range(2, max_alt_arity + 1):
            for combo in _compositions(budget, arity, by_size):
                bucket.add(ALT(combo))
    return by_size

def _compositions(total, parts, by_size):
    """yield ordered tuples of `parts` regexes whose rsizes sum to `total`."""
    if parts == 1:
        for r in by_size.get(total, ()):
            yield (r,)
        return
    for first_size in range(1, total - (parts - 1) + 1):
        for r in by_size.get(first_size, ()):
            for rest in _compositions(total - first_size, parts - 1, by_size):
                yield (r,) + rest

def clean_regexes(maxsize):
    bs = gen_upto(maxsize)
    out = []
    for n in range(1, maxsize + 1):
        for r in bs[n]:
            if apder_nf(r):
                out.append(r)
    out.sort(key=rsize)
    return out

# ============================================================================
# TESTS
# ============================================================================
def banner(s): print('\n' + '=' * 78 + '\n' + s + '\n' + '=' * 78)

def t1_hand_values():
    banner('[T1] three hand-computed N values (kill-criterion #1 anchors)')
    cases = [
        ('N(a.(a*.a*))', N(SEQ(a, SEQ(As, As))),    'a.a*'),
        ('N(a*.a*)',     N(SEQ(As, As)),            'a*'),
        ('N((b*+c*).a*)',N(SEQ(ALT([Bs, Cs]), As)), '(b*+c*).a*'),
    ]
    ok = True
    for name, got, want in cases:
        g = pp(got)
        good = (g == want)
        ok &= good
        print(f'  {name:16s} = {g:14s} want {want:14s}  {"OK" if good else "*** MISMATCH ***"}')
    return ok

def t6_idempotent(regs):
    banner('[T6] N idempotent: N(N r) == N r')
    bad = [r for r in regs if N(N(r)) != N(r)]
    if bad:
        print(f'  *** {len(bad)} FAILURES, smallest: {pp(min(bad, key=rsize))}')
        return False
    print(f'  0 / {len(regs)} violations (exhaustive)')
    return True

def t2_rsimp4_shadow(regs, conts):
    banner('[T2] nstrong_rsimp4_shadow:  N(sigma4(r,k)) == nplug(N r, N k)   (KILL-CRIT #1)')
    viol = []
    total = 0
    for r in regs:
        for k in conts:
            total += 1
            if N(sigma4(r, k)) != nplug(N(r), N(k)):
                viol.append((r, k))
    if viol:
        r, k = min(viol, key=lambda rk: rsize(rk[0]) + rsize(rk[1]))
        print(f'  *** {len(viol)} / {total} violations')
        print(f'      smallest CE: r={pp(r)}  k={pp(k)}')
        print(f'        sigma4(r,k)         = {pp(sigma4(r,k))}')
        print(f'        N(sigma4(r,k))      = {pp(N(sigma4(r,k)))}')
        print(f'        nplug(N r, N k)     = {pp(nplug(N(r),N(k)))}')
        return False
    print(f'  0 / {total} violations (exhaustive over r, curated k)')
    return True

def t3_nplug_assoc(regs):
    banner('[T3] nplug_assoc on N-normal triples: nplug(nplug(x,y),z) == nplug(x,nplug(y,z))')
    norm = sorted({N(r) for r in regs}, key=rsize)
    # keep it tractable: triples over the smaller normal forms
    small = [r for r in norm if rsize(r) <= 5]
    viol = []
    total = 0
    for x in small:
        for y in small:
            for z in small:
                total += 1
                if nplug(nplug(x, y), z) != nplug(x, nplug(y, z)):
                    viol.append((x, y, z))
    if viol:
        x, y, z = min(viol, key=lambda t: sum(rsize(e) for e in t))
        print(f'  *** {len(viol)} / {total} violations')
        print(f'      smallest CE: x={pp(x)} y={pp(y)} z={pp(z)}')
        print(f'        (xy)z = {pp(nplug(nplug(x,y),z))}   x(yz) = {pp(nplug(x,nplug(y,z)))}')
        return False
    print(f'  0 / {total} violations (N-normal triples, rsize<=5)')
    return True

def t7_NS_identity(regs):
    banner('[T7] Wave-4 shadow identity:  N(S r) == N r'
           '\n      (connects the S-form opening shadow to the route target ndlforms(N q)).')
    viol = [r for r in regs if N(S(r)) != N(r)]
    if viol:
        r = min(viol, key=rsize)
        print(f'  *** {len(viol)} violations, smallest r={pp(r)}: N(S r)={pp(N(S(r)))}  N r={pp(N(r))}')
        return False
    print(f'  0 / {len(regs)} violations (exhaustive)')
    return True

def t4_old_universe_has_uncollapsed(regs):
    banner('[T4] OLD universe carries non-N-normal (uncollapsed s*.s*) rows  =>  exact'
           '\n      containment into any N-normal universe is FALSE (motivates SHADOW).')
    def has_self_star_seq(x):
        # detect a SEQ(STAR s, STAR s ...) i.e. a row that S did NOT collapse but N would
        if is_seq(x):
            l, r = x[1], x[2]
            if is_star(l) and (l == r or (is_seq(r) and r[1] == l)):
                return True
            return has_self_star_seq(l) or has_self_star_seq(r)
        if is_alt(x):  return any(has_self_star_seq(q) for q in x[1])
        if is_star(x): return has_self_star_seq(x[1])
        return False
    # seed with the named CEs (their witness roots have rsize 9, beyond the small enum)
    seed = [SEQ(CE2[0], CE2[1]), SEQ(CE1[0], CE1[1]), CE3[0], CE4[0]]
    witnesses = []
    for r in list(regs) + seed:
        U = apder_strong_dlfrontier(r)
        for x in U:
            if N(x) != x and has_self_star_seq(x):
                witnesses.append((r, x))
                break
    if not witnesses:
        print('  (no small witness found at this size -- enlarge enum)')
        return False
    r, x = min(witnesses, key=lambda rx: rsize(rx[0]))
    print(f'  smallest clean r with an uncollapsed self-star row in U(r):')
    print(f'     r       = {pp(r)}   (rsize {rsize(r)})')
    print(f'     x in U  = {pp(x)}      (x != N(x), so x is NOT N-normal)')
    print(f'     N(x)    = {pp(N(x))}   <- the shadow')
    print(f'  => U(r) is NOT a subset of any set of N-normal forms.  ({len(witnesses)} such r found)')
    return True

def t5_opening_shadow(regs):
    banner('[T5] old_opening_shadow:  x in row_dlforms(q)  =>  N(x) in ndlforms(N q)'
           '\n      (the Wave-2A bridge; tested raw and S-applied).')
    viol_raw = []; viol_S = []; total = 0
    for q in regs:
        nq = N(q); ndq = ndlforms(nq)
        for x in row_dlforms(q):
            total += 1
            if N(x) not in ndq:
                viol_raw.append((q, x))
        snq = N(S(q)); ndsq = ndlforms(snq)
        for x in row_dlforms(S(q)):
            if N(x) not in ndsq:
                viol_S.append((q, x))
    def report(name, viol):
        if viol:
            q, x = min(viol, key=lambda qx: rsize(qx[0]))
            print(f'  {name}: *** {len(viol)} violations, smallest q={pp(q)}, x={pp(x)}, N(x)={pp(N(x))}')
            return False
        print(f'  {name}: 0 violations')
        return True
    ok1 = report('raw   x in dl(q)   -> N x in dN(N q)   ', viol_raw)
    ok2 = report('S-form x in dl(S q) -> N x in dN(N(S q))', viol_S)
    print(f'  (total raw pairs checked: {total})')
    return ok1, ok2

def named_ce_report():
    banner('[NAMED CEs] replay of route2_verdict.md sec.3 examples')
    def show(tag, r):
        U = apder_strong_dlfrontier(r)
        nonnorm = sorted([x for x in U if N(x) != x], key=rsize)
        print(f'  {tag}: r = {pp(r)}   |U(r)|={len(U)}   non-N-normal rows in U: {len(nonnorm)}')
        for x in nonnorm[:4]:
            print(f'        uncollapsed {pp(x):20s} -> shadow N(x)={pp(N(x))}')
    show('CE1  1+(b*a*)@a*    ', SEQ(*CE1) if CE1[1] else CE1[0])
    show('CE2  (b*a*)+(c*a*)@a*', SEQ(CE2[0], CE2[1]))
    show('CE3  collapsing-tail', CE3[0])
    show('CE4  reachable-wrap ', CE4[0])
    show('CE5  deep-tail(3)   ', CE5[0])
    show('CE6  1+(c*+1)*      ', CE6[0])
    print(f'  K_UNREACH = {pp(K_UNREACH)}   N(K_UNREACH) = {pp(N(K_UNREACH))}  (b*.b* -> b*)')

def main():
    MAX = 7
    print(f'enumerating clean regexes up to rsize {MAX} (alphabet {_ALPHABET}) ...')
    regs = clean_regexes(MAX)
    print(f'  {len(regs)} clean (apder_nf) regexes')
    conts = [ONE, a, b, As, Bs, SEQ(As, As), SEQ(Bs, Bs), ALT([Bs, Cs]),
             SEQ(As, b), SEQ(ALT([Bs, Cs]), As)]
    print(f'  {len(conts)} curated continuations k')

    results = {}
    results['T1'] = t1_hand_values()
    results['T6'] = t6_idempotent(regs)
    results['T2'] = t2_rsimp4_shadow(regs, conts)
    results['T3'] = t3_nplug_assoc(regs)
    results['T7'] = t7_NS_identity(regs)
    results['T4'] = t4_old_universe_has_uncollapsed(regs)
    r5a, r5b = t5_opening_shadow(regs)
    results['T5_raw'] = r5a
    results['T5_S']   = r5b
    named_ce_report()

    banner('SUMMARY')
    for k, v in results.items():
        print(f'  {k:8s} : {"PASS" if v else "FAIL"}')

if __name__ == '__main__':
    main()
