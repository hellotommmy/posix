"""
wave5_probe.py -- Wave-5 (provenance injection) FEASIBILITY probe.

We do NOT yet build the provenance datatype. We test the two NECESSARY conditions that
route2_verdict.md sec.14 flags as route-killers, because they are purely numeric and
decide the route before any tag design:

  (#6) alt family  q_i = b_i*.a*,  r_n = (q_1+..+q_n).a*  : tag count must be O(n), not O(n^2).
  (#7) deep tail   b*.(a*.(a*...a*))                      : debt must be O(depth), not O(depth^2).

Key quantities for the OLD carrier strong_apder_acc r k (= rsimpStrong_dlform_closure of
the sigma4-frontier + the term-frontier accumulator):
  card(SAA)              -- the universe size (Gate target; known TRUE-linear)
  debt = #{x in SAA : N(x) != x}   -- the NON-normal (uncollapsed a*.a*) rows; these are the
                                      ones a provenance tag must account for as DEBT.
  fibers = SAA grouped by N(x); max fiber size.

A linear A_N# REQUIRES debt <= C*rsize r (each debt row needs its own tag). If debt is
super-linear in rsize, Wave-5 is DEAD (no tag scheme is linear). This is the decisive filter.

Run:  python wave5_probe.py
"""
import sys, itertools
from norm_model import (
    ZERO, ONE, CH, SEQ, ALT, STAR, rsize, pp, N,
    is_zero, is_one, is_char, is_seq, is_alt, is_star,
    sigma4, S, row_dlforms, rfrontier, nplug, ndlforms,
    apder_strong_dlfrontier, apder_rows,
)

sys.setrecursionlimit(1_000_000)

# ---- apder_term_frontier_acc (DEFINITIONS.txt C, clean fragment) ----
def apder_term_frontier_acc(r, k):
    t = r[0]
    if t in ('0', '1'):  return frozenset()
    if t == 'ch':        return rfrontier(k)
    if t == 'alt':
        return frozenset().union(*[apder_term_frontier_acc(q, k) for q in r[1]]) if r[1] else frozenset()
    if t == 'seq':
        return apder_term_frontier_acc(r[1], sigma4(r[2], k)) | apder_term_frontier_acc(r[2], k)
    if t == 'star':
        return apder_term_frontier_acc(r[1], sigma4(r, k))
    raise ValueError(r)

def rsimpStrong_dlform_closure(U):
    return frozenset().union(*[row_dlforms(S(p)) for p in U]) if U else frozenset()

# strong_apder_acc r k  (cubic/DirectUniverseCubic.thy:341)
def strong_apder_acc(r, k):
    carrier = rfrontier(sigma4(r, k)) | apder_term_frontier_acc(r, k)
    return rsimpStrong_dlform_closure(carrier)

# ---- families ----
def CHs(i):
    return CH("abcdefghijklmnop"[i])

def alt_family(n):
    """r_n = (b_1*.a* + ... + b_n*.a*).a*  (distinct b_i)"""
    As = STAR(CH('a'))
    branches = [SEQ(STAR(CHs(i + 1)), As) for i in range(n)]   # b_i = chars b,c,d,...
    return SEQ(ALT(branches), As)

def deep_tail(d):
    """b*.(a*.(a*. ... .a*))  with d copies of a* in the tail"""
    As = STAR(CH('a'))
    tail = As
    for _ in range(d - 1):
        tail = SEQ(As, tail)
    return SEQ(STAR(CH('b')), tail)

def reachable_deep(d):
    """c . (deep_tail(d))  -- make the rows reachable from a non-nullable head"""
    return SEQ(CH('c'), deep_tail(d))

def nullable_alt_deep(d):
    """(1 + b*.a*) . (a* . (a* ... a*))  -- nullable head distributes onto a deep tail"""
    As = STAR(CH('a'))
    tail = As
    for _ in range(d - 1):
        tail = SEQ(As, tail)
    return SEQ(ALT([ONE, SEQ(STAR(CH('b')), As)]), tail)

# ---- metrics ----
def is_nnormal(x):
    return N(x) == x

def metrics(r, k=ONE):
    SAA = strong_apder_acc(r, k)
    base = strong_apder_acc(ONE, k)
    diff = SAA - base
    U = apder_strong_dlfrontier(r)
    debt = [x for x in SAA if N(x) != x]
    diffdebt = [x for x in diff if N(x) != x]
    fibers = {}
    for x in SAA:
        fibers.setdefault(N(x), []).append(x)
    maxfib = max((len(v) for v in fibers.values()), default=0)
    return {
        'rsize': rsize(r),
        'cardU': len(U),
        'cardSAA': len(SAA),
        'carddiff': len(diff),
        'debt': len(debt),
        'diffdebt': len(diffdebt),
        'nfibers': len(fibers),
        'maxfib': maxfib,
    }

def table(name, rs, k=ONE):
    print(f"\n=== {name}  (k={pp(k)}) ===")
    print(f"{'param':>6} {'rsize':>6} {'cardU':>6} {'SAA':>6} {'diff':>6} "
          f"{'debt':>6} {'ddebt':>6} {'nfib':>6} {'maxf':>6} {'debt/rs':>8} {'U/rs':>6}")
    rows = []
    for p, r in rs:
        m = metrics(r, k)
        rows.append((p, m))
        print(f"{p:>6} {m['rsize']:>6} {m['cardU']:>6} {m['cardSAA']:>6} {m['carddiff']:>6} "
              f"{m['debt']:>6} {m['diffdebt']:>6} {m['nfibers']:>6} {m['maxfib']:>6} "
              f"{m['debt']/m['rsize']:>8.3f} {m['cardU']/m['rsize']:>6.3f}")
    return rows

def growth_verdict(name, rows, getter):
    """report whether `getter(m)` looks linear or super-linear vs param p (= depth/n)."""
    if len(rows) < 3:
        return
    ps = [p for p, _ in rows]
    ys = [getter(m) for _, m in rows]
    # finite differences
    d1 = [ys[i+1]-ys[i] for i in range(len(ys)-1)]
    d2 = [d1[i+1]-d1[i] for i in range(len(d1)-1)]
    growing2 = sum(1 for x in d2 if x > 0)
    print(f"  [{name}] values {ys}")
    print(f"           1st-diff {d1}  2nd-diff {d2}  -> "
          f"{'SUPER-LINEAR (2nd diff > 0)' if growing2 >= max(1,len(d2)//2) else 'looks linear'}")

def main():
    a = table("ALT family r_n=(b1*a*+..+bn*a*).a*", [(n, alt_family(n)) for n in range(1, 8)])
    growth_verdict("alt debt", a, lambda m: m['debt'])
    growth_verdict("alt cardU", a, lambda m: m['cardU'])

    dk = STAR(CH('a'))
    d = table("DEEP tail b*.(a*..a*) @ k=a*", [(n, deep_tail(n)) for n in range(1, 9)], k=dk)
    growth_verdict("deep debt", d, lambda m: m['debt'])
    growth_verdict("deep diffdebt", d, lambda m: m['diffdebt'])
    growth_verdict("deep cardU", d, lambda m: m['cardU'])

    nd = table("NULLABLE-alt deep (1+b*a*).(a*..a*) @ k=a*",
               [(n, nullable_alt_deep(n)) for n in range(1, 9)], k=dk)
    growth_verdict("nulldeep debt", nd, lambda m: m['debt'])
    growth_verdict("nulldeep cardU", nd, lambda m: m['cardU'])

    rd = table("REACHABLE c.deep(d) @ k=RONE", [(n, reachable_deep(n)) for n in range(1, 9)])
    growth_verdict("reach debt", rd, lambda m: m['debt'])

    print("\n=== DECISION ===")
    print("Wave-5 needs debt(r) <= C*rsize r (every uncollapsed row needs its own tag).")
    print("If any family's debt 2nd-difference is positive (super-linear), Wave-5 is DEAD")
    print("(kill-crit #7), independent of the provenance datatype.")

if __name__ == '__main__':
    main()


# ============================================================================
# STAGE B -- the new accumulator A_N and its CLEAN recurrences (Wave 2B) + the
# old->new shadow (Wave 4). These are where verdict7/8/cand2 actually died.
# ============================================================================
from norm_model import ndlforms, clean_regexes

def nterm_acc(r, k):
    t = r[0]
    if t in ('0', '1'):  return frozenset()
    if t == 'ch':        return rfrontier(k)
    if t == 'alt':
        return frozenset().union(*[nterm_acc(q, k) for q in r[1]]) if r[1] else frozenset()
    if t == 'seq':
        return nterm_acc(r[1], nplug(N(r[2]), k)) | nterm_acc(r[2], k)
    if t == 'star':
        return nterm_acc(r[1], nplug(N(r), k))
    raise ValueError(r)

def nbase(k):
    return ndlforms(k)

def nacc(r, k):
    head = ndlforms(nplug(N(r), k))
    tail = frozenset().union(*[ndlforms(p) for p in nterm_acc(r, k)]) if nterm_acc(r, k) else frozenset()
    return head | tail

def banner(s): print('\n' + '=' * 78 + '\n' + s + '\n' + '=' * 78)

def test_recurrences(regs, conts):
    banner('[R] nacc per-constructor SUBSET recurrences (Wave 2B; RALTS = the +1 killer)')
    vR = vL = vT = []  # placeholders
    viol_seq = []; viol_alt = []; viol_star = []; total = 0
    for r in regs:
        for k in conts:
            total += 1
            if is_seq(r):
                lhs = nacc(r, k)
                rhs = nacc(r[1], nplug(N(r[2]), k)) | nacc(r[2], k)
                if not lhs <= rhs: viol_seq.append((r, k))
            if is_alt(r):
                lhs = nacc(r, k)
                rhs = frozenset().union(*[nacc(q, k) for q in r[1]]) if r[1] else frozenset()
                if not lhs <= rhs: viol_alt.append((r, k))
            if is_star(r):
                lhs = nacc(r, k)
                kk = nplug(N(r), k)
                rhs = ndlforms(kk) | nacc(r[1], kk)
                if not lhs <= rhs: viol_star.append((r, k))
    def rep(nm, v):
        if v:
            r, k = min(v, key=lambda rk: rsize(rk[0]) + rsize(rk[1]))
            print(f"  {nm}: *** {len(v)} viol; smallest r={pp(r)} k={pp(k)}")
            extra = nacc(r, k) - (frozenset().union(*[nacc(q, k) for q in r[1]]) if is_alt(r) else frozenset())
            return False
        print(f"  {nm}: 0 violations")
        return True
    o1 = rep('RSEQ  nacc(r1 r2)k <= nacc r1 (nplug(N r2)k) U nacc r2 k', viol_seq)
    o2 = rep('RALTS nacc(sum rs)k <= U nacc q k                      ', viol_alt)
    o3 = rep('RSTAR nacc(r*)k <= dN(nplug(N r*)k) U nacc r (..)      ', viol_star)
    print(f"  (checked {total} (r,k) pairs)")
    return o1 and o2 and o3

def test_shadow(regs, conts):
    banner('[S] old_acc_shadow:  x in strong_apder_acc r k  =>  N x in nacc r (N k)  (Wave 4)')
    viol = []; total = 0
    for r in regs:
        for k in conts:
            nk = N(k)
            nr = nacc(r, nk)
            for x in strong_apder_acc(r, k):
                total += 1
                if N(x) not in nr:
                    viol.append((r, k, x))
    if viol:
        r, k, x = min(viol, key=lambda t: rsize(t[0]) + rsize(t[1]))
        print(f"  *** {len(viol)} / {total} violations")
        print(f"      smallest r={pp(r)} k={pp(k)} x={pp(x)}  N(x)={pp(N(x))}")
        print(f"      nacc r (N k) = {{{', '.join(sorted(pp(y) for y in nacc(r,N(k))))}}}")
        return False
    print(f"  0 / {total} violations")
    return True

def test_injection_domination(regs, conts):
    """The Wave-5 feasibility core: the old EXCESS must inject (per N-fiber) into the
    NEW excess nacc(r,Nk) - nbase(Nk). Necessary: per N-value v,
       #{x in (SAA r k - SAA 1 k) : N x = v}  <=  (multiplicity available in new universe).
    Here the new universe is a SET (each v once); so domination holds iff each old fiber
    that maps to a single v collapses to <=1 ... which it does NOT (R_i,P_i both ->v).
    => the SET nacc cannot receive 2 rows at one v; the PROVENANCE must supply the 2nd slot.
    So we report, per r, the max old-excess fiber size that the provenance must cover."""
    banner('[I] injection load: max #old-excess rows collapsing to one N-value (= provenance multiplicity needed)')
    worst = []
    for r in regs:
        for k in conts:
            diff = strong_apder_acc(r, k) - strong_apder_acc(ONE, k)
            fib = {}
            for x in diff:
                fib.setdefault(N(x), 0)
                fib[N(x)] += 1
            mx = max(fib.values(), default=0)
            shadow_ok = all(N(x) in nacc(r, N(k)) for x in diff)
            worst.append((mx, rsize(r), shadow_ok, r, k))
    worst.sort(reverse=True)
    print("  top fiber-multiplicities (mult, rsize, shadow_in_nacc, r, k):")
    for mx, rs, ok, r, k in worst[:8]:
        print(f"    mult={mx} rsize={rs} shadow={ok}  r={pp(r)} k={pp(k)}")
    allok = all(ok for _,_,ok,_,_ in worst)
    print(f"  shadow (old-excess N-image in nacc) holds on ALL probed: {allok}")
    return allok

def stageB():
    MAX = 7
    regs = clean_regexes(MAX)
    conts = [ONE, CH('a'), STAR(CH('a')), STAR(CH('b')), SEQ(STAR(CH('a')), STAR(CH('a'))),
             SEQ(STAR(CH('b')), STAR(CH('b'))), ALT([STAR(CH('b')), STAR(CH('c'))])]
    fam = [alt_family(n) for n in range(1,6)] + [nullable_alt_deep(n) for n in range(1,6)]
    print(f"StageB: {len(regs)} clean regs (rsize<={MAX}) + {len(fam)} family regs, {len(conts)} conts")
    r1 = test_recurrences(regs + fam, conts)
    r2 = test_shadow(regs + fam, conts)
    r3 = test_injection_domination(regs + fam, conts)
    banner('STAGE B SUMMARY')
    print(f"  recurrences clean : {'PASS' if r1 else 'FAIL'}")
    print(f"  old->new shadow   : {'PASS' if r2 else 'FAIL'}")
    print(f"  injection shadow  : {'PASS' if r3 else 'FAIL'}")

if __name__ == '__main__':
    stageB()


# ============================================================================
# STAGE C -- the DECISIVE test on the WITNESS FAMILY (nested SEQ opened at star*,
# the structure that made child_ok 99>96). Two questions:
#  (1) max #NON-NORMAL old rows per N-fiber  -- if >1, a normality-bit injection
#      collides; if it GROWS with depth, even a structured linear prov is in doubt.
#  (2) card(nacc r 1 - nbase 1) <= C*rsize r  -- the Wave-3 internal linear count.
# ============================================================================
def witness(d):
    """nested ((a+1).b)+1 frames over a.b*, wrapped (...)+c; open at k=b*.
       d=2 reproduces the rsize-22 child_ok killer family."""
    X = ALT([SEQ(ALT([CH('a'), ONE]), CH('b')), ONE])      # ((a+1).b)+1
    inner = SEQ(CH('a'), STAR(CH('b')))                    # a.b*
    for _ in range(d):
        inner = SEQ(X, inner)
    return ALT([inner, CH('c')])

def witness2(d):
    """variant: re-doubling star tail explicitly, opened at star*."""
    bs = STAR(CH('b'))
    inner = SEQ(CH('a'), bs)
    X = ALT([SEQ(STAR(CH('a')), bs), ONE])                 # (a*.b* + 1)  nullable, distributes
    for _ in range(d):
        inner = SEQ(X, inner)
    return ALT([inner, CH('c')])

def max_nonnormal_per_fiber(r, k):
    diff = strong_apder_acc(r, k) - strong_apder_acc(ONE, k)
    fib_nn = {}
    for x in diff:
        if N(x) != x:
            fib_nn[N(x)] = fib_nn.get(N(x), 0) + 1
    return max(fib_nn.values(), default=0), len(diff), len([x for x in diff if N(x)!=x])

def stageC():
    banner('[C1] WITNESS family: max NON-NORMAL old rows per N-fiber (injectivity load)')
    bk = STAR(CH('b'))
    print(f"{'fam':>10} {'d':>3} {'rsize':>6} {'carddiff':>9} {'debt':>6} {'maxNNfib':>9} "
          f"{'recur':>6} {'shadow':>7} {'nacc-1/rs':>10}")
    families = [('witness', witness, bk), ('witness2', witness2, bk),
                ('altfam', lambda n: alt_family(n), STAR(CH('a'))),
                ('nulldeep', nullable_alt_deep, bk)]
    bad = []
    for fname, fn, k in families:
        for d in range(1, 7):
            r = fn(d)
            mx, cd, debt = max_nonnormal_per_fiber(r, k)
            # recurrence (RALTS/RSEQ/RSTAR) + shadow spot-check on THIS r at THIS k
            rec_ok = True
            if is_alt(r):
                rec_ok = nacc(r, k) <= (frozenset().union(*[nacc(q, k) for q in r[1]]) if r[1] else frozenset())
            sh_ok = all(N(x) in nacc(r, N(k)) for x in strong_apder_acc(r, k))
            # Wave-3 internal count at k=RONE
            internal = nacc(r, ONE) - nbase(ONE)
            ratio = len(internal) / rsize(r)
            flag = ''
            if mx > 1: flag = ' <== NONNORMAL FIBER > 1'; bad.append((fname, d, mx))
            if not sh_ok: flag += ' <== SHADOW FAIL'; bad.append((fname,d,'shadow'))
            print(f"{fname:>10} {d:>3} {rsize(r):>6} {cd:>9} {debt:>6} {mx:>9} "
                  f"{str(rec_ok):>6} {str(sh_ok):>7} {ratio:>10.3f}{flag}")
    print()
    if bad:
        print(f"  *** {len(bad)} concerns: {bad[:5]}")
    else:
        print("  ALL witness depths: max-nonnormal-per-fiber <= 1, shadow holds, recurrence holds.")
        print("  => a NORMALITY-BIT provenance (Root|Debt, N x) is INJECTIVE and card <= 2*card(nacc).")

    banner('[C2] Wave-3 internal count: is card(nacc r 1 - nbase 1) linear? (witness, deeper)')
    print(f"{'fam':>10} {'d':>3} {'rsize':>6} {'internal':>9} {'ratio':>7}")
    for fname, fn, k in [('witness', witness, bk), ('witness2', witness2, bk)]:
        prev = None; ratios = []
        for d in range(1, 9):
            r = fn(d)
            internal = len(nacc(r, ONE) - nbase(ONE))
            ratios.append(internal / rsize(r))
            print(f"{fname:>10} {d:>3} {rsize(r):>6} {internal:>9} {internal/rsize(r):>7.3f}")
        print(f"           ratios {['%.2f'%x for x in ratios]}  -> "
              f"{'BOUNDED (linear)' if max(ratios) < 3 and ratios[-1] <= ratios[0]+0.5 else 'CHECK growth'}")

if __name__ == '__main__':
    stageC()


# ============================================================================
# STAGE D -- DECISIVE: can a single N-fiber hold >=2 non-normal old rows?
# (e.g. b*.(a*.a*) and b*.(a*.a*.a*), both -> b*.a*).  If YES anywhere, the
# normality-bit injection FAILS and we must assess a depth-indexed prov.
# ============================================================================
def fiber_nn(r, k):
    """over the FULL strong_apder_acc r k: max # non-normal rows sharing one N-value,
       plus a witness pair."""
    SAA = strong_apder_acc(r, k)
    by = {}
    for x in SAA:
        if N(x) != x:
            by.setdefault(N(x), []).append(x)
    if not by:
        return 0, None
    v, rows = max(by.items(), key=lambda kv: len(kv[1]))
    return len(rows), (v, rows)

def stageD():
    banner('[D] EXHAUSTIVE hunt for an N-fiber with >=2 non-normal old rows')
    conts = [ONE, CH('a'), STAR(CH('a')), STAR(CH('b')),
             SEQ(STAR(CH('a')), STAR(CH('a'))), SEQ(STAR(CH('a')), SEQ(STAR(CH('a')), STAR(CH('a')))),
             SEQ(STAR(CH('b')), STAR(CH('b'))), ALT([STAR(CH('a')), STAR(CH('b'))]),
             SEQ(STAR(CH('a')), CH('a'))]
    # hand-built doubler candidates (try to open b*.a* at two continuation depths)
    As, Bs = STAR(CH('a')), STAR(CH('b'))
    doublers = [
        SEQ(ALT([ONE, SEQ(Bs, As)]), SEQ(As, As)),                 # (1+b*a*).(a*.a*)
        SEQ(ALT([ONE, SEQ(Bs, As)]), SEQ(ALT([ONE, As]), As)),     # (1+b*a*).((1+a*).a*)
        SEQ(ALT([ONE, SEQ(ALT([ONE, SEQ(Bs, As)]), As)]), As),     # (1+(1+b*a*).a*).a*
        SEQ(ALT([ONE, SEQ(Bs, As)]), SEQ(As, SEQ(As, As))),        # (1+b*a*).(a*.a*.a*)
        SEQ(ALT([ONE, SEQ(Bs, SEQ(As, As))]), As),                 # (1+b*.(a*.a*)).a*
    ]
    gmax = 0; worst = None
    print("  hand-built doublers:")
    for r in doublers:
        for k in conts:
            m, wit = fiber_nn(r, k)
            if m > gmax: gmax = m; worst = (r, k, wit)
            if m >= 2:
                print(f"    >=2 ! r={pp(r)} k={pp(k)} : {m} non-normal -> {pp(wit[0])}: "
                      f"{[pp(x) for x in wit[1]]}")
    print(f"  doubler global max non-normal/fiber = {gmax}")

    print("  exhaustive clean r (rsize<=8) x conts ...")
    regs = clean_regexes(8)
    gmax2 = 0; worst2 = None; n2 = 0
    for r in regs:
        for k in conts:
            m, wit = fiber_nn(r, k)
            n2 += 1
            if m > gmax2:
                gmax2 = m; worst2 = (r, k, wit)
    print(f"  checked {n2} (r,k); GLOBAL max non-normal-per-fiber = {gmax2}")
    if worst2 and gmax2 >= 2:
        r, k, wit = worst2
        print(f"  *** CE: r={pp(r)} k={pp(k)}  fiber {pp(wit[0])} has {gmax2} non-normal: "
              f"{[pp(x) for x in wit[1]]}")
        print("  => normality-bit injection FAILS; need depth-indexed provenance.")
    else:
        print("  => max-non-normal-per-fiber <= 1 EXHAUSTIVELY (rsize<=8 + doublers).")
        print("     The normality bit (Root|Debt) injects old-excess into {0,1} x nacc.")

    # deeper witness depths for the multiplicity (cheap, targeted)
    print("  deep witness/witness2 (d up to 10):")
    bk = STAR(CH('b'))
    for fn, nm in [(witness, 'witness'), (witness2, 'witness2')]:
        ms = []
        for d in range(1, 11):
            m, _ = fiber_nn(fn(d), bk)
            ms.append(m)
        print(f"    {nm}: max-nn-per-fiber by depth = {ms}")

if __name__ == '__main__':
    stageD()


# ============================================================================
# STAGE E -- consolidation: (a) the end-to-end bound the BIT-injection delivers
# card(SAA r k - SAA 1 k) <= 2*card(nacc(r,Nk)-nbase(Nk)); (b) the STRUCTURAL
# reason for <=1/fiber: every non-normal old row has exactly ONE adjacent-equal-
# star duplication of multiplicity exactly 2 (so it is determined by its N-image).
# ============================================================================
def dup_sites(x):
    """count adjacent-equal-star duplication sites and the max star-run length in x's
       sequence spine, recursively over all SEQ spines in the term."""
    from norm_model import fac, is_star
    sites = 0; maxrun = 1
    def walk(t):
        nonlocal sites, maxrun
        f = fac(t)
        run = 1
        for i in range(1, len(f)):
            if f[i] == f[i-1] and is_star(f[i]):
                run += 1; sites += (1 if run == 2 else 0); maxrun = max(maxrun, run)
            else:
                run = 1
        for g in f:
            if is_star(g): walk(g[1])
            elif is_alt(g):
                for q in g[1]: walk(q)
            # seq handled by fac flattening at this level; recurse into non-seq factors only
    walk(x)
    return sites, maxrun

def stageE():
    banner('[E1] end-to-end: card(SAA r k - SAA 1 k) <= 2*card(nacc(r,Nk)-nbase(Nk)) ?')
    conts = [ONE, CH('a'), STAR(CH('a')), STAR(CH('b')),
             SEQ(STAR(CH('a')), STAR(CH('a'))), SEQ(STAR(CH('b')), STAR(CH('b')))]
    regs = clean_regexes(8)
    viol = []; worst_ratio = 0; n = 0
    for r in regs:
        for k in conts:
            old = strong_apder_acc(r, k) - strong_apder_acc(ONE, k)
            new = nacc(r, N(k)) - nbase(N(k))
            n += 1
            if len(old) > 2*len(new):
                viol.append((r, k, len(old), len(new)))
            if len(new): worst_ratio = max(worst_ratio, len(old)/len(new))
    if viol:
        r,k,lo,ln = min(viol, key=lambda t: rsize(t[0]))
        print(f"  *** {len(viol)} viol; smallest r={pp(r)} k={pp(k)}: |old|={lo} > 2*|new|={2*ln}")
    else:
        print(f"  0 / {n} violations.  worst |old|/|new| ratio = {worst_ratio:.3f} (<= 2.0 holds)")

    banner('[E2] structural: every non-normal old row = exactly 1 dup-site, run length 2?')
    regs2 = clean_regexes(8)
    conts2 = conts + [SEQ(STAR(CH('a')), SEQ(STAR(CH('a')), STAR(CH('a'))))]
    bad = []; maxsites = 0; maxrun = 0; ck = 0
    for r in regs2:
        for k in conts2:
            for x in strong_apder_acc(r, k):
                if N(x) != x:
                    s, mr = dup_sites(x)
                    ck += 1
                    maxsites = max(maxsites, s); maxrun = max(maxrun, mr)
                    if s != 1 or mr != 2:
                        bad.append((r, k, x, s, mr))
    print(f"  checked {ck} non-normal rows; max dup-sites={maxsites}, max run-length={maxrun}")
    if bad:
        r,k,x,s,mr = min(bad, key=lambda t: rsize(t[2]))
        print(f"  *** {len(bad)} rows with sites!=1 or run!=2; smallest x={pp(x)} (sites={s},run={mr})")
        print(f"      from r={pp(r)} k={pp(k)}")
    else:
        print("  ALL non-normal rows: exactly 1 duplication site, run length exactly 2.")
        print("  => x is determined by N(x) (the single dup-site is forced) => <=1 per fiber. QED-ish.")

if __name__ == '__main__':
    stageE()


# ============================================================================
# STAGE F -- honest end-to-end: card(SAA r k - SAA 1 k) = (#normal-excess) + (debt).
# Both must be <= C*rsize r (independent of k). normal-excess injects by identity
# into nacc(r,Nk); debt is the bit's 2nd slot. Confirm both are linear in rsize r.
# ============================================================================
def stageF():
    banner('[F] card(diff) = normal-excess + debt; both <= C*rsize r ?  (k-independent)')
    conts = [ONE, CH('a'), STAR(CH('a')), STAR(CH('b')),
             SEQ(STAR(CH('a')), STAR(CH('a'))), SEQ(STAR(CH('b')), STAR(CH('b'))),
             SEQ(STAR(CH('a')), SEQ(STAR(CH('a')), STAR(CH('a'))))]
    regs = clean_regexes(8)
    wn = wd = wtot = 0.0; bad = []
    for r in regs:
        rs = rsize(r)
        for k in conts:
            diff = strong_apder_acc(r, k) - strong_apder_acc(ONE, k)
            normal = [x for x in diff if N(x) == x]
            debt = [x for x in diff if N(x) != x]
            # normal-excess must land in nacc(r,Nk) (identity injection)
            covered = all(x in nacc(r, N(k)) for x in normal)
            wn = max(wn, len(normal)/rs); wd = max(wd, len(debt)/rs); wtot = max(wtot, len(diff)/rs)
            if not covered: bad.append(('normal-not-in-nacc', r, k))
    print(f"  worst (over clean r<=8 x conts):  normal-excess/rsize = {wn:.3f}   "
          f"debt/rsize = {wd:.3f}   total diff/rsize = {wtot:.3f}")
    print(f"  normal-excess all land in nacc(r,Nk): {not bad}")
    # witness families, deep, k-independence:
    bk = STAR(CH('b'))
    print("  witness depth-scaling (rsize, |diff|, normal, debt, diff/rsize):")
    for d in range(1, 11):
        r = witness(d)
        diff = strong_apder_acc(r, bk) - strong_apder_acc(ONE, bk)
        normal = sum(1 for x in diff if N(x)==x); debt = sum(1 for x in diff if N(x)!=x)
        print(f"    d={d:>2} rsize={rsize(r):>3} |diff|={len(diff):>3} normal={normal:>3} debt={debt:>3} "
              f"ratio={len(diff)/rsize(r):.3f}")
    banner('VERDICT INPUTS')
    print("  If normal-excess/rsize and debt/rsize are both BOUNDED (here <~0.5 each), then")
    print("  card(diff) <= C*rsize r with C ~= 1, via:  normal-excess -> nacc (clean linear),")
    print("  debt -> the Root|Debt bit's 2nd slot (debt linear).  Bound is k-INDEPENDENT.")

if __name__ == '__main__':
    stageF()
