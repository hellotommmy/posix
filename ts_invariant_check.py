# ts_invariant_check.py
# INDEPENDENT adversarial sample-check of the GPT Pro T+S telescoping invariant
# (GPT_PRO_DLAW_VERDICT.md) and the four T/S bridge lemmas, on the clean
# legacy/rntimes-free fragment.  Written from scratch (NOT derived from
# scratch_rowcount_check.py) so it cross-checks Codex's Step-0 gate with a
# second, deeper, more targeted family set.  Mirror verified line-by-line vs:
#   rsimp4_SEQ_atom            BasicIdentities.thy:287          ==  s  (sigma)
#   rfrontier                  GeneralRegexBound.thy:3862       ==  F
#   apder_term_frontier_acc    AntimirovFactoredTransition.thy:1739 == A (acc)
#   apder_zw2                  AntimirovFactoredTransition.thy:28967 == W (STAR=Suc!)
#   apder_nf                   AntimirovFactoredTransition.thy:1791 (nonalt/rnonseq)
#   apder_zero_budget_trivial  AntimirovFactoredTransition.thy:30611 == zbt
# clean == legacy_rrexp & rntimes_free & apder_nf & apder_zero_budget_trivial;
# legacy & rntimes_free are automatically True on {Z,O,C,SEQ,ALTS,STAR}.
#
#   T(r,k): clean r --> clean k --> card((F (s r k) Un A r k) - F k) <= W r
#   S(r,k): clean r --> clean k --> 0 < W r --> Suc(card(A r k - F k)) <= W r
#
# Bridges sample-checked here too:
#   sigma_clean           : clean r & clean k -> clean (s r k)
#   sigma_RONE_id_nf      : apder_nf r -> s r RONE = r   (+ frontier version)
#   clean_zero_budget_root: clean r & W r = 0 -> r in {Z,O}
#   alts_positive_member  : clean(ALTS rs) & 0<W -> EX q in rs. 0<W q
import sys, random
sys.setrecursionlimit(1_000_000)

Z = ('Z',); O = ('O',)
def C(c):     return ('C', c)
def SEQ(a, b):return ('SEQ', a, b)
def ALTS(rs): return ('ALTS', tuple(rs))
def STAR(r):  return ('STAR', r)

# ---- faithful mirror of the Isabelle definitions --------------------------
def s(r1, r2):                       # rsimp4_SEQ_atom  (sigma)
    if r1 == Z: return Z
    if r1 == O: return r2
    if r1[0] == 'SEQ': return s(r1[1], s(r1[2], r2))
    if r2 == Z: return Z
    if r2 == O: return r1
    return SEQ(r1, r2)

def F(r):                            # rfrontier
    if r == Z: return set()
    if r[0] == 'ALTS':
        out = set()
        for q in r[1]: out |= F(q)
        return out
    return {r}

def A(r, k):                         # apder_term_frontier_acc
    t = r[0]
    if t in ('Z', 'O'): return set()
    if t == 'C': return F(k)
    if t == 'ALTS':
        out = set()
        for q in r[1]: out |= A(q, k)
        return out
    if t == 'SEQ': return A(r[1], s(r[2], k)) | A(r[2], k)
    if t == 'STAR': return A(r[1], s(r, k))
    raise ValueError(t)

def W(r):                            # apder_zw2  (corrected: STAR = Suc)
    t = r[0]
    if t in ('Z', 'O'): return 0
    if t == 'C': return 1
    if t == 'ALTS': return sum(W(q) for q in r[1])
    if t == 'SEQ': return W(r[1]) + W(r[2])
    if t == 'STAR': return 1 + W(r[1])
    raise ValueError(t)

def nf(r):                           # apder_nf
    t = r[0]
    if t in ('Z', 'O', 'C'): return True
    if t == 'ALTS':
        return all(nf(q) and q[0] != 'ALTS' and q != Z for q in r[1])
    if t == 'SEQ':
        return (nf(r[1]) and nf(r[2]) and r[1][0] != 'SEQ'
                and r[1] not in (Z, O) and r[2] not in (Z, O))
    if t == 'STAR': return nf(r[1])
    return True

def zbt(r):                          # apder_zero_budget_trivial
    t = r[0]
    if t in ('Z', 'O', 'C'): return True
    if t == 'ALTS': return W(r) != 0 and all(zbt(q) for q in r[1])
    if t == 'SEQ': return zbt(r[1]) and zbt(r[2])
    if t == 'STAR': return zbt(r[1])
    return False

def clean(r):                        # legacy & rntimes_free auto-True here
    return nf(r) and zbt(r)

def depth(r):
    t = r[0]
    if t in ('Z', 'O', 'C'): return 0
    if t == 'ALTS': return 1 + max(depth(q) for q in r[1])
    if t == 'SEQ': return 1 + max(depth(r[1]), depth(r[2]))
    if t == 'STAR': return 1 + depth(r[1])
    return 0

def subterms(r):
    yield r
    t = r[0]
    if t == 'ALTS':
        for q in r[1]: yield from subterms(q)
    elif t == 'SEQ':
        yield from subterms(r[1]); yield from subterms(r[2])
    elif t == 'STAR':
        yield from subterms(r[1])

# ---- invariant checks -----------------------------------------------------
class St:
    def __init__(self):
        self.T_tested = self.T_viol = self.T_tight = 0
        self.S_tested = self.S_viol = self.S_tight = 0
        self.T_minmargin = self.S_minmargin = 10**9
        self.maxdepth = 0; self.deep_pairs = 0
        self.examples = []
        # bridges
        self.sc_viol = []      # sigma_clean
        self.zr_viol = []      # clean_zero_budget_root
        self.ap_viol = []      # alts_positive_member
        self.ro_viol = []      # sigma_RONE_id_nf (identity)
        self.rof_viol = []     # sigma_RONE frontier version

def check_pair(r, k, st):
    dr = depth(r)
    st.maxdepth = max(st.maxdepth, dr, depth(k))
    if dr >= 5: st.deep_pairs += 1
    Fk = F(k); Ark = A(r, k); Wr = W(r)
    tc = len((F(s(r, k)) | Ark) - Fk)
    st.T_tested += 1
    if tc > Wr:
        st.T_viol += 1
        if len(st.examples) < 30: st.examples.append(('T', r, k, tc, Wr))
    else:
        st.T_minmargin = min(st.T_minmargin, Wr - tc)
        if Wr - tc == 0: st.T_tight += 1
    if Wr > 0:
        sc = len(Ark - Fk)
        st.S_tested += 1
        if sc + 1 > Wr:
            st.S_viol += 1
            if len(st.examples) < 30: st.examples.append(('S', r, k, sc, Wr))
        else:
            st.S_minmargin = min(st.S_minmargin, (Wr - 1) - sc)
            if (Wr - 1) - sc == 0: st.S_tight += 1

def check_bridges_single(r, st):
    # clean_zero_budget_root
    if clean(r) and W(r) == 0 and r not in (Z, O):
        st.zr_viol.append(r)
    # alts_positive_member
    if r[0] == 'ALTS' and clean(r) and W(r) > 0 and not any(W(q) > 0 for q in r[1]):
        st.ap_viol.append(r)
    # sigma_RONE_id_nf  (premise: apder_nf only)
    if nf(r):
        if s(r, O) != r: st.ro_viol.append((r, s(r, O)))
        if F(s(r, O)) != F(r): st.rof_viol.append((r, s(r, O)))

def check_sigma_clean(r, k, st):
    if clean(r) and clean(k) and not clean(s(r, k)):
        st.sc_viol.append((r, k, s(r, k)))

# ---- directed danger families --------------------------------------------
def tower(base, n):
    r = base
    for _ in range(n): r = STAR(r)
    return r

def seqchain(atoms):
    r = atoms[-1]
    for a in reversed(atoms[:-1]): r = SEQ(a, r)
    return r

a, b, cc, dd, ee = C('a'), C('b'), C('c'), C('d'), C('e')

def directed_r_pool():
    P = []
    for n in range(1, 11): P.append(tower(O, n))      # deep zero-width star towers
    for n in range(1, 9):  P.append(tower(a, n))      # deep char star towers
    for m in range(2, 6):
        P.append(ALTS([tower(O, i) for i in range(1, m + 1)]))   # wide alts of 0-width towers
        P.append(ALTS([tower(a, i) for i in range(1, m + 1)]))
    P.append(ALTS([a, b, tower(O, 3), tower(O, 4)]))
    P.append(ALTS([tower(a, 2), tower(O, 2), b]))
    P.append(ALTS([a, tower(O, 2), tower(STAR(O), 2)]))
    for L in range(2, 7):                              # singleton-continuation SEQ chains
        P.append(seqchain([C(chr(ord('a') + i)) for i in range(L)]))
    P.append(SEQ(a, ALTS([a, tower(a, 2)])))           # D+ overdraw witness
    P.append(SEQ(b, ALTS([a, STAR(O), tower(O, 2)])))  # awidth-CE relative
    P.append(SEQ(a, ALTS([tower(O, 2), tower(O, 3), b])))
    P.append(SEQ(a, SEQ(ALTS([tower(O, 2), b]), tower(O, 3))))
    P.append(STAR(ALTS([a, tower(O, 2)])))
    P.append(STAR(SEQ(a, tower(O, 2))))
    P.append(SEQ(tower(O, 2), seqchain([a, ALTS([a, b]), tower(O, 3)])))
    P.append(ALTS([seqchain([a, b, cc]), tower(O, 4), STAR(ALTS([a, tower(O, 2)]))]))
    P.append(SEQ(a, SEQ(b, SEQ(cc, SEQ(dd, ee)))))     # deep right SEQ tower
    P.append(STAR(STAR(SEQ(a, ALTS([b, tower(O, 2)])))))
    return P

def directed_k_pool():
    return [Z, O, a, cc,
            tower(O, 2), tower(O, 3), tower(O, 5),
            ALTS([a, b]), ALTS([tower(O, 2), cc]), ALTS([tower(O, 2), tower(O, 3)]),
            SEQ(cc, dd), tower(a, 2), seqchain([a, b, cc]),
            SEQ(a, ALTS([b, tower(O, 2)]))]

# directed nf-but-not-necessarily-clean cases for sigma_RONE_id_nf
DIRECTED_NF = [ALTS([O, O]), ALTS([O, O, O]), ALTS([O, C('a')]),
               ALTS([O, STAR(O)]), STAR(ALTS([O, O])),
               SEQ(C('a'), ALTS([O, O])), ALTS([STAR(O), O, C('a')])]

# ---- clean-by-construction random generator -------------------------------
def gc(d, rng, role='any'):
    # roles: any | nonZO | nonalt_nz (ALTS member) | seqleft
    if d <= 0:
        if role == 'any':       return rng.choice([Z, O, C('a'), C('b')])
        if role == 'nonZO':     return rng.choice([C('a'), C('b')])
        if role == 'nonalt_nz': return rng.choice([O, C('a'), C('b')])
        if role == 'seqleft':   return rng.choice([C('a'), C('b')])
    if role == 'nonalt_nz':
        ch = rng.choices(['STAR', 'SEQ', 'char', 'O'], weights=[4, 2, 2, 1])[0]
    elif role == 'seqleft':
        ch = rng.choices(['STAR', 'ALTS', 'char'], weights=[4, 3, 2])[0]
    elif role == 'nonZO':
        ch = rng.choices(['STAR', 'ALTS', 'SEQ', 'char'], weights=[4, 3, 3, 2])[0]
    else:  # any
        ch = rng.choices(['STAR', 'ALTS', 'SEQ', 'char', 'O', 'Z'],
                         weights=[4, 3, 3, 2, 1, 1])[0]
    if ch == 'char': return C(rng.choice('ab'))
    if ch == 'O':    return O
    if ch == 'Z':    return Z
    if ch == 'STAR': return STAR(gc(d - 1, rng, 'any'))      # STAR(O)/STAR(Z) wanted
    if ch == 'ALTS':
        n = rng.randint(2, 4)
        ms = [gc(d - 1, rng, 'nonalt_nz') for _ in range(n)]
        if all(W(m) == 0 for m in ms): ms[rng.randrange(n)] = C(rng.choice('ab'))
        return ALTS(tuple(ms))
    # SEQ
    return SEQ(gc(d - 1, rng, 'seqleft'), gc(d - 1, rng, 'nonZO'))

def run(nrandom=150000, seeds=(1, 2, 3, 7, 101)):
    st = St()
    # 1. directed grid
    R = [r for r in directed_r_pool()]
    K = [k for k in directed_k_pool()]
    rbad = [r for r in R if not clean(r)]
    if rbad:
        print("WARN: directed r-pool has non-clean members (skipped):", len(rbad))
    Rc = [r for r in R if clean(r)]
    Kc = [k for k in K if clean(k)]
    grid = 0
    for r in Rc:
        for x in subterms(r): check_bridges_single(x, st)
        for k in Kc:
            check_pair(r, k, st); check_sigma_clean(r, k, st); grid += 1
    for k in Kc:
        for x in subterms(k): check_bridges_single(x, st)
    for r in DIRECTED_NF:
        check_bridges_single(r, st)
    # 2. random clean samples
    rnd = 0
    for sd in seeds:
        rng = random.Random(sd)
        per = nrandom // len(seeds)
        for _ in range(per):
            r = gc(rng.randint(0, 8), rng, 'any')
            k = gc(rng.randint(0, 6), rng, 'any')
            if not (clean(r) and clean(k)):   # safety net (should not fire)
                continue
            check_pair(r, k, st); check_sigma_clean(r, k, st); rnd += 1
            for x in subterms(r): check_bridges_single(x, st)
    # ---- report ----
    print(f"directed grid pairs : {grid}")
    print(f"random clean pairs  : {rnd}")
    print(f"max depth tested    : {st.maxdepth}   (deep r>=5 pairs: {st.deep_pairs})")
    print(f"T: tested={st.T_tested} violations={st.T_viol} "
          f"min_margin={st.T_minmargin} tight(margin0)={st.T_tight}")
    print(f"S: tested={st.S_tested} violations={st.S_viol} "
          f"min_margin={st.S_minmargin} tight(margin0)={st.S_tight}")
    print(f"bridge sigma_clean            violations: {len(st.sc_viol)}")
    print(f"bridge sigma_RONE_id  (ident) violations: {len(st.ro_viol)}")
    print(f"bridge sigma_RONE     (frntr) violations: {len(st.rof_viol)}")
    print(f"bridge clean_zero_budget_root violations: {len(st.zr_viol)}")
    print(f"bridge alts_positive_member   violations: {len(st.ap_viol)}")
    for tag, lst in (('sigma_clean', st.sc_viol), ('RONE_id', st.ro_viol),
                     ('RONE_frontier', st.rof_viol), ('zero_root', st.zr_viol),
                     ('alts_pos', st.ap_viol)):
        for ex in lst[:5]:
            print(f"  {tag} CE: {ex}")
    for ex in st.examples[:10]:
        print("  T/S CE:", ex)
    ok = (st.T_viol == 0 and st.S_viol == 0 and not st.sc_viol and not st.ro_viol
          and not st.rof_viol and not st.zr_viol and not st.ap_viol
          and st.maxdepth >= 5)
    print("\nGATE RESULT:", "PASS" if ok else "FAIL")
    return ok

if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 150000
    sys.exit(0 if run(n) else 1)
