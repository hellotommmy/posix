# Row-count (D law) checker: mirror of apder_term_frontier_acc etc.
# Usage: python scratch_rowcount_check.py [samples]
# Validates the OPEN law card(acc r k - F k) <= zwidth r on random nf
# terms, and asserts all FALSIFIED strengthenings stay falsified by
# their recorded counterexamples.  See MATHPROBLEM_ROWCOUNT.md.
import sys, random
sys.setrecursionlimit(1000000)

Z = ('Z',); O = ('O',)
def C(ch): return ('C', ch)
def SEQ(a, b): return ('SEQ', a, b)
def ALTS(rs): return ('ALTS', tuple(rs))
def STAR(r): return ('STAR', r)

def rsimp4(r1, r2):
    if r1 == Z: return Z
    if r1 == O: return r2
    if r1[0] == 'SEQ': return rsimp4(r1[1], rsimp4(r1[2], r2))
    if r2 == Z: return Z
    if r2 == O: return r1
    return SEQ(r1, r2)

def rfrontier(r):
    if r == Z: return set()
    if r[0] == 'ALTS':
        out = set()
        for q in r[1]: out |= rfrontier(q)
        return out
    return {r}

def acc(r, k):
    t = r[0]
    if t in ('Z', 'O'): return set()
    if t == 'C': return rfrontier(k)
    if t == 'ALTS':
        out = set()
        for q in r[1]: out |= acc(q, k)
        return out
    if t == 'SEQ':
        return acc(r[1], rsimp4(r[2], k)) | acc(r[2], k)
    if t == 'STAR':
        return acc(r[1], rsimp4(r, k))
    raise ValueError(t)

def zwidth(r):
    t = r[0]
    if t in ('Z', 'O'): return 0
    if t == 'C': return 1
    if t == 'ALTS': return sum(zwidth(q) for q in r[1])
    if t == 'SEQ': return zwidth(r[1]) + zwidth(r[2])
    if t == 'STAR': return max(1, zwidth(r[1]))
    raise ValueError(t)

def nf(r):
    t = r[0]
    if t in ('Z', 'O', 'C'): return True
    if t == 'ALTS':
        return all(nf(q) and q[0] != 'ALTS' and q != Z for q in r[1])
    if t == 'SEQ':
        return (nf(r[1]) and nf(r[2]) and r[1][0] != 'SEQ'
                and r[1] not in (Z, O) and r[2] not in (Z, O))
    if t == 'STAR': return nf(r[1])
    return True

def rand_re(depth, rng):
    if depth == 0:
        return rng.choice([C(rng.choice('ab')), O])
    t = rng.randrange(6)
    if t == 0: return C(rng.choice('ab'))
    if t == 1: return SEQ(rand_re(depth-1, rng), rand_re(depth-1, rng))
    if t == 2: return ALTS([rand_re(depth-1, rng)
                            for _ in range(rng.randrange(2, 4))])
    if t == 3: return STAR(rand_re(depth-1, rng))
    if t == 4: return STAR(O)
    return C(rng.choice('ab'))

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    rng = random.Random(101)
    viol = 0; tested = 0
    for _ in range(n):
        r = rand_re(rng.randrange(1, 5), rng)
        k = rand_re(rng.randrange(0, 3), rng)
        if not (nf(r) and nf(k)): continue
        tested += 1
        if len(acc(r, k) - rfrontier(k)) > zwidth(r):
            viol += 1
            print("VIOLATION:", r, k)
    print(f"D law: tested={tested} violations={viol}")

    # falsified strengthenings stay falsified
    a = C('a')
    ce_r = SEQ(a, ALTS([a, STAR(STAR(a))]))
    A = acc(ce_r, O); Fk = rfrontier(O)
    d = len(A - Fk); z = zwidth(ce_r)
    assert d == z == 3, (d, z)
    assert Fk and Fk <= A, "subset-discount CE shape changed"
    print("falsified-strengthening CE intact: D+ overdraws at", d, "=", z)

    ce2 = SEQ(C('b'), ALTS([a, STAR(O), STAR(STAR(O))]))
    def awidth(r):
        t = r[0]
        if t in ('Z', 'O'): return 0
        if t == 'C': return 1
        if t == 'ALTS': return sum(awidth(q) for q in r[1])
        if t == 'SEQ': return awidth(r[1]) + awidth(r[2])
        if t == 'STAR': return awidth(r[1])
    d2 = len(acc(ce2, O) - rfrontier(O))
    assert d2 > awidth(ce2), "awidth CE changed"
    print("awidth-law CE intact:", d2, ">", awidth(ce2))

if __name__ == "__main__":
    main()