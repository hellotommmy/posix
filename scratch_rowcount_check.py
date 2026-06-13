# Row-count (D law) and opened-boundary checker.
# Usage:
#   python scratch_rowcount_check.py [samples]
#   python scratch_rowcount_check.py opened [samples] [max_depth]
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

def rsimp7(r1, r2):
    if r1[0] == 'STAR' and r2[0] == 'STAR' and r1[1] == r2[1]:
        return r1
    if (r1[0] == 'STAR' and r2[0] == 'SEQ'
            and r2[1][0] == 'STAR' and r1[1] == r2[1][1]):
        return SEQ(r1, r2[2])
    return rsimp4(r1, r2)

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

def rsize(r):
    t = r[0]
    if t in ('Z', 'O', 'C'): return 1
    if t == 'ALTS': return 1 + sum(rsize(q) for q in r[1])
    if t == 'SEQ': return 1 + rsize(r[1]) + rsize(r[2])
    if t == 'STAR': return 1 + rsize(r[1])
    raise ValueError(t)

def zw2(r):
    t = r[0]
    if t in ('Z', 'O'): return 0
    if t == 'C': return 1
    if t == 'ALTS': return sum(zw2(q) for q in r[1])
    if t == 'SEQ': return zw2(r[1]) + zw2(r[2])
    if t == 'STAR': return 1 + zw2(r[1])
    raise ValueError(t)

def zwidth(r):
    t = r[0]
    if t in ('Z', 'O'): return 0
    if t == 'C': return 1
    if t == 'ALTS': return sum(zwidth(q) for q in r[1])
    if t == 'SEQ': return zwidth(r[1]) + zwidth(r[2])
    if t == 'STAR': return max(1, zwidth(r[1]))
    raise ValueError(t)

def open_pot(r):
    t = r[0]
    if t in ('Z', 'O'): return 0
    if t == 'C': return 2
    if t == 'ALTS': return sum(open_pot(q) for q in r[1])
    if t == 'SEQ':
        return open_pot(r[1]) + open_pot(r[2]) + zw2(r[1]) * (rsize(r[2]) + 2)
    if t == 'STAR':
        return open_pot(r[1]) + (zw2(r[1]) + 1) * (rsize(r) + 2)
    raise ValueError(t)

def row_dlforms(r):
    t = r[0]
    if t == 'Z':
        return set()
    if t == 'ALTS':
        out = set()
        for q in r[1]: out |= row_dlforms(q)
        return out
    if t == 'SEQ' and r[1][0] == 'ALTS':
        out = set()
        for q in r[1][1]: out |= row_dlforms(rsimp7(q, r[2]))
        return out
    return rfrontier(r)

def row_dlformss(rows):
    out = set()
    for q in rows: out |= row_dlforms(q)
    return out

def rsize_set(rows):
    return sum(rsize(q) for q in rows)

def odfront(k):
    return row_dlformss(rfrontier(k))

def opened_boundary_forms(r, k):
    carrier_rows = rfrontier(rsimp4(r, k)) | acc(r, k)
    return row_dlformss(carrier_rows) - odfront(k)

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

def nonzero_nonone(r):
    return r not in (Z, O)

def nonseq(r):
    return r[0] != 'SEQ'

def nonalt(r):
    return r[0] != 'ALTS'

def zbt(r):
    t = r[0]
    if t in ('Z', 'O', 'C'): return True
    if t == 'ALTS':
        return zw2(r) != 0 and all(zbt(q) for q in r[1])
    if t == 'SEQ':
        return zbt(r[1]) and zbt(r[2])
    if t == 'STAR':
        return zbt(r[1])
    return False

def clean(r):
    return nf(r) and zbt(r)

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

def rand_clean(depth, rng, *, allow_zero_one=True, allow_seq=True, allow_alt=True):
    if depth <= 0:
        atoms = [C(rng.choice('abc'))]
        if allow_zero_one:
            atoms += [O, Z]
        return rng.choice(atoms)

    choices = ['C', 'STAR']
    if allow_zero_one:
        choices += ['O', 'Z']
    if allow_seq:
        choices.append('SEQ')
    if allow_alt:
        choices.append('ALTS')
    t = rng.choice(choices)

    if t == 'C':
        return C(rng.choice('abc'))
    if t == 'O':
        return O
    if t == 'Z':
        return Z
    if t == 'STAR':
        return STAR(rand_clean(depth - 1, rng, allow_zero_one=True))
    if t == 'SEQ':
        left = rand_clean(
            depth - 1, rng, allow_zero_one=False, allow_seq=False, allow_alt=True)
        right = rand_clean(depth - 1, rng, allow_zero_one=False)
        return SEQ(left, right)
    if t == 'ALTS':
        n = rng.randrange(2, 5)
        rows = []
        has_positive = False
        for _ in range(n):
            q = rand_clean(
                depth - 1, rng, allow_zero_one=True, allow_seq=True, allow_alt=False)
            if q == Z:
                q = O
            rows.append(q)
            has_positive = has_positive or zw2(q) != 0
        if not has_positive:
            rows[rng.randrange(n)] = C(rng.choice('abc'))
        return ALTS(rows)
    raise AssertionError(t)

def ronepair_tower(n):
    tail = C('c')
    step_head = ALTS([O, C('a')])
    for _ in range(n):
        tail = SEQ(step_head, tail)
    return tail

def opened_check(samples=100000, max_depth=5, seed=20260614):
    rng = random.Random(seed)
    violations = []
    tested = 0
    worst_slack = None
    worst_cubic_slack = None
    max_seen_depth = 0

    explicit = [(ronepair_tower(n), C('b')) for n in range(max_depth + 1)]
    for item_no in range(samples + len(explicit)):
        if item_no < len(explicit):
            r, k = explicit[item_no]
            depth_seen = item_no
        else:
            depth_seen = rng.randrange(1, max_depth + 1)
            r = rand_clean(depth_seen, rng)
            k = rand_clean(rng.randrange(0, max_depth + 1), rng)
        if not (clean(r) and clean(k)):
            raise AssertionError(("generator produced non-clean term", r, k))
        tested += 1
        max_seen_depth = max(max_seen_depth, depth_seen)

        lhs = rsize_set(opened_boundary_forms(r, k))
        rhs = open_pot(r) + zw2(r) * (1 + rsize(k))
        cubic_lhs = open_pot(r) + zw2(r) * 2
        cubic_rhs = (rsize(r) + 3) ** 3
        slack = rhs - lhs
        cubic_slack = cubic_rhs - cubic_lhs
        if worst_slack is None or slack < worst_slack[0]:
            worst_slack = (slack, lhs, rhs, r, k)
        if worst_cubic_slack is None or cubic_slack < worst_cubic_slack[0]:
            worst_cubic_slack = (cubic_slack, cubic_lhs, cubic_rhs, r)
        if lhs > rhs or cubic_lhs > cubic_rhs:
            violations.append((lhs, rhs, cubic_lhs, cubic_rhs, r, k))
            print("OPENED VIOLATION:", violations[-1])
            break

    print(
        "opened-boundary:",
        f"tested={tested}",
        f"max_depth={max_seen_depth}",
        f"violations={len(violations)}")
    if worst_slack:
        slack, lhs, rhs, r, k = worst_slack
        print("tightest potential slack:", slack, "lhs=", lhs, "rhs=", rhs,
              "r=", r, "k=", k)
    if worst_cubic_slack:
        slack, lhs, rhs, r = worst_cubic_slack
        print("tightest cubic slack:", slack, "lhs=", lhs, "rhs=", rhs,
              "r=", r)
    return not violations

def jstar_check(samples=100000, seed=137):
    rng = random.Random(seed)
    v = 0; tested = 0; nz = 0
    for _ in range(samples):
        r1 = rand_re(rng.randrange(0, 4), rng)
        r2 = rand_re(rng.randrange(0, 4), rng)
        k = rand_re(rng.randrange(0, 3), rng)
        if not (nf(r1) and nf(r2) and nf(k)): continue
        if r1 in (Z, O) or r2 in (Z, O) or r1[0] == 'SEQ': continue
        tested += 1
        s4 = rsimp4(r2, k)
        A1 = acc(r1, s4); A2 = acc(r2, k)
        Fs = rfrontier(s4); Fk = rfrontier(k)
        t2 = len((A1 & Fs) - Fk - A2)
        if t2 > 0: nz += 1
        if len(A1 - Fs) + t2 + len(A2 - Fk) > zwidth(r1) + zwidth(r2):
            v += 1
            print("J* VIOLATION:", r1, r2, k)
    print(f"J*: tested={tested} nontrivial={nz} violations={v}")
    return v == 0
def main():
    if len(sys.argv) > 1 and sys.argv[1] == "opened":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
        d = int(sys.argv[3]) if len(sys.argv) > 3 else 5
        ok = opened_check(n, d)
        if not ok:
            sys.exit(1)
        return

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
    jstar_check(60000)

if __name__ == "__main__":
    main()
