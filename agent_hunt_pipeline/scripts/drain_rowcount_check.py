"""Depth-5 sampler for the verdict2 continuation-parametric drain invariant."""
import random
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

import scratch_rowcount_check as b  # noqa: E402

Z = b.Z
O = b.O
C = b.C
SEQ = b.SEQ
ALTS = b.ALTS
STAR = b.STAR


def rflts(rs):
    out = []
    for r in rs:
        if r == Z:
            continue
        if r[0] == "ALTS":
            out.extend(r[1])
        else:
            out.append(r)
    return out


def rdistinct(rs):
    seen, out = set(), []
    for r in rs:
        if r not in seen:
            seen.add(r)
            out.append(r)
    return out


def rsimp_ALTs(rs):
    if len(rs) == 0:
        return Z
    if len(rs) == 1:
        return rs[0]
    return ALTS(rs)


def rprune_eq_against(covered, rs):
    cov = set(covered)
    return [r for r in rs if r not in cov]


def rsimpStrong_prune_pair_raw(earlier, later):
    if (
        earlier[0] == "SEQ"
        and earlier[1][0] == "ALTS"
        and later[0] == "SEQ"
        and later[1][0] == "ALTS"
        and earlier[2] == later[2]
    ):
        return b.rsimp7(
            rsimp_ALTs(rprune_eq_against(earlier[1][1], list(later[1][1]))),
            later[2],
        )
    return later


def rsimpStrong_prune_against_rows_raw(seen, r):
    for x in seen:
        r = rsimpStrong_prune_pair_raw(x, r)
    return r


def rsimpStrong_prune_rows_raw(rs):
    seen, out = [], []
    for r in rs:
        r2 = rsimpStrong_prune_against_rows_raw(seen, r)
        out.append(r2)
        seen.insert(0, r2)
    return out


def rsimpStrong_ALTs_raw(rs):
    return rsimp_ALTs(rdistinct(rflts(rsimpStrong_prune_rows_raw(rs))))


def rsimpStrong_raw(r):
    t = r[0]
    if t in ("Z", "O", "C"):
        return r
    if t == "SEQ":
        return b.rsimp7(rsimpStrong_raw(r[1]), rsimpStrong_raw(r[2]))
    if t == "ALTS":
        return rsimpStrong_ALTs_raw(rflts([rsimpStrong_raw(q) for q in r[1]]))
    if t == "STAR":
        s = rsimpStrong_raw(r[1])
        if s in (Z, O):
            return O
        if s[0] == "STAR":
            return s
        return STAR(s)
    raise ValueError(t)


def rpath_continuations_acc(r, k):
    t = r[0]
    if t in ("Z", "O"):
        return set()
    if t == "C":
        return {k}
    if t == "ALTS":
        out = set()
        for q in r[1]:
            out |= rpath_continuations_acc(q, k)
        return out
    if t == "SEQ":
        return rpath_continuations_acc(r[1], b.rsimp4(r[2], k)) | rpath_continuations_acc(r[2], k)
    if t == "STAR":
        return rpath_continuations_acc(r[1], b.rsimp4(r, k))
    raise ValueError(t)


def partial_derivative_live_row_universe(r):
    paths = rpath_continuations_acc(r, O)
    out = {Z, O, r} | paths | b.rfrontier(r)
    for q in paths:
        out |= b.rfrontier(q)
    return out


def strong_opened_live(r):
    return b.row_dlformss(rsimpStrong_raw(q) for q in partial_derivative_live_row_universe(r))


def nseq(p, k):
    return rsimpStrong_raw(b.rsimp7(rsimpStrong_raw(p), rsimpStrong_raw(k)))


def strong_child_drain(p, k):
    return strong_opened_live(nseq(p, k)) - strong_opened_live(rsimpStrong_raw(k))


def drain_pot(r):
    return b.open_pot(r)


def drain_w(r):
    return b.zw2(r)


def drain_child_budget(p, k):
    return drain_pot(p) + drain_w(p) * (1 + b.rsize(k))


def directed_drain_cases(max_depth):
    a, bch, c = C("a"), C("b"), C("c")
    cases = [
        (STAR(ALTS([a])), O),
        (STAR(ALTS([STAR(a), O, bch])), STAR(ALTS([STAR(a), O, bch]))),
        (STAR(a), STAR(bch)),
        (SEQ(ALTS([O, a]), SEQ(ALTS([O, a]), c)), O),
        (SEQ(ALTS([O, a]), c), SEQ(ALTS([O, a]), c)),
        (STAR(STAR(a)), bch),
        (ALTS([STAR(a), O, bch]), STAR(ALTS([STAR(a), O, bch]))),
    ]
    cases.extend((b.ronepair_tower(n), bch) for n in range(max_depth + 1))
    return cases


def drain_check(samples=100000, max_depth=5, seed=20260614):
    rng = random.Random(seed)
    violations = []
    tested = 0
    max_seen_depth = 0
    worst_child_slack = None
    worst_cubic_slack = None

    explicit = directed_drain_cases(max_depth)
    for item_no in range(samples + len(explicit)):
        if item_no < len(explicit):
            raw_p, raw_k = explicit[item_no]
            depth_seen = max_depth
        else:
            depth_seen = rng.randrange(1, max_depth + 1)
            raw_p = b.rand_clean(depth_seen, rng)
            raw_k = b.rand_clean(rng.randrange(0, max_depth + 1), rng)

        p = rsimpStrong_raw(raw_p)
        k = rsimpStrong_raw(raw_k)
        if not (b.nf(p) and b.nf(k)):
            continue
        tested += 1
        max_seen_depth = max(max_seen_depth, depth_seen)

        lhs = b.rsize_set(strong_child_drain(p, k))
        rhs = drain_child_budget(p, k)
        child_slack = rhs - lhs
        if worst_child_slack is None or child_slack < worst_child_slack[0]:
            worst_child_slack = (child_slack, lhs, rhs, p, k, nseq(p, k))

        cubic_lhs = drain_pot(p)
        cubic_rhs = b.rsize(p) * (b.rsize(p) + 2) ** 2
        cubic_slack = cubic_rhs - cubic_lhs
        if worst_cubic_slack is None or cubic_slack < worst_cubic_slack[0]:
            worst_cubic_slack = (cubic_slack, cubic_lhs, cubic_rhs, p)

        if lhs > rhs or cubic_lhs > cubic_rhs:
            violations.append((lhs, rhs, cubic_lhs, cubic_rhs, p, k, nseq(p, k)))
            print("DRAIN VIOLATION:", violations[-1])
            break

    print(
        "drain-child:",
        f"tested={tested}",
        f"max_depth={max_seen_depth}",
        f"violations={len(violations)}",
    )
    if worst_child_slack:
        slack, lhs, rhs, p, k, nk = worst_child_slack
        print("tightest child slack:", slack, "lhs=", lhs, "rhs=", rhs, "p=", p, "k=", k, "nseq=", nk)
    if worst_cubic_slack:
        slack, lhs, rhs, p = worst_cubic_slack
        print("tightest cubic slack:", slack, "lhs=", lhs, "rhs=", rhs, "p=", p)
    return not violations


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 100000
    d = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    if not drain_check(n, d):
        sys.exit(1)


if __name__ == "__main__":
    main()
