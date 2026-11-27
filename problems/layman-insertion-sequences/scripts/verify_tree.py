# Layman's conjectures (C.3) and (C.5): exhaustive check of the recurrence tree down to a given period.
# Exact integer/rational arithmetic for the sequences; high-precision decimals only to locate sample ratios.
import sys
from fractions import Fraction as Fr
from decimal import Decimal as Dc, getcontext
getcontext().prec = 80

def rdis_theta(theta, n):
    """I(k) for k = 1/(1+theta), theta a Fraction; also the run lengths j."""
    P, Q = theta.numerator, theta.denominator
    X, Y, out, js = 1, 1, [], []
    for _ in range(n):
        out.append(X)
        # R while Y/X <= theta, i.e. Q*Y <= P*X
        j = (P * X - Q * Y) // (Q * X) + 1 if Q * Y <= P * X else 0
        js.append(j)
        Y += j * X
        X += Y
    return out, js

def trace(word):
    a, b, c, d = 1, 0, 0, 1
    for j in word:
        a, b, c, d = a + c, b + d, j * a + (j + 1) * c, j * b + (j + 1) * d
    assert a * d - b * c == 1
    return a + d

def cycle_points(word):
    """L-points T (values of Y/X at the moments a term settles) on the periodic orbit of the cyclic word."""
    T = Dc(1)
    pts = []
    for rep in range(400):
        for j in word:
            T = j + T / (1 + T)
            if rep == 399:
                pts.append(T)
    return pts

def to_fr(x, den=10**40):
    return Fr(int(x * den), den)

def has_type(a, C, D, start=0):
    return all(a[i + 2 * D] + a[i] == C * a[i + D] for i in range(start, len(a) - 2 * D))

def check_node(word, C_expected, stats):
    D = len(word)
    C = trace(word)
    assert C == C_expected, (word, C, C_expected)
    pts = cycle_points(word)
    lo, hi = max(pts) - 1, min(pts)          # predicted plateau [lo, hi) for theta
    assert hi > lo, word
    N = 4 * D + 12
    seqs = {}
    samples = 24
    for s in range(1, samples):
        th = to_fr(lo + (hi - lo) * s / samples)
        a, js = rdis_theta(th, N)
        assert has_type(a, C, D), (word, th)
        # run lengths are purely periodic after the first one, and are a rotation of the word
        tail = js[1:1 + D]
        assert any(tail == list(word[r:] + word[:r]) for r in range(D)), (word, tail)
        assert js[1:] == (tail * (N // D + 1))[:N - 1], (word, js)
        seqs.setdefault(tuple(a), []).append(s)
    assert len(seqs) == 2, (word, len(seqs))
    s1, s2 = sorted(seqs)
    assert s1[:D] == s2[:D] and s1[D] != s2[D], word      # twins: same first D terms, different (D+1)-th
    # each twin occupies a contiguous part of the plateau
    for v in seqs.values():
        assert v == list(range(v[0], v[-1] + 1)), word
    # just outside the plateau the type is different
    eps = (hi - lo) / 10**6
    for th in (to_fr(lo - eps), to_fr(hi + eps)):
        if th > 0:
            a, _ = rdis_theta(th, 6 * D + 40)
            assert not has_type(a, C, D, start=0), (word, 'outside')
    stats['nodes'] += 1
    return lo, hi, C

def descend(u, v, x, maxD, stats, types, n):
    """u < v are Farey neighbours (words); x is the word of the 'unused parent' of the pair's child."""
    w = u + v
    if len(w) > maxD:
        return
    C = trace(u) * trace(v) - trace(x)       # Layman's rule (L*R - X, l + r)
    lo, hi, C = check_node(w, C, stats)
    types[(C, len(w))] = (n, w)
    lu, hu = stats['plateau'][u]; lv, hv = stats['plateau'][v]
    assert hu < lo and hi < lv, (u, v)       # the child's ratios lie strictly between the parents'
    stats['plateau'][w] = (lo, hi)
    descend(u, w, v, maxD, stats, types, n)
    descend(w, v, u, maxD, stats, types, n)

if __name__ == '__main__':
    maxD = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    maxn = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    stats = {'nodes': 0, 'plateau': {}}
    types = {}
    for n in range(0, maxn + 1):
        for j in (n, n + 1):
            w = (j,)
            if w in stats['plateau']:
                continue
            if j == 0:
                # k = 1: no insertion is ever refused; type (2,1) occurs for theta = 0 only
                a, _ = rdis_theta(Fr(0), 30)
                assert a == list(range(1, 31)) and trace(w) == 2
                stats['plateau'][w] = (Dc(0), Dc(0)); types[(2, 1)] = (0, w)
            else:
                lo, hi, C = check_node(w, j + 2, stats)
                stats['plateau'][w] = (lo, hi); types[(C, 1)] = (n, w)
        # root child: trace(S_n S_{n+1}) = (n+2)(n+3) - 2, the "unused parent" being R with trace 2
        w = (n, n + 1)
        C = (n + 2) * (n + 3) - 2
        lo, hi, C = check_node(w, C, stats)
        types[(C, 2)] = (n, w)
        lu, hu = stats['plateau'][(n,)]; lv, hv = stats['plateau'][(n + 1,)]
        assert hu < lo and hi < lv
        stats['plateau'][w] = (lo, hi)
        descend((n,), w, (n + 1,), maxD, stats, types, n)
        descend(w, (n + 1,), (n,), maxD, stats, types, n)
    print('tree nodes checked (period <= %d, run lengths in {n, n+1}, n <= %d): %d' % (maxD, maxn, stats['nodes']))
    print('each: Layman rule for C, plateau located, 23 ratios inside all of type (C, D), run lengths purely periodic,')
    print('      exactly two sequences (same first D terms, different next term), type lost just outside, ordering of plateaus')
    # (C.5) second half on a grid: every ratio on the grid whose period is <= maxD has a type from the tree
    seen, missing = 0, 0
    for den in range(1, 36):
        for num in range(0, (maxn + 1) * den + 1):
            th = Fr(num, den)
            if th.denominator != den:
                continue
            a, js = rdis_theta(th, 8 * maxD + 30)
            tail = js[1:]
            Dfound = next((D for D in range(1, maxD + 1) if tail[:-D] == tail[D:]), None)
            if Dfound is None:
                continue
            seen += 1
            C = trace(tuple(tail[:Dfound]))
            if (C, Dfound) not in types or not has_type(a, C, Dfound):
                missing += 1
    print('grid ratios with period <= %d: %d, of which with a type outside the tree: %d' % (maxD, seen, missing))
    print('sample types:', sorted(types)[:24])
    print('ALL OK' if missing == 0 else 'FAILURE')
    sys.exit(0 if missing == 0 else 1)
