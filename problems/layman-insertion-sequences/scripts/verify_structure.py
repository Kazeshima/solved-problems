# Exact check of the structure theorem: the tree of pairs (U, V), the plateaus [fix(UV), fix(VU)],
# the twin point s, and the two itineraries.  Words are written in time order over {R, L}:
#   R: t -> t + 1   (an insertion; taken when t <= theta)
#   L: t -> t/(1+t) (a term settles; taken when t > theta)
# Everything is exact (integers and Fractions).  usage: python verify_structure.py [max word length]
import sys
from fractions import Fraction as Fr
from math import isqrt

MAT = {'R': (1, 0, 1, 1), 'L': (1, 1, 0, 1)}   # acting on columns (X, Y): R: Y += X ; L: X += Y

def mat(word):                                  # matrix of the word, letters applied left to right
    a, b, c, d = 1, 0, 0, 1
    for ch in word:
        e, f, g, h = MAT[ch]
        a, b, c, d = e * a + f * c, e * b + f * d, g * a + h * c, g * b + h * d
    return a, b, c, d

def apply(word, t):                             # t = Y/X
    a, b, c, d = mat(word)
    return (c + d * t) / (a + b * t)

def side_of_fix(word, theta):
    """sign of theta - fix(word), fix = attracting fixed point in (0, oo) of t -> (c + d t)/(a + b t)."""
    a, b, c, d = mat(word)
    val = b * theta * theta + (a - d) * theta - c    # b t^2 + (a-d) t - c vanishes at the fixed point
    return (val > 0) - (val < 0)

def fix_approx(word, den):
    """rationals just below and just above the fixed point, within 2/den."""
    a, b, c, d = mat(word)
    disc = (a - d) ** 2 + 4 * b * c
    r = isqrt(disc * den * den)
    lo = Fr((d - a) * den + r - 1, 2 * b * den)
    hi = Fr((d - a) * den + r + 2, 2 * b * den)
    assert side_of_fix(word, lo) < 0 < side_of_fix(word, hi)
    return lo, hi

def itinerary(theta, n):
    X, Y, w, out = 1, 1, [], []
    P, Q = theta.numerator, theta.denominator
    while len(w) < n:
        if Q * Y <= P * X:
            Y += X; w.append('R')
        else:
            out.append(X); X += Y; w.append('L')
    return ''.join(w), out

def check(U, V, s, pre, maxlen, stats):
    W = U + V
    if len(W) > maxlen:
        return
    a, b, c, d = mat(W)
    C, D = a + d, W.count('L')
    n = 6 * len(W) + len(pre) + 8
    den = 10 ** 30
    lo_in = fix_approx(U + V, den)[1]            # just above fix(UV): inside the plateau
    lo_out = fix_approx(U + V, den)[0]
    hi_in = fix_approx(V + U, den)[0]            # just below fix(VU): inside
    hi_out = fix_approx(V + U, den)[1]
    assert lo_in < s <= hi_in, (U, V, s)         # the twin point is inside the plateau
    lowW = (pre + (V + U) * n)[:n]               # theta < s : start is to the right of the cut
    highW = (pre + (U + V) * n)[:n]              # theta >= s
    eps = Fr(1, 10 ** 25)
    for th, want in ((lo_in, lowW), (s - eps, lowW), ((lo_in + s) / 2, lowW),
                     (s, highW), (s + eps, highW), ((s + hi_in) / 2, highW), (hi_in, highW)):
        w, out = itinerary(th, n)
        assert w == want, (U, V, th)
        assert all(out[i + 2 * D] + out[i] == C * out[i + D] for i in range(len(out) - 2 * D)), (U, V)
    # outside the plateau the itinerary is a different one (the difference shows after about
    # log(1/distance) periods, so use a coarser distance and a longer run)
    n2 = 60 * len(W) + len(pre) + 400
    for th in (fix_approx(U + V, 10 ** 8)[0], fix_approx(V + U, 10 ** 8)[1]):
        if th > 0:
            w, _ = itinerary(th, n2)
            assert w != (pre + (V + U) * n2)[:n2] and w != (pre + (U + V) * n2)[:n2], (U, V, 'outside')
    key = (C, D)
    assert key not in stats['types'], ('two tree nodes with the same type', key)
    stats['types'][key] = W
    stats['nodes'] += 1
    # Layman's rule: trace(child) = trace(parent pair product) - trace(unused parent)
    tU, tV, tW = sum(mat(U)[::3]), sum(mat(V)[::3]), C
    assert sum(mat(U + V + V)[::3]) == tW * tV - tU and sum(mat(U + V + U)[::3]) == tW * tU - tV
    # children: theta < fix(UV) -> (UV, V), start moves by V ; theta > fix(VU) -> (U, VU), start moves by U
    check(U + V, V, apply(V, s), pre + V, maxlen, stats)
    check(U, V + U, apply(U, s), pre + U, maxlen, stats)

if __name__ == '__main__':
    maxlen = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    stats = {'nodes': 0, 'types': {}}
    check('R', 'L', Fr(1), '', maxlen, stats)
    print('pairs (U, V) with |UV| <= %d: %d checked' % (maxlen, stats['nodes']))
    print('for each: twin point inside the plateau; itinerary of the start equals prefix.(VU)^oo below the twin point')
    print('          and prefix.(UV)^oo from it on, at 7 exact ratios; recurrence type (trace, #L); a different')
    print('          itinerary just outside [fix(UV), fix(VU)]; all types distinct; Layman rule for both children')
    by = sorted(stats['types'].items(), key=lambda kv: (kv[0][1], kv[0][0]))
    print('types with D <= 4:', [k for k, _ in by if k[1] <= 4])
    print('ALL OK')
