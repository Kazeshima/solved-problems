# The exceptional set E: explicit ratios whose insertion sequence satisfies no recurrence.
#
# A point theta of E is given by an infinite path in the tree of pairs (U, V) that makes both kinds of step
# infinitely often: kind 1 is (U, V) -> (UV, V), taken when theta < fix(UV); kind 3 is (U, V) -> (U, VU), taken
# when theta > fix(VU).  For a periodic pattern of kinds this script
#   (1) computes the orbit points s_n of the start, which bound theta from both sides,
#   (2) confirms with exact rational arithmetic that every theta between the bounds follows the path
#       (all computed steps but the last two or three, which the bounds are not yet fine enough to decide),
#   (3) confirms that the itinerary read off the path is the one obtained by running the process,
#   (4) lists the insertion sequence and tests every recurrence a(n+2D) = C a(n+D) - a(n) with D <= Dmax.
# Step (4) is evidence only: the proof that no recurrence holds is in PROOF.md, section 7.
import sys
from fractions import Fraction as Fr

R, L = (1, 0, 1, 1), (1, 1, 0, 1)            # (a, b, c, d) stands for X' = aX + bY, Y' = cX + dY

def then(M, N):
    """the matrix of 'first M, then N'"""
    a, b, c, d = M
    e, f, g, h = N
    return (e * a + f * c, e * b + f * d, g * a + h * c, g * b + h * d)

def act(M, t):
    a, b, c, d = M
    return (c + d * t) / (a + b * t)

def follow(pattern, depth, wordlen):
    """nodes of the path, bounds lo < theta < hi, and the first letters of the itinerary of the start"""
    MU, MV, U, V = R, L, 'R', 'L'
    s, lo, hi, itin, nodes = Fr(1), None, None, '', []
    for n in range(depth):
        kind = pattern[n % len(pattern)]
        nodes.append((MU, MV, kind))
        if kind == 1:                         # the orbit point s is to the right of theta and moves by V
            hi = s if hi is None else min(hi, s)
            s = act(MV, s)
            if V is not None and len(itin) < wordlen:
                itin += V
            MU = then(MU, MV)
            U = U + V if U is not None and V is not None and len(U) + len(V) <= wordlen else None
        else:                                 # the orbit point s is to the left of theta and moves by U
            lo = s if lo is None else max(lo, s)
            s = act(MU, s)
            if U is not None and len(itin) < wordlen:
                itin += U
            MV = then(MV, MU)
            V = V + U if U is not None and V is not None and len(U) + len(V) <= wordlen else None
    return nodes, lo, hi, itin

def depth_followed(nodes, th):
    """number of nodes of the path at which th is in the prescribed case"""
    for n, (MU, MV, kind) in enumerate(nodes):
        vu, uv = act(then(MU, MV), th), act(then(MV, MU), th)     # v(u(th)) and u(v(th))
        if not (vu < uv and (th < vu if kind == 1 else th > uv)):
            return n
    return len(nodes)

def simulate(lo, hi, nmax):
    """run the process for an unknown theta in (lo, hi); stop when a comparison cannot be decided"""
    X, Y, w, out = 1, 1, [], [1]
    while len(w) < nmax:
        if Y * lo.denominator <= lo.numerator * X:        # Y/X <= lo < theta
            Y += X
            w.append('R')
        elif Y * hi.denominator >= hi.numerator * X:      # Y/X >= hi > theta
            X += Y
            out.append(X)
            w.append('L')
        else:
            break
    return ''.join(w), out

def longest_run(a, D, start):
    """longest stretch of consecutive n >= start with a(n+2D) + a(n) = C a(n+D) for one integer C"""
    best = run = 0
    prev = None
    for n in range(start, len(a) - 2 * D):
        q, r = divmod(a[n + 2 * D] + a[n], a[n + D])
        C = q if r == 0 else None
        run = run + 1 if C is not None and C == prev else (1 if C is not None else 0)
        prev = C
        best = max(best, run)
    return best

def digits(x, n):
    return '%d.%s' % (x.numerator // x.denominator, str((x.numerator % x.denominator) * 10 ** n // x.denominator).zfill(n))

if __name__ == '__main__':
    depth = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    wordlen = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
    Dmax = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    ok = True
    for pattern in ((1, 3), (3, 1), (1, 1, 3), (1, 3, 3), (1, 3, 3, 1, 3)):
        nodes, lo, hi, itin = follow(pattern, depth, wordlen)
        assert 0 < lo < hi
        dl, dh = depth_followed(nodes, lo), depth_followed(nodes, hi)
        w, a = simulate(lo, hi, len(itin))
        same = (w == itin[:len(w)]) and len(w) == len(itin)
        gap = hi - lo
        agree = 0
        while gap * 10 ** (agree + 1) < 1:
            agree += 1
        k_lo, k_hi = 1 / (1 + hi), 1 / (1 + lo)
        T = len(a)
        runs = [longest_run(a, D, T // 2) for D in range(1, Dmax + 1)]
        window = [T - 2 * D - T // 2 for D in range(1, Dmax + 1)]
        norec = all(r < n for r, n in zip(runs, window))
        print('pattern of steps %s repeated' % (pattern,))
        print('  theta = %s...   k = 1/(1+theta) = %s...   (bounds agree to %d digits)'
              % (digits(lo, min(agree, 40)), digits(k_lo, min(agree, 40)), agree))
        print('  every theta between the bounds follows the path for the first %d of %d steps' % (min(dl, dh), depth))
        print('  itinerary from the path = itinerary of the process on the first %d moves: %s' % (len(w), same))
        print('  first terms:', a[:14])
        print('  %d terms; for each D <= %d the relation a(n+2D) + a(n) = C a(n+D) fails for some n in the second half: %s'
              % (T, Dmax, norec))
        print('  longest stretch on which one relation holds: %d consecutive n (D = %d)'
              % (max(runs), runs.index(max(runs)) + 1))
        ok &= same and norec and min(dl, dh) >= depth - 3 and digits(k_lo, 30) == digits(k_hi, 30)
    print('ALL OK' if ok else 'FAILURE')
    sys.exit(0 if ok else 1)
