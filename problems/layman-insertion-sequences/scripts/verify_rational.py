# (1) Every rational ratio lies in a plateau: run the renormalization exactly for all theta = P/Q in a range,
#     and confirm the predicted itinerary and recurrence type by direct simulation.
# (2) Distinct plateaus have distinct types (C, D), also against powers of shorter period words.
import sys
from fractions import Fraction as Fr

MAT = {'R': (1, 0, 1, 1), 'L': (1, 1, 0, 1)}
def mat(word):
    a, b, c, d = 1, 0, 0, 1
    for ch in word:
        e, f, g, h = MAT[ch]
        a, b, c, d = e * a + f * c, e * b + f * d, g * a + h * c, g * b + h * d
    return a, b, c, d
def apply(word, t):
    a, b, c, d = mat(word)
    return (c + d * t) / (a + b * t)

def renormalize(theta, maxdepth=10**6):
    """returns (U, V, s, prefix, depth) for the node whose plateau contains theta."""
    U, V, s, pre = 'R', 'L', Fr(1), ''
    for depth in range(maxdepth):
        vu = apply(U + V, theta)     # first U, then V
        uv = apply(V + U, theta)
        assert vu < uv
        if theta < vu:
            s, pre = apply(V, s), pre + V
            U = U + V
        elif theta > uv:
            s, pre = apply(U, s), pre + U
            V = V + U
        else:
            return U, V, s, pre, depth
    raise RuntimeError('no plateau found')

def itinerary(theta, n):
    X, Y, w, out = 1, 1, [], []
    P, Q = theta.numerator, theta.denominator
    while len(w) < n:
        if Q * Y <= P * X:
            Y += X; w.append('R')
        else:
            out.append(X); X += Y; w.append('L')
    return ''.join(w), out

if __name__ == '__main__':
    maxden = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    count, maxdepth, maxlen = 0, 0, 0
    for Q in range(1, maxden + 1):
        for P in range(1, 4 * Q + 1):
            th = Fr(P, Q)
            if th.denominator != Q:
                continue
            U, V, s, pre, depth = renormalize(th)
            W = (V + U) if th < s else (U + V)
            n = len(pre) + 3 * len(W) + 5
            w, out = itinerary(th, n)
            assert w == (pre + W * n)[:n], th
            a, b, c, d = mat(U + V)
            C, D = a + d, (U + V).count('L')
            if len(out) > 2 * D:
                assert all(out[i + 2 * D] + out[i] == C * out[i + D] for i in range(len(out) - 2 * D)), th
            count += 1; maxdepth = max(maxdepth, depth); maxlen = max(maxlen, len(U + V))
    print('rational theta = P/Q with Q <= %d, 0 < theta <= 4: %d values, all in a plateau' % (maxden, count))
    print('  deepest node: depth %d; longest period word: %d letters' % (maxdepth, maxlen))

    # (2) collisions of types
    maxlen2 = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    words = []
    def descend(U, V):
        if len(U) + len(V) > maxlen2:
            return
        words.append(U + V)
        descend(U + V, V); descend(U, V + U)
    descend('R', 'L')
    types = {}
    for W in words:
        a, b, c, d = mat(W)
        types.setdefault((a + d, W.count('L')), []).append(W)
    coll = {k: v for k, v in types.items() if len(v) > 1}
    Dmax = max(k[1] for k in types)
    # powers: a sequence with period word z also satisfies the recurrence of type (trace(z^e), e*|z|_L)
    powcoll = 0
    for W in words:
        a, b, c, d = mat(W)
        t, D = a + d, W.count('L')
        prev, cur, e = 2, t, 1          # traces of powers: T_{e+1} = t*T_e - T_{e-1}
        while (e + 1) * D <= Dmax:
            prev, cur, e = cur, t * cur - prev, e + 1
            if (cur, e * D) in types:
                powcoll += 1
    print('period words of length <= %d: %d; pairs of plateaus with the same type: %d; coincidences with powers: %d'
          % (maxlen2, len(words), len(coll), powcoll))
    print('ALL OK' if not coll and powcoll == 0 else 'COLLISION FOUND')
    sys.exit(0 if not coll and powcoll == 0 else 1)
