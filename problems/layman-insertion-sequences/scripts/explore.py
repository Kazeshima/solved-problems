# Ratio-determined insertion sequences (Layman 2003): exploration.
from fractions import Fraction as Fr
import sys

def by_lists(k, stages, nterms):
    """Literal definition: S0=(1,1); insert a+b between a,b iff k*b <= a. Returns stable prefix."""
    S = [1, 1]
    for _ in range(stages):
        T = []
        for a, b in zip(S, S[1:]):
            T.append(a)
            if k * b <= a:
                T.append(a + b)
        T.append(S[-1])
        S = T[: 4 * nterms + 8] if len(T) > 4 * nterms + 8 else T
    return S[:nterms]

def by_process(k, nterms):
    """(X,Y) process: R if k*(X+Y) <= X else output X and L."""
    X, Y = 1, 1
    out, word = [], []
    while len(out) < nterms:
        if k * (X + Y) <= X:
            Y = X + Y; word.append('R')
        else:
            out.append(X); X = X + Y; word.append('L')
    return out, ''.join(word)

if __name__ == '__main__':
    ok = True
    for k in [Fr(1), Fr(1, 2), Fr(1, 3), Fr(7, 11), Fr(376, 1000), Fr(33344, 100000), Fr(62048, 100000),
              Fr(62528, 100000), Fr(75008, 100000), Fr(79136, 100000), Fr(79296, 100000), Fr(36704, 100000), Fr(264, 1000)]:
        a, w = by_process(k, 14)
        b = by_lists(k, 60, 14)
        same = (a == b)
        ok &= same
        print(float(k), a[:13], w[:40], 'lists agree' if same else 'MISMATCH %s' % b)
    print('ALL OK' if ok else 'SOME MISMATCH')
    sys.exit(0 if ok else 1)
