# Numerical check of every statement that is to be formalized (exact integer arithmetic).
import sys
from fractions import Fraction as Fr

def run_len(p, q, X, Y):
    return (q * X - p * (X + Y)) // (p * X) + 1 if p * (X + Y) <= q * X else 0

def rdis(p, q, n):
    X, Y, out = 1, 1, []
    for _ in range(n):
        out.append(X)
        Y = Y + run_len(p, q, X, Y) * X
        X = X + Y
    return out

def rec_ok(a, C, D):
    return all(a[i + 2 * D] + a[i] == C * a[i + D] for i in range(len(a) - 2 * D))

def prod_ok(a, c):   # a(n)*a(n+3) = c + a(n+1)*a(n+2)
    return all(a[i] * a[i + 3] == c + a[i + 1] * a[i + 2] for i in range(len(a) - 3))

N = 60
ok = True
oeis = [  # name, p, q, data prefix, C, D, constant in the product identity
    ('A082630', 7, 11, [1,2,5,8,19,30,71,112,265,418,989,1560,3691], 4, 2, -2),
    ('A082981', 4, 5, [1,2,3,4,9,14,19,24,53,82,111,140,309,478,647,816,1801], 6, 4, None),
    ('A085260', 833344, 10000000, [1,12,155,2003,25884,334489,4322473,55857660], 13, 1, 143),
    ('A085376', 36704, 100000, [1,3,11,30,109,297,1079,2940,10681,29103], 10, 2, -3),
    ('A085348', 264, 1000, [1,4,19,72,341,1292,6119,23184,109801], 18, 2, -4),
    ('A085349', 26688, 100000, [1,4,15,71,269,1274,4827,22861,86617], 18, 2, 11),
]
for name, p, q, data, C, D, c in oeis:
    a = rdis(p, q, N)
    r1 = a[:len(data)] == data
    r2 = rec_ok(a, C, D)
    r3 = True if c is None else prod_ok(a, c)
    print(name, 'data', r1, 'recurrence (%d,%d)' % (C, D), r2, 'product identity', r3)
    ok &= r1 and r2 and r3
# extra claims in A082981: quadratic invariants of the sections
a = rdis(4, 5, N)
print('A082981 states:', [(a[i], a[i+1]-a[i]) for i in range(0, 12)])

def U(m, n):
    s = [1, m + 1]
    while len(s) < n: s.append((m + 1) * s[-1] - s[-2])
    return s[:n]
def V(m, n):
    s = [1, m]
    while len(s) < n: s.append((m + 1) * s[-1] - s[-2])
    return s[:n]
for m in range(1, 41):
    ks = [Fr(1, m), Fr(m, m * m + m - 1), (Fr(1, m) + Fr(m, m * m + m - 1)) / 2]
    for k in ks:
        ok &= rdis(k.numerator, k.denominator, 40) == U(m, 40)
    # just outside the stated range the sequence must change, on at least one side
    if m >= 2:
        ks = [Fr(m + 1, m * m + m - 1), Fr(1, m) + Fr(1, 10**9), (Fr(1, m) + Fr(m + 1, m * m + m - 1)) / 2]
        for k in ks:
            ok &= rdis(k.numerator, k.denominator, 40) == V(m, 40)
        a = rdis(m, m * m - 1, 44)
        ok &= rec_ok(a, m * m + m - 2, 2)
        ok &= Fr(1, m) < Fr(m, m * m - 1) < Fr(1, m - 1)
        if m <= 4: print('C.4 m=%d k=%s' % (m, Fr(m, m*m-1)), a[:8])
print('ALL OK' if ok else 'FAILURE')
sys.exit(0 if ok else 1)
