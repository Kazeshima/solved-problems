"""Exact character-expansion coefficients and numeric checks of the rate calculation."""
from fractions import Fraction
from itertools import product
from math import atan, exp, log1p, sin, sqrt

joint = [(p, q, p*q) for p, q in product((1, -1), repeat=2)]
def spectrum(c):
    return sorted(sum(a*b for a, b in zip(c, r)) for r in joint)

assert spectrum((1, 1, 1)) == [-1, -1, -1, 3]
for c in ((1, 1, -1), (1, -1, 1), (-1, 1, 1)):
    assert spectrum(c) == [-3, 1, 1, 1]

coefficients = [Fraction(6**k + 3*(-2)**k, 8*k) for k in range(1, 6)]
assert coefficients == [0, 3, 8, 42, 192]
def bias(d):
    x = 1 / sqrt(2*d)
    phase = d/8 * (atan(6*x) - 3*atan(2*x))
    magnitude = exp(-d/16 * (log1p(36*x*x) + 3*log1p(4*x*x)))
    return -magnitude * sin(phase)

for n in (4, 8, 12, 16, 20, 24):
    d = 2**n
    assert 0 < bias(d) <= 2*sqrt(2*(d+2))/(d+4)
    print(n, format(sqrt(d)*bias(d), ".9f"))
assert abs(sqrt(2**20)*bias(2**20) - 2*sqrt(2)*exp(-1.5)) < 0.00002
print("Exact expansion coefficients and four joint eigenspaces verified.")
