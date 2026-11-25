"""Independent falsification attempts. The tolerance is only for these diagnostics."""

from cmath import exp
from itertools import product
from math import cos, pi, sin, sqrt
from random import Random


def check():
    rng = Random(314159)
    max_error = 0.0
    max_excess = -float("inf")
    intervals = 0
    for n in [*range(4, 42, 2), 64, 126, 256, 510, 1024, 4094]:
        e = (-1) ** (n // 2 + 1)
        d = pi / (4 * (n + 1))
        f = lambda y, s: sin(y) * cos(y)**n - s * cos(y) * sin(y)**n
        t = f(d, e)
        r = cos(d)**(n+1) + e * sin(d)**(n+1)
        s = 1 if n % 8 in (0, 2) else -1
        assert f(-d, 1) < 0

        for left, right, sign in [(-3, -2, 1), (-2, -1, 1), (-1, 0, 1),
                                  (0, 1, 1), (1, 2, -1), (2, 3, -1)]:
            # Deliberately cluster probes next to the transition points.
            for u in [0, 1, 2**-24, 1-2**-24, *[rng.random() for _ in range(250)]]:
                x = (left + (right-left)*u)*d
                a = pi/4 + (n+1)*x
                raw = -sin(x)*cos(x)**n + e*cos(x)*sin(x)**n + t*sin(a)
                assert sign * raw >= -1e-12
                intervals += 1
        for _ in range(200):
            y = rng.uniform(3*d, pi/4)
            assert sqrt(cos(y)**(2*n) + sin(y)**(2*n)) + t < r
        if n > 10:
            continue
        subsets = list(product([0, 1], repeat=n))
        weights = [2**(1-n)*cos((n-1)*pi/4-sum(bits)*pi/2) for bits in subsets]
        theta = 2*pi*{0:3*n/4+1, 2:n/4+0.5, 4:n/4, 6:3*n/4+0.5}[n%8]/(n+1)
        for _ in range(40):
            angles = [theta + rng.uniform(-0.03, 0.03) for _ in range(n)]
            # Alternating, antipodal and independent phases stress the reduction.
            for trial in [angles, [a + pi*(i%2) for i,a in enumerate(angles)],
                          [rng.uniform(-pi, pi) for _ in range(n)]]:
                p = sum(c*exp(1j*sum(a for b,a in zip(bits,trial) if b))
                        for c,bits in zip(weights,subsets))
                excess = abs(p-s*t)-r
                max_excess = max(max_excess, excess)
                assert excess < 2e-12
        # Direct Eq. (1), with the GHZ correlator calculated by the two basis flips.
        raw = sum(c*(1j*exp(-1j*sum(bits)*theta)-1j*exp(1j*sum(bits)*theta)).real/2
                  for c,bits in zip(weights,subsets))
        eq24 = cos(theta/2+pi/4)**n*sin(n*theta/2+pi/4) + cos(theta/2-pi/4)**n*sin(n*theta/2-pi/4)
        max_error = max(max_error, abs(raw-r), abs(raw-eq24))
        assert abs(raw-r) < 2e-12 and abs(raw-eq24) < 2e-12
        wrong_center = abs(complex(s*t,r) + s*t)
        assert wrong_center > r
    print(f"{intervals} derivative-sign probes, including all interval boundaries")
    print(f"Worst sampled off-diagonal disk excess = {max_excess:.4g}")
    print(f"Largest direct GHZ / Eq. (24) / radius discrepancy = {max_error:.4g}")
    print("Reproduced the negative-y counterexample and detected reversed disk centers.")


if __name__ == "__main__":
    check()
