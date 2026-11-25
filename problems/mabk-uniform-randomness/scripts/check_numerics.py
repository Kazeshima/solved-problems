#!/usr/bin/env python3
"""Floating-point diagnostics, not a universal proof. Python standard library only."""
import cmath
import math
import random


def parameters(n):
    d = math.pi / (4 * (n + 1))
    e = 1 if n % 4 == 2 else -1
    t = math.sin(d) * math.cos(d)**n - e * math.cos(d) * math.sin(d)**n
    r = math.cos(d)**(n + 1) + e * math.sin(d)**(n + 1)
    tau = t if n % 8 in (0, 2) else -t
    return d, e, t, r, tau


def canonical(n, x, e):
    return cmath.exp(1j * (math.pi / 4 + n * x)) * (math.cos(x)**n + 1j * e * math.sin(x)**n)


def poly(zs):
    n = len(zs)
    phi = (n - 1) * math.pi / 4
    # Divide each factor by two to avoid large intermediates.
    return (cmath.exp(1j*phi) * math.prod((1-1j*z)/2 for z in zs)
            + cmath.exp(-1j*phi) * math.prod((1+1j*z)/2 for z in zs))


def angle(n):
    j = {0: 3*n/4+1, 2: n/4+0.5, 4: n/4, 6: 3*n/4+0.5}[n%8]
    return 2*math.pi*j/(n+1)


def main():
    rng = random.Random(20261125)
    tolerance = 3e-10
    table = {2: 1.299038105676658, 4: 2.658283776100125,
             6: 5.412519474140316, 8: 10.93208547970192,
             10: 22.00126183851497, 12: 44.19316043036512}
    ns = list(range(2, 66, 2)) + [96, 128, 256, 512, 1024]
    print('MABK numerical diagnostics (double precision, seed 20261125)')
    print('n     normalized_r        max_sample_excess   saturation_error')
    for n in ns:
        d, e, t, r, tau = parameters(n)
        points = [-math.pi/4 + math.pi*j/40000 for j in range(20001)] + [d, -d, 0, -3*d, 3*d]
        # Exclude the last two points if outside the canonical interval (N=2).
        points = [x for x in points if abs(x) <= math.pi/4 + 1e-14]
        excess = max(abs(canonical(n, x, e)-t)-r for x in points)
        equality_error = abs(canonical(n,d,e)-complex(t,r))
        ghz_error = abs(poly([cmath.exp(1j*angle(n))]*n).imag-r)
        assert excess <= tolerance, (n, 'sampled canonical violation', excess)
        assert max(equality_error,ghz_error) <= tolerance, (n, 'contact/saturation', equality_error,ghz_error)
        if n in table:
            assert abs(2**((n-1)/2)*r-table[n]) <= 1e-10, (n, 'published Table 2 mismatch')
        # Random torus checks plus exact diagonal contact; no global optimality inference.
        if n <= 32:
            for _ in range(1000):
                zs = [cmath.exp(1j*rng.uniform(-math.pi, math.pi)) for _ in range(n)]
                assert abs(poly(zs)-tau) <= r+tolerance, (n, 'sampled torus violation')
        # Check residue transformation at random upper-semicircle angles.
        for _ in range(12):
            x = rng.uniform(-math.pi/4,math.pi/4)
            y = -x if n%8 in (0,4) else x
            w = poly([cmath.exp(1j*(math.pi/2+2*y))]*n)
            c = canonical(n,x,e)
            expected = {0:c.conjugate(),2:c,4:-c.conjugate(),6:-c}[n%8]
            assert abs(w-expected) <= tolerance, (n,'mod-8 transformation')
        print(f'{n:4d}  {r:.14f}    {excess:+.3e}          {max(equality_error,ghz_error):.3e}')
    print(f'PASS: {len(ns)} even N values, published Table 2 rows N=2..12,')
    print('      canonical contacts, finite grids, mod-8 identities, and sampled torus points.')
    print('This is diagnostic evidence only; Lean and mathematical review remain required.')

if __name__ == '__main__':
    main()
