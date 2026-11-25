#!/usr/bin/env python3
"""Exact rational verification independent of Lean; no numerical search."""
from fractions import Fraction as Q
from itertools import product
import sympy as S


def potts_weight(i, j, beta):
    return beta if i == j else Q(1)


def bp_direct(p, r, beta):
    g = [sum(p[a] * r[b] * potts_weight(i, a, beta)
             * potts_weight(i, b, beta)
             for a, b in product(range(4), repeat=2)) for i in range(4)]
    return tuple(x / sum(g) for x in g)


def bp_factor(p, r, beta):
    g = [(1-(1-beta)*a)*(1-(1-beta)*b) for a,b in zip(p,r)]
    return tuple(x/sum(g) for x in g)


def check():
    p, r, s, t = [tuple(map(Q, v)) for v in [(1,0,0,0),(0,1,0,0),
                 (0,0,1,0),(Q(1,2),Q(1,2),0,0)]]
    for a in (p,r,s,t):
        assert all(x >= 0 for x in a) and sum(a) == 1
    beta = Q(1,2)
    u, v = bp_direct(p,r,beta), bp_direct(s,t,beta)
    assert u == bp_factor(p,r,beta) == (Q(1,6),Q(1,6),Q(1,3),Q(1,3))
    assert v == bp_factor(s,t,beta) == (Q(1,4),Q(1,4),Q(1,6),Q(1,3))
    w = tuple((a+b)/2 for a,b in zip(u,v))
    assert w == (Q(5,24),Q(5,24),Q(1,4),Q(1,3))
    assert max(Q(0), 1-Q(4,3)) <= beta <= 1
    print('u, v, w =', u, v, w)
    # Boundary identity is a polynomial identity modulo the two simplex equations.
    P = S.symbols('p1:5'); R = S.symbols('r1:5')
    h = [(2-a)*(2-b) for a,b in zip(P,R)]
    rhs = 6*P[3]+(6-2*P[3])*R[3]+sum(P[i]*R[i] for i in range(3))
    assert S.expand(sum(h[:3])-2*h[3]-rhs+2*(sum(P)-1)+2*(sum(R)-1)) == 0
    print('Symbolic boundary identity: PASS')
    # On the boundary, h4=4 and Z=12. Disjointness and target w force
    # p_i+r_i=(4-12*w_i)/2; each p_i is either 0 or that value.
    forced = tuple((4-12*x)/2 for x in w[:3])
    assert forced == (Q(3,4),Q(3,4),Q(1,2))
    sums = [sum(xs) for xs in product(*[(Q(0),a) for a in forced])]
    assert len(sums)==8 and all(x != 1 for x in sums)
    print('All eight forced support cases fail simplex sum:', sums)
    print('Admissibility, endpoints, midpoint, symbolic identity and contradiction: PASS')

if __name__ == '__main__':
    check()
