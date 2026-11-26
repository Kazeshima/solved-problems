"""Brute-force check of the individual claims made in oeis/a060621_proof.txt.

For every consistent graph on n vertices and every pair i < j it checks Lemma 1, Lemma 2(a), the
forced neighbourhoods used in Sections 3 and 4, the sizes of the classes DU and DD, and the
per-pair flip count of Section 5.

usage: python check_proof_claims.py 7      (all graphs on n vertices are enumerated: keep n <= 7)
"""
import sys
from itertools import combinations


def row_ok(adj, p, n):
    seq = [(adj[p] >> q) & 1 for q in range(n) if q != p]
    inc = all(seq[t] <= seq[t + 1] for t in range(len(seq) - 1))
    dec = all(seq[t] >= seq[t + 1] for t in range(len(seq) - 1))
    return inc or dec


def consistent_graphs(n):
    pairs = list(combinations(range(n), 2))
    out = []
    for mask in range(1 << len(pairs)):
        adj = [0] * n
        for t, (x, y) in enumerate(pairs):
            if (mask >> t) & 1:
                adj[x] |= 1 << y
                adj[y] |= 1 << x
        if all(row_ok(adj, p, n) for p in range(n)):
            out.append(tuple(adj))
    return out


def bits(xs):
    m = 0
    for x in xs:
        m |= 1 << x
    return m


def main():
    bound = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    for n in range(2, bound + 1):
        gs = consistent_graphs(n)
        gset = set(gs)
        V = range(n)
        checked = 0
        for i in range(n):
            for j in range(i + 1, n):
                A = [q for q in V if q < i]
                B = [q for q in V if i < q < j]
                C = [q for q in V if q > j]
                mA, mB, mC = bits(A), bits(B), bits(C)
                cls = {"DD": [], "DU": [], "UD": [], "UU": []}
                for g in gs:
                    # Lemma 1
                    if not (g[i] >> j) & 1:
                        h = list(g)
                        h[i] |= 1 << j
                        h[j] |= 1 << i
                        flip = tuple(h) in gset
                        cond = g[i] in (mA | mB, mC) and g[j] in (mA, mB | mC)
                        assert flip == cond, ("lemma1", n, i, j, g)
                    if g[i] == mA | mB and g[j] == mA:
                        cls["DD"].append(g)
                    if g[i] == mA | mB and g[j] == mB | mC:
                        cls["DU"].append(g)
                    if g[i] == mC and g[j] == mA:
                        cls["UD"].append(g)
                    if g[i] == mC and g[j] == mB | mC:
                        cls["UU"].append(g)
                # Lemma 2(a): complement of G + ij
                full = (1 << n) - 1
                def comp(g):
                    h = [(full ^ g[p]) & ~(1 << p) for p in V]
                    h[i] &= ~(1 << j)
                    h[j] &= ~(1 << i)
                    return tuple(h)
                assert sorted(comp(g) for g in cls["DD"]) == sorted(cls["UU"])
                assert sorted(comp(g) for g in cls["DU"]) == sorted(cls["UD"])
                # Section 3, DU
                for g in cls["DU"]:
                    if not A and not C:
                        want = [full & ~(1 << p) for p in V]
                        want[i] &= ~(1 << j)
                        want[j] &= ~(1 << i)
                        assert g == tuple(want)
                    if A:
                        a = max(A)
                        nb = g[a]
                        Bp = [q for q in B if (nb >> q) & 1]
                        assert nb == bits([q for q in A if q != a]) | (1 << i) | bits(Bp)
                        assert Bp == B[:len(Bp)]
                        if len(Bp) == len(B):
                            assert nb == bits([q for q in V if q < j and q != a])
                        else:
                            b = max(B)
                            assert not (g[a] >> b) & 1
                            assert g[b] == bits([q for q in V if q >= i and q != b])
                        checked += 1
                # Section 4, DD
                for g in cls["DD"]:
                    if len(B) >= 2:
                        b1, b2 = min(B), max(B)
                        if (g[b1] >> b2) & 1:
                            assert g[b1] == bits([q for q in V if q < j and q != b1])
                        else:
                            assert g[b2] == mA | (1 << i)
                    elif len(B) == 1:
                        assert g[B[0]] == mA | (1 << i)
                    elif A and C:
                        a, c = max(A), min(C)
                        if (g[a] >> c) & 1:
                            assert g[c] == mA
                        else:
                            assert g[a] == bits([q for q in A if q != a]) | (1 << i) | (1 << j)
                    elif not C:
                        if len(A) >= 2:
                            a1, a2 = min(A), max(A)
                            if (g[a1] >> a2) & 1:
                                assert g[a2] == full & ~(1 << a2)
                            else:
                                assert g[a1] == (1 << i) | (1 << j)
                        elif len(A) == 1:
                            assert g[A[0]] == (1 << i) | (1 << j)
                    checked += 1
                # sizes and the per-pair flip count of Section 5
                from math import comb
                al, be, ga = len(A), len(B), len(C)
                assert len(cls["DU"]) == comb(al + be + ga, be)
                assert len(cls["DD"]) == 2 ** (max(be - 1, 0) + max(al + ga - 1, 0))
                if n >= 3:
                    tot = sum(len(v) for v in cls.values())
                    extra = 2 ** (n - 2) if (j - i == 1 or j - i == n - 1) else 2 ** (n - 3)
                    assert tot == 2 * comb(n - 2, j - i - 1) + extra, (n, i, j, tot)
        print("n=%d: %d consistent graphs, %d class members checked, all claims hold"
              % (n, len(gs), checked), flush=True)
    print("PROSE CLAIMS OK")


if __name__ == "__main__":
    main()
