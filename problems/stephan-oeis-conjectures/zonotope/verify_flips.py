"""Brute-force check of the flip count for the higher Bruhat order B(n, n-3).

Model: a graph on {0, ..., n-1} is *consistent* when every neighbourhood N(p) is an initial or
a final segment of the other vertices.  A *flip* is a pair (G, e) with e a non-edge of G such
that G and G + e are both consistent.

For every n up to the bound given on the command line the script
  * enumerates all consistent graphs (adding one vertex at a time),
  * counts the flips and compares with n (n + 5) 2^(n - 4)  (OEIS A060621, offset n = d + 3),
  * classifies the flips at each pair i < j by the shape of the rows of i and j and compares
    the four class sizes with the formulas used in the proof:
        DD and UU :  2^((b-1)^+ + (a+c-1)^+)      DU and UD :  C(a+b+c, b)
    where a, b, c are the numbers of vertices below i, between i and j, above j.

usage: python verify_flips.py 13
"""
import sys
from math import comb

OEIS_A060621 = [12, 36, 100, 264, 672, 1664, 4032, 9600, 22528, 52224]  # d = 0..9, n = d + 3


def row_ok(row, p, n):
    seq = [(row >> q) & 1 for q in range(n) if q != p]
    inc = all(seq[i] <= seq[i + 1] for i in range(len(seq) - 1))
    dec = all(seq[i] >= seq[i + 1] for i in range(len(seq) - 1))
    return inc or dec


def extend(graphs, k):
    """All consistent graphs on k + 1 vertices, from those on k vertices."""
    out = []
    cands = set()
    for t in range(k + 1):
        cands.add((1 << t) - 1)                       # initial segment {0..t-1}
        cands.add(((1 << k) - 1) ^ ((1 << t) - 1))    # final segment {t..k-1}
    for adj in graphs:
        for nb in cands:
            new = [adj[p] | (((nb >> p) & 1) << k) for p in range(k)] + [nb]
            if all(row_ok(new[p], p, k + 1) for p in range(k)):
                out.append(tuple(new))
    return out


def main():
    bound = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    graphs = [(0,)]
    ok_all = True
    for k in range(1, bound):
        graphs = extend(graphs, k)
        n = k + 1
        gs = set(graphs)
        assert len(gs) == len(graphs)
        flips = 0
        cls = {}
        for adj in graphs:
            for i in range(n):
                for j in range(i + 1, n):
                    if (adj[i] >> j) & 1:
                        continue
                    new = list(adj)
                    new[i] |= 1 << j
                    new[j] |= 1 << i
                    if tuple(new) in gs:
                        flips += 1
                        i_down = adj[i] == (((1 << j) - 1) & ~(1 << i))
                        j_down = adj[j] == (1 << i) - 1
                        key = (i, j, "D" if i_down else "U", "D" if j_down else "U")
                        cls[key] = cls.get(key, 0) + 1
        if n < 3:
            continue
        formula = n * (n + 5) * 2 ** n // 16
        ok_cls = True
        for i in range(n):
            for j in range(i + 1, n):
                a, b, c = i, j - i - 1, n - 1 - j
                x = 2 ** (max(b - 1, 0) + max(a + c - 1, 0))
                y = comb(a + b + c, b)
                got = [cls.get((i, j, s, t), 0) for (s, t) in
                       (("D", "D"), ("U", "U"), ("D", "U"), ("U", "D"))]
                if got != [x, x, y, y]:
                    ok_cls = False
        oeis = OEIS_A060621[n - 3] if n - 3 < len(OEIS_A060621) else None
        ok = flips == formula and ok_cls and (oeis is None or oeis == flips) \
            and len(graphs) == 2 ** n + n * 2 ** (n - 2) - 2 * n
        ok_all = ok_all and ok
        print("n=%d consistent graphs=%d flips=%d formula=%d OEIS=%s classes_ok=%s %s"
              % (n, len(graphs), flips, formula, oeis, ok_cls, "OK" if ok else "MISMATCH"),
              flush=True)
    print("ALL OK" if ok_all else "FAILED")
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
