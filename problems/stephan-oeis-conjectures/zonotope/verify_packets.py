"""Check of the flip count straight from the packet definition (no graph model).

B(n, k) is isomorphic to the consistent subsets of C([n], k+1) under single-step inclusion
(Ziegler 1993, Theorem 4.1): a set U of (k+1)-subsets is *consistent* when, for every
(k+2)-subset X, the members of the packet P(X) = {X - {x} : x in X} that lie in U form a
prefix or a suffix of P(X) in lexicographic order.

Here k = n - 3.  For each n the script enumerates all subsets of C([n], n-2), keeps the
consistent ones and counts the pairs (U, U + {y}) of consistent sets.  It prints the number of
consistent sets (OEIS A060602) and the number of such pairs (OEIS A060621), and compares them
with 2^n + n 2^(n-2) - 2n and n (n + 5) 2^(n-4).

This is independent of verify_flips.py, which uses the complemented (graph) form of the model.

usage: python verify_packets.py 7      (n = 7 needs 2^21 subsets; n = 8 would need 2^28)
"""
import sys
from itertools import combinations


def run(n):
    k1 = n - 2                                    # size of the subsets, k + 1
    elems = sorted(combinations(range(n), k1))    # sorted tuples: lexicographic order
    index = {s: t for t, s in enumerate(elems)}
    packets = []
    for X in combinations(range(n), k1 + 1):
        members = sorted(tuple(v for v in X if v != x) for x in X)   # P(X) in lex order
        bits = [1 << index[s] for s in members]
        full = sum(bits)
        allowed = set()
        for t in range(len(bits) + 1):
            pre = sum(bits[:t])
            allowed.add(pre)            # prefix
            allowed.add(full ^ pre)     # suffix
        packets.append((full, allowed))
    m = len(elems)
    consistent = set()
    for U in range(1 << m):
        for full, allowed in packets:
            if (U & full) not in allowed:
                break
        else:
            consistent.add(U)
    flips = 0
    for U in consistent:
        for t in range(m):
            if not (U >> t) & 1 and (U | (1 << t)) in consistent:
                flips += 1
    return len(consistent), flips


def main():
    bound = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    ok_all = True
    for n in range(3, bound + 1):
        sets, flips = run(n)
        want_sets = 2 ** n + n * 2 ** (n - 2) - 2 * n
        want_flips = n * (n + 5) * 2 ** n // 16
        ok = sets == want_sets and flips == want_flips
        ok_all = ok_all and ok
        print("n=%d d=%d consistent sets=%d (formula %d) flips=%d (formula %d) %s"
              % (n, n - 3, sets, want_sets, flips, want_flips, "OK" if ok else "MISMATCH"),
              flush=True)
    print("ALL OK" if ok_all else "FAILED")
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
