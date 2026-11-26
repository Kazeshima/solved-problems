"""Checks for Stephan's Conjecture 85:  A080795(2n) = 2^n * A006154(2n).

1. Counts minimax trees by brute force (all labelled plane binary trees on n nodes in which the
   label of every node is the minimum or the maximum of its subtree) and compares the counts with
   the recurrence used in MinimaxTrees.lean and with the terms listed in OEIS A080795.
2. Counts ordered set partitions into blocks of odd size by brute force and compares the counts
   with the recurrence used in MinimaxTrees.lean and with the terms listed in OEIS A006154.
3. Checks the identity a(2n) = 2^n b(2n) for the two recurrences up to the given bound.

usage: python verify_identity.py [brute-force bound, default 7] [identity bound on 2n, default 400]
"""
import sys
from itertools import combinations, permutations
from math import comb

OEIS_A080795 = [1, 1, 4, 20, 128, 1024, 9856, 110720, 1421312, 20525056, 329334784, 5812797440,
                111923560448, 2334639652864, 52444850814976, 1262260748288000,
                32405895451246592, 883950436237705216, 25530268718794276864]
OEIS_A006154 = [1, 1, 2, 7, 32, 181, 1232, 9787, 88832, 907081, 10291712, 128445967, 1748805632,
                25794366781, 409725396992, 6973071372547, 126585529106432, 2441591202059281,
                49863806091395072, 1074927056650469527, 24392086908129247232,
                581176736647853024581]


def a_rec(bound):
    """a(0) = 1, a(n+1) = 2 * sum_k C(n,k) a(k) a(n-k) - 0^n."""
    a = [1]
    for n in range(bound):
        a.append(2 * sum(comb(n, k) * a[k] * a[n - k] for k in range(n + 1)) - (1 if n == 0 else 0))
    return a


def b_rec(bound):
    """b(0) = 1, b(n+1) = sum over even k <= n of C(n+1, k+1) b(n-k)."""
    b = [1]
    for n in range(bound):
        b.append(sum(comb(n + 1, k + 1) * b[n - k] for k in range(0, n + 1, 2)))
    return b


def shapes(n):
    """Plane binary trees with n nodes: None, or (left, right)."""
    if n == 0:
        return [None]
    out = []
    for k in range(n):
        for left in shapes(k):
            for right in shapes(n - 1 - k):
                out.append((left, right))
    return out


def is_minimax(shape, labels, pos):
    """Reads the labels of `shape` in preorder from labels[pos:].  Returns (ok, next position,
    minimum, maximum) for the subtree."""
    root = labels[pos]
    lo = hi = root
    pos += 1
    for child in shape:
        if child is not None:
            ok, pos, clo, chi = is_minimax(child, labels, pos)
            if not ok:
                return False, pos, lo, hi
            lo, hi = min(lo, clo), max(hi, chi)
    return (root == lo or root == hi), pos, lo, hi


def count_minimax(n):
    if n == 0:
        return 1
    total = 0
    for shape in shapes(n):
        for labels in permutations(range(n)):
            if is_minimax(shape, labels, 0)[0]:
                total += 1
    return total


def count_odd_ordered_partitions(n):
    """Ordered set partitions of {0..n-1} into blocks of odd size, by explicit enumeration."""
    def rec(rest):
        if not rest:
            return 1
        total = 0
        for size in range(1, len(rest) + 1, 2):
            for block in combinations(rest, size):
                chosen = set(block)
                total += rec(tuple(x for x in rest if x not in chosen))
        return total
    return rec(tuple(range(n)))


def main():
    brute = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    bound = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    a = a_rec(bound + 1)
    b = b_rec(bound + 1)
    ok = a[:len(OEIS_A080795)] == OEIS_A080795 and b[:len(OEIS_A006154)] == OEIS_A006154
    print("recurrences reproduce the %d + %d terms listed in the OEIS: %s"
          % (len(OEIS_A080795), len(OEIS_A006154), ok), flush=True)
    for n in range(brute + 1):
        ta, tb = count_minimax(n), count_odd_ordered_partitions(n)
        good = ta == a[n] and tb == b[n]
        ok = ok and good
        print("n=%d minimax trees=%d (recurrence %d) odd ordered partitions=%d (recurrence %d) %s"
              % (n, ta, a[n], tb, b[n], "OK" if good else "MISMATCH"), flush=True)
    bad = [n for n in range(bound // 2 + 1) if a[2 * n] != 2 ** n * b[2 * n]]
    ok = ok and not bad
    print("a(2n) = 2^n b(2n) for 0 <= 2n <= %d: %s" % (bound, "OK" if not bad else "FAILS at %s" % bad))
    print("ALL OK" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
