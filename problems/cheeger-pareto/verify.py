#!/usr/bin/env python3
"""Reconstruct the labeled graph and discover its certificate. Standard library only."""
import argparse
import csv
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path


def check(condition, message):
    if not condition:
        raise ValueError(message)


def decode(code):
    """McKay's short graph6 format (orders 0 through 62), zero-based labels."""
    values = [ord(char) - 63 for char in code]
    check(values and all(0 <= v < 64 for v in values), "bad graph6 character")
    n, *words = values
    check(n < 63, "the short graph6 header is required")
    count = n * (n - 1) // 2
    check(len(words) == (count + 5) // 6, "wrong payload length")
    bits = "".join(f"{word:06b}" for word in words)
    check("1" not in bits[count:], "nonzero padding")
    pairs = ((u, v) for v in range(n) for u in range(v))
    edges = [(u, v) for (u, v), bit in zip(pairs, bits) if bit == "1"]
    return n, sorted(edges)


def vertices(mask, n):
    return tuple(v for v in range(n) if mask & (1 << v))


def inspect(code):
    n, edges = decode(code)
    check(n >= 2, "the Cheeger minimum needs a nonempty admissible set")
    adj = [0] * n
    for u, v in edges:
        check(0 <= u < v < n and not adj[u] & (1 << v), "bad unordered edge")
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    visited = {0}
    todo = [0]
    while todo:
        for v in vertices(adj[todo.pop()], n):
            if v not in visited:
                visited.add(v)
                todo.append(v)
    check(len(visited) == n, "disconnected graph")

    cuts = {}
    for mask in range(1 << n):
        size = mask.bit_count()
        if size > n // 2:
            continue
        direct = sum(((mask >> u) ^ (mask >> v)) & 1 for u, v in edges)
        via_neighbors = sum((adj[v] & ~mask).bit_count() for v in vertices(mask, n))
        check(direct == via_neighbors, f"cut mismatch at mask {mask}")
        cuts[mask] = direct
    check(cuts[0] == 0, "empty cut")
    h = min(Fraction(cut, mask.bit_count()) for mask, cut in cuts.items() if mask)
    return n, edges, adj, cuts, h


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-cuts", type=Path, metavar="FILE",
                        help="write every admissible labeled cut as a TSV file")
    args = parser.parse_args()
    code = Path(__file__).with_name("graph6.txt").read_text(encoding="ascii").strip()
    n, edges, adj, cuts, h = inspect(code)
    full = (1 << n) - 1
    k = n // 2
    print(f"graph6={code} n={n} edges={len(edges)} connected=True")
    print("edges:", *edges)
    print("degrees:", *(neighbors.bit_count() for neighbors in adj))

    # For each possible support, discover the largest feasible one-coordinate mass.
    # Its saturated inequalities certify real Pareto maximality if they cover V.
    candidates = []
    for v in range(n):
        bit = 1 << v
        mass = min(cut for mask, cut in cuts.items() if mask & bit)
        tight = [mask for mask, cut in cuts.items() if mask & bit and cut == mass]
        union = 0
        for mask in tight:
            union |= mask
        if union == full and mass < k * h:
            candidates.append((v, mass, tight))
    check(candidates, "no certified one-coordinate counterexample")
    hub, mass, tight = candidates[0]
    vector = tuple(mass if v == hub else 0 for v in range(n))
    print(f"discovered support={hub} vector={vector}")
    print("size  admissible  min_cut  min_cut_with_support  min_ratio")
    for size in range(k + 1):
        row = [m for m in cuts if m.bit_count() == size]
        check(len(row) == comb(n, size), f"missing cuts of size {size}")
        minimum = min(cuts[m] for m in row)
        with_hub = [cuts[m] for m in row if m & (1 << hub)]
        print(f"{size:4} {len(row):11} {minimum:8} "
              f"{str(min(with_hub) if with_hub else '-'):>21} "
              f"{str(Fraction(minimum, size) if size else '-'):>10}")
    for mask, cut in cuts.items():
        check(sum(vector[v] for v in vertices(mask, n)) <= cut, f"infeasible at {mask}")
        check(h * mask.bit_count() <= cut, f"expansion at {mask}")
    minimizers = [vertices(m, n) for m in cuts if m and h * m.bit_count() == cuts[m]]
    print("Cheeger minimizers:", *minimizers)
    # Three disjoint triples together with the common hub supply a short tight cover.
    cover = [mask for mask in tight if mask.bit_count() == 4]
    cover = next((family for family in combinations(cover, 3)
                  if family[0] | family[1] | family[2] == full), None)
    check(cover is not None, "missing three-set certificate")
    for mask in cover:
        print(f"tight S={vertices(mask,n)} cut={cuts[mask]} mass={mass}")
    check((code, n, len(edges), hub, mass, h, k * h) ==
          ("IJOG[BHvO", 10, 18, 9, 6, Fraction(4, 3), Fraction(20, 3)),
          "mismatch with the submitted claims")
    if args.write_cuts:
        with args.write_cuts.open("w", encoding="ascii", newline="") as handle:
            writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
            writer.writerow(("mask", "vertices", "size", "boundary", "mass"))
            for mask, cut in cuts.items():
                subset = vertices(mask, n)
                writer.writerow((mask, ",".join(map(str, subset)), len(subset),
                                 cut, sum(vector[v] for v in subset)))
    print(f"PASS: {len(cuts)} admissible sets including empty; h={h}; "
          f"sum(x)={sum(vector)} < {k*h}; gap={k*h-sum(vector)}")


if __name__ == "__main__":
    main()
