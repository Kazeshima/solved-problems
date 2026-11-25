#!/usr/bin/env python3
"""Generate or verify exact certificates for unrestricted real Pareto vectors.

Run without arguments to verify the shipped certificates offline. Use
--generate CATALOG to read graph2c.g6 through graph9c.g6 and regenerate them.
The covering obstruction and its proof are in MINIMALITY.md and CheegerMinimum/.
"""
import argparse
from collections import Counter
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from verify import decode

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / "evidence"
GRAPH_CERT = EVIDENCE / "all-real-graphs.tsv.gz"
COVER_CERT = EVIDENCE / "cover-obstructions.json"
# Byte hashes of McKay's connected simple graph6 catalogs, with LF line endings.
CATALOG = {
    2: (1, "fae4bfc454bd04363dcd5222772f2973b1193e1ff6f676e822a427323a677ef9"),
    3: (2, "5966edf890849db6cb03626431916231a81a30c9db9a4781a4a8f2e5dc7e6129"),
    4: (6, "d7da485669f2dc74b81c02f18774a07430937684896833d59f138b10debb5005"),
    5: (21, "3c436a6a15f554e3eff3ce9178fddd3d75db6d365b3c6b102b64afe82145050b"),
    6: (112, "2dc8cbb1c05a12b5dcb28b6227cee86d585f203347f6aebb8fcbdb2b9bdf5fd7"),
    7: (853, "ec46e9ec29eddb1d6e41bdea6be940c523ed6024eebe202b4bd176370c90f72e"),
    8: (11117, "0002354f1ab3344a2706626a037ad15367bf23a2163aa68f552c3a169ca9a036"),
    9: (261080, "ad4fda3b6c7157e6711270cdc9cefdc06ac5154d7bd6ce295e1ac41808755c65"),
}


def require(test, message):
    if not test:
        raise ValueError(message)


class Order:
    def __init__(self, n):
        self.n, self.k = n, n // 2
        self.full = (1 << n) - 1
        self.groups = [[] for _ in range(self.k + 1)]
        self.small = []
        self.allowed = []
        for mask in range(1, self.full + 1):
            size = mask.bit_count()
            if size <= self.k:
                self.groups[size].append(mask)
                self.allowed.append((mask, mask & (mask - 1), (mask & -mask).bit_length() - 1))
            if size < self.k:
                self.small.append(mask)
        self.all_sets = (1 << len(self.small)) - 1
        self.contains = [sum(1 << i for i, a in enumerate(self.small) if a & (1 << v))
                         for v in range(n)]
        self.compatible = [
            sum(1 << j for j, b in enumerate(self.small)
                if a & b and (a | b).bit_count() > self.k
                and (a | b).bit_count() != n - self.k)
            for a in self.small
        ]

    def children(self, remaining, pool):
        v = (remaining & -remaining).bit_length() - 1
        choices = pool & self.contains[v]
        while choices:
            bit = choices & -choices
            i = bit.bit_length() - 1
            yield remaining & ~self.small[i], pool & self.compatible[i]
            choices ^= bit

    def cover_possible(self, remaining, pool):
        if not remaining:
            return True
        return any(self.cover_possible(r, p) for r, p in self.children(remaining, pool))

    def graph_record(self, code, independent):
        n, edges = decode(code)
        require(n == self.n, "wrong graph order")
        adj = [0] * n
        for u, v in edges:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
        cut = [0] * (1 << n)
        degrees = [a.bit_count() for a in adj]
        if independent:
            # Count the unique endpoint inside the set for each crossing edge.
            for mask, _, _ in self.allowed:
                pending, outside, value = mask, self.full ^ mask, 0
                while pending:
                    bit = pending & -pending
                    value += (adj[bit.bit_length() - 1] & outside).bit_count()
                    pending ^= bit
                cut[mask] = value
        else:
            for mask, rest, v in self.allowed:
                cut[mask] = cut[rest] + degrees[v] - 2 * (adj[v] & rest).bit_count()

        numerator, denominator = n, 1
        for size in range(1, self.k + 1):
            best = min(map(cut.__getitem__, self.groups[size]))
            if best * denominator < numerator * size:
                numerator, denominator = best, size
        h = Fraction(numerator, denominator)
        require(h > 0, "disconnected catalog record")
        pool = sum(1 << i for i, a in enumerate(self.small)
                   if cut[a] * denominator < self.k * numerator)
        return h, pool


def make_obstructions(orders):
    result = {}
    for n, order in orders.items():
        reached, todo = set(), [(order.full, order.all_sets)]
        while todo:
            state = todo.pop()
            if state in reached:
                continue
            remaining, pool = state
            require(remaining != 0, f"abstract cover found at order {n}")
            reached.add(state)
            todo.extend(order.children(remaining, pool))
        result[str(n)] = [[remaining, format(pool, "x")] for remaining, pool in sorted(reached)]
    return result


def check_obstructions(data, orders):
    require(set(data) == {str(n) for n in orders}, "wrong obstruction orders")
    for n, order in orders.items():
        states = {(r, int(p, 16)) for r, p in data[str(n)]}
        require(len(states) == len(data[str(n)]), "duplicate state")
        require((order.full, order.all_sets) in states, f"missing root at order {n}")
        for rest, pool in states:
            require(0 < rest <= order.full and 0 <= pool <= order.all_sets, "invalid state")
            # Check closure directly against individual set masks and lead vertex.
            lead = rest & -rest
            for i, a in enumerate(order.small):
                if pool & (1 << i) and a & lead:
                    next_state = rest & ~a, pool & order.compatible[i]
                    require(next_state[0] < rest and next_state in states, "unproved branch")


HEADER = "graph6\th\tcheap_sets_hex\tcompatible_cover\n"


def run(catalog, directory):
    orders = {n: Order(n) for n in CATALOG}
    cover_file = directory / COVER_CERT.name
    graph_file = directory / GRAPH_CERT.name
    if catalog:
        data = make_obstructions(orders)
        cover_file.write_text(json.dumps(data, separators=(",", ":")) + "\n",
                              encoding="ascii", newline="\n")
    else:
        data = json.loads(cover_file.read_text(encoding="ascii"))
    check_obstructions(data, orders)

    # A genuine violation must survive the necessary-condition search.
    control = Order(10)
    control_h, control_pool = control.graph_record("IJOG[BHvO", independent=not catalog)
    require(control_h == Fraction(4, 3) and control.cover_possible(control.full, control_pool),
            "the ten-vertex positive control was rejected")

    counts = Counter()
    digests = {n: hashlib.sha256() for n in orders}

    def record(code):
        n = ord(code[0]) - 63
        order = orders[n]
        h, pool = order.graph_record(code, independent=not catalog)
        require(not order.cover_possible(order.full, pool), f"unresolved graph {code}")
        counts[n] += 1
        digests[n].update((code + "\n").encode("ascii"))
        return f"{code}\t{h.numerator}/{h.denominator}\t{pool:x}\t0\n"

    if catalog:
        # Suppress date and file-name metadata to make the gzip deterministic.
        with graph_file.open("wb") as output, gzip.GzipFile(
                filename="", mode="wb", fileobj=output, compresslevel=9, mtime=0) as zipped:
            zipped.write(HEADER.encode("ascii"))
            for n in orders:
                with (catalog / f"graph{n}c.g6").open(encoding="ascii") as src:
                    for line in src:
                        code = line.rstrip("\r\n")
                        require(ord(code[0]) - 63 == n, "record in wrong input file")
                        zipped.write(record(code).encode("ascii"))
    else:
        with gzip.open(graph_file, "rt", encoding="ascii", newline="") as src:
            require(src.readline() == HEADER, "bad certificate header")
            for row in src:
                code = row.split("\t", 1)[0]
                require(record(code) == row, f"incorrect certificate row for {code}")

    for n, (expected, digest) in CATALOG.items():
        require(counts[n] == expected and digests[n].hexdigest() == digest,
                f"catalog identity mismatch at order {n}")
        print(f"n={n}: {counts[n]} connected graphs, all excluded over the reals; "
              f"{len(data[str(n)])} universal proof states")
    print(f"PASS: {sum(counts.values())} graphs; minimum counterexample order = 10")
    print("Positive control: IJOG[BHvO survives the cover test; its real witness is in CheegerPareto.lean.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate", metavar="CATALOG", type=Path)
    inputs = parser.parse_args().generate
    if inputs:
        with TemporaryDirectory(dir=EVIDENCE) as tmp:
            staging = Path(tmp)
            run(inputs, staging)
            for target in (COVER_CERT, GRAPH_CERT):
                (staging / target.name).replace(target)
    else:
        run(None, EVIDENCE)
