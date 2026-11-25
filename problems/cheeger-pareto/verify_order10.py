#!/usr/bin/env python3
"""Replay the order-ten classification offline using Python and two C++17 programs."""
import argparse
from collections import Counter
import csv
from fractions import Fraction
import filecmp
import hashlib
from itertools import permutations, product
import json
import lzma
from math import comb, factorial
import os
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory

from verify import check, inspect, vertices

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "order10"
DATA = SRC / "data"
COUNT = 11_716_571
CATALOG_SHA256 = "0642748d4518ce8cb30e5b13866ef527357064082729730316f3d57dc41b65f5"


def automorphism_count(n, edges, adj):
    """Direct degree-preserving permutations, used only on the three witnesses."""
    degree = [a.bit_count() for a in adj]
    blocks = [[v for v in range(n) if degree[v] == d] for d in sorted(set(degree))]
    domain = [v for block in blocks for v in block]
    edge_set = set(edges)
    count = 0
    for images in product(*(permutations(block) for block in blocks)):
        f = dict(zip(domain, (v for block in images for v in block)))
        if all(tuple(sorted((f[a], f[b]))) in edge_set for a, b in edges):
            count += 1
    return count


def witnesses():
    data = json.loads((SRC / "witnesses.json").read_text(encoding="ascii"))
    result = {}
    for row in data["graphs"]:
        code = row["graph6"]
        n, edges, adj, cuts, h = inspect(code)
        hub, mass = row["hub"], row["rho"]
        check(n == 10 and len(edges) == row["edges"] and h == Fraction(row["h"]), code)
        check(len(cuts) == 638 and mass < 5*h, f"wrong gap for {code}")
        check(min(c for s, c in cuts.items() if (s >> hub) & 1) == mass, "hub bound")
        attainer = sum(1 << v for v in data["expansion_attainer"])
        check(attainer and cuts[attainer] == h * attainer.bit_count(), "Cheeger attainer")
        covered = 0
        for block in data["tight_cover"]:
            mask = sum(1 << v for v in block)
            check(list(vertices(mask, n)) == block and hub in block and cuts[mask] == mass,
                  "invalid tight row")
            covered |= mask
        check(covered == (1 << n) - 1, "incomplete real Pareto certificate")
        check(automorphism_count(n, edges, adj) == row["automorphisms"], "wrong group order")
        check(code not in result, "repeated witness")
        result[code] = row
        print(f"{code}: |E|={len(edges)} h={h} rho={mass} 5h={5*h} |Aut|={row['automorphisms']}")
    original = data["original"]
    _, source, _, _, _ = inspect(original["graph6"])
    _, dest, _, _, _ = inspect(original["representative"])
    f = original["old_to_representative"]
    check(original["representative"] in result and sorted(f) == list(range(10)), "bad relabeling")
    check({tuple(sorted((f[a], f[b]))) for a, b in source} == set(dest), "relabeling mismatch")
    return result


def unpack(source, destination, expected_bytes):
    digest = hashlib.sha256()
    size = 0
    with lzma.open(source, "rb") as compressed, destination.open("wb") as raw:
        for part in iter(lambda: compressed.read(1 << 20), b""):
            size += len(part)
            check(size <= expected_bytes, f"invalid expanded size of {source.name}")
            raw.write(part)
            digest.update(part)
    check(size == expected_bytes, f"truncated {source.name}")
    return digest.hexdigest()


def compile_tool(name, tmp):
    compiler = os.environ.get("CXX") or shutil.which("c++") or shutil.which("cl")
    if not compiler:
        raise RuntimeError("A C++17 compiler is needed. On Windows, use a Visual Studio developer shell.")
    binary = tmp / (name + (".exe" if os.name == "nt" else ""))
    source = str(SRC / (name + ".cpp"))
    if Path(compiler).stem.lower() == "cl":
        command = [compiler, "/nologo", "/O2", "/std:c++17", "/EHsc", "/openmp",
                   source, "/Fe" + str(binary)]
        subprocess.run(command, cwd=tmp, check=True)
    else:
        base = [compiler, "-O3", "-std=c++17", source, "-o", str(binary)]
        parallel = subprocess.run([*base, "-fopenmp"], cwd=tmp, capture_output=True)
        if parallel.returncode:  # Apple Clang without OpenMP also supports a serial replay.
            subprocess.run(base, cwd=tmp, check=True)
    return binary


def labeled_connected(n):
    counts = [0] * (n + 1)
    for v in range(1, n + 1):
        counts[v] = 2 ** comb(v, 2) - sum(
            comb(v - 1, k - 1) * counts[k] * 2 ** comb(v - k, 2) for k in range(1, v))
    return counts[n]


def check_orbit_sum(path):
    groups = Counter()
    value = shift = 0
    for byte in path.read_bytes():
        value |= (byte & 127) << shift
        if byte & 128:
            shift += 7
        else:
            check(value > 0 and factorial(10) % value == 0, "invalid group order")
            groups[value] += 1
            value = shift = 0
    check(not shift and sum(groups.values()) == COUNT, "incomplete automorphism data")
    mass = sum(count * (factorial(10) // size) for size, count in groups.items())
    check(mass == labeled_connected(10), "orbit sum failed")
    return mass


def check_row(code, entry, proof, survivors):
    """Small standard-library checker for a single encoded refutation."""
    n, _, _, costs, h = inspect(code)
    full = (1 << n) - 1
    t, status = entry & full, entry >> 10
    check(n == 10 and t in costs and t and costs[t] == h * t.bit_count(), "bad reference cut")
    if status == 2:
        check(code in survivors and not proof, "missing positive witness")
        return
    scale, cap = t.bit_count(), 5 * costs[t]
    pool = sorted(a for a, c in costs.items() if a.bit_count() in (3, 4) and scale * c < cap)
    union = 0
    for a in pool:
        union |= a
    check(status == int(union == full), "wrong exclusion stage")
    cursor = 0

    def visit(rest, available):
        nonlocal cursor
        check(rest and cursor < len(proof), "missing proof node")
        v = proof[cursor]
        cursor += 1
        check(v < n and rest & (1 << v), "pivot outside remaining vertices")
        for a in available:
            if a & (1 << v):
                left = rest & ~a
                next_pool = [b for b in available if b & left and a & b
                             and (a | b).bit_count() > 5
                             and scale * (costs[a] + costs[b] - costs[a & b]) < cap]
                visit(left, next_pool)
    visit(full, pool)
    check(cursor == len(proof), "trailing proof node")


def export_lean(code, entry, survivors, path):
    """Produce a closed Lean check starting from the requested labeled graph."""
    from verify import decode

    literal = json.dumps(code)
    if entry >> 10 == 2:
        model = list(survivors).index(code)
        source = f"""import CheegerTen
open CheegerPareto.Ten
example : code ({model} : Model) = {literal} := by decide +kernel
theorem result : Violates (edgesOf {model}) := violations {model}
#print axioms result
"""
    else:
        _, edges = decode(code)
        edge_text = ", ".join(f"({a},{b})" for a, b in edges)
        subset = ", ".join(map(str, vertices(entry & 1023, 10)))
        source = f"""import CheegerTen
open scoped BigOperators
open CheegerPareto CheegerPareto.Ten
namespace CatalogRow
def graph : EdgeSet 10 := {{{edge_text}}}
def reference : Finset V := {{{subset}}}
private def words := {literal}.toList.map (fun c => c.toNat - 63)
private def bit (p : ℕ) := (words.getD (1 + p / 6) 0).testBit (5 - p % 6)
theorem identifies : words.head? = some 10 ∧ words.length = 9 ∧
    (∀ i : Fin 3, bit (45 + i.val) = false) ∧
    ∀ a b : V, (a,b) ∈ graph ↔ a < b ∧ bit (b.val * (b.val-1) / 2 + a.val) = true := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem checked : search graph reference 10 Finset.univ (pool graph reference) = false := by
  decide +kernel
theorem result {{h : ℝ}} (hh : IsCheeger graph h) {{z : V → ℝ}} (hz : Pareto graph z) :
    5 * h ≤ ∑ v, z v :=
  excluded_by_search reference (by decide +kernel) (by decide +kernel) checked hh hz
#print axioms result
end CatalogRow
"""
    with path.open("x", encoding="utf-8", newline="\n") as output:
        output.write(source)


def inspect_record(index, survivors, lean_output=None):
    check(0 <= index < COUNT, "row out of range")
    with lzma.open(DATA / "graph10c.g6.xz", "rb") as src:
        src.seek(10 * index)
        code = src.read(10).decode("ascii").strip()
    with lzma.open(DATA / "cut-certificates.u16le.xz", "rb") as src:
        src.seek(2 * index)
        entry = int.from_bytes(src.read(2), "little")
    raw = lzma.decompress((DATA / "cover-proofs.bin.xz").read_bytes())
    pos = 0
    for ordinal in range(index + 1):
        length = shift = 0
        while True:
            b = raw[pos]
            pos += 1
            length |= (b & 127) << shift
            if b < 128:
                break
            shift += 7
        if ordinal == index:
            proof = raw[pos:pos + length]
            check(len(proof) == length, "truncated proof")
            check_row(code, entry, proof, survivors)
            print(f"PASS: row {index} {code}, reference mask={entry & 1023}, "
                  f"status={entry >> 10}, proof nodes={length}")
            if lean_output:
                export_lean(code, entry, survivors, lean_output)
        pos += length


def rejection_controls(tmp, audit, env, corpus, cuts, proofs):
    """Ensure corrupted branches, duplicated classes and omissions fail independently."""
    with corpus.open("rb") as f:
        f.seek(343 * 10)
        code = f.read(10)
    with cuts.open("rb") as f:
        f.seek(343 * 2)
        entry = f.read(2)
    with proofs.open("rb") as f:
        for _ in range(344):
            size = f.read(1)[0]
            check(size < 128, "unexpected proof length in control sample")
            tree = f.read(size)
    check(size > 3 and int.from_bytes(entry, "little") >> 10 == 1, "bad negative control row")
    reference = bytes([73, 8])  # {0,3,6}, status 2
    positive = b"ICOceQd{W\n"
    cases = [
        ("wrong cut", positive, bytes([1, 8]), b"\x00", 4),
        ("invalid pivot", code, entry, bytes([size, 10]) + tree[1:], 4),
        ("deleted child", code, entry, bytes([size - 1]) + tree[:-1], 4),
        ("trailing node", code, entry, bytes([size + 1]) + tree + b"\x00", 4),
        ("duplicate class", positive * 2, reference * 2, b"\x00\x00", 7),
        ("isomorphic relabelings", b"IJOG[BHvO\nICOceQd|O\n",
         (2048 + 385).to_bytes(2, "little") + reference, b"\x00\x00", 7),
        ("omitted classes", positive, reference, b"\x00", 8),
    ]
    inputs = [tmp / ("control-" + s) for s in ("graphs", "cuts", "trees", "groups")]
    for label, records, thresholds, nodes, expected in cases:
        for f, content in zip(inputs, (records, thresholds, nodes)):
            f.write_bytes(content)
        trial = subprocess.run([audit, *inputs], env=env, capture_output=True)
        check(trial.returncode == expected, f"failed rejection control: {label}")
    print("Rejected corrupted reference cuts, invalid pivots, missing children, trailing nodes, "
          "duplicate classes, isomorphic relabelings and an incomplete census.")


def replay(tmp, args, survivors):
    corpus, cuts, groups = (tmp / f for f in ("graph10c.g6", "cuts.bin", "groups.bin"))
    digest = unpack(DATA / "graph10c.g6.xz", corpus, 10 * COUNT)
    check(digest == CATALOG_SHA256, "catalog SHA-256 mismatch")
    unpack(DATA / "cut-certificates.u16le.xz", cuts, 2 * COUNT)
    unpack(DATA / "automorphisms.uleb128.xz", groups, 11_718_252)
    proofs = tmp / "trees.bin"
    unpack(DATA / "cover-proofs.bin.xz", proofs, 35_965_867)
    env = dict(os.environ)
    env.setdefault("OMP_NUM_THREADS", str(min(8, os.cpu_count() or 1)))
    screen = args.screen_exe.resolve() if args.screen_exe else compile_tool("screen", tmp)
    audit = args.audit_exe.resolve() if args.audit_exe else compile_tool("audit", tmp)
    rejection_controls(tmp, audit, env, corpus, cuts, proofs)

    generated, found = tmp / "generated.bin", tmp / "found.tsv"
    generated_proofs = tmp / "generated-trees.bin"
    run = subprocess.run([screen, corpus, generated, found, generated_proofs], env=env, check=True,
                         stdout=subprocess.PIPE, text=True)
    check(filecmp.cmp(cuts, generated, shallow=False), "cut certificates differ")
    check(filecmp.cmp(proofs, generated_proofs, shallow=False), "refutation trees differ")
    check(run.stdout.splitlines() == (DATA / "by-edges.tsv").read_text().splitlines(),
          "edge-count strata differ")
    check(found.read_text().splitlines() == (DATA / "survivors.tsv").read_text().splitlines(),
          "survivor table differs")
    with found.open() as table:
        rows = list(csv.DictReader(table, delimiter="\t"))
    check(len(rows) == len(survivors) and {r["graph6"] for r in rows} == set(survivors),
          "a surviving graph lacks an exact real witness")
    with corpus.open("rb") as src:
        for row in rows:
            code = row["graph6"]
            witness = survivors[code]
            index = int(row["index"])
            src.seek(10 * index)
            check(src.read(10) == (code + "\n").encode("ascii"), "catalog index")
            check(index == witness["catalog_index"] and int(row["edges"]) == witness["edges"]
                  and int(row["12kh"]) == 60 * Fraction(witness["h"]), "candidate fields")

    rebuilt = tmp / "rebuilt-groups.bin"
    run = subprocess.run([audit, corpus, cuts, proofs, rebuilt], env=env, check=True,
                         stdout=subprocess.PIPE, text=True)
    check(filecmp.cmp(groups, rebuilt, shallow=False), "automorphism stream differs")
    check(run.stdout.splitlines() == (DATA / "census-replay.log").read_text().splitlines(),
          "canonical audit differs")
    lines = set(run.stdout.splitlines())
    for row in survivors.values():
        index, code, m = row["catalog_index"], row["graph6"], row["edges"]
        level = 60 * Fraction(row["h"])
        check(f"candidate {index} {code} edges={m} 12kh={level} key={row['canonical_key']} "
              f"aut={row['automorphisms']}" in lines, "canonical key or stabilizer mismatch")
    print(run.stdout.rstrip())
    labeled = check_orbit_sum(groups)
    minimum = min(row["edges"] for row in survivors.values())
    print(f"PASS: {COUNT} connected classes, {labeled} labeled graphs, "
          f"{len(survivors)} violating classes. Minimum edges = {minimum}.")
    print("All edge minimizers:", *(code for code, row in survivors.items() if row["edges"] == minimum))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--witnesses-only", action="store_true", help="check the three positive examples only")
    mode.add_argument("--row", type=int, metavar="INDEX",
                      help="check one zero-based catalog row with Python alone")
    parser.add_argument("--lean-out", type=Path, metavar="NEW_FILE",
                        help="with --row, write a separately kernel-checkable Lean source")
    parser.add_argument("--screen-exe", type=Path, help="use an already compiled screen.cpp")
    parser.add_argument("--audit-exe", type=Path, help="use an already compiled audit.cpp")
    args = parser.parse_args()
    if args.lean_out and args.row is None:
        parser.error("--lean-out requires --row")
    known = witnesses()
    if args.row is not None:
        inspect_record(args.row, known, args.lean_out)
    elif not args.witnesses_only:
        scratch = ROOT / ".lake"
        scratch.mkdir(exist_ok=True)
        with TemporaryDirectory(prefix="order-ten-", dir=scratch) as tmp:
            replay(Path(tmp), args, known)
