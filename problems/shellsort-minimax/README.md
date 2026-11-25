# Exact Shellsort minimax

For ordinary Shellsort on permutations of distinct keys, exhaustive computational certificates give the exact minimum, over gap tables, of the worst number of **executed key comparisons**. A legal table has strictly decreasing positive gaps below the input length and ends in 1. Each failed key comparison that stops a scan counts once. The seven certificates cover all 4,161,536 legal tables for the sizes below.

| Keys | Minimum worst-case comparisons | All minimizing gap tables |
|---:|---:|---|
| 17 | 86 | (9,6,4,1) |
| 18 | 94 | (17,9,6,4,1) |
| 19 | 103 | (9,7,4,1) |
| 20 | 112 | (11,7,5,1) |
| 21 | 121 | (9,7,4,1), (20,9,7,4,1) |
| 22 | 131 | (5,3,1), (7,5,4,1), (8,7,3,1), (9,7,4,1), (21,8,7,3,1) |
| 23 | 139 | (9,7,4,1), (22,9,7,4,1) |

Ying Wai Lee established the finite optima through 16 keys. Mike Dokken (mkdokken) subsequently published the candidate values and ties above. The certificates establish the upper bound for every winner and a strict exclusion for every other table. Project S and LeanPool contain closely related marked-key and threshold arguments for the mean-cost problem. [Lee's paper](https://arxiv.org/abs/2112.11127) · [Dokken's tables](https://github.com/mkdokken/ShellSort/blob/cc4a0533c6ce9cc4eaa4d371141621eba9bbcdf0/README.md) · [Detailed attribution](PRIOR_ART.md)

Lean 4.19.0 proves that an actual execution trace has its Boolean-lattice path cost, that a permutation attains the Bellman maximum, and that the certificate checker is sound. The full global numerical certificates at sizes 17–23 were replayed computationally. A complete size-five instance and individual witnesses for all thirteen winning rows at sizes 17–23 were checked by the Lean kernel. [Program theorem](Execution.lean) · [Formal coverage](PROOF_STATUS.md)

- [Mathematical and computational review](REVIEW.md)
- [Prior art and search limitations](PRIOR_ART.md)
- [Paper](paper.pdf) and [editable Typst source](paper.typ)
- [Original archive](original/shellsort_minimax_v3.zip), SHA-256 `e4add74b4fd20395b9ee74a03cf49e574cffce6ac72fdc0156a071677e9a15ce`
- [Size 17–21 replay](logs/strict-replay.txt), [size 22](logs/verify22.txt), [size 23](logs/verify23.txt) and [larger fixed-table bounds](logs/larger-bounds.txt)

## Build and check the mathematics

Run the following commands from this problem directory with Git on PATH. The `lean-toolchain` file selects Lean 4.19.0, and the Lake manifest pins mathlib and its transitive dependencies.

```sh
lake exe cache get
lake build
lake env lean --trust=0 Audit.lean
lake env lean --trust=0 Replay.lean
```

The catalog uses Lake’s standard `.lake/packages` directory. The pinned mathlib cache looks for ProofWidgets there on a fresh installation. The recorded Windows build reused a preinstalled shared copy of the same package revisions. The first attempted dependency clone was stopped once the local cache was available. Its setup log is separate from the successful build of the original drafts in `logs/build-drafts.txt`. No local absolute path is required by the project configuration. The counted chain loop is in `Operational.lean`. The complete program and its attained maximum theorem are in `Execution.lean`. `Charging.lean` connects its traces to the arithmetic recurrence. The certificate checker is in `Certificates.lean`. `Executable.lean` also contains a mutable-array executable retained from the archive.

## Reproduce the computations

A C++20 compiler and Python 3.10 or later suffice. Use the following Unix commands or run `build-msvc.cmd` on Windows, where the executables have an additional `.exe` suffix.

```sh
mkdir -p .work
c++ -std=c++20 -O3 minimax.cpp -o .work/minimax
c++ -std=c++20 -O3 minimax_fast.cpp -o .work/minimax_fast
c++ -std=c++20 -O3 potential.cpp -o .work/potential
python -O audit.py --small 8 --binary .work/minimax
python -O oracle.py --certificate cert17.txt cert18.txt cert19.txt cert20.txt cert21_fast.txt
python -O check_extension.py --full .work/potential --mixed .work/minimax cert22.txt cert23.txt
python families.py
python families.py --partial 24 25 26 27 28 29 30 --binary .work/minimax > logs/larger-bounds.txt
python compressed.py --bounds logs/larger-bounds.txt
```

`oracle.py` computes winner maxima independently by forward relaxation on all subsets. The extension verifier checks every raw record with Python, computes all winner upper bounds using a second, reverse full-lattice solver, computes them again by mixed-radix DP, and executes the reconstructed maximizing permutations. To regenerate a certificate, direct the output to a fresh path, for example `.work/minimax_fast 22 cert .work/reproduced22.txt`. The resulting witness pool can vary across C++ standard libraries. The row coverage, optimum and ties must agree. The working original five files retain their exact received bytes. Use `check_extension.py` with any of the seven files for a second native upper-bound replay.

The original generator's search statistics classify the *method used during the search*. Rejection witnesses discovered by an exact DP also become X rows in the finished certificate. Historical archive files beginning with `validation_`, `cert_run` or a bare input size are original evidence. New logs are under [logs](logs). The historical round reports mention earlier-round scripts that were absent from the supplied ZIP. Reproduction of those restricted claims here uses `families.py`.

## Reproduce the kernel reflection examples

```sh
python reflect.py --certificate cert5.txt --full .work/potential --mixed .work/minimax --out SmallCertificate.lean
python reflect.py --certificate cert17.txt --first 0 --limit 8 --out Slice17.lean
python reflect.py --witnesses winner_witnesses.txt --out WinnerWitnesses.lean
python reflect.py --witnesses extension_witnesses.txt --out ExtensionWitnesses.lean
python potential_pilot.py --binary .work/potential
lake build
```

The translator supplies untrusted data. Lean decides the finite tests and applies the proved soundness theorem. The size-five example covers all eight gap tables and names all three minimizers. The size-17 examples replay a contiguous group of exclusions and a block of upper-potential inequalities. The numerical boundary of each instance is recorded in [PROOF_STATUS.md](PROOF_STATUS.md).

## Provenance

The enclosed original ZIP preserves all 47 input files. It can be extracted separately for a file-by-file comparison. This catalog edition adds the result table and public provenance here, uses the standard dependency directory, and replaces one machine-specific temporary pathname in the audit log. All comparison data, certificate bytes, proof sources and measured results match the reviewed snapshot. Run `sha256sum -c SHA256SUMS` from this directory to verify the catalog edition. Generative AI assisted with the original research, review and Lean formalization.

To regenerate the paper with Typst, run `typst compile paper.typ paper.pdf`. The verified typesetting run used Typst 0.15.2 and Cambria. The bibliographic scripts `search_sources.py`, `search_overlap.py` and `search_followup.py` repeat the public searches. Service availability and later index results can differ from the saved evidence.
