# Formal verification status

The program-level theorem is `ShellMinimax.executed_maximum` in [Execution.lean](Execution.lean). Its arithmetic path theorem is `ShellMinimax.actual_threshold_maximum` in [Charging.lean](Charging.lean). For every positive gap list and every permutation of the ranks in `Fin n`, the length of the executed insertion comparison trace is bounded by `thresholdMaximum n H`. A second conjunct gives a permutation with equality. Validity for every legal descending table follows immediately. Its hypotheses concern positive gaps. Arbitrary rank permutations are admissible.

The model reads each residue in ordinary position order and inserts into the sorted prefix, held in reverse order so the rightmost predecessor is examined first. `Operational.ins` returns one comparison when it stops at a smaller or equal predecessor, charges a successful shift and recurses on a larger predecessor, and charges zero on an empty prefix. Distinct keys give the strict-key model in the question. Recording the key once per comparison makes trace length the operational cost. The executable `Operational.step` materializes each residue result once. `Operational.execute` returns the final array and its trace, and `execute_trace` identifies that program with the comparison trace used by the path proof. `ShellMinimax.slots_eq` in `Geometry.lean` identifies each residue with its arithmetic progression, and `index_lt_colLen` rules out the fallback read on legal passes.

## Kernel entry points

Names below are under `ShellMinimax`, except for explicitly qualified child namespaces. A library import of `Shellsort` exposes these theorems.

| Claim | Lean entry points | Scope |
|---|---|---|
| Executed insertion charge and nonempty-prefix stopping comparison | `Operational.ins_count`, `pass_charge` | The actual scan and the exact predecessor-count expression. |
| Sorting commutes with a monotone projection | `Operational.map_values`, `Operational.pass_map`, `pass_le` | Includes binary thresholds. The sorted list at position i is below a cut precisely when its chain offset lies inside the selected prefix. |
| Cardinality, monotonicity and singleton transport | `binaryPass_card`, `binaryPass_mono`, `binaryPass_insert`, `transported_fresh`, `pass_mark` | Positive gaps for transport. Includes unequal final chain lengths. |
| Positions and rank permutations correspond bijectively | `positions_walk`, `positions_injective`, `permutation_of_walk` | The reverse direction is unique existence for every maximal walk. |
| Exact cost on one input | `actual_threshold_path` | Actual trace length equals the sum of the archive's arithmetic edge weights. |
| Attainable fixed-table maximum | `walk_le_bellman`, `bellman_attained`, `actual_threshold_maximum`, `executed_maximum` | All permutations and all positive gap lists. |
| Full counting polynomial | `distribution_paths`, `distribution_actual` in [Distribution.lean](Distribution.lean) | The edge recurrence equals the sum of a monomial for each permutation with exponent its executed comparison count. Moment and complexity formulas are derived analytically. |
| Mandatory comparisons per pass | `pass_baseline`, `baseline_le` in [Baseline.lean](Baseline.lean) | Lower bounds for every actual execution, summed across passes. |
| Legal schedules and complete row coverage | `Certificate.legal_last`, `Certificate.enumeration`, `Certificate.tableGaps_eq` | Finite powerset enumeration agrees with the positive strictly descending schedule definition and compulsory gap 1. |
| Finite certificate soundness | `Certificate.potential_upper`, `Certificate.row_sound`, `Certificate.certificate_sound` in [Certificates.lean](Certificates.lean) | Witness parsing supplies data. The checker validates permutations, executes them, checks each strict exclusion, verifies every local upper inequality for winners, and requires at least one winner. |
| Complete numerical example | `Reflected5.global`, `Reflected5.exact_minimizers` in [SmallCertificate.lean](SmallCertificate.lean) | All eight schedules at n=5. The optimum is 10 and the complete list is (1), (3,1), (4,3,1). |
| All reported winner lower bounds | `Witnesses.w17_9_attains` through `Witnesses.w23_22_attains` in [original-size proofs](WinnerWitnesses.lean) and [extension proofs](ExtensionWitnesses.lean) | Thirteen individual inputs for the thirteen winning rows at sizes 17–23. Each gives an actual permutation at the stated value. |
| Concrete size-17 subcertificates | `Reflected17.mask0` through `mask7`, `Block17.state0` through `state7` | The first eight losing masks and a separate serial replay of masks 256–271, plus all 124 outgoing edges of the first eight states for (9,6,4,1). The two kinds of index refer to different objects. |

The root declaration `thresholdMaximum_exact` in the original draft only stated an extremum over a weighted path model. The operational identification and permutation reconstruction in the table are additional kernel-checked results. The archived mutable-array program and its two `#eval` examples have no role in these proofs.

## Axioms and reproduction

The project pins Lean 4.19.0 (6caaee842e94), Lake 5.0.0 and mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b. Per-module compilation and direct theorem audits are recorded under [full source build](logs/lake-build.txt), [final program build](logs/execution-build.txt), [axioms](logs/axioms.txt) and [environment](logs/environment.txt). The audit file lists each queried declaration and the kernel's reported dependencies. No project axiom, admitted theorem or native reduction axiom is part of the mathematical proof. Standard Lean foundations used in these proofs may include propositional extensionality, quotient soundness and classical choice. For the principal maximum, the certificate theorem, and the concrete witness and numerical entry points, the audit reports exactly `propext`, `Classical.choice` and `Quot.sound`. The finite tests use kernel reduction of proof terms.

```sh
lake exe cache get
lake build
lake env lean --trust=0 Audit.lean
lake env lean --trust=0 Replay.lean
```

The last command takes the transitive used-constant closure of the selected results, rejects unsafe/partial dependencies and axioms outside Lean Init, and sends the declarations back through the kernel in module order. The recorded replay accepted 28 theorem roots and 3,129 dependencies and roots above Init. [Replay program](Replay.lean) · [Replay log](logs/kernel-replay.txt)

## Large numerical instances and reflection

**Open numerical theorem.** For each n=17 through 23 the project lacks a single kernel-checked instance of `certificate_sound` with all rows and every winning potential verified. The external computations establish these optima and all their ties under the mathematical path proof. The individual witness theorems prove each winning table costs *at least* the tabled value.

For remaining-cost certificates, the checker accepts a nonnegative function V on subsets, verifies V(empty) ≤ U and requires w(S,x) + V(S∪{x}) ≤ V(S) on every edge. This proves the upper bound by telescoping. An untrusted DP may emit these labels. For n=17 the supplied compressed potential unpacks to 131,072 little-endian UInt16 labels, 262,144 bytes. DEFLATE reduces this to 72,865 bytes. The exporter performs a lossless round trip and records both SHA-256 values. The kernel pilot embeds the labels on the eight selected sources and all their successors, then checks all the local inequalities. Joining separately generated sparse blocks for a global proof requires every block to refer to one shared V or to prove agreement on each boundary. Hash identity alone would not establish that statement in Lean. [Compressed potential](evidence/potential17.zlib) · [Export](logs/potential17-export.txt) · [Kernel pilot](logs/Potential17.txt)

The six original winning tables have 62,980,096 full-lattice edge inequalities in total. The five original raw files contain 1,015,802 strict losing rows. These counts distinguish the cost of a global numerical proof from successful reduction of one input or a few DP states. The source generator accepts contiguous certificate slices. The size-five instance exercises all layers, including strict exclusions, full potentials, coverage and tie identification. The repository retains measured pilot logs. [Small global example](logs/SmallCertificate.txt) · [Eight exclusion masks](logs/Slice17.txt) · [Winner reductions](logs/WinnerWitnesses.txt)

A larger monolithic trial generated the 256 original size-17 exclusions for masks 256–511. After 1,285.7 seconds it had consumed 537 CPU seconds and held 6,358,327,296 bytes in its working set. The shared host had 1,126 MiB of physical memory free. The run stopped at the 2 GiB free-memory floor with no completed chunk theorem. The captured source can be regenerated exactly with the command below. These measurements give a practical limit of this proof representation under this workload. They do not establish a lower bound for other reflection strategies. The verified short blocks, the compact numerical table and the formal potential lemma supply a starting point for a faster shared-table kernel checker. [Measured resources](logs/bench17-resources.jsonl) · [Benchmark result](logs/bench17.txt) · [Benchmark input](evidence/Bench17.lean)

```sh
python reflect.py --certificate cert17.txt --first 256 --limit 256 --timed --out evidence/Bench17.lean
python reflect.py --certificate cert17.txt --first 256 --limit 16 --timed --out evidence/Serial16.lean
lake env lean -j 1 -DElab.async=false --trust=0 evidence/Serial16.lean
```

The smaller serial retry checked all sixteen rows at masks 256–271. Its two internal timestamps were 77.711 seconds apart, with 140.54 seconds elapsed including process startup, imports and teardown. These rows are additional kernel witnesses. The input lengths and distribution of B/X/O records vary across the five large files, so a straight-line timing forecast would be unjustified. An earlier reflection attempt also isolated a reduction problem in the generic sorted-finset schedule. The final checker uses an explicitly filtered descending range and proves its equivalence in `tableGaps_eq`. [Serial run](logs/serial16.txt) · [Checked input](evidence/Serial16.lean)

## Analytical and implementation boundaries

The first-pass extremal preimage, exact product-of-chains optimization, asymptotic operation counts, quotient-block two-pass optimization, simultaneous two-pass localization, nested fiber construction, nested asymptotic and power-of-two formulas have handwritten arguments and computational tests as described in [the review](REVIEW.md). Full Lean statements connecting the mixed-radix executable and those restricted-family theorems to the operational model remain open. The kernel theorem uses a counted functional chain insertion. A refinement proof for the separate imperative array program remains open. The C++ memory layout, Python parser, SHA-256 implementation and compilers are also outside this kernel proof. The certificate soundness theorem checks data directly. The unrestricted asymptotic optimum and the complete finite minimizer sets for sizes 24–30 remain open in this project.
