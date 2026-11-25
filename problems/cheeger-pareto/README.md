# A counterexample to the floor-corrected Cheeger–Pareto inequality

The connected simple graph with graph6 encoding `IJOG[BHvO` has 10 vertices, 18 edges, Cheeger constant $4/3$, and an attained minimum efficient mass $\rho(G)=6$. The proposed lower bound is $5(4/3)=20/3$. This refutes jinni's Conjecture B. The earlier unrounded Conjecture A was refuted by DSM. [Question B](https://math.stackexchange.com/questions/5118288) · [MO revision introducing B](https://mathoverflow.net/revisions/c774f5bd-ab71-4085-8a45-7df5d7b6ddec/view-source) · [DSM's answer](https://mathoverflow.net/a/506124)

For a finite simple graph of order $n\ge2$, let $k=\lfloor n/2\rfloor$. Write $c(S)$ for the number of edges with exactly one endpoint in $S$ and set $h(G)=\min_{1\le |S|\le k}c(S)/|S|$. The feasible vectors are all $x\in\mathbb R_{\ge0}^{V}$ with $x(S)=\sum_{v\in S}x_v\le c(S)$ for every $|S|\le k$. A vector is Pareto-efficient if every feasible $y$ dominating it coordinatewise equals it. Conjecture B asserted $\rho(G)=\min_{x\text{ efficient}}x(V)\ge k h(G)$.

Use labels 0 through 9. The vector $x=6e_9$ is feasible. The sets $\{0,7,8,9\}$, $\{1,2,3,9\}$, and $\{4,5,6,9\}$ each have boundary six and cover every vertex. They force equality with $x$ for any dominating feasible real vector. Conversely, a feasible vector of mass below six can be increased at vertex 9, which proves the claimed minimum.

## Research materials

| Material | Contents |
|---|---|
| [Paper (PDF)](output/pdf/paper.pdf) · [LaTeX source](paper.tex) | Two-page proof from the triangle structure, independent of exhaustive computation. |
| [Finite certificate](PROOF.md) · [All cuts](evidence/cuts.tsv) | Exact cut minima, witnesses, and all 638 admissible labeled subsets. |
| [Lean source](CheegerPareto.lean) · [Dependency lock](lake-manifest.json) | General definitions, kernel-checked cuts, graph6 identity, connectivity certificate, real-vector proofs and the final negation. |
| [Review](REVIEW.md) · [Literature search](SEARCH.md) · [Problem status](problem-status.md) | Acceptance criteria, original errors, prior art, dated query evidence, restrictions and attribution. |
| [Independent verifier](verify.py) · [Standard output](verification.txt) | Graph6 decoding, reachability, two cut counts, discovery of the support, exact rational comparisons and a tight cover. |
| [Smaller-graph search](search_spikes.c) · [Results](evidence/small-graphs.log) | A separate catalog scan restricted to witnesses supported on one vertex. |

## Reproduce the formal and numerical checks

Install Lean through [elan](https://github.com/leanprover/elan) or use the [official Lean 4.19.0 release](https://github.com/leanprover/lean4/releases/tag/v4.19.0). Run the following from the project directory with Git and Python 3.10 or newer. The verifier uses the Python standard library.

~~~sh
lake update
lake exe cache get
lake build
lake env lean CheegerPareto.lean
python3 verify.py
~~~

The shipped manifest fixes the Mathlib commit to **c44e0c8ee63ca166450922a373c7409c5d26b00b** (v4.19.0) and locks its eight transitive dependencies. For replay of that exact lock, one can start at the cache command. Setting **MATHLIB_NO_CACHE_ON_UPDATE=1** skips Mathlib's automatic cache download during the update when the explicit cache command follows. In Windows installations with the Python launcher, **py -3 verify.py** runs the same verifier.

The direct Lean check prints

~~~text
'CheegerPareto.not_conjectureB' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

The finite decisions use kernel reduction. The Python check ends with a gap of $2/3$. To regenerate the complete cut certificate, run **python3 verify.py --write-cuts evidence/cuts.tsv**. Masks use bit $v$ for vertex $v$. The two-page paper builds with **tectonic --outdir output/pdf paper.tex**. [Update](evidence/lake-update.log) · [Cache](evidence/lake-cache.log) · [Build](evidence/lake-build.log) · [Direct Lean check](evidence/lean.log) · [Python run](evidence/python.log)

## Optional searches

The submitted **search_milp.py** is preserved as discovery provenance. Its NumPy/SciPy mixed-integer model, time limits and floating-point tolerances play no role in verification. Solver output can vary.

The independent C99 program **search_spikes.c** checks every possible single-vertex support. For a fixed support $u$, the only possible efficient weight is the least admissible boundary through $u$. A smaller weight admits an increase at $u$. At that least boundary, efficiency is equivalent to the union of the tight sets covering the graph. The necessity follows by increasing any uncovered coordinate by less than the minimum of its positive slacks. For a connected graph every nonempty cut has positive capacity, so all relevant tight sets contain $u$.

Compile with **cc -O2 -std=c99 search_spikes.c -o scan-spikes**. Run **./scan-spikes graph6.txt** for the positive control. Provide the connected catalog files **graph2c.g6** through **graph9c.g6** as successive arguments to reproduce the scan. All 273,192 graphs gave zero violations in this support class. Disconnected graphs have $h=0$ for $n\ge2$ and therefore satisfy B. Minimality with unrestricted real vectors remains open in this review.

The compressed TSV preserves the original graph6 codes in catalog order and adds the exact expansion and violating supports for each graph. The second and third columns are review calculations. The log gives the individual input URLs and SHA-256 checksums. [Full scan](evidence/spike-scan.tsv.gz) · [Input details](evidence/small-graphs.log) · [Brendan McKay's graph catalog](https://users.cecs.anu.edu.au/~bdm/data/graphs.html) · [Data attribution and CC BY 4.0](https://users.cecs.anu.edu.au/~bdm/data/) · [License](https://creativecommons.org/licenses/by/4.0/)
