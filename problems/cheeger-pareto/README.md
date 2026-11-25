# The three least-order counterexamples to the Cheeger–Pareto bound

There are **exactly three** connected counterexamples at order ten. The minimum is **18 edges**, attained by `ICOceQd{W` and `ICOceQd|O`. The latter is the original `IJOG[BHvO` under a relabeling. Both have h = 4/3 and minimum efficient mass 6. The remaining class, `ICOceQd~w`, has 21 edges, h = 5/3 and minimum efficient mass 8. The exact census covers arbitrary nonnegative real Pareto vectors. [Order-ten classification, certificates and replay](ORDER10.md) · [Machine-readable witnesses](order10/witnesses.json)

**Conjecture B is false, and the minimum counterexample order is 10.** On the connected simple graph encoded by `IJOG[BHvO`, the Cheeger constant is $4/3$ and the least total mass of an efficient vector is $6<20/3$. Every simple graph of order 2 through 9 satisfies B for **every** nonnegative real Pareto-efficient vector. [English paper](output/pdf/paper.pdf) · [Minimum-order proof](MINIMALITY.md) · [Lean theorem](CheegerMinimum.lean)

## Original questions

jinni asked about the coefficient $n/2$ on MathOverflow. DSM refuted this first version. Revision 5 introduced the coefficient $\lfloor n/2\rfloor$, and the Mathematics Stack Exchange question asked specifically about this revised statement. [MathOverflow 506070](https://mathoverflow.net/questions/506070/conjecture-involving-the-cheeger-constant-of-a-graph) · [Revision introducing B](https://mathoverflow.net/revisions/c774f5bd-ab71-4085-8a45-7df5d7b6ddec/view-source) · [Mathematics Stack Exchange 5118288](https://math.stackexchange.com/questions/5118288/conjecture-involving-the-cheeger-constant-of-a-graph) · [DSM's answer](https://mathoverflow.net/a/506124)

## Statement and proof

For a finite simple graph of order $n\ge2$, let $k=\lfloor n/2\rfloor$ and let $c(S)$ count edges with exactly one endpoint in $S$. Put $h=\min_{1\le |S|\le k}c(S)/|S|$. A nonnegative real vector $x$ is feasible if $x(S)=\sum_{v\in S}x_v\le c(S)$ for every $|S|\le k$. It is Pareto-efficient if the only feasible $y\ge x$ componentwise is $x$ itself. B asserts that every efficient vector has $x(V)\ge kh$, equivalently that their minimum mass $\rho(G)$ is at least $kh$.

For the ten-vertex witness, put $x=6e_9$. The three tight sets $\{0,7,8,9\}$, $\{1,2,3,9\}$ and $\{4,5,6,9\}$ cover the vertices and force equality with any dominating feasible real vector. A feasible vector of total below six can be increased at vertex 9. For the lower bound on order, submodularity restricts how the maximal tight sets of a hypothetical violation can meet. Through order nine only an eight-vertex cover by triples could remain, and that incidence pattern is impossible. [Exact graph certificate](PROOF.md) · [Lower-bound argument](MINIMALITY.md) · [LaTeX paper](paper.tex)

## Reproduce

With Lean 4.19.0, Git, Python 3.10 or newer and a C++17 compiler, run the following from this directory. The manifest pins all nine package revisions, including Mathlib v4.19.0 at **c44e0c8ee63ca166450922a373c7409c5d26b00b**. An initial **lake update** can regenerate the manifest. The commands below reuse the lock as shipped.

~~~sh
lake exe cache get
lake build
lake env lean CheegerPareto.lean
lake env lean CheegerMinimum.lean
lake env lean CheegerTen.lean
python3 verify.py
python3 verify_minimum.py
python3 verify_order10.py
~~~

The first two Python checks use the standard library. The witness check covers all 638 admissible cuts of the witness, including the empty set. The minimum-order checker verifies the per-graph exact certificates for all 273,192 connected representatives through order nine and the graph-independent obstruction certificates. The order-ten driver also compiles two C++17 tools and verifies the complete set of cut, tree and orbit certificates offline. The principal minimum-order Lean declarations are **CheegerPareto.not_conjectureB**, **CheegerPareto.rho_exact** and **CheegerPareto.minimum_counterexample_order**. Their axiom reports list **propext**, **Classical.choice** and **Quot.sound**. [Lean proof of the counterexample](CheegerPareto.lean) · [Axiom report for minimality](evidence/minimum-lean.log) · [Verification of the real-vector search](evidence/all-real-replay.log)

In a full checkout of the public repository, this extra command uses the existing kernel-replay driver to check the final theorem and its transitive mathematical dependencies starting from Lean's **Init**. The recorded run rechecked 4,488 declarations from 228 modules. [Replay log](evidence/minimum-kernel-replay.log)

~~~sh
lake env lean --run ../mabk-uniform-randomness/review/DependencyReplay.lean CheegerMinimum CheegerPareto.minimum_counterexample_order
~~~

## Research and data

| Material | Contents |
|---|---|
| [Review](REVIEW.md) · [Originality search](SEARCH.md) · [Problem status](problem-status.md) | Independent review, provenance, source history, search limitations and outcome. |
| [All witness cuts](evidence/cuts.tsv) · [Witness verifier](verify.py) | Labeled boundaries and masses. Run **python3 verify.py --write-cuts evidence/cuts.tsv** to regenerate. |
| [All-real certificates](evidence/all-real-graphs.tsv.gz) · [Universal proof states](evidence/cover-obstructions.json) | Exact per-graph records, checked offline. Format, data hashes and regeneration instructions are in [MINIMALITY.md](MINIMALITY.md). |
| [Order-ten certificates](order10/data/) · [Independent checker](order10/audit.cpp) | All 11,716,571 graphs, minimizing cuts, explicit negative proof trees, automorphism orders and positive witnesses. The orbit sum checks completeness against the labeled-graph recurrence. |
| [Earlier one-coordinate scan](search_spikes.c) · [Original scan results](evidence/spike-scan.tsv.gz) | Historical calculation for single-coordinate witnesses. The unrestricted proof and checker above settle minimum order. |
| [Discovery script](search_milp.py) | The original NumPy/SciPy mixed-integer search was used only to discover a candidate. |

The graph6 inputs in both census archives come from Brendan D. McKay's **Combinatorial Data**, under CC BY 4.0. The additional certificate fields and proofs were generated in this project. The paper builds with **tectonic --outdir output/pdf paper.tex**. [Graph catalog](https://users.cecs.anu.edu.au/~bdm/data/graphs.html) · [Attribution](https://users.cecs.anu.edu.au/~bdm/data/) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
