# Minimum order for arbitrary real vectors

**The least counterexample order is 10.** The lower bound holds for every finite simple graph of orders 2 through 9 and every nonnegative real Pareto-efficient vector. The graph with graph6 string `IJOG[BHvO` attains the least order. [Paper](paper.tex) · [Formal least-order theorem](CheegerMinimum.lean) · [Conjecture B](https://math.stackexchange.com/questions/5118288)

## Why it suffices to check covers by sets

Put $k=\lfloor n/2\rfloor$, let $c$ count crossing edges, and suppose that an efficient vector $z$ has $w=z(V)<kh$. Necessarily $h>0$. Every vertex lies in a tight admissible set. Otherwise its coordinate could be increased by the least positive slack of the finitely many constraints containing it. Therefore the inclusion-maximal tight sets cover $V$. Each has size less than $k$ since $h|S|\le c(S)=z(S)\le w$. At least two are needed.

For distinct inclusion-maximal tight sets $A,B$, write $I=A\cap B$ and $U=A\cup B$. The cut difference $c(A)+c(B)-c(I)-c(U)$ is twice the number of edges from $A\setminus B$ to $B\setminus A$. Feasibility on $I$ and nonnegativity imply

$$
c(U)\le c(A)+c(B)-c(I)\le z(A)+z(B)-z(I)=z(U)\le w.
$$

Hence $|U|>k$, since otherwise $U$ would itself be tight. Also $|U|\ne n-k$, since its complement would then have size $k$ and boundary at least $kh$. Finally $I$ is nonempty, since disjointness would give $w\ge h(|A|+|B|)>kh$. These three necessary conditions hold simultaneously for every distinct pair. Their proof quantifies over genuine real vectors and uses no integrality or restriction on support. [Lean cut and Pareto lemmas](CheegerMinimum/Analytic.lean)

## Excluding all smaller orders

The intersection condition gives $k<|U|\le2k-3$, so $k\ge4$. For $n\le9$ this forces $k=4$, with both sets triples meeting at precisely one point. Their union has size five, ruling out $n=9$ by $|U|\ne n-k$.

At order eight, suppose such triples covered all vertices. Two triples cover five, so select three distinct triples. They cover at most seven because each meets the first. A fourth triple through an outside point has only two remaining positions to meet the original three. One point $p$ therefore belongs to three triples. These triples cover seven points and their six vertices other than $p$ come in three disjoint pairs. A triple through the eighth point cannot omit $p$, as it would have to meet all three pairs. Nor can it contain $p$, since both its other points would then have to be outside the seven. This rules out order eight and completes the lower bound. The ten-vertex example gives the upper bound. [Lean cover obstruction](CheegerMinimum/Covers.lean) · [Witness](CheegerPareto.lean)

## Exact certificate and independent replay

Run **python3 verify_minimum.py** from the problem directory. No network, external solver or nonstandard Python package is needed. The generator used McKay's connected graph6 files and an incremental boundary count. The default verifier computes each boundary afresh by counting neighbors outside the set. Both use integer cross-products to compare ratios. The verifier reconstructs the original graph6 byte stream of each order and checks its count and SHA-256. [Checker](verify_minimum.py) · [Catalog](https://users.cecs.anu.edu.au/~bdm/data/graphs.html) · [Catalog digests](evidence/small-graphs.log)

For order $n$, list the nonempty subsets of size less than $k$ in increasing order of their integer vertex mask. In **all-real-graphs.tsv.gz**, each row records the graph6 string, reduced $h$, a hexadecimal bitset and the cover-search result. Bit $j$ is set exactly when the $j$-th candidate $A$ satisfies $c(A)<kh$. A zero in the last column means that these candidates do not contain a covering family satisfying the three pair conditions. The candidate result is only an exclusion test. On the ten-vertex positive control it admits a cover, whose actual feasibility and efficiency are independently proved in Lean. [All labeled graph records](evidence/all-real-graphs.tsv.gz) · [Generation log](evidence/all-real-generation.log) · [Independent replay](evidence/all-real-replay.log)

**cover-obstructions.json** is a second, graph-independent certificate. Its key is the order. Each state is a pair consisting of the remaining vertex mask in decimal and the available candidate bitset in hexadecimal. The verifier requires the full root and a nonempty remaining mask in every state. For each candidate covering the least remaining vertex, it demands the exact successor obtained by deleting that candidate's vertices and retaining only candidates pairwise compatible with it. Every transition decreases the remaining mask. A real counterexample would give choices reaching the empty mask, which is absent. The file certifies the full candidate pool before graph-specific costs discard any sets. The Lean proof uses neither certificate file. [Finite proof states](evidence/cover-obstructions.json)

| Order | Connected isomorphism classes checked | States in the universal certificate | Unresolved graphs |
|---:|---:|---:|---:|
| 2 | 1 | 1 | 0 |
| 3 | 2 | 1 | 0 |
| 4 | 6 | 2 | 0 |
| 5 | 21 | 2 | 0 |
| 6 | 112 | 7 | 0 |
| 7 | 853 | 8 | 0 |
| 8 | 11,117 | 3,060 | 0 |
| 9 | 261,080 | 38 | 0 |
| **Total** | **273,192** | **3,119** | **0** |

To regenerate, download **graph2c.g6** through **graph9c.g6** from the linked catalog into one directory and run **python3 verify_minimum.py --generate DIRECTORY**. The original graph6 records are Brendan D. McKay's data under CC BY 4.0. The added columns and the cover proof states were computed in this project. [Attribution](https://users.cecs.anu.edu.au/~bdm/data/) · [License](https://creativecommons.org/licenses/by/4.0/)

For the formal verification run **lake build** and **lake env lean CheegerMinimum.lean**. The theorem **CheegerPareto.minimum_counterexample_order** states an attained least order for the exact graph and real-vector definitions of B. The lower-bound theorem applies to disconnected graphs as well. [Build log](evidence/minimum-build.log) · [Axiom report](evidence/minimum-lean.log)

All three order-ten isomorphism classes and both 18-edge minimizers are identified in the [order-ten classification](ORDER10.md).
