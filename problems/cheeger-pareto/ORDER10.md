# The connected ten-vertex counterexamples

**Exactly three isomorphism classes violate Conjecture B on ten vertices. The minimum edge count at this order is 18, attained by exactly two classes.** The census covers all nonnegative real Pareto-efficient vectors.

| Catalog graph6 | Edges | $h$ | $\rho$ | $5h-\rho$ | Automorphisms |
|---|---:|---:|---:|---:|---:|
| `ICOceQd{W` | 18 | 4/3 | 6 | 2/3 | 6 |
| <code>ICOceQd&#124;O</code> | 18 | 4/3 | 6 | 2/3 | 4 |
| `ICOceQd~w` | 21 | 5/3 | 8 | 1/3 | 48 |

In the order shown, the zero-based positions in McKay's connected catalog are 8,003,575, 8,003,577 and 8,003,588. The original `IJOG[BHvO` is the second graph. The permutation sending its successive vertices 0 through 9 to **2, 7, 4, 1, 0, 3, 6, 5, 8, 9** carries its edge set to the second catalog edge set. The second graph has a degree-four vertex and the first has none. [Exact witnesses and permutation](order10/witnesses.json) · [Lean isomorphism and nonuniqueness proofs](CheegerTen.lean)

## Positive certificates

All three graphs have the triangles on $\{0,3,6\}$, $\{1,4,7\}$, $\{2,5,8\}$ and $\{0,7,8\}$. The only other edges are incident to vertex 9. In the first graph its neighbors are $\{0,1,2,3,7,8\}$. In the second they are $\{0,1,2,3,5,7\}$. In the third it is adjacent to all nine other vertices.

For the two 18-edge graphs the least boundaries at sizes 1 through 5 are **2, 3, 4, 6, 7**. For the 21-edge graph they are **3, 4, 5, 8, 9**. The set $\{0,3,6\}$ attains the Cheeger ratio in every case. The minimum boundary of any admissible set containing 9 is, respectively, 6, 6 and 8. Give vertex 9 that weight and all other vertices zero. Adjoining 9 to each of the first three triangles produces tight four-sets which cover all vertices. Every feasible real vector dominating this spike must agree with it on each tight set. Conversely, for a feasible vector of smaller total, adding the deficit at vertex 9 preserves all cut inequalities. This proves the exact efficient minima in the table. [Kernel-checked graph and cut data](CheegerTen/Models.lean) · [Real-vector proofs](CheegerTen.lean)

## Why a finite refutation rules out every real vector

Let $z$ be an efficient real vector of total $w<5h$. Every vertex belongs to an inclusion-maximal tight admissible set. Otherwise one could increase an uncovered coordinate by the least positive slack in the finitely many constraints through it. Every tight set has fewer than five vertices, because $h|A|\le c(A)=z(A)\le w$.

For distinct maximal tight sets $A,B$, put $I=A\cap B$ and $U=A\cup B$. Cut submodularity and feasibility on $I$ give $c(U)\le z(U)$. If $|U|\le5$ then $U$ is tight, contradicting maximality. Disjointness would give $w\ge h(|A|+|B|)>5h$. Thus $I$ is nonempty and $|U|>5$. Every maximal tight set has a different partner since it cannot cover ten vertices by itself. As the partner has size at most four, every maximal tight set has size **three or four**.

Choose a nonempty reference cut $T$ of size at most five. The census supplies one attaining $h$. Every maximal tight set must satisfy $|T|c(A)<5c(T)$. Distinct members also satisfy

$$
c(A)+c(B)-c(I)\le z(A)+z(B)-z(I)=z(U)\le w<5h .
$$

In integer arithmetic the last necessary comparison is $|T|(c(A)+c(B))<5c(T)+|T|c(I)$. One implementation uses this cut arithmetic. The other uses $c(U)+2e(A\setminus B,B\setminus A)$, the same left-side capacity after subtracting $c(I)$. All tests remain sound if the reference cut merely upper-bounds $h$. [Lean exclusion theorem](CheegerTen/Exclusion.lean)

Start with all eligible triples and four-sets. At every node the supplied refutation names a remaining vertex. For each available set containing it, the checker visits the corresponding child after removing that set's vertices and filtering the other sets by compatibility and intersection with the remainder. A node with no eligible set through its pivot closes that branch. Every supplied pivot must be uncovered, including at a leaf. A feasible violating cover would force a branch reaching the empty remainder. This makes a complete refutation impossible for a genuine counterexample. The verifier checks that every required child is present and that no bytes remain unused.

Of **11,716,571** representatives, **9,885,683** lacked even an initial cover. A further **1,830,885** had a covering union but no compatible covering family. The remaining **three** all have the exact real witnesses above. All **774,628** representatives with 9–17 edges were excluded. Among **561,106** with 18 edges, exactly the first two rows of the table survive. Across the **10,380,837** denser graphs, exactly the 21-edge row survives. The negative certificates contain **24,249,296** vertex choices in **11,716,568** trees. The largest has 121 nodes. [Strata for every edge count](order10/data/by-edges.tsv) · [Audit output](order10/data/census-replay.log)

## Independent check of the isomorphism-class census

The input comes from Brendan McKay's collection. Completeness was also verified independently of the catalog publisher. For each connected input, the auditor forms an ordered partition of vertices, refining each cell by its vertices' neighbor counts in each splitter cell. It chooses a smallest nonsingleton cell, with ties resolved by the cell order, and branches on the vertex singled out first. Further refinements preserve the order of existing cells. A discrete partition encodes a labeled adjacency string. The minimum string over the leaves is the key.

Relabeling transports the entire tree and leaves its minimum key invariant. Equal keys exhibit identical adjacencies in the corresponding leaf orders. Different branches give different vertex orders since the first individualized vertex retains its place ahead of its former cell mates. Fixing one minimizing leaf, its images under automorphisms are exactly the minimizing leaves. The number of such leaves therefore equals $|\mathrm{Aut}(G)|$. The implementation groups vertices in a cell when exchanging them and fixing the others preserves adjacency. Their branches have equal keys and counts, so one branch is evaluated and its count multiplied by the group size.

All input keys were distinct. The sum of $10!/|\mathrm{Aut}(G)|$ was **34,496,488,594,816**. To obtain the total independently, count all labeled graphs by the size $j$ of the component containing vertex 0:

$$
C_n=2^{\binom n2}-\sum_{j=1}^{n-1}\binom{n-1}{j-1}C_j\,2^{\binom{n-j}{2}},\qquad C_1=1.
$$

$C_{10}$ equals the orbit sum. The representatives are connected and their disjoint orbits already account for every connected labeled graph. This checks both omissions and duplicates. The three positive stabilizers were also counted by direct degree-preserving permutations in Python. [Canonical-labeling and orbit auditor](order10/audit.cpp) · [Raw catalog source](https://users.cecs.anu.edu.au/~bdm/data/graphs.html)

## Replay and binary formats

~~~sh
python3 verify_order10.py                         # both C++17 passes and the Python checks
python3 verify_order10.py --witnesses-only        # Python only, three positive cases
python3 verify_order10.py --row 343               # Python only, one 16-node negative certificate
lake build
lake env lean CheegerTen.lean
python3 verify_order10.py --row 343 --lean-out .lake/CatalogRow343.lean
lake env lean .lake/CatalogRow343.lean
~~~

The optional export writes a new Lean file for the requested row. For a negative record it identifies the graph6 adjacency and checks the finite exclusion by kernel reduction. A positive record refers to the corresponding proved model. Row 343 was exported and checked locally and is included in CI. [Individual-row Lean replay](evidence/order-ten-row-343.log)

The full replay uses a C++17 compiler and Python 3.10 or later with its standard library. OpenMP is optional. On Windows run in a Visual Studio developer shell, or supply **--screen-exe** and **--audit-exe** pointing to programs built from the two shipped sources. No download or solver is needed for the census. The replay stages uncompressed inputs under the project's ignored **.lake** directory and removes them when it finishes. [Replay driver](verify_order10.py) · [Generator](order10/screen.cpp) · [Independent checker](order10/audit.cpp) · [Recorded run](evidence/order-ten-verification.log)

All four XZ streams are ordered by the same zero-based catalog index. Their decompressed formats are as follows.

| File | Contents |
|---|---|
| [graph10c.g6.xz](order10/data/graph10c.g6.xz) | The original 117,165,710 graph6 bytes, including LF terminators. SHA-256 **0642748d4518ce8cb30e5b13866ef527357064082729730316f3d57dc41b65f5**. |
| [cut-certificates.u16le.xz](order10/data/cut-certificates.u16le.xz) | One little-endian 16-bit integer per graph. Bits 0–9 give the vertex mask of $T$. The remaining bits give status 0 for a missing vertex, 1 for a refuted covering union, or 2 for a survivor. |
| [cover-proofs.bin.xz](order10/data/cover-proofs.bin.xz) | Per graph, an unsigned LEB128 byte count followed by that many one-byte pivot labels in preorder. Child sets are visited in ascending numeric mask order. A positive record has length zero. |
| [automorphisms.uleb128.xz](order10/data/automorphisms.uleb128.xz) | One positive automorphism-group order per graph, encoded as unsigned LEB128. These orders are independently regenerated before orbit summation. |

The Lean kernel verifies the mathematical exclusion rule for any valid tree, all three sets of witness properties, the original relabeling and nonuniqueness at 18 edges. The complete catalog traversal, byte-level checking and orbit count are exact external computations. The global exhaustiveness claim combines those computations with the proved rule. [Lean axiom report](evidence/order-ten-lean.log) · [Kernel replays](evidence/order-ten-kernel-replay.log)

Brendan D. McKay's graph6 data are redistributed under CC BY 4.0 with lossless XZ recompression. The reference cut, disposition, tree and group-order fields were computed here. [Original compressed file](https://users.cecs.anu.edu.au/~bdm/data/graph10c.g6.gz) · [Attribution and terms](https://users.cecs.anu.edu.au/~bdm/data/) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
