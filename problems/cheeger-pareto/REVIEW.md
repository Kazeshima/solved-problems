# Independent review of the Cheeger–Pareto counterexample and its minimum order

**Verdict for Conjecture B, minimum order and the ten-vertex census: ACCEPTED.** The least order is 10. At order ten exactly three isomorphism classes violate B, two with the minimum of 18 edges. Review completed on 25 November 2026. Acceptance here means that the mathematical result, formal theorem, statement comparison and bounded public originality search all passed. The original submission did not compile.

| Criterion | Result | Grounds |
|---|---|---|
| MATHEMATICAL_CORRECTNESS | PASS | Exact graph6 reconstruction, all small cuts, a separate analytic proof, and a tight cover for all real competitors. The efficient minimum is exactly 6. A general tight-cover argument excludes all smaller graphs. |
| FORMAL_VERIFICATION | PASS | Lean 4.19.0 checked the revised file and the Lake library. The counterexample, its exact efficient mass and the least-order theorem have only the three standard axiom dependencies printed below. |
| STATEMENT_FIDELITY | PASS | The original seven general definitions are source-identical to the submission and were independently matched to revision 5 of MO and to MSE. The attained real minimum was also proved explicitly for this graph. |
| NOVELTY | PASS | No prior resolution of B was located across the documented public sources and alternative formulations. The single-vertex support idea is already present in DSM's answer to A. [Search report](SEARCH.md) |

## Source and statement audit

The original submission has SHA-256 **433e03c2449dba32a37ad783b11d80dffa527fffbcee915c73e6aa9630f35d23**. Its report, proof, code and solver output were treated as claims.

| Mathematical issue | Check against the sources and the Lean declarations |
|---|---|
| Graph class | Finite simple undirected graphs. Give any finite vertex set a labeling by **Fin n** and store each edge once with its smaller endpoint first. Conversely every **OrderedEdges** finite set defines such a graph. Relabeling preserves sizes, cut counts, sums and domination. The source imposes no connectivity restriction. This witness is connected. |
| Admissibility | The effective cardinality limit is natural-number division **n / 2**. Sets of size exactly half are included, including both sides at even order. The empty set is included in feasibility. |
| Cheeger constant | **cutSize** counts edges with exactly one endpoint in the set. **IsCheeger** proves a lower bound on every nonempty admissible cut ratio and equality on one such cut. Multiplication by the positive cardinality preserves the comparison. The source's displayed minimum omits a nonemptiness qualifier needed for division by zero to be avoided. For orders 0 and 1 the displayed ratio has no admissible argument. The domain on which it is defined has n ≥ 2. Every convention extending it to smaller orders still includes this ten-vertex witness. |
| Feasible vectors | **Feasible E z** asserts coordinatewise nonnegativity and every admissible cut inequality for **z : Fin n → ℝ**. |
| Pareto order | For all real **y**, feasibility and coordinatewise **z ≤ y** imply **y = z**. This rules out even a strict increase at just one coordinate and allows competitors of arbitrary real values. |
| Target | A used the coefficient n/2 over the reals. B uses floor(n/2). The proposed lower bound on a minimum is equivalent to the lower bound on every efficient mass. **least_mass_iff** records this order-theoretic equivalence for an attained minimum. **rho_exact** supplies an unconditional attained minimum for this witness. |

For completeness, on every graph of order at least two the feasible polytope is nonempty and compact. The zero vector is feasible and the singleton constraints bound each coordinate by its degree. A point maximizing the total is efficient. A feasible point is efficient exactly when each coordinate belongs to a tight admissible set. For necessity, increase any uncovered coordinate by less than the least positive slack of the finitely many constraints through it. Sufficiency follows from summing the nonnegative differences on each tight set. The efficient locus is thus a finite intersection (over coordinates) of finite unions of closed tight faces. Its mass minimum exists. [MSE problem](https://math.stackexchange.com/questions/5118288) · [MO revision history](https://mathoverflow.net/posts/506070/revisions)

## Findings and repairs

1. **The original Lean proof failed at line 131.** In **tight_coordinate**, the bound on the real sum ended in the cast of a natural-number six. The proof's other inequality used the real numeral six. The original final linear-arithmetic step failed to close the equality. Lean's error recovery consequently printed **sorryAx** and the command exited 1. The repair normalizes the cast and proves the two inequalities separately with antisymmetry and the existing domination hypothesis. [Failure on the untouched input](evidence/submitted-lean.log)
2. **The submitted finite certificates extended the trusted base.** All nine uses of **native_decide** were removed. The finite checks now use **decide +kernel**, with bounded resources on the two large powerset checks. The new graph6 certificate verifies the header, all 45 adjacency positions and the three padding bits. The connectivity certificate supplies a path of length at most two to the hub for every vertex. The native evaluator in this Lean version would have introduced **Lean.ofReduceBool**. [Lean 4.19 tactic implementation and documentation](https://github.com/leanprover/lean4/blob/v4.19.0/src/Init/Tactics.lean)
3. **The submitted Python verifier hard-coded the edge list and vector.** It neither decoded the named graph6 input nor checked connectivity, and its assertions could be disabled by optimized Python. The replacement uses the graph6 file as its graph input, discovers the successful support and its weight, checks reachability, and computes each boundary by endpoint disagreement and by outside-neighbor counts. It checks exact feasibility, finds the minimizing sets and reconstructs the tight cover. Validation uses explicit exceptions. [Program](verify.py) · [Graph6 specification](https://users.cecs.anu.edu.au/~bdm/data/formats.txt)
4. **The supplied material gave only an upper bound on ρ and an enumerative cut proof.** The new lower bound on efficient mass proves the minimum is exactly six. It is formalized as an attained minimum, which directly checks the quantity in the source. The English paper proves the cut bounds separately using four edge-disjoint triangles and six spokes. [Paper source](paper.tex) · [Enumeration proof](PROOF.md)
5. **Dependencies and successful build evidence were missing.** The reviewed release matches the original version pin. Lake generated a checked-in-ready manifest with exact revisions for all nine packages. Each checkout was compared with the manifest and checked for tracked modifications. [Environment and declaration checks](evidence/environment.log)
6. **The prior-art report omitted important checks.** The live APIs resolved the conflicting answer count. A degree-eight description in DSM's second example is a degree-ten vertex with weight eight. Exact cut checks and the hub lower bound show that both old graphs satisfy B for every efficient point. Exact code searches were complemented by semantic queries, formalization repositories, the AI research tracker and mathematical publication databases. Scholar's session challenge and the restricted MathSciNet search are recorded. The archive establishes the submitted witness, without establishing first discovery worldwide. [Prior-art review](SEARCH.md)
7. **A local English answer cannot be called ready for this particular website.** The mathematical note and its self-contained enumeration snippet were checked. Mathematics Stack Exchange expressly disallows LLM-drafted answers. A human contributor must independently author any eventual post. The first review was completed locally. [MSE policy](https://math.stackexchange.com/help/gen-ai-policy)

## Executed acceptance checks

| Command | Observed result |
|---|---|
| **lake update** | Exit 0. Created the manifest from the pinned Mathlib release. [Log](evidence/lake-update.log) |
| **lake exe cache get** | Exit 0. All 6,641 requested cache files downloaded and unpacked. [Log](evidence/lake-cache.log) |
| **lake build** | Exit 0. Built **CheegerPareto**. [Log](evidence/lake-build.log) |
| **lake env lean CheegerPareto.lean** | Exit 0. Elaborated the source and printed the axiom dependencies. [Log](evidence/lean.log) |
| **python3 verify.py** | Exit 0 on CPython 3.12.14. Read 18 edges, found the efficient spike, and checked all 638 admissible subsets. [Log](evidence/python.log) |

The exact final output for the principal claims is

~~~text
'CheegerPareto.rho_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'CheegerPareto.not_conjectureB' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

These are propositional extensionality, classical choice, and quotient soundness. The graph6 certificate depends on **propext** and **Quot.sound**. The reviewed source contains zero occurrences of admitted proofs, user axioms, or native-decision tactics. The numerical search and its evidence files are outside the Lean proof's trusted dependencies. Lean and the standard Mathlib binary cache were used in the conventional toolchain trust model.

The independently computed minimum boundaries by set size 1 through 5 were **2, 3, 4, 6, 7**. The corresponding minima containing vertex 9 were **6, 7, 6, 6, 7**. The equality sets for expansion were precisely **{0,7,8}**, **{1,2,3}**, and **{4,5,6}**. Each becomes a tight feasible constraint after adjoining 9. All three have size four. [Raw labeled cuts](evidence/cuts.tsv)

## Minimum order and independent certificates

**The minimum counterexample order is 10 for unrestricted real Pareto vectors.** An efficient point below the conjectured bound would give a cover of the vertices by inclusion-maximal tight sets. Distinct members intersect, their union exceeds the size cutoff, and the complement of that union cannot have size equal to the cutoff. For orders through nine this leaves only triples on eight points meeting pairwise once. Such triples cannot cover eight points. The proof and formalization quantify over every graph, independently of the graph catalog. [Full argument](MINIMALITY.md) · [Analytic reduction](CheegerMinimum/Analytic.lean) · [Set-theoretic obstruction](CheegerMinimum/Covers.lean)

The exact checker separately excluded all 273,192 connected graph representatives of orders 2 through 9 over the full real domain. It tests a necessary condition for any violating efficient vector. Failure to find a compatible cover certifies the whole real polytope. The generator counted boundaries by adding one vertex at a time. The verifier recomputed them by counting outside neighbors, reconstructed the catalog SHA-256 of each order, checked all graph records and verified closure of all 3,119 graph-independent proof states. The ten-vertex positive control survives the same cover test. The old one-coordinate search is retained as historical evidence. [Per-order results and formats](MINIMALITY.md) · [Offline replay](evidence/all-real-replay.log) · [Negative controls](evidence/minimum-controls.log)

Both **lake build** and **lake env lean CheegerMinimum.lean** completed successfully. The independent dependency replay submitted **4,488** declarations from **228** modules to the kernel starting with only Lean's **Init**. The lower bound and the attained least-order theorem both have exactly the following axiom dependencies.

~~~text
'CheegerPareto.bound_through_nine' depends on axioms: [propext, Classical.choice, Quot.sound]
'CheegerPareto.minimum_counterexample_order' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

The CI and the package README give the replay command. The proof uses no native-decision axiom, LP oracle, graph catalog or read-in certificate. [Least-order theorem](CheegerMinimum.lean) · [Build](evidence/minimum-build.log) · [Direct check](evidence/minimum-lean.log) · [Dependency replay](evidence/minimum-kernel-replay.log)

The English manuscript contains the construction, the minimum-order argument and the order-ten classification. The public repository cites both original questions. The MSE help center disallows AI-generated drafts. The MathOverflow help center asks for mathematical content that the poster can personally provide and notes that AI-generated mathematics is likely to be deleted. This project supplies a public answer with provenance in the repository. No answer, comment or edit was posted on either thread by this project. [MSE policy](https://math.stackexchange.com/help/gen-ai-policy) · [MO policy](https://mathoverflow.net/help/gen-ai-policy)


## Complete classification at order ten

**Exactly three connected isomorphism classes violate B. Eighteen is the minimum number of edges at this order and two classes attain it.** In catalog labels the edge minimizers are `ICOceQd{W` and `ICOceQd|O`, each with $h=4/3$, $\rho=6$, and a tight-cover witness $6e_9$. The original `IJOG[BHvO` maps to the second one. Its degree-four vertex distinguishes it from the first one. The only further class is `ICOceQd~w`, with 21 edges, $h=5/3$ and $\rho=8$ attained by $8e_9$. [Complete records, tight sets and relabeling](order10/witnesses.json) · [English proof and certificate format](ORDER10.md)

The order-ten test follows from maximality and cut submodularity over the real polytope. Any violation supplies a cover by triples and four-sets of capacity below $5h$. For two distinct members $A,B$, the intersection is nonempty, the union has at least six vertices, and $c(A)+c(B)-c(A\cap B)<5h$. These conditions let a finite proof tree rule out every possible real witness on an excluded graph. The two independent native implementations use different graph-cut calculations and branch choices. The auditor also consumes each supplied pivot and verifies every required child, including terminal branches. A total of 24,249,296 pivot nodes were checked for 11,716,568 negative instances. The three survivors were then verified positively. [Generator](order10/screen.cpp) · [Independent checker](order10/audit.cpp)

The canonical audit found 11,716,571 distinct keys. Direct orbit summation gave 34,496,488,594,816 labeled connected graphs, matching the component-size recurrence exactly. This addresses the possibility that the catalog contained duplicates or omitted a class. All 774,628 representatives with fewer than 18 edges were excluded. The 18-edge stratum had 561,106 representatives and exactly two positive certificates. Files for the complete input, attaining cuts, refutation trees and automorphism orders are included in the package. [Full replay](evidence/order-ten-verification.log) · [Counts by edge number](order10/data/by-edges.tsv)

**Formal scope.** Lean proves the soundness of a refutation tree for an arbitrary nonnegative real vector, identifies the three graph6 records, checks the exact Cheeger and efficient-mass values, establishes connectivity and proves two nonisomorphic 18-edge violations. The order-ten catalog traversal and orbit completeness check run outside Lean. Thus the exact global classification and the lower bound of 18 edges are computer-assisted results combining the kernel-checked rule with the independently replayed finite census. The previous theorem proving 10 is the least vertex order is wholly internal to Lean. [Lean exclusion rule](CheegerTen/Exclusion.lean) · [Witness theorems](CheegerTen.lean) · [Axiom audit](evidence/order-ten-lean.log) · [Transitive kernel replays](evidence/order-ten-kernel-replay.log)

Corruption controls rejected a false minimizing cut, a pivot outside the remainder, a missing child, trailing tree data, a duplicated isomorphism class and an incomplete set of orbits. All comparisons in the census are integer comparisons. The exact real conclusions use nonnegativity, saturation and the finite-slack argument. The four-page English paper includes the classification and the two proof layers.
