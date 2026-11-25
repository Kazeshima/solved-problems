#set document(title: "Exact worst-case comparison counts for finite Shellsort", author: ())
#set page(paper: "a4", margin: (x: 25mm, top: 23mm, bottom: 22mm), numbering: "1")
#set text(font: "Cambria", size: 12pt)
#set par(justify: true, leading: 0.68em, spacing: 0.78em)
#set heading(numbering: "1.")
#show heading: set block(above: 1.1em, below: 0.55em)
#let label(t) = text(weight: "bold", t)

#align(center)[#text(size: 22pt, weight: "bold")[Exact worst-case comparison counts\ for finite Shellsort]]
#align(center)[Research manuscript · November 2026]

#label[Abstract.] Fix the length of a permutation and a decreasing Shellsort gap sequence. We identify its exact number of executed key comparisons with the weight of a maximal path in the lattice of subsets of the input positions. The edge for one rank accounts for its shifts and its possible terminating comparison on each pass. Dynamic programming gives an attained worst case in $O(p n 2^n)$ word operations for $p$ passes. We give a machine-checked proof for ordinary linear insertion and independently replay exhaustive certificates of gap optimality. The finite comparison counts had been proposed previously. The certificates establish the upper bounds, the strict exclusions and the complete sets of ties.

= Model and finite results

For $n >= 2$ the keys are a permutation of $0,...,n-1$. A legal table is a strictly decreasing sequence of positive integers below $n$, ending in 1. A pass with gap $h$ performs left-to-right insertion on each residue chain. While an original key is being inserted, a comparison that finds a smaller predecessor ends the scan. Reaching the left boundary costs no further key comparison. Let $C(H,A)$ be this count and $M_n = min_H max_A C(H,A)$.

#figure(
  table(columns: (auto,auto,auto,1fr), inset: 5pt, align: (right,right,right,left),
    stroke: none, table.hline(), table.header([*n*],[*Tables*],[*$M_n$*],[*All minimizing gap sequences*]),table.hline(),
    [17],[32,768],[86],[(9,6,4,1)],
    [18],[65,536],[94],[(17,9,6,4,1)],
    [19],[131,072],[103],[(9,7,4,1)],
    [20],[262,144],[112],[(11,7,5,1)],
    [21],[524,288],[121],[(9,7,4,1), (20,9,7,4,1)],
    [22],[1,048,576],[131],[(5,3,1), (7,5,4,1), (8,7,3,1), (9,7,4,1), (21,8,7,3,1)],
    [23],[2,097,152],[139],[(9,7,4,1), (22,9,7,4,1)],
    table.hline()),
  caption: [Exhaustive computational certificates. Every reported winner has a maximizing permutation and a recomputed upper bound.])

Lee established finite optima through 16 and reported larger-size upper bounds [1]. Dokken's later table lists the candidate values and ties in Table 1 [2]. The evidence here addresses the exhaustive certification step. Section 4 specifies the distinction between the algorithmic theorem checked by Lean and the numerical evidence.

#pagebreak()
= Comparisons as path weights

For an input $A$, let $S_k = {i : A[i] < k}$. Consecutive sets differ by one position. Conversely, given a maximal path from the empty to the full set, assigning rank $k$ to the position added in step $k$ recovers its unique permutation.

#label[Threshold transport.] For residue $r$, write $R_r = (r,r+h,...)$ truncated at $n$. Define $T_h(S)$ by selecting the first $|S inter R_r|$ slots of each chain. Sorting a chain preserves its multiset and places its smaller keys first. Thresholding the sorted array therefore gives precisely $T_h(S)$. This map preserves cardinality and inclusion. Adding $x$ to $S$, with $x in.not S$, increases just one chain count. Its new last selected slot is
$ x' = (x mod h) + h | S inter R_(x mod h) |. $
It lies in range because the original unselected $x$ also belongs to that residue. The two consecutive transported thresholds locate the same rank after each pass.

#label[Insertion charge.] Immediately before a pass, suppose rank $k$ is at $x$, with smaller ranks at $S$. Its $t = floor(x/h)$ original predecessors in its chain have already been sorted when it is inserted. Later original elements have had no part in this insertion. Let $s$ count the predecessors in $S$. Exactly $t-s$ larger keys shift. If $s>0$ the scan makes one additional comparison and stops. Thus its charge is
$ c_h(S,x) = t-s + bold(1)_(s>0). $
When $t=0$ this formula gives zero. Other residue chains are disjoint, so interleaving their insertion steps preserves each within-chain execution.

#label[Theorem 1.] Starting from an adjacent pair $(S,S union {x})$, sum the charges over the gaps of $H$. After each charge replace $(S,x)$ by $(T_h(S),x')$ as above. Denote the result by $w_H(S,x)$. For every permutation $A$,
$ C(H,A) = sum_(k=0)^(n-1) w_H(S_k, A^(-1)[k]). $

#label[Proof.] The threshold transport identifies each rank at every pass, and the smaller predecessor test gives exactly its insertion comparisons on that pass. Assign each executed comparison to the key currently being inserted. Summing the disjoint assignments over ranks and passes gives the assertion. The Lean proof additionally collapses the keys to the three ordered classes below, equal to, and above the marked rank. A prior Lean development proves tagged-position transport and threshold commutation [6]. Here the projection also preserves the marked comparison trace count. It then identifies that count with the displayed arithmetic charge.

#pagebreak()
= Maximization, compression and the distribution

Let $D(S)$ be the largest path weight from the empty set to $S$. With $D(emptyset)=0$, the last added position gives
$ D(S) = max_(x in S) (D(S without {x}) + w_H(S without {x},x)). $
The last-step split is exhaustive and each predecessor path can be extended by its indicated position. By Theorem 1 and the path–permutation bijection, $D([n])$ is the exact maximum of $C(H,A)$. Recording a maximizing predecessor reconstructs a maximizing permutation.

There are $2^n$ states and $n 2^(n-1)$ directed edges. At a fixed source set scan all $n$ slots once per pass to obtain counts, prefix counts and the transported threshold. With these arrays each outgoing edge requires $O(p)$ work. In a word model that holds an index or subset mask in one word, time is $O(p n 2^n)$ and working storage is $O(2^n + p n)$ words for the full lattice. Recomputing every table gives the coarse bound $O(n^2 4^n)$. An implementation that retains all pass images uses additional memory.

#label[First-pass compression.] Fix the keys assigned to each first-gap chain of length $m_r$. Reversing that chain maximizes its insertion cost at $binom(m_r,2)$ and produces the same sorted chain. This first-pass reduction is present in Lee [1]. In the resulting sorted output, a threshold is specified by digits $0 <= d_r <= m_r$. Its selected keys occupy precisely those initial chain segments. A digit increment fixes the next rank and every full digit path gives a sorted output. Apply the path recurrence to the remaining passes and add $sum_r binom(m_r,2)$. Reversing the first chains of a maximizing output attains the total. For $n=q h + r$, the new state count is $(q+2)^r (q+1)^(h-r)$.

#label[Distribution.] For a polynomial $F_S$, replace the maximum by addition and add an edge weight by multiplying by $z^(w_H)$. With $F_emptyset=1$, the coefficient of $z^j$ in the terminal polynomial counts inputs using $j$ comparisons. Each path occurs once. In particular, each edge with $|S|=k$ occurs on $k! (n-k-1)!$ paths. Dividing its weighted contribution by $n!$ gives its contribution to the uniform mean. The variance follows from the first two factorial moments. Maximizing the cost on the first-pass fibers discards their internal cost distribution. Project S independently gives the marked-position charge, transport and corresponding mean weighting in its fixed-table average-cost algorithm [3].

#pagebreak()
= Reproducibility and verification

Bit $h-2$ of a row index chooses gap $h$ for $2 <= h < n$. Each index from zero to $2^(n-2)-1$ chooses one table and gap 1 is compulsory. At candidate bound $U$, the certificate can exclude a table by a strict baseline or by executing a supplied permutation. On a pass every insertion except the first of each chain executes at least one comparison, giving the baseline $n-h$. If the bound equals $U$, the table still needs examination for a possible tie.

For each proposed winner the verifier separately computes the exact maximum and executes a maximizing permutation. Checking every index, including the final record, establishes completeness of the search. The original five files cover 1,015,808 tables. Including the two extensions gives 4,161,536 tables. The review includes separate forward and reverse full-lattice recurrences, mixed-radix maximization, hash checks, malformed-certificate tests and full histogram comparison with literal permutations for every table through $n=8$. The search generator may discover exclusion witnesses heuristically. The proof of an exclusion uses only the resulting permutation.

#label[Formal scope.] The entry point #raw("actual_threshold_maximum") quantifies over every permutation and proves that ordinary comparison traces have an attained maximum equal to the explicit arithmetic Bellman recurrence. A second theorem, #raw("certificate_sound"), interprets finite certificate rows and independently checked upper potentials. For a remaining-cost potential $V$, verify $V(emptyset)<=U$ and
$ w_H(S,x) + V(S union {x}) <= V(S) $
on every legal edge. Summation along a full path proves its cost at most $U$. A winning row must also give an input at cost $U$. The large global results in Table 1 use the external exhaustive replays. The repository gives separate kernel evidence for individual inputs and reports numerical replay coverage.

#label[Scope of the research claim.] The finite global certificates and longest-path application are the proposed contributions. Public code already gives the general two-pass worst-case formula [2] and the per-rank charge for computing an exact mean [3]. An asymptotic lower bound for unrestricted Shellsort [4] and a construction with small average cost [5] concern different questions. Finite enumeration establishes no unrestricted asymptotic optimum.

#heading(level: 1, numbering: none)[References]
#set text(size: 9.5pt)
\[1\] Y. W. Lee. _Optimal Gap Sequences in Shellsort for n ≤ 16 Elements._ 2021. #link("https://arxiv.org/abs/2112.11127")[arXiv:2112.11127].

\[2\] mkdokken. _ShellSort._ Tables and #raw("worst_case_two_gap.c"), revision #raw("cc4a0533"). #link("https://github.com/mkdokken/ShellSort/tree/cc4a0533c6ce9cc4eaa4d371141621eba9bbcdf0")[Source repository].

\[3\] Project S. _Exact mean shifts and comparisons for a preset Shellsort gap table._ Research code, 25 November 2026, revision #raw("ded350f4"). #link("https://github.com/EternalYMZ/Project-S/blob/ded350f49e772f485d42ffb90a62d3ff02d76878/research/2026-11-25/exact_shellsort_mean.py")[Source code].

\[4\] B. Poonen. The worst case in Shellsort and related algorithms. _Journal of Algorithms_ 15 (1993), 101–124. #link("https://doi.org/10.1006/jagm.1993.1032")[Publisher].

\[5\] C. Du and Z. Wan. _Shellsort with O(n log n) Average-Case Complexity._ 2026. #link("https://arxiv.org/abs/2611.27671v1")[arXiv:2611.27671].


\[6\] M. Yu. #raw("TagThreshold.lean"), ShellsortMean, LeanPool revision #raw("67a81208"). #link("https://github.com/LeanPool/lean-pool/blob/67a81208bb92d879df07c7ce70b8580e55ee310a/LeanPool/ShellsortMean/TagThreshold.lean")[Formal source].
