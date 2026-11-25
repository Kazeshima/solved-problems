# Exact minimax cost of two-pass Shellsort — candidate research note

Status: mathematical derivation and Python checks completed; Lean code is an uncompiled, partial formalization draft. No claim of novelty or kernel verification is made. The unrestricted optimal sequence problem is not solved here.

## Model

Sort n distinct keys with strictly two passes (h,1), 2 <= h < n, using ordinary insertion sort within residue classes. Count every key comparison (including unsuccessful comparisons). No sentinel or binary insertion search. Write n=qh+r, 0<=r<h.

Define

    W(n,h) = h*choose(q,2) + r*q + choose(h,2)*choose(q+1,2) + (q+1)*choose(r,2).
    C(n,h) = W(n,h) + n - (h if r=0 else r).

Claim: W and C are the exact maximum number of exchanges and comparisons, respectively. Moreover, all minimizers of C over 2<=h<n can be obtained with O(sqrt(n)) evaluations of C.

## Proof

The first pass costs at most sum choose(m_i,2), where m_i=q+1 for residues i<r and q otherwise. Reversing every chain attains both the comparison and exchange bounds.

For two sorted chains A,B, with A earlier in each row, the earlier chain length is m or m+1 and the later chain length is m. For every i<j<m, A_i>B_j and B_i>A_j cannot both hold, by monotonicity. Each such pair contributes at most one inversion. The m diagonal pairs contribute at most m. If A is longer, pair the extra candidates B_i>A_m with A_i>B_i; those too are mutually exclusive. Thus the cross-chain inversion count is at most choose(m+1,2). Summing over pairs gives choose(h,2)*choose(q+1,2)+(q+1)*choose(r,2).

In ordinary insertion sort the comparison count is inversion count plus the number of non-record-minimum entries (other than the first). All n-h elements after the first row are non-record minima. If a first-row entry from residue j belongs to the initial equal-length group (all residues when r=0; the r long chains otherwise) and is not a record minimum, some i<j has A_i[0]<A_j[0]. Its equal-length pair loses the first diagonal inversion and hence at least one from the pair budget. Choosing one such i for each j charges distinct pairs. This pays for every extra non-record comparison in the initial group; the remaining h-r short chains contribute at most h-r such comparisons when r>0.

Attainment: assign disjoint contiguous intervals of ranks, with all long chains smaller than all short chains and descending intervals within each group. After chain sorting the within-group pairs attain their inversion budgets in descending block order and the mixed pairs attain their budgets in ascending block order. The first row of the initial group consists entirely of record minima, and every short chain is a non-record minimum when r>0. Reverse each chain at input to achieve the first-pass bounds without affecting this second-pass arrangement. This simultaneously achieves W and C.

For r>0 and q fixed, four times C is quadratic in h with leading coefficient q(q+1)(2q+1)>0 and linear coefficient -q*((4n+1)(q+1)-4). Its vertex is ((4n+1)(q+1)-4)/(2(q+1)(2q+1)). Restrict to integers floor(n/(q+1))+1 <= h <= floor((n-1)/q), intersected with [2,n-1]. Check the floor and ceil of the vertex, clamped to the interval; check r=0 separately at h=n/q if legal. There are O(sqrt(n)) distinct integer quotient blocks. This is a count of exact arithmetic evaluations, not a bit complexity bound.

## Reproduce

    python verify.py

See verification.txt for the actual Python results. The exhaustive cases test the real adjacent-exchange implementation, not merely the formula. The larger cases test the witness and compare quotient-block minimization with a complete scan over h.

## Lean 4 draft

    lake update
    lake exe cache get
    lake build

TwoPass.lean attempts the paired-inversion bound, equality constructions for pairs, and the first-row penalty / global grid upper bound. The file has not been compiled because the environment had no Lean/Lake/elan or network access to install Lean. Remaining work includes kernel-checking and fixing this draft, proving the bridge to actual insertion-sort comparisons, formalizing the complete rank-permutation witness, deriving the closed-form sum, and proving correctness and candidate-count complexity of the quotient-block solver. The Python checks do not replace these steps.

## Prior art / novelty caveat

- Knuth, The Art of Computer Programming, Vol. 3, section 5.2.1: classical two-pass average-case analysis.
- https://arxiv.org/abs/2112.11127 (Lee, exhaustive/reduced minimax search for general sequences, exact n<=16).
- https://arxiv.org/abs/2611.27671 (Du and Wan, average O(n log n) preprint).
- https://github.com/EternalYMZ/Optimal-mean-comparisons-in-Shellsort (existing Lean statements for unrestricted exact average minimizer existence and order).
- https://github.com/LeanPool/lean-pool/blob/main/LeanPool/ShellsortMean/VerifiedOptimum.lean
- https://github.com/EternalYMZ/Project-S (many related Shellsort bounds and formalizations).
- https://github.com/Nannde/shellsort-three-pass-optimality (three-pass average asymptotics).
- https://github.com/mkdokken/ShellSort (heuristic average-cost search).
- https://github.com/openai/math (no direct Shellsort match in repository code search).

Targeted searches of web-indexed scholarly sources, GitHub code and repository search, and the above sources did not reveal this exact restricted minimax formula. This does not certify novelty: subscription-only indexes, unindexed manuscripts, non-default branches, and inaccessible sources have not been comprehensively searched. Independent review required.
