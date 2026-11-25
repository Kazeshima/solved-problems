# Exact minimax Shellsort: two-pass asymptotics and nested-gap schedules

**Status (2026-11-25): candidate research results with handwritten proofs and executed independent Python tests. Lean source drafts have NOT been compiled or kernel checked.** No assertion that unrestricted Shellsort minimax gap selection is solved. These are ordinary linear-insertion passes on distinct keys, counting all key comparisons, including a final failed comparison if the insertion stops before the chain boundary. The computation of the gap table is not included in the sorting cost. This package extends ROUND1.md, TwoPass.lean and verify.py.

## 1. Two-pass minimax localization

For `2 <= h < n`, write `n=qh+r`, `0<=r<h`. From the extremal counting argument in ROUND1.md,

```
W = h*C(q,2)+r*q+C(h,2)*C(q+1,2)+(q+1)*C(r,2)
C = W+n-(h if r==0 else r)
```

Here `C(k,2)=k(k-1)/2`, W is the exact maximum of swaps, C the exact maximum of comparisons, and the maxima are simultaneously attained. An exact quotient-block algorithm computing **all** minimizing h uses O(sqrt(n)) arithmetic operations (not a bit-complexity claim). Proof in ROUND1.md.

**Theorem.** Let h_n be any integer minimizer of C. As n tends to infinity,

```
h_n = sqrt(2n) + O(n^(1/4)),
(n mod h_n)/h_n = 1/2 + O(n^(-1/4)),
min C = n^2/4 + n^(3/2)/(2 sqrt(2)) + O(n).
```

**Proof.** Polynomial expansion gives

```
4W = n^2 + q*n + q*h^2/2 + q*(2r-h)^2/2 + r^2 + q*r - 3n + r.
```

Substitution q=(n-r)/h gives the second identity

```
4W = n^2+n^2/h+n*h/2+q*(2r-h)^2/2
     +r^2-r^2/h-r*h/2-3n+r.
```

The final comparison correction is between 0 and n. The absolute value of the last line plus four times that correction is at most h^2+4n (use 0<=r<h<=n and r^2/h<=r). Define T=sqrt(2n) and use

```
n^2/(4h)+n*h/8 - n*T/4 = n*(h-T)^2/(8h).
```

For the upper bound, construct a simultaneous integer approximation. Let A=ceil(sqrt(n/2)). Define F(t)=2A^2+A+t-2t^2. Then 0<F(0)-n<=5A, and F(t-1)-F(t)=4t-3>0 for integers t>=1. Let t be the first positive integer with F(t)<=n. Taking t<=ceil(sqrt(5A)) is sufficient because 2t^2-t>=t^2 for t>=1. Hence t=O(n^(1/4)). Let e=n-F(t); minimality gives 0<=e<4t-3. Put a=A+t, h=2a, q=A-t, r=a+e. For all sufficiently large n, q>=1 and e<a, so n=qh+r with 0<=r<h. Consequently h=T+O(n^(1/4)) and r-h/2=O(n^(1/4)). The second identity and gap-defect identity give C<=n^2/4+n*T/4+O(n), since both squared defects are O(n) after multiplication by their coefficients.

For any minimizer h the first identity gives q*n+q*h^2/2 <= 4C-n^2+3n = O(n^(3/2)). Because h<n and q=floor(n/h)>=n/(2h), each summand separately bounds h, showing h=Theta(sqrt(n)). Thus the centered error is O(n), and the second identity, minus the leading optimal expression, is the sum of two nonnegative defects n*(h-T)^2/(8h) and q*(2r-h)^2/8, up to O(n). Both defects are O(n) by the upper bound. As q and h are Theta(sqrt(n)), this proves both localization claims and the minimum-cost expansion. All constants are uniform over the set of minimizing h. QED.

## 2. Exact worst cost for nested gap schedules (any array size)

A schedule is nested if n>h1>...>hp=1 and h_(i+1) divides h_i. The first gap need not divide n.

Let I(n,a)=a*C(floor(n/a),2)+(n mod a)*floor(n/a), the number of within-a-chain unordered position pairs. It is the exact worst first-pass comparison count. Let B(m,k) denote the exact maximum comparison count of ordinary insertion sort on a k-sorted array of length m (1<=k<=m):

```
m=q*k+r; 0<=r<k
B(m,k) = C(k,2)*C(q+1,2)+(q+1)*C(r,2)+m-(k if r==0 else r)
```

This is the second-pass term from ROUND1, with its proof unchanged for k=1 or k=m. For a>b>=1 with b|a, write n=b*m+s and k=a/b. Define

```
E(n;a,b) = (b-s)*B(m,k)+s*B(m+1,k).
```

**Theorem (exact fiber composition).** The exact worst comparison count for every nested schedule equals I(n,h1)+sum_i E(n;h_i,h_(i+1)).

**Proof.** The b-chains have lengths m or m+1. In each b-chain the a-sorted property is precisely k-sortedness. Their sorting costs therefore sum to at most E. Conversely, fix an arbitrary b-sorted output permutation y. The sorted keys of each b-chain of y define an order-isomorphism from local ranks to those keys. Arrange them in the k-sorted local extremal pattern for B (ROUND1): the longer chains have the lower ranks, within each length group the earlier chain has the larger rank interval, and every chain is ascending. This input is a-sorted, has output y under b-sorting, and costs exactly E. Thus EVERY output fiber has an extremal preimage. Similarly, for any h1-sorted array its chain-reversal preimage realizes I(n,h1) and produces it. Starting from the sorted permutation and repeatedly constructing such preimages backwards yields one original permutation attaining all individual bounds simultaneously. QED.

**Algorithm.** Put a source edge of weight I(n,b) to each 1<=b<n, and an edge a->b of weight E whenever b is a proper divisor of a. The DAG has fewer than n^2 edges; in fact sum_b(floor((n-1)/b)-1)=O(n log n). The shortest path from source to 1 yields one exact minimax nested schedule, and storing all minimizing predecessor ties yields all optimal schedules (output size may be large). The shortest-path computation uses O(n log n) arithmetic operations and the supplied implementation stores O(n log n) edges. An on-demand proper-multiple relaxation with adjacency lists avoided may reduce storage; no such implementation is claimed. No polynomial bit-complexity assertion is made.

## 3. Sharp leading behavior of the optimal nested class

**Theorem.** For the optimal cost in this class, allowing any number of passes,

```
C_nested^*(n) = n(n-1)/4 + Theta(n log n).
```

**Proof.** For a b-chain of length m, split into k=a/b earlier subchains of lengths q or q+1. Denote by H the number of pairs of positions in different earlier subchains within this b-chain, and by Z the sum of their common length over all unordered equal-length pairs of subchains. The paired inversion calculation gives maximum swaps (H+Z)/2: a pair of equal length l contributes l(l+1)/2 instead of l^2/2, and a mixed pair of lengths l,l+1 contributes exactly half their product. Thus

```
C = n(n-1)/4 + I(n,h1)/2 + sum_transitions (Z_total/2 + R),
```

where R is the number of failed comparisons of the extremal b-pass, and Z_total is summed over all b-chains. The baseline telescopes because sum H=I(n,b)-I(n,a), and the first pass gives I(n,h1) instead of I(n,h1)/2. In the explicit witness, n-a<=R<=n (all entries beyond the first local row are non-record-minima). All overhead terms are nonnegative.

For the upper bound, use the gaps consisting of descending powers of two strictly below n, ending at 1. Their initial ratio n/h1 is at most two, so I(n,h1)=O(n). Every later ratio is 2, and every b-chain has Z at most its length, so Z_total=O(n) per pass. R<=n. There are O(log n) passes.

For the lower bound, let k0=n/h1>1, and for each transition k=a/b>=2. Their product is n. If k0>=4, then floor(k0)-1>=k0/4 and I(n,h1)/2 >= n*(floor(k0)-1)/4 >= n*k0/16; if k0<4, its logarithm is bounded by a constant. For a transition k>=4, in a b-chain of length m with remainder r, we have Z >= q*(C(r,2)+C(k-r,2)) >= q*k*(k-2)/4 >= q*k^2/8. Since q>=m/(2k), Z/2 >= m*k/32. Summing over the b-chains gives at least n*k/32, which is >= n*ln(k)/32. For k=2 or 3 and a<=n/2, the term R>=n-a>=n/2 also bounds n*ln(k)/32. At most one transition can have a>n/2 because the next gap is at most a/2; if that transition has k=2 or 3 its omitted logarithm is bounded by ln(3). The total overhead is at least (n/32)*(ln n-ln 4-ln 3), establishing the asymptotic lower bound. QED.

This is a quadratic worst-case class: the result must not be mistaken for the optimal unrestricted Shellsort (e.g. Pratt's nonnested sequences have subquadratic worst-case bounds).

## 4. Explicit optimum for powers-of-two gaps when n=2^m

Restrict further to gaps all powers of 2. This is the same as allowing only divisors of n in nested schedules when n=2^m, not allowing arbitrary first gaps. The optimal ratios, starting at fictitious gap n, are uniquely

* even m=2t: t ratios equal to 4;
* odd m=2t+1: an initial ratio 2, then t ratios equal to 4.

For example n=64 gives (16,4,1), n=128 gives (64,16,4,1). This is a closed-form result within the stated class, not a claim that these are optimal among all nested schedules at those sizes.

**Proof.** Since every gap divides n, the transition from a to b (including a=n fictitiously for the first transition) has

```
4 E = n^2*(1/b-1/a)+n*(a/b+3)-4*a.
```

Thus 4C=n(n-1)+n*sum(k_i+3)-4*sum(a_i), where k_i=a_i/b_i=2^e_i, e_i>=1, sum e_i=m, and a_i is the gap before that ratio. Swapping any adjacent inverted pair of ratios x>y changes only the intermediate gap, from a/x to a/y, and strictly improves the cost. An optimum has sorted ratios. Splitting an exponent e>=4 into 2 and e-2 changes the scaled cost by n*(4-(x-1)*(y-1))-4*b<0 with x=4,y>=4,b=a/x. Hence exponents <=3. Two adjacent exponents 1 can be merged to exponent 2 with strict improvement: the split costs 3n-4b>0, since b<=n/2. Two adjacent exponents 3 can be replaced by three exponents 2, lowering sum(k_i+3) by 1 and increasing the sum of intermediate gaps. So there is at most one 1 and at most one 3.

For even m, the only competing pattern to all 2s is (1,2,...,2,3), with t>=0 copies of 2. Compared with t+2 copies of 2, the competing pattern has sum(k_i+3) larger by 2, and sum(a_i)/n larger by (1-4^(-t-1))/3 < 1/3, hence costs strictly more. For odd m=2t+1, t>=1, compare (1,2,...,2) with t copies of 2, against (2,...,2,3) with t-1 copies of 2. The first has sum(k_i+3) larger by 1 but sum(a_i)/n larger by 1/3+(2/3)*4^(-t)>1/3, so costs strictly less. m=1 is immediate. This proves uniqueness. Summing the geometric series gives

```
m=2t:   C = n(n-1)/4 + 7nt/4 - 4(n-1)/3
m=2t+1: C = n(n-1)/4 + n(5+7t)/4 - (5n-4)/3
```

QED.

## 5. Why arbitrary gaps cannot yet be handled by the same method

For n=5, gaps (3,2,1), the three independent stage maxima over actual executions are 2,4,6, but the exact joint maximum is 11, not 12.

Analytical check: after 3- and 2-sorting, write y=(A,B,C,D,E); it satisfies A<C<E, B<D, A<D, B<E (persistence of 3-sortedness follows from comparing the minima/maxima of the two 2-chains, or the standard preservation theorem). The only potential inversions are A>B, B>C, C>D, D>E. The final insertion cost is 4+1[B>C]+1[C>D]+1[D>E], because the non-record comparison at B cancels the inversion A>B. If C>D, the other two cannot hold. Hence the maximum is 6, requiring B>C and D>E, which fixes y=(0,2,1,4,3) in ranks. Any 3-sorted preimage under the 2-pass must have B,D-chain ranks {2,4} and A,C,E-chain ranks {0,1,3}. Its b<e condition forces rank 2 at b, rank 4 at d, rank 3 at e. Thus its second pass costs 3 (one comparison in the odd chain, two in the even chain). The independent stage maxima cannot coincide. The input (4,3,1,0,2) gives costs (2,3,6); (0,1,3,4,2) gives (2,4,5). Thus the exact maximum 11 is attained. The supplied program checks all 120 permutations.

## Reproduction

```
python verify.py
python advance.py
lake update
lake exe cache get
lake build
```

Python outputs are in verification.txt and verification_v2.txt. The tests check actual adjacent-exchange insertion loops and exact arithmetic. MinimaxCore.lean attempts algebraic identities, the minimal-crossing construction and abstract exact-fiber composition. FiniteChecks.lean attempts a kernel-reduction finite counterexample on a concrete generator, which is still uncompiled. TwoPass.lean is retained from round 1. The following are **not complete formalized results**: the bridge from the grid formula to actual insertion execution for all n, the full optimality and asymptotic theorems, the Shellsort-specific exact-fiber construction, the divisor DAG optimizer and its complexity, and the power-of-two proof. The environment has no lean, lake or elan; DNS/network installation failed. Do not claim kernel verification until these gaps are closed, the project is built and axioms audited. No `sorry` is intentionally used in the Lean drafts, but that alone is not validation.

## Prior art and provenance

Targeted follow-up searches of scholarly web indexes and GitHub code, combined with the earlier Project S and LeanPool inspection, did not identify the exact two-pass minimax localization or the nested exact-fiber / optimal-cost results above. The search is not a comprehensive clearance: some subscription-only indexes, unpublished notes, GitHub non-default branches, and unindexed material are unavailable. Classical quadratic worst-case results for Shell's original sequence are established and not claimed here. Related sources:

- Poonen (1993), The Worst Case in Shellsort and Related Algorithms, https://doi.org/10.1006/jagm.1993.1032
- Sedgewick (1986), A New Upper Bound for Shellsort, https://sedgewick.io/wp-content/themes/sedgewick/papers/1986Shellsort.pdf
- Lee (2021), https://arxiv.org/abs/2112.11127
- Vitányi (2018), On the Average-Case Complexity of Shellsort, https://ir.cwi.nl/pub/26831/26831.pdf
- https://github.com/mkdokken/ShellSort (heuristic minimax search and finite optimal schedules)
- https://github.com/EternalYMZ/Project-S and https://github.com/LeanPool/lean-pool/tree/main/LeanPool/ShellsortMean (recent related formalizations, mainly average cost)
- https://github.com/Nannde/shellsort-three-pass-optimality (three-pass average asymptotic analysis)

The proofs here use combinatorial pair counting, elementary arithmetic and exact extremal preimage composition, not a claimed application of an OpenAI tensor complexity result. Independent novelty and formal proof review are required.
