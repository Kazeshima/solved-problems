# Two conjectures from Ralf Stephan's OEIS list

## Conjecture credit

**Ralf Stephan** collected one hundred observations about OEIS sequences in *Prove or disprove. 100 conjectures from the OEIS* (2004). This entry settles two of them. [Stephan's list](https://arxiv.org/abs/math/0409509)

**Conjecture 69.** Matthieu Latapy contributed OEIS A060621 in 2001: the number of flips between the $d$-dimensional tilings of the zonotope $Z(d+3,d)$. Stephan observed in April 2004 that the ten known terms satisfy $a(d)=2^d(d^2+11d+24)/2$, and Colin Barker recorded the matching empirical generating function in 2013. [OEIS A060621](https://oeis.org/A060621) · [Latapy's paper](https://arxiv.org/abs/math/0008022)

**Conjecture 85.** Dominique Foata and Guo-Niu Han introduced minimax trees, and Emanuele Munarini contributed their counting sequence as OEIS A080795 in 2003. OEIS A006154, from Simon Plouffe, counts ordered partitions of an $n$-set into blocks of odd size. Stephan conjectured in April 2004 that $\mathrm{A080795}(2n)=2^n \mathrm{A006154}(2n)$. [OEIS A080795](https://oeis.org/A080795) · [OEIS A006154](https://oeis.org/A006154) · [Foata and Han](https://doi.org/10.1006/aama.2001.0740)

On 26 November 2026 the OEIS entries still showed both statements as an observation and a conjecture.

## Result for Conjecture 69: flips between zonotope tilings in codimension three

**Proved for every $d\ge0$.** The number of flips is

$$
a(d)=(d+3)(d+8) 2^{d-1}=(d^2+11d+24) 2^{d-1}.
$$

With $n=d+3$ generators this says that the Hasse diagram of the higher Bruhat order $B(n,n-3)$ has $n(n+5) 2^{n-4}$ edges. The argument has two parts.

**Reduction, cited.** By Ziegler's Theorem 4.1 the flip graph of the fine zonotopal tilings of the cyclic zonotope $Z(n,d)$ is the Hasse diagram of $B(n,d)$, and $B(n,k)$ is the set of consistent families of $(k+1)$-subsets of $[n]$ under single-step inclusion. For $k=n-3$, replacing every $(n-2)$-subset by its complementary pair turns a consistent family into a graph on $[n]$ in which every neighbourhood $N(p)$ is an initial or a final segment of $[n]\setminus\lbrace p\rbrace$. A flip becomes a pair $(G,e)$, where $e$ is a non-edge of $G$ and both $G$ and $G+e$ are graphs of this kind.

**Count, formalized.** Fix $e=\lbrace i,j\rbrace$ with $i<j$. The flips at $e$ fall into four classes, according to the two possible shapes of $N(i)$ and of $N(j)$, and complementation pairs the classes. Two of them have $\binom{n-2}{j-i-1}$ elements each. The other two have $2^{n-4}$ elements each, or $2^{n-3}$ when $j-i\in\lbrace 1,n-1\rbrace$. Both counts come from bijections that delete a vertex whose neighbourhood is forced. Summing over all pairs gives the formula. [Written proof](proof/A060621.txt) · [Chinese write-up](Conjecture69.zh.md)

```lean
theorem ZonoFlips.card_flipPairs_eq (d : ℕ) :
    2 * (flipPairs (d + 3)).card = (d ^ 2 + 11 * d + 24) * 2 ^ d
```

Here `flipPairs n` is the set of pairs $(G,e)$ on the vertex set $\lbrace 0,\dots,n-1\rbrace$ described above. The companion theorem `flipCount_eq` states the count as $n(n+5) 2^{n-4}$ for $n\ge4$, and `flipCount_values` evaluates the ten terms listed in the OEIS. [Theorem](ZonotopeFlips/Total.lean#L249) · [Definition of the model](ZonotopeFlips/Basic.lean#L244) · [Axiom report](logs/zonotope_axioms.log)

### Scope

- The Lean development proves the count in the graph model. It does not formalize zonotopes, tilings or the higher Bruhat orders. That link rests on Ziegler's theorem in the form restated by Balitskiy and Wellman (Theorem 2.5) and by Chau (Theorem 2.12). Ziegler's paper was available only as a scan and was not read directly.
- The OEIS entry says “unary zonotope” without the word cyclic. Reading it as the cyclic zonotope follows the sibling entry A060602, whose formula is Ziegler's Proposition 7.1, and the model reproduces all ten terms that Latapy computed.
- Three scripts check the parts that Lean does not cover. One enumerates consistent families straight from the packet definition for $n\le7$. One enumerates the graph model for $n\le14$ and compares the number of graphs with Ziegler's $2^n+n2^{n-2}-2n$. One checks every individual claim of the written proof for $n\le7$.
- The search for an earlier proof covered the OEIS entry, the papers linked here and web searches, and found none. The proof has not been peer reviewed.

[Balitskiy and Wellman](https://arxiv.org/abs/1902.01530) · [Chau](https://arxiv.org/abs/2412.10532) · [Ziegler's preprint](https://www.mi.fu-berlin.de/math/groups/discgeom/ziegler/Preprintfiles/025PREPRINT.pdf) · [OEIS A060602](https://oeis.org/A060602) · [Enumeration logs](logs/)

## Result for Conjecture 85: minimax trees and ordered partitions into odd blocks

**Proved for every $n\ge0$.** Write $a(n)$ for A080795 and $b(n)$ for A006154. Then

$$
a(2n)=2^n b(2n).
$$

The exponential generating function $A$ of $a$ satisfies $A'=2A^2-1$ with $A(0)=1$, and that of $b$ is $B=1/(1-\sinh x)$. The Riccati equation linearizes, which gives $A=-U'/(2U)$ for $U=\cosh(\sqrt2 x)-\sqrt2 \sinh(\sqrt2 x)$. Adding each series to its image under $x\mapsto-x$ shows that $A(x)+A(-x)$ and $B(\sqrt2 x)+B(-\sqrt2 x)$ are both equal to $4/(3-\cosh(2\sqrt2 x))$. Comparing the coefficients of $x^{2n}$ gives the identity. [Written proof](proof/A080795.txt)

```lean
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * (∑ k : Fin (n + 1), n.choose k * a k * a (n - k)) - 0 ^ n

def b : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), if Even (k : ℕ) then (n + 1).choose (k + 1) * b (n - k) else 0

theorem MinimaxTrees.a_even (n : ℕ) : a (2 * n) = 2 ^ n * b (2 * n)
```

The proof works with formal power series over the reals and uses no analysis beyond $\sqrt2\cdot\sqrt2=2$. [Theorem](MinimaxTrees.lean#L244) · [Definitions](MinimaxTrees.lean#L38) · [Axiom report](logs/minimax_axioms.log)

### Scope

- The Lean statement concerns the two sequences defined by the recurrences above. They are the recurrences stated in the OEIS entries. For $a$ the root of a minimax tree carries the least or the greatest label and the other labels are split between the two subtrees. For $b$ the first block is an odd-sized subset. Trees and set partitions themselves are not formalized.
- A script enumerates minimax trees and ordered partitions into odd blocks for $n\le7$, compares the counts with the recurrences and with every term listed in the two OEIS entries, and checks the identity up to $2n=400$. Lean also proves the first six terms of each sequence from the definitions.
- Both generating functions are recorded in the OEIS entries, so the identity is a short computation once set up this way. A web search found no written proof, and the entry still marks the formula as conjectured. The proof has not been peer reviewed.

[Verification log](logs/minimax_verify.log)

## A further observation: lattice points in balls

Stephan noted in July 2003 that every known term of OEIS A055414, the number of points of $\mathbb{Z}^8$ of norm at most $n$, is congruent to 1 modulo 16. The entry carries no proof. The statement is a classical consequence of Jacobi's eight-square theorem, so it is not an open problem. The Lean proof here is elementary and more general: every ball of $\mathbb{Z}^{2^k}$ centred at the origin contains a number of lattice points congruent to 1 modulo $2^{k+1}$. [OEIS A055414](https://oeis.org/A055414)

```lean
theorem LatticeBall.A055414_mod_sixteen (n : ℕ) :
    (ballPoints 8 ((n : ℤ) ^ 2)).card % 16 = 1
```

[Theorem](LatticeBall.lean#L207) · [General statement](LatticeBall.lean#L185) · [Axiom report](logs/latticeball_axioms.log)

## Verification

Lean 4.19.0 reports exactly `propext`, `Classical.choice` and `Quot.sound` as the axioms of every theorem quoted above. The sources contain no `sorry`, no added axioms and no `native_decide`.

With elan and Python installed, run these commands from the repository root. The Lake manifest pins Mathlib and its dependencies.

```sh
cd problems/stephan-oeis-conjectures
sha256sum -c VERIFIED.sha256
python zonotope/verify_packets.py 7
python zonotope/verify_flips.py 12
python zonotope/check_proof_claims.py 6
python minimax/verify_identity.py 6 400
lake exe cache get
lake build
lake env lean tests/ExamplesZono.lean
lake env lean tests/AuditZono.lean
lake env lean tests/AuditMinimax.lean
lake env lean tests/AuditLatticeBall.lean
```

The recorded logs come from a Windows machine on which each module was compiled separately with `lean`. The workflow runs the full `lake build` on Ubuntu. [Compilation log](logs/lean_check.log) · [Verification workflow](../../.github/workflows/verify-stephan-oeis.yml)
