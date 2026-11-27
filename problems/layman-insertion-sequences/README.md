# Layman's conjectures on ratio-determined insertion sequences

## Conjecture credit

**John W. Layman** defined ratio-determined insertion sequences and stated five conjectures about them in the note *Ratio-Determined Insertion Sequences and the Tree of their Recurrence Types* (23 June 2003). He contributed six of the sequences to the OEIS, each with a conjectured recurrence. **Ralf Stephan** added conjectured product identities to five of the entries in May 2004. [Layman's note](https://personal.math.vt.edu/layman/sequences/ins_seq.htm) · [OEIS A082630](https://oeis.org/A082630) · [A082981](https://oeis.org/A082981) · [A085260](https://oeis.org/A085260) · [A085376](https://oeis.org/A085376) · [A085348](https://oeis.org/A085348) · [A085349](https://oeis.org/A085349)

**The sequences.** Fix a ratio 0 < k ≤ 1 and start with the finite sequence (1, 1). One pass inserts the sum a + b between every two adjacent terms a, b with k·b ≤ a. The passes are repeated for ever, and I(k) is the termwise limit. For example I(1/2) = 1, 3, 8, 21, 55, …. A sequence has *recurrence type* (C, D) if a(n) = C·a(n−D) − a(n−2D).

**The conjectures.**

- **C.1** Every I(k) has a recurrence type.
- **C.2** For each positive integer m, I(1/m) has type (m+1, 1).
- **C.3** Exactly two insertion sequences have a given type. They share their first D terms and differ in the next one.
- **C.4** For each m > 1 some ratio strictly between 1/m and 1/(m−1) has type (m(m+1)−2, 2).
- **C.5** The types form a tree in which a new type (L·R − X, l + r) is inserted between a type and each of its two parents, and every insertion sequence has a type from this tree.

M. F. Hasler remarked in A085260 in November 2018 that its recurrence was “so far apparently unproved”. Zhuorui He described the two-variable process used below in A082630 in July 2025, without proof. On 26 November 2026 all six entries still showed their recurrences as conjectures.

## Result

| Conjecture | Verdict | Established by |
| --- | --- | --- |
| C.1 | True for every rational k. False for uncountably many irrational k, for example k = 0.63300245632267396054…. | Written proof |
| C.2 | True for every m ≥ 1. The same recurrence holds for all k with m/(m²+m−1) ≤ k ≤ 1/m. | Lean, `layman_C2` |
| C.3 | Each type comes from an interval of ratios, a *plateau*, which carries exactly two sequences with the stated property. That two plateaus never share a type is checked for period words of at most 40 letters and is not proved. | Written proof. Lean for the types (m+1, 1), `layman_C2_twin` |
| C.4 | True for every m ≥ 2, with the ratio k = m/(m²−1). | Lean, `layman_C4` and `layman_C4_between` |
| C.5 | The types are indexed by a binary tree of word pairs, Layman's rule is a trace identity for 2×2 matrices, and the ratios are ordered as he says. The last clause holds for every rational k and fails together with C.1. | Written proof |

The six OEIS entries, with terms numbered from 0:

| Entry | Ratio k | Recurrence, Layman 2003 | Product identity, Stephan 2004 |
| --- | --- | --- | --- |
| A082630 | 7/11 | a(n+4) = 4a(n+2) − a(n) | a(n)a(n+3) = a(n+1)a(n+2) − 2 |
| A082981 | 4/5 | a(n+8) = 6a(n+4) − a(n) | |
| A085260 | 0.0833344 | a(n+2) = 13a(n+1) − a(n) | a(n)a(n+3) = a(n+1)a(n+2) + 143 |
| A085376 | 0.36704 | a(n+4) = 10a(n+2) − a(n) | a(n)a(n+3) = a(n+1)a(n+2) − 3 |
| A085348 | 0.264 | a(n+4) = 18a(n+2) − a(n) | a(n)a(n+3) = a(n+1)a(n+2) − 4 |
| A085349 | 0.26688 | a(n+4) = 18a(n+2) − a(n) | a(n)a(n+3) = a(n+1)a(n+2) + 11 |

All eleven statements in this table are proved in Lean, for every n. Lean also proves Layman's remarks on A082630: 3a(2n)² + 6 is a square, a(2n+1) is even, and 3(a(2n+1)/2)² + 1 is a square.

### The reduction, formalized

Put θ = 1/k − 1. Start from (X, Y) = (1, 1) and repeat: replace (X, Y) by (X, X + Y) if Y/X ≤ θ, and by (X + Y, Y) otherwise. Then I(k) is the sequence of successive values of X. Lean proves this for every rational k = p/q, starting from the insertion passes as Layman defines them.

```lean
def pass (p q : ℕ) : List ℕ → List ℕ
  | [] => []
  | [a] => [a]
  | a :: b :: l =>
      if p * b ≤ q * a then a :: (a + b) :: pass p q (b :: l) else a :: pass p q (b :: l)

def stage (p q n : ℕ) : List ℕ := (pass p q)^[n] [1, 1]

def IsLimit (p q : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ i, ∃ N, ∀ n, N ≤ n → (stage p q n)[i]? = some (a i)

theorem isLimit_rdis (p q : ℕ) (hp : 0 < p) (hpq : p ≤ q) : IsLimit p q (rdis p q)
```

Here `rdis p q` is the two-variable process, with the runs of the first move taken in one step. The limit is unique (`IsLimit.unique`), so every later theorem about `rdis p q` is a theorem about I(p/q). [Definitions](Insertion/Core.lean#L16) · [Theorem](Insertion/Core.lean#L233)

### The two families, formalized

```lean
theorem layman_C2 (m p q : ℕ) (hm : 0 < m) (hp : 0 < p) (h1 : m * p ≤ q)
    (h2 : m * q + p ≤ (m * m + m) * p) :
    rdis p q 0 = 1 ∧ rdis p q 1 = m + 1 ∧
      ∀ n, rdis p q (n + 2) + rdis p q n = (m + 1) * rdis p q (n + 1)

theorem layman_C4 (m q : ℕ) (hm : 2 ≤ m) (hq : q + 1 = m * m) :
    (rdis m q 0 = 1 ∧ rdis m q 1 = m ∧ rdis m q 2 + 1 = m * m + m ∧
        rdis m q 3 + 2 * m = m * m * m + m * m) ∧
      ∀ n, rdis m q (n + 4) + rdis m q n + 2 * rdis m q (n + 2) =
        (m * m + m) * rdis m q (n + 2)
```

The hypotheses of `layman_C2` say m/(m²+m−1) ≤ p/q ≤ 1/m. Its companion `layman_C2_twin` covers 1/m < p/q ≤ (m+1)/(m²+m−1), where the sequence begins 1, m and satisfies the same recurrence. This is the second sequence of type (m+1, 1) that C.3 asks for. In `layman_C4` the ratio is m/(m²−1), and `layman_C4_between` states that it lies strictly between 1/m and 1/(m−1). The statements avoid subtraction, so the recurrence of C.4 appears with the term 2a(n+2) on the left. [C.2](Insertion/Families.lean#L64) · [Twin](Insertion/Families.lean#L146) · [C.4](Insertion/Families.lean#L235) · [OEIS entries](Insertion/OEIS.lean#L77)

### The structure theorem, proved on paper

The process is a map of the half-line: t = Y/X goes to t + 1 if t ≤ θ and to t/(1+t) otherwise. Write R and L for the two moves. Let 𝒯 be the set of pairs of words generated from (R, L) by the rules (U, V) → (UV, V) and (U, V) → (U, VU), and let ξ(W) be the positive fixed point of the map of a word W.

1. The intervals Π(U, V) = [ξ(UV), ξ(VU)] are pairwise disjoint, and the two children of a pair have their intervals on either side of it.
2. For θ in Π(U, V) the moves made from the start are periodic with a period word that is a rotation of UV. There are two possibilities, separated by one rational point inside the interval. So I(k) takes exactly two values there. Both have type (C, D), where C is the trace of the matrix of UV and D is the number of letters L in UV.
3. The traces obey trace(AB) + trace(AB⁻¹) = trace(A)·trace(B), which is Layman's rule (L·R − X, l + r).
4. The set E of θ in no interval is uncountable, has empty interior and contains no rational number. For θ in E the sequence satisfies no recurrence a(n) = C·a(n−D) − a(n−2D), not even from some point on.

The proof is a renormalization argument: a pair (U, V) acts as a first-return map of the same shape, and comparing θ with the two fixed points decides between stopping and passing to a child. A point of E is reached by renormalizing for ever. For rational θ this cannot happen, by the subtractive Euclidean algorithm. [Written proof](PROOF.md)

## Scope

- Lean proves the reduction, C.2, C.4 and the statements about the six OEIS entries, for rational ratios. It does not contain the tree 𝒯 or the structure theorem. The verdicts on C.1, C.3 and C.5 rest on the written proof, which has not been peer reviewed.
- The formal theorems concern the sequences defined by the insertion passes with the ratio stated in each OEIS entry. Lean checks by evaluation that these definitions reproduce the terms listed in the entries.
- Lean counts positions from 0, so `rdis p q 0 = 1` is the first term.
- One half of C.3 is open here: that two different plateaus cannot have the same type. A script finds no coincidence among the 489 period words of at most 40 letters.
- The counterexamples to C.1 are irrational ratios. For five of them a script computes the ratio to more than 500 digits, confirms that the moves predicted by the theory are the moves of the process for 4000 steps, and finds that every recurrence with D ≤ 60 fails on the computed terms. That computation illustrates the theorem. It is not a proof of it.
- Scripts check the written proof with exact rational arithmetic: all 79 pairs of 𝒯 with period at most 16, and all 4408 rational θ with denominator at most 60 and θ ≤ 4.
- Nothing is claimed about the measure or the arithmetic nature of E beyond irrationality. Sean Irvine's 2022 conjecture in A085376 and Layman's identifications of sections of A082981 with other entries were not examined.
- The search for an earlier proof covered the OEIS entries, Layman's pages and web searches for the name of the sequences, and found none.

[Script logs](logs/)

## Verification

Lean 4.19.0 reports no axioms beyond `propext`, `Classical.choice` and `Quot.sound` for the 26 audited theorems. The sources contain no `sorry`, no added axioms and no `native_decide`. [Axiom report](logs/lean_audit.log)

With elan and Python installed, run these commands from the repository root. The Lake manifest pins Mathlib and its dependencies.

```sh
cd problems/layman-insertion-sequences
sha256sum -c VERIFIED.sha256
python scripts/explore.py
python scripts/targets.py
python scripts/verify_tree.py 10 4
python scripts/verify_structure.py 16
python scripts/verify_rational.py 60 40
python scripts/verify_exceptional.py 18 4000 60
lake exe cache get
lake build
lake env lean tests/Audit.lean
```

The recorded logs come from a Windows machine on which each module was compiled separately with `lean`. The workflow runs the full `lake build` on Ubuntu. [Compilation log](logs/lean_check.log) · [Verification workflow](../../.github/workflows/verify-layman-insertion.yml)
