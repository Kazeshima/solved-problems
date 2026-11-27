# Ratio-determined insertion sequences: Layman's conjectures of 2003

Written on 26 and 27 November 2026. The proofs were found and written by Claude, an AI model made by Anthropic. They have not been peer reviewed. Section 9 says exactly which parts are checked by Lean, which are proved only on paper, and which are only checked by computation.

## 1. The problem

**Definition (J. W. Layman, 2003).** Fix a ratio 0 < k ≤ 1. Start with the finite sequence (1, 1). One *pass* inserts the sum a + b between every two adjacent terms a, b for which k·b ≤ a. Repeat the pass for ever. Every position is eventually constant, and the limit is the *ratio-determined insertion sequence* I(k). For example I(1) = 1, 2, 3, 4, …, I(1/2) = 1, 3, 8, 21, 55, … and I(1/3) = 1, 4, 15, 56, ….

Say that a sequence has *recurrence type* (C, D) if a(n) = C·a(n−D) − a(n−2D). In his note *Ratio-Determined Insertion Sequences and the Tree of their Recurrence Types* (23 June 2003) Layman stated five conjectures:

- **(C.1)** Each I(k) has a recurrence type (C, D) for some positive integers C and D.
- **(C.2)** For each positive integer m the sequence I(1/m) has type (m+1, 1).
- **(C.3)** If some I(k) has type (C, D), then exactly two distinct insertion sequences satisfy that recurrence. They have the same first D terms and differ in the (D+1)-th.
- **(C.4)** For each integer m > 1 there is a ratio strictly between 1/m and 1/(m−1) whose sequence has type (m(m+1) − 2, 2). (Layman's text has m(m−1) − 2; his example I(1/3), I(0.376), I(1/2) with types (4,1), (10,2), (3,1) shows that the product of the two neighbouring first entries is meant.)
- **(C.5)** The types form a tree: between a "child" type and each of its two "parent" types a new type (L·R − X, l + r) is inserted, where (L, l) and (R, r) are the two types and X is the first entry of the child's other parent. Every type in the tree is the type of some I(k), with k between the ratios of the parents, and every insertion sequence has a type from such a tree.

Layman added six of these sequences to the OEIS with their recurrences marked as conjectures (A082630, A082981, A085260, A085376, A085348, A085349). Ralf Stephan added conjectured product identities to five of them in May 2004. In November 2018 M. F. Hasler noted in A085260 that the recurrence was "so far apparently unproved", and the entries still read that way on 26 November 2026. A web search for the name of these sequences found only Layman's own pages and the OEIS entries.

## 2. Results

Write θ = 1/k − 1, so θ ≥ 0, and use the two moves

- R: (X, Y) ↦ (X, X + Y), that is t ↦ t + 1 for t = Y/X,
- L: (X, Y) ↦ (X + Y, Y), that is t ↦ t/(1 + t).

**Theorem 1 (reduction).** Start from (X, Y) = (1, 1) and repeat: apply R if Y/X ≤ θ, otherwise apply L. Then I(k) is the sequence of successive values of X. *(Lean: `isLimit_rdis`, for every rational k.)* The process was pointed out, without proof, by Zhuorui He in the OEIS entry A082630 in July 2025.

So I(k) is read off from the orbit of t = 1 under the map f(t) = t + 1 for t ≤ θ, f(t) = t/(1+t) for t > θ. The *itinerary* is the infinite word over {R, L} of the moves made. For a finite word W write W(t) for the result of applying its letters from left to right, M(W) for the corresponding 2×2 matrix, and, when W contains both letters, ξ(W) for the unique positive fixed point of t ↦ W(t).

**The tree.** Let 𝒯 be the set of pairs of words generated from (R, L) by the two rules (U, V) → (UV, V) and (U, V) → (U, VU). For a pair (U, V) put

- Π(U, V) = [ξ(UV), ξ(VU)], a closed interval with irrational endpoints, the *plateau*,
- C = trace M(UV) and D = number of letters L in UV.

**Theorem 2 (structure).**

1. The plateaus Π(U, V), (U, V) ∈ 𝒯, are pairwise disjoint and nonempty. The children of (U, V) have their plateaus on either side of Π(U, V): Π(UV, V) to the left and Π(U, VU) to the right.
2. For θ in Π(U, V) the itinerary of the start is purely periodic. There are a word w of |UV| − 2 letters and a rational number r in the interior of Π(U, V) such that the itinerary is (wRL)^∞ for θ ≥ r and (wLR)^∞ for θ < r. Both period words are rotations of UV.
3. Hence on Π(U, V) the sequence I(k) takes exactly two values. Both satisfy a(n+2D) = C·a(n+D) − a(n) for all n ≥ 1, they have the same first D terms, and their (D+1)-th terms differ.
4. The types obey trace M(UVV) = C·trace M(V) − trace M(U) and trace M(UVU) = C·trace M(U) − trace M(V), which is Layman's rule (L·R − X, l + r).
5. Let E be the set of θ > 0 in no plateau. E is uncountable and has empty interior, and it contains no rational number. For θ in E the sequence I(k) satisfies no recurrence a(n) = C·a(n−D) − a(n−2D), not even for all large n.

**An explicit exception.** The path in 𝒯 that alternates the two rules, beginning with (U, V) → (UV, V), belongs to exactly one θ, namely θ = 0.57977270074011922299…, that is k = 0.63300245632267396054…. Its sequence begins 1, 2, 5, 8, 19, 49, 79, 188, 297, 703, 1812, 2921, … and satisfies no recurrence of the kind above. The digits are computed in `scripts/verify_exceptional.py`.

**Consequences for the conjectures.**

| | Verdict | Where |
|---|---|---|
| C.1 | True for every rational k, and for every real k outside E. False for the uncountably many irrational k with θ in E. | Theorem 2, parts 3 and 5 |
| C.2 | True. I(1/m) = 1, m+1, … has type (m+1, 1), and so does I(k) for m/(m²+m−1) ≤ k ≤ 1/m. | Lean `layman_C2` |
| C.3 | True in this form: each plateau carries exactly two sequences, with the stated property. For 1/m < k ≤ (m+1)/(m²+m−1) the twin of I(1/m) is 1, m, …. That two different plateaus never share a type is checked for all period words of at most 40 letters, not proved. | Theorem 2 part 3, Lean `layman_C2_twin` |
| C.4 | True, with the ratio m/(m²−1). | Lean `layman_C4`, `layman_C4_between` |
| C.5 | The tree is 𝒯 with the trace rule, every type in it occurs, and the ratios are ordered as stated. The last sentence holds for every rational k and fails exactly on E. | Theorem 2 |

**Theorem 3 (the OEIS entries).** With terms numbered from 0:

| Entry | Ratio | Recurrence (Layman 2003) | Product identity (Stephan 2004) |
|---|---|---|---|
| A082630 | 7/11 | a(n+4) = 4a(n+2) − a(n) | a(n)a(n+3) = a(n+1)a(n+2) − 2 |
| A082981 | 4/5 | a(n+8) = 6a(n+4) − a(n) | |
| A085260 | 0.0833344 | a(n+2) = 13a(n+1) − a(n) | a(n)a(n+3) = a(n+1)a(n+2) + 143 |
| A085376 | 0.36704 | a(n+4) = 10a(n+2) − a(n) | a(n)a(n+3) = a(n+1)a(n+2) − 3 |
| A085348 | 0.264 | a(n+4) = 18a(n+2) − a(n) | a(n)a(n+3) = a(n+1)a(n+2) − 4 |
| A085349 | 0.26688 | a(n+4) = 18a(n+2) − a(n) | a(n)a(n+3) = a(n+1)a(n+2) + 11 |

For A082630 also 3a(2n)² + 6 is a square, a(2n+1) is even and 3(a(2n+1)/2)² + 1 is a square, as Layman observed. *(Lean: file `Insertion/OEIS.lean`.)*

## 3. Proof of Theorem 1

Call a term *settled* when no insertion will ever again be made directly to its left or right inside the settled prefix. Claim: after each pass the list has the form P, X, X+Y, Y, T, where P, X is a settled prefix and T is some tail, and one pass changes (P, X, Y) by one step of the process.

- After the first pass the list is 1, 2, 1, which is the claim with P empty and (X, Y) = (1, 1).
- Suppose the list is P, X, X+Y, Y, T. Since k ≤ 1 and Y < X + Y, the pair (X+Y, Y) always receives the insertion X + 2Y.
  - If k(X+Y) ≤ X, the pair (X, X+Y) receives 2X + Y. The list becomes P, X, 2X+Y, X+Y, …, which is the claim for the state (X, X+Y). This is the move R.
  - Otherwise nothing is inserted after X, and X+Y is settled. The list becomes P, X, X+Y, X+2Y, Y, …, which is the claim for the prefix P, X and the state (X+Y, Y). This is the move L.
- A settled prefix is never changed, and R can be applied only finitely often in a row because Y grows by X each time. So every position is eventually settled, and the settled terms are the successive values of X. ∎

The Lean proof follows this argument with rational k = p/q.

## 4. Words, matrices and recurrences

Let M(R) = [[1,0],[1,1]] and M(L) = [[1,1],[0,1]] act on columns (X, Y), and M(W) be the product for a word W, the first letter acting first. All M(W) have determinant 1 and nonnegative entries. The two matrices generate a free monoid, so W is determined by M(W).

**Lemma 4.1.** If W contains both letters, t ↦ W(t) is increasing on (0, ∞) and has exactly one fixed point ξ(W) there. Moreover W(t) > t for t < ξ(W) and W(t) < t for t > ξ(W). The number ξ(W) is irrational.

*Proof.* With M(W) = [[a,b],[c,d]], all entries positive, W(t) = (c + dt)/(a + bt) and W(t) − t = −(bt² + (a−d)t − c)/(a + bt). The quadratic has roots of opposite sign. Its discriminant is (a+d)² − 4, which is not a square because a + d ≥ 3. ∎

For the letters alone, R(t) > t and L(t) < t for all t > 0, R^n(t) → ∞ and L^n(t) → 0.

**Lemma 4.2 (periodic itinerary gives a recurrence).** Let u(1), u(2), … be the states right after each move L, so that a(n) is the first coordinate of u(n) for n ≥ 2. Suppose the itinerary from a vector u(1) with first coordinate a(1) is P^∞, where the word P ends with L and contains D letters L. Then a(n+2D) = C·a(n+D) − a(n) for all n ≥ 1, with C = trace M(P).

*Proof.* The itinerary from u(n) is Q^∞ for a rotation Q of P that ends with L, so u(n+D) = M(Q)u(n) and u(n+2D) = M(Q)²u(n). By Cayley–Hamilton M(Q)² = C·M(Q) − 1, since rotations have the same trace. ∎

**Lemma 4.3 (a recurrence forces a periodic itinerary).** If a(n+2D) = C·a(n+D) − a(n) for all large n, then the itinerary is eventually periodic.

*Proof.* The second coordinate of u(n) is a(n) − a(n−1), so the vectors satisfy u(n+2D) = C·u(n+D) − u(n) for large n. Let B(n) be the word of moves between u(n) and u(n+D). Runs of R have length at most θ + 1, so only finitely many words occur. If the pair (B(n), B(n+D)) = (B, B′) occurs for two indices n ≠ n′, the matrix M(B′)M(B) − C·M(B) + 1 kills u(n) and u(n′). These are distinct primitive positive vectors, hence independent, so the matrix is zero and M(B′) = C − M(B)⁻¹ = M(B) + δ with δ = C − trace M(B). Taking determinants gives δ(trace M(B) + δ) = 0. The value δ = −trace M(B) would make M(B′) = −M(B)⁻¹, which has negative diagonal entries. So δ = 0 and B′ = B. Only finitely many n have a pair that occurs once, so B(n+D) = B(n) for all large n. ∎

## 5. Renormalization

Fix θ > 0. Call a pair of words (U, V) *admissible* if, writing u, v for the maps,

- (A1) v(θ) < θ < u(θ),
- (A2) v(u(θ)) < u(v(θ)),
- (A3) every x in (v(θ), θ] has an itinerary beginning with U, and every x in (θ, u(θ)] has an itinerary beginning with V.

Put W = (v(θ), u(θ)] and F(x) = u(x) for x ≤ θ, F(x) = v(x) for x > θ. By (A1) and (A2), v(θ) < v(u(θ)) < u(v(θ)) < u(θ), so F maps W into W, and by (A3) the itinerary of a point of W is the concatenation of the blocks U, V read along its F-orbit.

**Lemma 5.1 (trichotomy).** Let (U, V) be admissible.

- (I) If θ < v(u(θ)), then (UV, V) is admissible.
- (III) If u(v(θ)) < θ, then (U, VU) is admissible.
- (II) If v(u(θ)) ≤ θ ≤ u(v(θ)), then F(x) > θ for x ≤ θ and F(x) ≤ θ for x > θ. So every itinerary of a point of W alternates the blocks: (UV)^∞ from x ≤ θ and (VU)^∞ from x > θ.

*Proof.* (I) The new maps are u′ = v∘u and v′ = v. (A1): v(θ) < θ < v(u(θ)). (A2): v(v(u(θ))) < v(u(v(θ))) because v is increasing. (A3): the new window is (v(θ), v(u(θ))]. A point x ≤ θ in it starts with U and u(x) > u(v(θ)) > θ, so V follows. A point x > θ in it lies in (θ, u(θ)] and starts with V. (III) is symmetric. (II) For x ≤ θ, u(x) > u(v(θ)) ≥ θ. For x > θ, v(x) ≤ v(u(θ)) ≤ θ. ∎

The pair (R, L) is admissible for every θ > 0: the window is (θ/(1+θ), θ+1], and L(R(θ)) < 1 < R(L(θ)). By Lemma 4.1 case (I) means θ < ξ(UV), case (III) means θ > ξ(VU), and case (II) means θ ∈ Π(U, V). Starting from (R, L) and following Lemma 5.1 gives a path in 𝒯 which either stops at a node whose plateau contains θ or goes on for ever.

**Lemma 5.2.** An infinite path makes both kinds of step infinitely often.

*Proof.* Suppose all steps from some pair (U, V) on are of kind (I). The pairs are then (UV^n, V), and θ < v^n(u(θ)) for all n. But v(θ) < θ, so v^n(u(θ)) tends to ξ(V) < θ, or to 0 if V = L. The other case is symmetric. ∎

**Proof of Theorem 2, part 1.** Let J(U, V) be the set of θ whose path reaches (U, V). Then J(R, L) = (0, ∞), J(UV, V) = J(U, V) ∩ (0, ξ(UV)) and J(U, VU) = J(U, V) ∩ (ξ(VU), ∞), so each J is an open interval and sets J of nodes not on a common branch are disjoint. The claim is that every J(U, V) is nonempty and contains Π(U, V), and that ξ(UV) < ξ(VU). Argue by induction on the depth of the node, assuming the claim for all its ancestors.

It is enough that J(U, V) contains a point θ₁ of case (I) and a point θ₃ of case (III). Indeed, by (A2) no point of J(U, V) is in both cases. If ξ(UV) ≥ θ₃, the points of J(U, V) just below θ₃ would be in both, being above ξ(VU) and below ξ(UV). So θ₁ < ξ(UV) < θ₃ and ξ(UV) lies in J(U, V). Then (A2) at θ = ξ(UV) says that VU moves ξ(UV) upwards, so ξ(UV) < ξ(VU) by Lemma 4.1, and ξ(VU) < θ₃.

Take the right end of J(U, V). If it is ∞, only steps of kind (III) were made, the pair is (R, LR^j), and u(v(θ)) = θ/(1+θ) + j + 1 < θ for large θ. Otherwise the right end is τ = ξ(U₀V₀) for the last ancestor (U₀, V₀) left by a step of kind (I), and all later steps were of kind (III). Here the induction hypothesis is used: each ancestor's interval contains its plateau, so every step cuts off a proper piece and J(U, V) is a nonempty interval ending at τ. The pair is (U₁, V₀U₁^i) with U₁ = U₀V₀ and some i ≥ 0. The point τ lies in Π(U₀, V₀), hence in J(U₀, V₀), so v₀(τ) < τ. Since u₁ fixes τ and is increasing, v(τ) = u₁^i(v₀(τ)) < τ and u(v(τ)) < u(τ) = τ. By continuity case (III) holds just below the right end.

The left end is symmetric. If it is 0, only steps of kind (I) were made, the pair is (RL^j, L), and v(u(θ)) tends to 1/(j+2) as θ → 0, so case (I) holds for small θ. Otherwise the left end is τ = ξ(V₀U₀) for the last ancestor left by a step of kind (III), the pair is (U₀V₁^i, V₁) with V₁ = V₀U₀, and u₀(τ) > τ gives u(τ) > τ and v(u(τ)) > τ, so case (I) holds just above the left end. ∎

## 6. Inside a plateau

**Proof of Theorem 2, parts 2 to 4.** Let (U, V) ∈ 𝒯 and N = |UV|. Write ℓ(W) for the number of letters L in a word W. The number |U|·ℓ(V) − ℓ(U)·|V| equals 1 at the root and is preserved by both rules, so N and D are coprime and UV is not a proper power.

Let θ be in the interior of Π(U, V). By Lemma 5.1 (II) the map v∘u sends (v(θ), θ] into itself, and its fixed point ξ(UV) lies in that interval. So the orbit of ξ(UV) is periodic with itinerary (UV)^∞ and least period N. Let p₁ < … < p_N be its points. They are the fixed points of the rotations of UV and do not depend on θ. Let p_c be the largest one that is ≤ θ. The points p₁, …, p_c are moved by R and the others by L. Images under L are less than 1 and images under R are greater than 1, and f is increasing on each side of θ, so

  f(p_i) = p_{i+N−c} for i ≤ c,  f(p_i) = p_{i−c} for i > c.

Thus f rotates the indices by N − c. In particular p_{N−c} = L(p_N) < 1 < R(p₁) = p_{N−c+1}, so the start 1 lies in the arc A₁ = (p_{N−c}, p_{N−c+1}).

An arc (p_i, p_{i+1}) with i ≠ c does not contain θ, so f maps it increasingly into the arc between the images of its ends, and all its points make the same move as its ends. Since the rotation has a single cycle, the arcs A₁, f(A₁), … are the arcs with indices N−c, 2(N−c), … and the arc (p_c, p_{c+1}) is reached after exactly N − 2 steps. Let w be the word of the first N − 2 moves of p_{N−c}, and r = w(1). Then r is rational, it is the same number for all θ in the interior of the plateau, and p_c < r < p_{c+1}.

- If r ≤ θ, then r and p_c both move by R. The interval (p_c, θ] is mapped by R into (p_N, θ+1], then by L into (p_{N−c}, 1) inside A₁, and so on along the same arcs. After N steps it returns to (p_c, x] with x = Φ(θ), where Φ is the map of the period word of p_c. Since Φ fixes p_c and θ > p_c, Lemma 4.1 gives Φ(θ) < θ. So the orbit of r follows that of p_c for ever, and the itinerary of the start is that of p_{N−c}, namely (wRL)^∞.
- If r > θ, the same argument with (θ, p_{c+1}) shows that the itinerary of the start is that of p_{N−c+1}, namely (wLR)^∞.

Both cases occur. Indeed the move made by each p_i is read off the word UV, so it is the same for every θ in the interior of the plateau, and therefore no p_i lies in the interior. The endpoints ξ(UV) and ξ(VU) are themselves among the p_i, so p_c = ξ(UV) and p_{c+1} = ξ(VU) for every such θ, and r lies strictly between. The endpoints of the plateau are irrational, while the points of the orbit of the start are rational. So each finite piece of the itinerary is constant near an endpoint, and the statement extends to the closed plateau. This proves part 2.

For part 3, the word w contains D − 1 letters L, so both itineraries produce the same terms a(1), …, a(D). If the state after w is (X, Y), the next term is 2X + Y after RL and X + Y after LR. For the recurrence apply Lemma 4.2. In the first case take u(1) = (1, 1) and P = wRL. In the second case take u(1) = (1, 0) and P = RwL, noting that R(1, 0) = (1, 1). Both words are rotations of UV, so C = trace M(UV).

Part 4 is the identity trace(AB) + trace(AB⁻¹) = trace(A)·trace(B) for matrices of determinant 1, with A = M(UV) and B = M(V) or M(U). ∎

Layman's trees sit inside 𝒯 as follows. A word with j letters R and one letter L has trace j + 2. For m ≥ 2 the pair (R, LR^{m−2}) has a period word with m − 1 letters R and type (m+1, 1). Its child (RLR^{m−2}, LR^{m−2}) has type ((m+1)m − 2, 2), and the subtree below it is Layman's tree between the types (m, 1) and (m+1, 1). The ratio k = 1 is θ = 0, where no insertion is ever refused and I(1) = 1, 2, 3, ….

The ordering in (C.5) also follows. In a pair (U, V) the word V is either L or a rotation of the period word of the last ancestor left by a step of kind (III), and the plateau of that ancestor ends where J(U, V) begins. The same holds for U on the right. So Π(U, V) lies strictly between the plateaus of its two parents, or to the right of θ = 0 when V = L.

## 7. The exceptional set

**Proof of Theorem 2, part 5.** Let E be the set of θ with an infinite path.

*E is uncountable.* Take any infinite sequence of steps that contains both kinds infinitely often. The corresponding intervals J are nested. Since each J contains its plateau, a step of kind (I) moves the right end strictly inside and a step of kind (III) moves the left end strictly inside. After one step of each kind the closure of the new interval lies in the old one, so the intersection is nonempty. Every point of it has this path. Different sequences give different points.

*The windows shrink.* Let θ ∈ E with pairs (U_n, V_n) and windows W_n. The next window is v_n((θ, u_n(θ)]) or u_n((v_n(θ), θ]). The derivative of L at a point x > θ is (1+x)⁻² < λ with λ = (1+θ)⁻² < 1, and the other moves have derivative at most 1. Every V_n begins with L, and after the first step of kind (I) every U_n contains an L. So from then on the length of the window shrinks by the factor λ at each step, and it tends to 0.

*The start follows the gaps.* Put s₀ = 1, and s_{n+1} = v_n(s_n) after a step of kind (I), s_{n+1} = u_n(s_n) after a step of kind (III). Then s_n lies in the gap (v_n(u_n(θ)), u_n(v_n(θ))], which is part of W_n. This holds for n = 0, and a step of kind (I) puts the gap to the right of θ and maps it by v_n onto the next gap, while a step of kind (III) puts it to the left of θ and maps it by u_n. So each s_n is a point of the orbit of the start, it is given by the path alone, s_n > θ at the steps of kind (I) and s_n < θ at the steps of kind (III), and |s_n − θ| is at most the length of W_n. Hence s_n → θ.

*E has empty interior.* By the last paragraph θ is determined by its path. Two points θ < θ′ of E therefore have different paths, and at the node where the paths separate θ is in case (I) and θ′ in case (III), so the plateau of that node lies between them.

*No recurrence.* Suppose the itinerary for θ ∈ E were eventually periodic, with L occurring with frequency a/b. For each n the itinerary is a finite word, leading to s_n, followed by blocks U_n and V_n. So a/b lies between the frequencies μ_n ≤ ν_n of L in U_n and V_n. These are neighbours in the Farey sense, and each step replaces one of them by their mediant. A fraction strictly between them has denominator at least |U_n| + |V_n|, which is unbounded. So a/b equals an endpoint, say μ_n, for all large n, which means that U_n no longer changes and all later steps are of kind (III). This contradicts Lemma 5.2. So the itinerary is not eventually periodic, and Lemma 4.3 shows that no recurrence of type (C, D) holds, even for large n.

*E contains no rational number.* Let θ ∈ E. The points s_n at the steps of kind (I) are orbit points to the right of θ that tend to θ, so there are orbit points y(1) > y(2) > … tending to θ. Apart from the start, every orbit point y has a unique predecessor, y − 1 if y > 1 and y/(1−y) if y < 1, and every orbit point is at least min(1, θ/(1+θ)). Put θ₀ = θ and θ_{i+1} = θ_i − 1 if θ_i > 1, θ_{i+1} = θ_i/(1−θ_i) if θ_i < 1. By induction the i-th predecessors of the y(m) exist for large m and tend to θ_i from above. If some θ_i were equal to 1, the next predecessors would tend to 0, which is impossible. If some θ_i were 0 the same contradiction arises. So the sequence θ_i never reaches 1. But for θ = P/Q the rule is the subtractive Euclidean algorithm on (P, Q), which reaches 1 after finitely many steps. Hence θ is irrational. ∎

So every rational ratio k lies in a plateau, and I(k) has a recurrence type from the tree, valid from the first term.

## 8. The infinite families and the OEIS entries

One step of the settled process can be written without the single moves: from (X, Y) the next state is (X + Y + jX, Y + jX), where j is the number of moves R made before the next L. The number j is determined by k(Y + jX) ≤ X < k(X + Y + jX), the first inequality being required only for j > 0 (Lean: `next_eq`).

- **C.2.** For m/(m²+m−1) ≤ k ≤ 1/m every step has j = m − 1, on the cone Y ≤ X, (m−1)X < mY. The step matrix has trace m + 1.
- **Twin of C.2.** For 1/m < k ≤ (m+1)/(m²+m−1) the first step has j = m − 2 and all later ones j = m − 1, on the cone (m+1)Y ≤ mX.
- **C.4.** For k = m/(m²−1) the steps alternate j = m − 2 and j = m − 1, on the cone Y ≤ X, (m−1)X < mY for the even states. The two-step matrix has trace m(m+1) − 2. The first terms are 1, m, m²+m−1, m³+m²−2m.
- **OEIS entries.** Each has a periodic pattern of j and a cone given by two linear inequalities on which the pattern is forced. The product identities follow from a quadratic invariant of the period-start states, for example X² + 2 = 3Y² for A082630.

## 9. What is verified, and how

**Checked by Lean 4.19.0 with Mathlib** (26 theorems, axioms `propext`, `Classical.choice`, `Quot.sound` only, no `sorry`, no `native_decide`; see `logs/lean_audit.log`):

- `Insertion/Core.lean`: the definitions `pass`, `stage`, `IsLimit` (the literal insertion process and its termwise limit), the process `rdis`, Theorem 1 as `isLimit_rdis` for all 0 < p ≤ q, uniqueness of the limit, and `next_eq`.
- `Insertion/Families.lean`: `layman_C2`, `layman_C2_twin`, `layman_C4`, `layman_C4_between`, for all m.
- `Insertion/OEIS.lean`: the 19 statements of Theorem 3, including the first terms of each sequence.

Lean counts positions from 0, so `rdis p q 0 = 1` is the first term.

The recorded logs come from a Windows machine on which each module was compiled separately with `lean`. The repository workflow runs `lake build` on Ubuntu.

**Proved on paper only:** Theorem 2 (sections 4 to 7), and Theorem 1 for irrational k.

**Checked by exact computation, not proved:** that two different plateaus never have the same type (C, D), and that no type coincides with the type of a power of a shorter period word. This was checked for all 489 period words of at most 40 letters (`scripts/verify_rational.py`).

**Computational checks of the paper proofs** (all exact integer or rational arithmetic, scripts in `scripts/`):

- `verify_structure.py`: for every pair of 𝒯 with |UV| ≤ 16, the twin point lies in the plateau, the itinerary is the predicted one at seven ratios including the twin point and points within 10⁻²⁵ of it and within 2·10⁻³⁰ of the endpoints, the type is (C, D), and the itinerary is different just outside.
- `verify_rational.py`: all 4408 rational θ = P/Q with Q ≤ 60 and 0 < θ ≤ 4 lie in a plateau, with the predicted itinerary and type.
- `verify_exceptional.py`: for five periodic paths of the kind used in section 7, the orbit points s_n of the first 18 steps enclose θ in an interval shorter than 10⁻⁵⁰⁰, every θ in that interval follows at least the first 15 steps of the path, and the itinerary given by the path agrees with the process on the first 4000 moves. On the resulting 1500 to 3700 terms each recurrence with D ≤ 60 fails somewhere in the second half. This last test is evidence, not a proof.
- `verify_tree.py`: the same tree in Layman's form, down to period 10.
- `targets.py`: every statement that was formalized, compared with direct simulation before the Lean work began.
- `explore.py`: the literal insertion passes agree with the two-variable process on Layman's examples.

Logs are in `logs/`.

**Not done.** No statement about the measure or the arithmetic nature of E beyond irrationality. Sean Irvine's 2022 conjecture in A085376 (partial sums of A129445) and Layman's identifications of sections of A082981 with other OEIS entries were not examined.

## Sources

- J. W. Layman, *Ratio-Determined Insertion Sequences and the Tree of their Recurrence Types*, 23 June 2003: https://personal.math.vt.edu/layman/sequences/ins_seq.htm (copy kept by the OEIS at https://oeis.org/A085376/a085376.txt)
- OEIS entries https://oeis.org/A082630, https://oeis.org/A082981, https://oeis.org/A085260, https://oeis.org/A085376, https://oeis.org/A085348, https://oeis.org/A085349
