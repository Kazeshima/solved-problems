# Lean formalization and verification

The theorem in [MABKCore.lean](../MABKCore.lean) states

```lean
theorem MABK.conjecture1 (n : ℕ) (hn : 2 ≤ n) (he : Even n) :
    IsGreatest (MABK.uniformValues n) (MABK.publishedMstar n)
```

Its two hypotheses restrict the party count. Expanding `IsGreatest` produces two obligations. The published value belongs to the physically realized, uniform-output set, and every member of that set is at most the published value. Both obligations have proofs.

## Reading the definitions against the paper

* In `MABKCore.lean` lines 13–18, `mabk` is Eq. (1) summed over all bit settings, encoded by the subsets of `Fin n`. It has real prefactor $2^{(1-n)/2}$. The target `publishedMstar` is $2^{(n-1)/2}$ times Eq. (24) evaluated at Eqs. (25)–(26). `Diagonal.lean` lines 210–216 define all four angle cases, and line 248 proves Eq. (24) for arbitrary angle. `published_value` identifies the published definition with $Q_n r$. [Original Eqs. (1) and (24)–(27)](https://arxiv.org/pdf/2308.07030v3)
* `Realization.lean` lines 26–38 defines a complex Hilbert space, a unit vector and two self-adjoint unitary observables per party. Observables of different parties commute. `Outcomes.lean` lines 28–33 constructs the effects $(I+(-1)^a A)/2$ and the joint outcome operator. The realization relation equates every probability to its Born expectation. `uniformValues` requires $p(a|\mathbf 0)=2^{-n}$ separately for every output string.
* The upper bound is valid even for commuting-operator projective devices. Ordinary local projectors tensored with identities satisfy precisely the commutations used in the proof. The general inequality `zero_correlator_bound` also applies directly to a contractive linear state functional, including normalized mixed states. The lower bound uses an actual tensor product of qubits, with both local bases and the normalized state constructed explicitly. These two facts put the maximum in the paper's tensor-product model at the same value. The tensor-POVM dilation in §2 of the manuscript was checked on paper. The Lean project uses the projective model of the original §2.1. [Paper, quantum model](https://arxiv.org/html/2308.07030v3#S2.SS1)

## Dependency map

| Stage | Proof in this project |
| --- | --- |
| General quantum upper bound | `Quantum.lean:60` generates the norm-closed abelian star algebra of the relative unitaries. The isometric Gelfand transform evaluates them at unit phases. `Quantum.lean:127` derives the shifted Bell bound. `Outcomes.lean:73` and `Outcomes.lean:82` prove the parity and Bell expectations from the Born probabilities. |
| Global torus reduction | `Symmetry.lean:142` proves diagonal attainment for any cardinality-dependent multiaffine polynomial, by compactness, a strict chord improvement and a second maximization. |
| Canonical curve and disk | `Curve.lean:39` computes the contact, line 47 the tangent, and line 70 the derivative of squared distance. `HalfTurn.lean:22`, `Estimates.lean:144` and `Disk.lean:101` establish the universal disk inequality for $n\ge4$. |
| Residue classes, both semicircles | `Diagonal.lean:190` proves the torus bound for even $n\ge4$. Line 216 proves contact at the published angle. Complex conjugation covers the other semicircle. |
| Two parties | `Two.lean:52` gives an independent exact torus proof. The squared diagonal distance is $27/32-(\operatorname{Re}z+1/2)^2/4$. `Bipartite.lean:14` also contains the independent real-vector CHSH inequality. |
| Physical attainment | `GHZ.lean:71` builds the complex GHZ ket and orthonormal local measurement bases. Lines 99 and 120 give all Born probabilities and exact uniformity. `Tensor.lean` constructs the local matrix embeddings, and `Realization.lean:133` proves that the tensor amplitudes agree with the general Hilbert-space Born rule. |
| Maximum | `MABKCore.lean:43` identifies the two formulas for the threshold. Lines 49–63 prove the upper bounds, line 68 gives tensor attainment, and line 76 combines both halves in the same model. |

The Gelfand isometry is applied only after proving that the generated closed algebra is unital, abelian and complete. The compactness argument takes two maxima on compact sets and proves strict improvement when the secondary endpoints differ. The interval integral lemmas are used with continuous derivatives and oriented endpoints verified in the proof. No phase-mixture representation of an arbitrary quantum behavior is assumed.

## Alternative analytic derivation used in Lean

For the central interval, parameterize the tangent angle by $v=\pi/4+(n+1)x-\beta$, where $\beta$ is an arbitrary support direction. Put $\rho(v)=nR(x)/(n+1)$ and let $g(v)$ be the projection of $C(x)-t$ on that direction. The formal estimates give $0\le R(x)\le1$ and $n/(n+1)\le r$, so $g'=-\rho\sin v$ with $0\le\rho\le r$. Set $q=g-r\cos(v)/2$. For $a\le b\le a+\pi$,

$$|q(b)-q(a)|\le (r/2)\int_a^b|\sin v|\,dv,\qquad
\int_b^{a+\pi}|\sin v|\,dv\ge\cos a+\cos b.$$

The complete half-turn integral is 2. Consequently $g\le r$ at either endpoint if the other has the tangent value $r\cos v$. The contact $x=d$ and any $|x|\le3d$ differ in tangent angle by at most $\pi$. Applying the result to every $\beta$ proves the disk inclusion there.

On the outer interval the proof bounds $\cos^n(3d)\le1-3nd^2$ by a secant bound and Bernoulli's inequality. It uses the monotonicity of $\cos^n y+\sin^n y$ on $[0,\pi/4]$ and the explicit bounds on $|t|$ and $r$. These inequalities suffice for a strict outer margin. The independent mathematical report checks the submitted six-interval derivative proof and its original constants separately.

## Verification

The submitted 246-line entry point built on the pinned toolchain with one style warning. It contained helper proofs and two unproved predicates. The completed project retains its definitions and derives the two disk claims, the upper bound and physical attainment. The finite-phase-mixture helper is outside the dependency chain of the final theorem.

The final build uses Lean 4.19.0 (commit `6caaee842e94`) and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The independent scripts, version pins and compiler outputs are included. [Build](../results/lake-build.log) · [Entry-point check](../results/lean-entry.log) · [Axiom inspection](../results/kernel-audit.log) · [Project kernel replay](../results/kernel-replay.log)

The clean build compiled all 15 project modules without warnings. A fresh check of the entry point exited successfully. `#print axioms MABK.conjecture1` returned exactly `[propext, Classical.choice, Quot.sound]`. An executable guard also checked equality against this three-element set. The source audit found no `sorry`, `admit`, `native_decide` or project axiom declarations. [Axiom inspection](../results/kernel-audit.log) · [Source audit](../results/source-audit.log)

Two runs resubmitted proof terms to the pinned Lean kernel. The first checked all 337 logical declarations in the project and listed 86 compiler-generated staging or specialization helpers outside the logic. The second started with only `Init` imported and checked the final theorem's 39,705 dependencies and declarations, drawn from 1,422 modules above `Init`. It rejects any additional axiom in that closure. Both runs used Lean's own kernel. [Project replay](../results/kernel-replay.log) · [Dependency replay](../results/dependency-replay.log)
