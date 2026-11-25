# The MABK randomness threshold for an even number of parties

## Conjecture credit

**Lewis Wooltorton, Peter Brown and Roger Colbeck** posed Conjecture 1 in §4.3.1 of *Expanding bipartite Bell inequalities for maximum multi-partite randomness*. They exhibited a GHZ strategy with uniform joint output on the all-zero input and conjectured that its MABK score was the largest possible under that constraint. [Original paper and author list](https://arxiv.org/abs/2308.07030v3) · [Original conjecture, §4.3.1](https://arxiv.org/html/2308.07030v3#S4.SS3.SSS1) · [Lewis Wooltorton’s GitHub profile](https://github.com/LewisWooltorton) · [Original companion repository](https://github.com/LewisWooltorton/expanding-BI)

## Result

**Solved for every even $N\ge2$.** This entry proves the matching upper bound in the normalization of the authors’ Eq. (1). The case $N=2$ was known. [Earlier bipartite result](https://arxiv.org/abs/2205.00124)

Let $d=\pi/[4(N+1)]$. The maximum over all strategies with $p(a\mid\mathbf 0)=2^{-N}$ for every output string $a$ is

$$
m_N^*=2^{(N-1)/2}\left(\cos^{N+1}d+(-1)^{N/2+1}\sin^{N+1}d\right).
$$

The upper bound already holds when the all-zero full correlator vanishes. The formal proof bounds a shifted Bell operator by the maximum of a symmetric polynomial on the unit torus, reduces it to one phase and proves the resulting disk inequality. The finite-dimensional GHZ construction then attains equality, with each output string having the required probability. All four residue classes modulo eight give the angles in Eqs. (25)–(27). The formalization covers the paper's projective model in arbitrary Hilbert dimension. The manuscript also gives the local dilation for tensor-product binary POVMs. [Mathematical proof](proof/Proof.md) · [Formal argument](review/FORMALIZATION_STATUS.md)

```lean
theorem MABK.conjecture1 (n : ℕ) (hn : 2 ≤ n) (he : Even n) :
    IsGreatest (MABK.uniformValues n) (MABK.publishedMstar n)
```

Lean 4.19.0 reports exactly `propext`, `Classical.choice` and `Quot.sound` as the theorem's axioms. A separate run of Lean's kernel checked 39,705 declarations from 1,422 modules above `Init`. The project sources contain no proof placeholders or additional axioms. The mathematical review records a corrected interval condition, an independent two-party proof and the limits of the priority search. [Theorem and definitions](MABKCore.lean#L76) · [Axiom report](results/kernel-audit.log) · [Dependency replay](results/dependency-replay.log) · [Independent review](review/INDEPENDENT_REVIEW.md)

Lewis Wooltorton states the same problem as Conjecture 7.1 in §7.4, printed page 101 of his Bristol thesis. It imposes the same output probabilities and proposes the same maximum, so the proof resolves that formulation as well. The resolution was reported in the paper's companion repository, and GitHub Actions reproduced the build and both kernel replays on Ubuntu. [Thesis, Conjecture 7.1](https://research-information.bris.ac.uk/files/460797363/LW_PhD_thesis.pdf) · [Author-repository issue](https://github.com/LewisWooltorton/expanding-BI/issues/1) · [Successful public verification](https://github.com/Kazeshima/solved-problems/actions/runs/45641247041)

## Reproduce the result

With elan installed, run these commands from the repository root. The Lake manifest pins mathlib and its dependencies.

```sh
cd problems/mabk-uniform-randomness
sha256sum -c VERIFIED.sha256
lake exe cache get
lake build
lake env lean MABKCore.lean
lake env lean review/KernelAudit.lean
lake env lean --run review/KernelReplay.lean
lake env lean --run review/DependencyReplay.lean
```

The SHA-256 file covers all 15 mathematical source files and the three review programs. The last program independently rechecks the transitive proof terms and identifies the major stages used by the final theorem. [Verification workflow](../../.github/workflows/verify-mabk.yml)
