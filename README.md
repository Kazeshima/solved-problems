# Solved problems

A collection of mathematical problems with proofs, source references and reproducible verification.

| Problem | Conjecture credit | Result and verification |
| --- | --- | --- |
| [Even-party MABK randomness threshold](problems/mabk-uniform-randomness/) | Lewis Wooltorton, Peter Brown and Roger Colbeck posed Conjecture 1. [Original conjecture, §4.3.1](https://arxiv.org/html/2308.07030v3#S4.SS3.SSS1) · [Lewis Wooltorton’s original repository](https://github.com/LewisWooltorton/expanding-BI) | Proved for every even number of parties $N\ge 2$. [Lean theorem](problems/mabk-uniform-randomness/MABKCore.lean#L76) · [Kernel replay](problems/mabk-uniform-randomness/results/dependency-replay.log) |
| [Cheeger bound for Pareto-efficient vectors](problems/cheeger-pareto/) | jinni posed Conjecture B. [MathOverflow 506070](https://mathoverflow.net/questions/506070) · [Mathematics Stack Exchange 5118288](https://math.stackexchange.com/questions/5118288) | Connected ten-vertex counterexample with $h=4/3$ and $\rho=6<20/3$. [Proof](problems/cheeger-pareto/paper.tex) · [Lean](problems/cheeger-pareto/CheegerPareto.lean) |
