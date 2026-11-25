# Solved problems

A collection of mathematical problems with proofs, source references and reproducible verification.

| Problem | Conjecture credit | Result and verification |
| --- | --- | --- |
| [Product belief propagation for the antiferromagnetic Potts model](problems/potts-bp-nonconvexity/) | Kuikui Liu, Nitya Mani and Francisco Pernice posed [Question 4](https://arxiv.org/pdf/2411.06541v2#page=12). See also [Mani's thesis, Question 3.9.18](https://dspace.mit.edu/handle/1721.1/159909). | Nonconvex for every $d\ge2$, $q\ge d+2$ and $0\le\beta<1$. [Short note (PDF)](problems/potts-bp-nonconvexity/output/pdf/paper.pdf) · [Lean theorem](problems/potts-bp-nonconvexity/PottsBPGeneral.lean) |
| [Even-party MABK randomness threshold](problems/mabk-uniform-randomness/) | Lewis Wooltorton, Peter Brown and Roger Colbeck posed Conjecture 1. [Original conjecture, §4.3.1](https://arxiv.org/html/2308.07030v3#S4.SS3.SSS1) · [Lewis Wooltorton’s original repository](https://github.com/LewisWooltorton/expanding-BI) | Proved for every even number of parties $N\ge 2$. [Lean theorem](problems/mabk-uniform-randomness/MABKCore.lean#L76) · [Kernel replay](problems/mabk-uniform-randomness/results/dependency-replay.log) |
