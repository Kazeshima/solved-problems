# Nonconvexity of the product belief-propagation image for the antiferromagnetic Potts model

**Kazeshima · 25 November 2026**

[Read the short note (PDF)](output/pdf/paper.pdf) · [LaTeX source](paper.tex)

In the four-colour model with two independent neighbours and diagonal interaction $\beta=1/2$, the product image contains $(1,1,2,2)/6$ and $(3,3,2,4)/12$. Their midpoint $(5,5,6,8)/24$ is unattainable. More generally, the image is nonconvex for all $d\ge2$, $q\ge d+2$ and $0\le\beta<1$, including proper colourings. Here each neighbour has its own arbitrary real probability vector on the closed simplex.

Kuikui Liu, Nitya Mani and Francisco Pernice posed the question in Section 4 of their preprint. Nitya Mani also posed it in her thesis. Their use of an extremal coordinate in Lemma 2.2 and Remark 3 is the methodological precedent. For the standard antiferromagnetic interaction, equality at the upper bound for one coordinate forces the neighbours' supports to be pairwise disjoint. The note uses that rigidity to exhibit missing convex combinations. The public literature search through 25 November 2026 did not identify an earlier equivalent solution. The result addresses the geometry of the BP image. [Question 4](https://arxiv.org/pdf/2411.06541v2#page=12) · [Definition 2](https://arxiv.org/pdf/2411.06541v2#page=5) · [Method in the original paper](https://arxiv.org/pdf/2411.06541v2#page=7) · [Thesis, Question 3.9.18, p. 163](https://dspace.mit.edu/handle/1721.1/159909) · [Catalog entry Q4813](https://github.com/10m-u/open-problems-catalog/blob/main/problems/mathematics/probability-stochastic-processes-part-3.md#q4813)

## Formal verification

| Component | Checked result |
| --- | --- |
| [Four-state example](PottsBP.lean) | Both endpoint memberships, midpoint nonattainment and nonconvexity over the reals |
| [Finite-expectation model](PottsBPSource.lean) | Equivalence of the paper's finite expectation and the product formula, positivity of the normalization on the admissible range, and `source_question4_false` |
| [Main theorem](PottsBPGeneral.lean) | `PottsBP.source_nonconvex_general` for the full stated parameter range |
| [Axiom audit](results/axioms.log) and [kernel replay](results/kernel-replay.log) | The final theorems use only `propext`, `Classical.choice` and `Quot.sound`. Replay checks 9,609 dependency declarations above Lean `Init`. |

From this directory, use Lean 4.19.0 and the supplied [Lake manifest](lake-manifest.json), which pins Mathlib v4.19.0. The Python program provides an additional exact rational and symbolic check of the four-colour witness.

```sh
python -m pip install -r requirements.txt
python verify.py
lake exe cache get
lake build
lake env lean --trust=0 Audit.lean
lake env lean Replay.lean
```

To typeset the note, run `tectonic --outdir output/pdf paper.tex`. Generative AI assisted with writing and formalization.
