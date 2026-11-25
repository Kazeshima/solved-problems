# Complete convexity classification

This is a local extension of the published Potts note. The new result and the older note have separate manuscript files. The theorem classifies one normalized update over independent real closed-simplex marginals with strictly positive normalizer.

[Manuscript (PDF)](paper.pdf) · [LaTeX](paper.tex) · [Independent review](REVIEW_REPORT.md) · [Full mathematical argument](PROOF.md) · [Prior art](PRIOR_ART_AUDIT.md) · [Scientific assessment](SCIENTIFIC_ASSESSMENT.md)

## Theorem

For integers $q\ge2$, $d\ge1$ and $0\le\beta\le1$, the product BP image is nonconvex exactly when $q\ge4$, $d\ge2$, and either $0<\beta<1$ or $\beta=0$ and $d\le q-2$. At $\beta=0$ and $d\ge q-1$ the image equals $\Delta_q$.

The main result is `PottsBP.source_nonconvex_iff`. The theorem `PottsBP.paper_classification` displays all quantifiers, the Potts matrix entries, the independent configuration probability and the normalizing denominator explicitly. `source_nonconvex_iff_on_defined_outputs` restates it using the original source image with the zero vector removed. [Final Lean statements](../PottsClassification.lean) · [Actual output and axioms](results/classification-axioms.log)

## Reproduce the verification

Start in the parent directory `problems/potts-bp-nonconvexity/`. Install Lean/Elan, Git and Python 3, and put `lake` on the path. The project pins Lean and Mathlib v4.19.0. A first run needs internet access for the official pinned dependencies and their compiled cache.

```sh
python -m pip install -r classification/requirements.txt
lake exe cache get
python classification/verify_formal.py
python verify.py
python classification/check_geometry.py
```

The formal driver checks all nine Git dependency revisions, builds the project, runs both the original and classification source entry points, compares the reported transitive axioms against the standard allowlist and replays the target dependency closure through Lean's kernel above `Init`. It does not require a Git working tree for the research sources themselves. For individual commands:

```sh
lake build
lake env lean PottsClassification.lean
lake env lean --trust=0 ClassificationAudit.lean
lake env lean ClassificationReplay.lean
```

The computational script uses exact rational arithmetic, an independent determinant-based planar hull, SciPy Qhull, scalar root finding and a separate least-squares search. The random streams use fixed seeds 4813 and 40963. [Summary](results/computations.json) · [Raw sample archive](results/computational-samples.jsonl.gz). Each JSONL record begins with its experiment name. Signature records contain $(q,d,\beta,n,L)$; large-degree rational slacks are stored as a signed hexadecimal numerator and denominator. Ternary reconstruction records retain chosen vertex IDs, mixing coefficients, target, recovered row marginals and their actual output. Optimization records retain initial and final logits, residuals and solver status. The exact and floating hull vertex-index lists are retained together.

The bibliography scripts `search_literature.py` and `check_primary_sources.py` reproduce the direct public requests and versioned full-text checks. The recorded search results are dated snapshots; database contents and rankings can change. The second script needs `pypdf`. To compile the manuscript use `tectonic --outdir classification classification/paper.tex`. LuaLaTeX or XeLaTeX also support its Unicode math fonts.

## Proof modules

| Module | Role |
|---|---|
| [Basic](../PottsClassBasic.lean) | Positive-normalizer source image, equality to the normalized factored image, scalar bounds and degree padding |
| [Column](../PottsClassColumn.lean) | Integer-baseline column tangent and the exact value of an interior cell at equality |
| [Finite-temperature obstruction](../PottsClassHot.lean) | Three shifted signatures and the $2/3$ row obstruction in arbitrary degree |
| [Colouring limit](../PottsClassZero.lean) | Explicit star messages and an IVT for every target in the closed simplex |
| [Two colours](../PottsClassTwo.lean) | Affine paths and the interval of attainable first coordinates |
| [Supporting edges](../PottsClassEdges.lean) | Linear halfspace bounds, attainable single-row transitions, ratio crossing |
| [Ratio fibre](../PottsClassFiber.lean) | Geometric interpolation and row repair preserving the projective ratio |
| [Three colours](../PottsClassThree.lean) | Upper and lower edge heights, IVT filling, convexity |
| [Classification](../PottsClassification.lean) | Exhaustion of regimes, domain correction, compatibility and literal source restatement |

The complete tested logs are in [results](results/). [Build](results/classification-build.log) · [Axiom audit](results/classification-axioms.log) · [Kernel replay](results/classification-replay.log) · [Machine-readable acceptance receipt](results/formal-acceptance.json).

A clean source-only project rebuild, reusing the pinned third-party cache, independently reproduced the result. The audit lists 60 declarations, and the 24 replay roots cover all 57 new named theorems/lemmas and 13,036 declarations above Lean Init. [Clean build and audit logs](results/clean/) · [PDF layout and font checks](results/paper-qa.json)

The [SHA-256 manifest](VERIFIED.sha256) is relative to the parent project directory. Run `sha256sum -c classification/VERIFIED.sha256` there to check the delivered files.
