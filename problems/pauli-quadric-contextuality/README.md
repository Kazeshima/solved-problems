# Contextuality of real Pauli quadrics

For the hyperbolic Pauli quadric, the contextuality degree is the minimum number of signed three-point lines violated by an assignment of outcomes to the points. This Lean 4 project proves the four-qubit classification, the exact five-qubit degree, and the limit of the violated fraction as the rank grows. [Mathematical proof](PROOF_AUDITED.md) · [Theorem and axiom transcript](logs/claim-c-final-axioms.txt)

| Geometry | Lean result |
| --- | --- |
| Four qubits, $Q^+(7,2)$ | The degree is **315**. Every optimum lies in the canonical real Clifford orbit. There are **61,440** optimal assignments on the 135 quadric points and **240** distinct violated-line sets. Each optimum has an incidence isomorphism with $DW(5,2)$. [Classification](lean/Quadric/ClaimB.lean#L59) |
| Five qubits, $Q^+(9,2)$ | **`Quadric.Five.degree_five : Quadric.degree 5 = 6975`**. The mixed assignment violates 6,975 of the 23,715 lines. [Exact degree](lean/Quadric/Five/Exact.lean#L45) · [Witness](lean/Quadric/Five/Witness.lean#L90) |
| General rank | `Quadric.contextuality_bounds` bounds the minimum violated fraction, and `Quadric.contextuality_limit` proves that it tends to **1/2**. [Statements](lean/Quadric/Asymptotic.lean#L85) · [Note on the asymptotic bound](manuscript/note.pdf) |

## Proof and prior work

Zhengyu Li, Amandeep Gupta and Vijay Ganesh established the four-qubit degree and classification by computer-assisted methods. Open problem 3 in their revised manuscript asks for a conceptual explanation of the dual polar space. Here a rank-one real Pauli operator determines an optimal assignment. The integer amplitude patterns and their quadratic Walsh phases give the real Clifford orbit. A principal-minor map on Lagrangian planes identifies the violated lines with pencils, and the Clifford action transports the incidence isomorphism to every optimum. Muller, Saniga, Giorgetti, Holweck and Kelleher had observed the four-qubit geometry and five-qubit witness numerically. [Open problems in the authors’ manuscript](https://github.com/BrianLi009/four-qubit-hyperbolic-quadric/blob/44a37dbd55029eec23f8c15f071e263984635444/main.tex#L927-L932) · [Li, Gupta and Ganesh](https://arxiv.org/abs/2610.26465v1) · [Muller et al.](https://arxiv.org/abs/2407.02928)

Brent W. Jonah gave the exact five-qubit value, the section argument and the finite certificate data. The revised Li–Gupta–Ganesh manuscript also gives the value. In the Lean proof, 18,752 normalized hyperplane assignments reduce to 18 representative systems. The 34,224 normalized completions are connected by checked signed words to 42 certified profiles. The elliptic lower bound of 315 lifts to 1,575 on a four-qubit symplectic section and then to 6,975 on the five-qubit quadric. The factors are $120/24$ and $496/112$, respectively. [Original deposit and data credit](sources/README.md) · [Census count](lean/Quadric/Five/Resources/CensusCount.lean#L29) · [Signed orbit theorem](lean/Quadric/Five/Exact.lean#L30) · [Section transfer](lean/Quadric/Five/SectionChain.lean)

Jonah’s work also gives an equivalent spectral bound and announces the flat-state characterization and an enumeration-free route. The general-rank limit answers the limit part of revised open problem 4. Its adjacent-section equality question is separate. The matching-order construction in §8 of the proof note is a paper argument. [Structure theorems](https://doi.org/10.5281/zenodo.23538829) · [Results digest](https://doi.org/10.5281/zenodo.23518569) · [Proof note](PROOF_AUDITED.md)

## Verification

The recorded source-only build used Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. An independent replay reconstructed **57,402 declarations above Lean `Init`** for 37 named targets. The replay accepted `propext`, `Classical.choice` and `Quot.sound` as the axioms in those targets. The manifest covers all 488 proof, verifier and configuration inputs, including their original line endings. [Source hashes](VERIFIED.sha256) · [Build and replay index](logs/claim-c-verification.md) · [Full replay transcript](logs/claim-c-final-replay.txt)

From this directory in a fresh checkout with elan and Python 3.10 or later installed, run

```sh
sha256sum --check --quiet VERIFIED.sha256
sha256sum --check --quiet EVIDENCE.sha256
(cd lean && lake exe cache get)
python3 -B tests/verify_claim_c.py lean --require-clean --jobs 2
```

The driver builds local modules in bounded batches, prints the theorem signatures and axioms, and runs `Replay.lean` from `Init`. The checked Lean data are included in the repository. For the independent matrix and incidence calculation, run `python3 -B tests/check_quadric.py --output-dir /path/to/output`. Its complete state and configuration tables can be compared with the retained samples. [Four-qubit states](logs/four-states.tsv.gz) · [Violated-line sets](logs/four-configurations.json.gz) · [Independent check](tests/check_quadric.py)
