# Sources for the independent review

The target is Conjecture 1 of Wooltorton, Brown and Colbeck, *Expanding bipartite Bell inequalities for maximum multi-partite randomness*. The review uses arXiv v3, dated 1 December 2025. Equation (1) sets the Bell normalization, Eqs. (24)–(27) define the candidate maximum, §4.3.1 states the conjecture, and Appendix C.4 compares attainable values to numerical upper bounds. The publisher issued the journal version on 5 December 2025. [arXiv v3](https://arxiv.org/abs/2308.07030v3) · [Versioned PDF](https://arxiv.org/pdf/2308.07030v3) · [Quantum 9, 1930](https://quantum-journal.org/papers/q-2025-12-05-1930/)

The inspected v3 PDF has SHA-256 `0951cd6ad94ac27dbacea13c630eb2a88cd70b4ff8bd20228c9542ff458dc07e`. The paper and the third-party repository can be obtained directly from the cited sources.

| Primary source | Role |
| --- | --- |
| [Wooltorton, Brown and Colbeck, bipartite analysis](https://arxiv.org/abs/2205.00124) | Exact two-party threshold |
| [Companion repository, revision c4b3271](https://github.com/LewisWooltorton/expanding-BI/tree/c4b3271bfe9d920c383667ef6c7b80ad4188f3e4) | Numerical SDP accompanying Appendix C.4 |
| [Werner and Wolf](https://arxiv.org/abs/quant-ph/0102024) | Full-correlation phase optimization with two dichotomic settings per party |
| [Borcea, Brändén and Liggett, Theorem 4.6](https://arxiv.org/abs/0707.2340) | Grace–Walsh–Szegő coincidence theorem, which also gives the symmetric diagonal maximum with the maximum modulus theorem |
| [Pinned mathlib revision](https://github.com/leanprover-community/mathlib4/tree/c44e0c8ee63ca166450922a373c7409c5d26b00b) | Formal dependencies, including the Gelfand isometry, integral calculus and trigonometry |
| [Pinned Lean kernel replay code](https://github.com/leanprover/lean4/blob/v4.19.0/src/Lean/Replay.lean) | Independent replay of serialized project proof terms using the same Lean kernel |

The public search of scholarly sources and GitHub repositories, code, issues, pull requests and commits is documented with queries, candidate matches and limitations in the [independent review](../review/INDEPENDENT_REVIEW.md).
