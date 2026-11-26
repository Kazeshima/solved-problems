# Five-qubit verification

The project build directory was absent at the start. The numbered finite checks and the final public library were built from source in that workspace. The pinned dependency cache was shared. The final independent replay accepted 57,402 declarations above Lean Init.

| Verification | Transcript |
|---|---|
| Fresh project build and shared mathematical core | [Log](claim-c-clean-build.txt) |
| All 42 matrix certificates | [Log](claim-c-clean-certificates.txt) |
| All second-level packed rows | [Log](claim-c-clean-census-blocks.txt) |
| Eighteen exact row membership theorems | [Log](claim-c-clean-census-cases.txt) |
| Comparison with the signed Pauli lines | [Log](claim-c-clean-case-geometry.txt) |
| Directed elliptic line validity and distinctness | [Log](claim-c-clean-tagged-lines.txt) |
| Signed symmetries on the elliptic catalogue | [Log](claim-c-clean-symmetries.txt) |
| Frame and orbit transfer | [Log](claim-c-clean-orbit-transfer.txt) |
| Hyperplane orbit words | [Log](claim-c-clean-hyperplane-orbits.txt) |
| Large completion word packets | [Log](claim-c-clean-large-orbit-packets.txt) |
| Dense completion rows and their corresponding witnesses | [Log](claim-c-clean-largest-row-alignments.txt) |
| Completion orbit words | [Log](claim-c-clean-completion-orbits.txt) |
| Per-case assembly and counts | [Log](claim-c-clean-census-closure.txt) |
| Hyperplane census assembly | [Log](claim-c-clean-hyperplane-closure.txt) |
| All 18 cases and the distinct completion count | [Log](claim-c-clean-classified-census.txt) |
| Elliptic reduction using the 42 profiles | [Log](claim-c-clean-elliptic-reduction.txt) |
| Unconditional theorem | [Log](claim-c-unconditional-build.txt) |
| Public library build | [Log](claim-c-final-build.txt) |
| Theorem signatures and axioms | [Log](claim-c-final-axioms.txt) |
| Full independent kernel replay | [Log](claim-c-final-replay.txt) |

[Checked Lean input hashes](../VERIFIED.sha256) · [Original input hashes](claim-c-input-digests.tsv) · [Compiler and dependency revisions](claim-c-environment.txt)

The replay also recorded the number of declarations and elapsed milliseconds for each project module. [Module-by-module replay](claim-c-replayed-modules.tsv) · [Project proof object and source hashes](claim-c-proof-objects.tsv)


The installed workspace cache passed the object-hash check, Lake's up-to-date check and a fresh import of the public endpoints. [Installed cache check](claim-c-installed-cache.txt)
