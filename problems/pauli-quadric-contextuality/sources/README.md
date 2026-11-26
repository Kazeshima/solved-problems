# Certificate inputs and attribution

Brent W. Jonah’s *A section–square law for Pauli quadrics, and an independently regenerated proof that the four-qubit elliptic quadric has contextuality degree 315* supplies the 42 integer certificates, census instances, candidate lists and transporter words used here. The Zenodo record licenses its materials under **CC BY 4.0**. The generators translate those data into Lean declarations, reorder the witnesses to match the checked rows and supply integer Gram factors. Lean checks the data against the signed Pauli geometry and verifies the bounds. [Source record](https://doi.org/10.5281/zenodo.23510634) · [License](https://creativecommons.org/licenses/by/4.0/) · [Jonah’s five-qubit theorem](https://doi.org/10.5281/zenodo.23518323)

| Deposited file | Local filename for regeneration |
| --- | --- |
| [P1R_EVIDENCE_20261020.zip](https://zenodo.org/api/records/23510634/files/P1R_EVIDENCE_20261020.zip/content) | `jonah-evidence.zip` |
| [CPL_PROOF_LOG_20261020.zip](https://zenodo.org/api/records/23510634/files/CPL_PROOF_LOG_20261020.zip/content) | `jonah-proof.zip` |

To inspect or regenerate the proposed data, save both files in this directory under the local names and run the following from the problem directory. The input checker compares the archive hashes, the individual census entries against the deposited manifest, and the two copies of `L7R_CERTS_42.txt`. [Archive hashes](SHA256SUMS) · [Recorded input digests](../logs/claim-c-input-digests.tsv)

```sh
python3 -B tests/verify_claim_c_inputs.py
```

The recorded generators used Python 3.12.14 and NumPy 2.3.5. Floating-point arithmetic proposes Gram factors during generation. The checked inequality and all matrix identities are integral. The census proofs verify threshold comparisons with packed natural numbers. A full Lean build uses the committed declarations directly. [Gram factors](../tests/generate_claim_c_gram.py) · [Certificate soundness](../lean/Quadric/Five/Certificates.lean) · [Packed comparisons](../lean/Quadric/Five/OneBlock.lean)
