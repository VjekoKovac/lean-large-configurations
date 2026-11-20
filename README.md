# Near-optimal density theorems for large dilates of large point configurations

Lean 4 proofs of Theorems 1, 2, and 3 of Vjekoslav Kovač and Adian Anibal Santos Sepčić. The original mathematical source and the formalization have the same two authors. Codex AI agents prepared the Lean proofs, explanatory files, and labeled AI reviews. [Original paper, arXiv:2604.18544v1](https://arxiv.org/abs/2604.18544v1)

| Source | Declaration in [Solution.lean](Solution.lean) | Conclusion |
|---|---|---|
| Theorem 1 | `Density.euclidean` | A Euclidean collinear n-point obstruction of actual density at least 1 − C log(n)/n, with absolute C. |
| Theorem 2 | `Density.integerLp` | For each integer p ≥ 2, a collinear obstruction with the lower-density bound. For even p the constant is independent of dimension and the actual density exists. |
| Theorem 3 | `Density.nonEuclideanLp` | For real p > 1, p ≠ 2, and every n ≥ 2d+1, an n-point obstruction with actual density exactly 1 − 1/(n−2d+2). |

In each row d ≥ 1, the measurable set and pattern are fixed along one sequence of positive forbidden scales tending to infinity. A forbidden copy means any pairwise distance-preserving labeling after rescaling. All three declarations are proved unconditionally in the project. Source-build Lean Comparator and a second comparison of separately created exports both passed. Lean, NanoDa, and con-ron accepted the proofs. [Verification transcripts](docs/verification.md)

## Read and check the mathematics

* [Challenge.lean](Challenge.lean) states the comparison targets, using only Mathlib imports. Its three specification proofs use `sorry` so that the statements can be reviewed independently. [Solution.lean](Solution.lean) imports the proof development and supplies all three proofs. Lean checks the two roots separately.
* [Proof map](docs/proof-map.md) gives the hypotheses, quantifier order, constants, domains, construction, and proof dependencies. [Fourier estimates](docs/fourier-proof.md) explains the change to the paper's Section 3. The project proves a short-shift Weyl bound and a finite Fejér-kernel counting estimate with a larger auxiliary prime. These give the same logarithmic density bound and permit the paper's exact-cardinality thinning argument.
* [Mathlib attribution](docs/mathlib-attribution.md) identifies reused Lean declarations. [Statement review](docs/independent-review.md), [proof audit](docs/proof-audit.md), and [independent final review](docs/fresh-review.md) distinguish AI mathematical review from kernel checking.
* [Verification record](docs/verification.md) gives the commands, versions, logs, axiom reports, trust restrictions, and limits of the local run. [formalization.yaml](formalization.yaml) records provenance and authorship.


The supplied repository source uses the Apache License 2.0. The paper and imported projects retain their own licenses.
