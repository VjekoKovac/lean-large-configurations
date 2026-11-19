# Near-optimal density theorems for large dilates of large point configurations

Lean 4 proofs of Theorems 1, 2, and 3 of Vjekoslav Kovač and Adian Anibal Santos Sepčić. The original mathematical source and the formalization have the same two authors. Codex AI agents prepared the Lean proofs, explanatory files, and labeled AI reviews. [Original paper, arXiv:2604.18544v1](https://arxiv.org/abs/2604.18544v1)

| Source | Declaration in [Solution.lean](Solution.lean) | Conclusion |
|---|---|---|
| Theorem 1 | `Density.euclidean` | A Euclidean collinear n-point obstruction of actual density at least 1 − C log(n)/n, with absolute C. |
| Theorem 2 | `Density.integerLp` | For each integer p ≥ 2, a collinear obstruction with the lower-density bound. For even p the constant is independent of dimension and the actual density exists. |
| Theorem 3 | `Density.nonEuclideanLp` | For real p > 1, p ≠ 2, and every n ≥ 2d+1, an n-point obstruction with actual density exactly 1 − 1/(n−2d+2). |

In each row d ≥ 1, the measurable set and pattern are fixed along one sequence of positive forbidden scales tending to infinity. A forbidden copy means any pairwise distance-preserving labeling after rescaling. All three declarations are proved unconditionally in the project. Source-build Lean Comparator and a second comparison of separately created exports both passed. Lean, NanoDa, and con-ron accepted the proofs. [Verification transcripts](docs/verification.md)

## First session

Install the official Lean 4 extension in VS Code and follow its setup prompt. Extract the archive, choose **File → Open Folder**, and select the directory containing `lean-toolchain`. Opening that folder lets Lean select the project's pinned version. In the integrated terminal run the following commands. The first fetch can take several minutes and uses several GiB of disk. [Official Lean installation](https://lean-lang.org/install/)

```sh
lake exe cache get
lake build
lake env lean AxiomReport.lean
```

Open [Solution.lean](Solution.lean). Place the cursor on `Density.integerLp` (inside the namespace it appears as `integerLp`) and use **Go to Definition** on `integerLp_of_hitting` to follow the deduction. The proof of `euclidean` is a good first exercise: it specializes the dimension-uniform even case to 2. The guided session also works through the exact threshold for an eight-point planar pattern. [First Lean session](docs/first-lean-session.md)

## Read and check the mathematics

* [Challenge.lean](Challenge.lean) states the comparison targets, using only Mathlib imports. Its three specification proofs use `sorry` so that the statements can be reviewed independently. [Solution.lean](Solution.lean) imports the proof development and supplies all three proofs. Lean checks the two roots separately.
* [Proof map](docs/proof-map.md) gives the hypotheses, quantifier order, constants, domains, construction, and proof dependencies. [Fourier estimates](docs/fourier-proof.md) explains the change to the paper's Section 3. The project proves a short-shift Weyl bound and a finite Fejér-kernel counting estimate with a larger auxiliary prime. These give the same logarithmic density bound and permit the paper's exact-cardinality thinning argument.
* [Mathlib attribution](docs/mathlib-attribution.md) identifies reused Lean declarations. [Statement review](docs/independent-review.md), [proof audit](docs/proof-audit.md), and [independent final review](docs/fresh-review.md) distinguish AI mathematical review from kernel checking.
* [Verification record](docs/verification.md) gives the commands, versions, logs, axiom reports, trust restrictions, and limits of the local run. [formalization.yaml](formalization.yaml) records provenance and authorship.

## GitHub and Palomar

1. Create an empty **public** GitHub repository, for example `lean-density-large-configurations`. Leave GitHub's initial README, license, and gitignore unchecked because this folder already contains those files.
2. In this folder run the commands below. Replace `YOUR-ACCOUNT` and the repository name with the repository you created. If Git requests an author identity, use your own name and the email address you want attached to your Git commits. The mathematical authorship is already recorded in the metadata.

   ```sh
   git init -b main
   git add .
   git commit -m "Formalize three density theorems for large configurations"
   git remote add origin https://github.com/YOUR-ACCOUNT/lean-density-large-configurations.git
   git push -u origin main
   git rev-parse HEAD
   ```

3. Open the repository's **Actions** tab and check the verification workflow for that commit. Its Comparator job uses the standard source-build sandbox. The full three-theorem configuration is [comparator.json](comparator.json). On a Linux machine with bubblewrap the same job can be run with `bash scripts/verify-comparator.sh`.
4. Read the Challenge and metadata under both authors' names. At the Palomar submission page, enter the public `owner/repository`, the full 40-character output of `git rev-parse HEAD`, and `comparator.json`. The authors can record any human review or endorsements they have actually made. If any file changes before submission, commit the change, recheck the new commit, and use its SHA. [Submission instructions](https://palomar-registry.org/how-to-submit) · [Submission form](https://submit.palomar-registry.org/)

The organization follows the DFR project and the Palomar starter repository. DFR’s version-1 registry record illustrates how Palomar connects a theorem to a specific Git commit. [DFR repository](https://github.com/roos-j/lean-dfr) · [DFR registry entry](https://palomar-registry.org/entry?id=PALOMAR-2026-10-21-000004&version=1) · [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate)

The supplied repository source uses the Apache License 2.0. The paper and imported projects retain their own licenses.
