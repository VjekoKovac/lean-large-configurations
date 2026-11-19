# Verification record

All three formal theorems are unconditional. The source is arXiv:2604.18544v1, Introduction, Theorems 1–3. Verification took place on Linux on 19 November 2026.

## Pinned environment and clean build

| Component | Version or revision |
|---|---|
| Lean | 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Lake | `5.0.0-src+eb6cafb` from the same Lean release |
| Mathlib | v4.35.0, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| Comparator, default Lean kernel, NanoDa, con-ron | Binaries bundled in the pinned Lean toolchain |
| bubblewrap | 0.12.0 |

A fresh project directory contained copies of the final Lean sources, Lake configuration, manifest, and toolchain pin. It reused the pinned external dependency cache. Its own build directory started empty. The following commands compiled the project modules and printed the axioms of the three declarations from the solution. The Lake job total includes dependencies. [Full commands and output](checks/clean-build.txt)

```sh
lean --version
lake --version
lake build
lake env lean AxiomReport.lean
```

```text
Build completed successfully (3572 jobs).
'Density.euclidean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.integerLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.nonEuclideanLp' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The three `sorry` warnings come from the three declarations in the independent Challenge, following the Palomar specification convention. The Solution dependency closure excludes the Challenge. The proof files contain no `sorry`, custom axiom declarations, or native proof evaluation. The project uses proof-producing tactics including `norm_num`, `omega`, `ring`, `positivity`, and `linarith` to construct kernel-checkable terms. Examples include the Fejér inequalities with the constants 100 and 1,000,000, the recursive Weyl error budget, the cardinality of the cross, and the endpoint density calculation in the tutorial.

## Independent comparison

The checked-in `comparator.json` selects all three public names, compares `Challenge` against `Solution`, and permits exactly the three axioms printed above. All mathematical definitions in the Challenge have specified bodies. An AI reviewer who wrote none of the statements or proofs checked the public meanings against arXiv and the supplied manuscript. [Fresh review](fresh-review.md)

The primary source-mode run used the bundled `lake comparator` to build and export the two modules separately and compare them under the three-axiom policy. It returned **Your solution is okay!** after all three kernels accepted. On the preparation host, bubblewrap required two extra mount points and a pre-created offline network namespace. The host adapter retained Lake’s own build isolation. The unmodified default launch and its host-specific errors are recorded alongside the successful run. GitHub CI uses the ordinary command below. [Source-judgment transcript](checks/comparator-source.txt) · [Exact host command and isolation details](checks/source-environment.md)

```sh
bash scripts/verify-comparator.sh
```

A second, export-mode run built both modules, used the pinned `leanexport` to export the selected declarations, then ran the bundled `lake comparator` on those environments. A read-only external sandbox supplied the offline isolation for that run. Its transcript records the `--inadvisably-no-sandbox` option for Lake's inner sandbox. The only files passed to that judgment, other than system files and the pinned toolchain, were the exports and configuration. The following command reproduces this mode on a Linux host supporting the requisite user and network namespaces. [Script](../scripts/check-exports.sh) · [Actual transcript](checks/comparator-all.txt)

```sh
bash scripts/check-exports.sh all /tmp/density-lean-exports
```

The run compared the three configured names. Both independent kernels and Lean's default kernel accepted the solution under the configured axiom allowlist. Con-ron accepted 45,629 declarations in the replay. The proof and configuration input hashes allow the compared files to be checked after unpacking. [Hashes](checks/proof-inputs.sha256)

```sh
sha256sum -c docs/checks/proof-inputs.sha256
```

## Metadata and external status

The metadata was validated against the upstream v0.4 JSON schema. The record gives the revision and schema digest. This validates the file format. Palomar makes its own mechanical and editorial decisions on a public Git commit. [Schema check](checks/metadata.txt)

The two authors were supplied by the project owner. Human review and coauthor endorsement were not recorded in this session. The source paper's human authorship and its own AI disclosure are distinct from the role of AI in preparing these Lean files. Local verification covered the three introduction theorems. The project does not claim a formal proof of Corollary 4, Section 5, the p=1 case of the published Proposition 5, the general classical Erdős–Turán inequality, or Vaughan's full Weyl inequality. The local workflow produced no GitHub Actions run, public commit, or Palomar registration.
