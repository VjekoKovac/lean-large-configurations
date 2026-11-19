# Independent AI review

A Codex agent separate from the statement author compared the statements in `Challenge.lean` with the paper. This was a mathematical reading by an AI agent. A successful kernel or Comparator run is a different claim, and its status belongs in the verification report.

## Source comparison

The three theorem environments in the uploaded manuscript agree with the arXiv v1 source. There are two differences in auxiliary results. Proposition 5 starts at integer $p=1$ on arXiv and at $p=2$ in the upload. Only $p\ge 2$ is needed for Theorems 1–2. The elementary argument of Section 5 starts at $n=4$ on arXiv and at $n=9$ in the upload. That argument is outside the proof of the three targets. The uploaded manuscript also adds the range of the earlier Falconer–Kovač–Yavicoli bound and edits affiliations. [arXiv v1 source archive](https://arxiv.org/src/2604.18544v1)

| File | SHA-256 |
| --- | --- |
| `density_large_configurations.tex` in the arXiv v1 archive | `f7549361731f531e7f45894a5c2b56c62137c4e1b3bbd19d0ee30d4303dce0e6` |
| Uploaded `density_large_configurations.tex` | `792ae6dc87497ad6d69b975fe3753f277c2aa742aa06acde067c050a42225a38` |

The recorded Challenge SHA-256 after the cutoff review was `d3e35d9dbbf7ebc03ac0c6e3da76ff91c2492a6b73be158d0a295b29f220f837`. A text comparison found that its public definitions from `Point` through `FullLpStatement` matched those in `Density/Definitions.lean`.

## Statement checks

| Issue | Review finding |
| --- | --- |
| Underlying space | `Fin d → ℝ` uses product Lebesgue measure. `lpDistance` computes the finite-exponent distance from the coordinates, including the square-root-of-sum-of-squares formula at exponent two. |
| Measurability and density | `NullMeasurableSet E volume` allows all Lebesgue-measurable witnesses. Densities refer to cubes of side $R$ centered at the origin with no supremum over translates. The intersection is bounded for each finite positive $R$, so conversion of the measure to a real number is legitimate. Taking a real limit as $R\to+\infty$ ignores values at $R\le 0$. |
| Meaning of a copy | An injection from the pattern labels into $E$ gives a bijection onto its image. The equalities cover every pair. A proof that rules out only ambient translations or linear isometries would miss cases. |
| Pattern and scales | Exact cardinality, one fixed set and one fixed pattern, pointwise positivity of the scales, divergence to positive infinity, and exclusion at every index are all present. Indexing from zero reindexes the paper's sequence. |
| Theorem 1 | A single positive constant works in every positive dimension. The conclusion asks for an actual limit. The cutoff has also been moved outside the dimension quantifier. The proof obtains it from Proposition 5 with $p=2$ and the inequality $K_2\log n/n<1$, both independent of dimension. |
| Theorem 2 | The first part ranges over natural exponents at least two. It gives a lower limit and allows the constant to depend on $d,p$. For each even $p$, the second part uses a single constant and cutoff in all positive dimensions and asks for an actual limit for the constructed obstruction. |
| Theorem 3 | The exponent ranges over all real $p>1$ other than two, including nonintegers below two. The conclusion uses the exact limit $1-1/(n-2d+2)$ at every $n\ge 2d+1$. The subtractions are real. There is no collinearity condition. |

## Proof checks a reader can repeat

* The even-exponent proof and the odd-exponent proof need different density conclusions. The odd proof takes the intersection over all $2^d$ sign patterns before considering an embedding. The sign choice depending on the hypothetical direction then selects one of those constraints.
* In the proof of Proposition 5 the source proves the exponential sum estimate for all lower-order real coefficients and all $1\le m<Q$. Each discrepancy argument only uses frequencies up to its chosen cutoff. The prime denominator is what keeps $m/Q$ in lowest terms. A pointwise equidistribution theorem alone supplies neither the bound nor its uniformity. The thinning step also needs exactly $n$ distinct labels.
* The construction for Theorem 3 has $m=n-2d+2\ge 3$ consecutive labels on its first axis and $2(d-1)$ additional labels. For $d=1$ the second family is empty. The strict-convexity equality forces antipodal pairs after centering. The strict cases of the scalar Clarkson inequalities give disjoint supports between distinct axes. Counting $d$ nonempty, pairwise disjoint supports among $d$ coordinates forces signed coordinate directions.
* The stripe in Theorem 3 is half open. Its complementary half-open arc has length exactly $1/m$ and meets every translate of the equally spaced $m$-point grid, even when an endpoint is a grid point. Replacing the forbidden arc by an open arc would invalidate this endpoint argument.

The kernel reports for the three unconditional solution declarations appear in [main-axioms.txt](checks/main-axioms.txt).

## AI review of the slice estimates and the polynomial reduction

A second AI reviewer checked the arguments in `PowerSlices.lean`, `PowerBand.lean`, `SliceDensity.lean`, `ShellDensity.lean`, and `Hitting.lean` against the corresponding passages in arXiv v1. This reviewer wrote the public statement definitions and some of the geometric and Fejér lemmas. The separate statement review above was performed by another agent.

- **Centered cubes.** The change to first-coordinate slices uses the product measure-preserving equivalence and integrates over the remaining coordinates of the same cube. In dimension one the remaining space has a single point of mass one. The bound on each slice has absolute error at most 16 for all real translates. This gives error at most 16/R in the d-dimensional density ratio. In the one-dimensional argument the code controls each complete cell by adjacent secant slopes of the concave function t ↦ t^(1/p), which telescope. This replaces the mean-value estimate in the appendix. Countably many endpoints may be discarded when calculating measures. For the geometric exclusion, the allowed bands themselves stay open.
- **Odd p.** The set is fixed by intersecting all sign choices. The direction of a purported copy selects one signed constraint within this already fixed intersection. Summing the densities of the complements accounts for the factor 2ᵈ. The proof only needs the lower limit here.
- **Polynomial input.** For each degree, the same bandwidth, accuracy, sample size, and leading coefficient work for every vector of real lower coefficients. For thinning, the necessary quantitative conclusion is a lower bound of (4ε/5)Q samples in each arc of length 9ε/10. The finite Fourier estimates are sufficient for this step. After thinning, apply the half-open arc conclusion at u+ε/2 to obtain a point strictly inside the open interval (u,u+2ε). Doubling the constant preserves the claimed order. Translating the test interval absorbs the constant coefficient B₀. Mapping the finite sample from natural to integer indices preserves its exact cardinality.
- **Cutoff.** For the even case the cutoff comes from the polynomial input together with 0 < K log(n)/n < 1. Both depend only on p, so the dimension-uniform cutoff in the reviewed Challenge also follows from the printed construction. For d=1, Theorem 3 has denominator n. At n=2d+1 it has denominator 3.
