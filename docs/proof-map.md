# From the paper to the Lean declarations

The source is Kovač and Santos Sepčić, [arXiv:2604.18544v1](https://arxiv.org/html/2604.18544v1). Sections 2 and 3 prove Theorem 2, whose last clause gives Theorem 1. Section 4 proves Theorem 3 independently. The unnumbered problems, Corollary 4, and the weaker estimate in Section 5 are outside the three targets.

## Reading the statements

For a dimension `d : ℕ`, a point is a function from `Fin d` to ℝ. Use the product of one-dimensional Lebesgue measures. The coordinate function type has a default sup metric, so the Challenge spells out the distance as the real number
`(∑ i, |x i - y i| ^ p) ^ (1 / p)` for finite real p > 1. Theorem 1 uses p = 2. The finite coordinate sum also makes sense in dimension one. Lebesgue measurability is `NullMeasurableSet E volume`, which includes the completion of the Borel measure.

For every positive real R use the closed centered cube of side R. Divide the volume of its intersection with E by Rᵈ. Actual density a means this ratio tends to a as the real side length tends to +∞. Lower density is the liminf of the same function. The cube has finite volume, which justifies the conversion from the extended nonnegative reals to ℝ. Neither definition takes a supremum over translations.

A configuration is a finite set P with exactly n distinct elements. Collinearity means all elements belong to a translate of the span of one nonzero real direction. For a forbidden scale r, a would-be copy is an injection from P into E satisfying all pairwise scaled distance equations. Such an injection is bijective onto its image. This quantification includes finite metric embeddings whether or not they extend to an isometry of the ambient space. The same E and P work along one full sequence of strictly positive, divergent, real scales. A sequence indexed from zero simply reindexes the tail used in print.

| Source | Parameters fixed before the witnesses | Density required | Geometry |
|---|---|---|---|
| Theorem 1 | One absolute C > 0, every integer d ≥ 1, all sufficiently large integers n | Actual density ≥ 1 − C log(n)/n | Collinear P, Euclidean distances |
| Theorem 2, first clause | Every integer d ≥ 1 and integer p ≥ 2, then C > 0 depending on d,p and all sufficiently large n | Lower density ≥ 1 − C log(n)/n | Collinear P, ℓᵖ distances |
| Theorem 2, even clause | Each even integer p ≥ 2, then one C > 0 for all d ≥ 1 and sufficiently large n | Actual density ≥ 1 − C log(n)/n | Collinear P, ℓᵖ distances |
| Theorem 3 | Every integer d ≥ 1, real p > 1 with p ≠ 2, and integer n ≥ 2d+1 | Actual density **equal** to 1 − 1/(n−2d+2) | An n-point P without a collinearity requirement, ℓᵖ distances |

All logarithms are natural. The threshold in the Euclidean and even clauses is chosen before d in Lean. The proof permits this strengthening because Proposition 5 and the requirement that its gap be smaller than 1 only involve p and n. In Theorem 3 the denominator uses real subtraction. At the endpoint n = 2d + 1 it equals 3. In dimension one it equals n.

## Proposition 5 and Theorems 1 and 2

The steps below give the argument in the paper. In Steps 1–3 the Lean development proves the specialized cancellation and short-arc estimates at a larger polynomial sample size. The separate [Fourier proof guide](fourier-proof.md) gives the exact Lean parameters and inequalities.

1. Fix an integer p ≥ 2. Seek Kₚ > 0, depending only on p. For sufficiently large n, put ε = Kₚ log(n)/n with 0 < ε < 1. Choose a prime Q strictly between n^(2^p) and 2n^(2^p), and set A = 1/Q. Write xₖ(B) = A kᵖ + ∑ᵢ Bᵢ kⁱ modulo 1 for 1 ≤ i < p and 0 ≤ k < Q. The lower coefficients are arbitrary reals.
2. For each 1 ≤ m < Q, m/Q is reduced. With length Q and η = 2^(−p), Vaughan's Weyl bound gives |∑ₖ exp(2πim xₖ)| ≤ cₚ Q^(1−2^(−p)), uniformly in B and m. The Erdős–Turán inequality with cutoff Q−1 and the harmonic sum bound turn this into discrepancy ≤ c′ₚ log(n)/n. Choose Kₚ so this is ≤ ε/10. Every arc of length 9ε/10 then contains at least 4εQ/5 of the indices, counted with multiplicity of phases.
3. Discretize coefficient i with mesh ≤ ε/(100pQⁱ). There are Oₚ(Q^(p(p−1)/2)/ε^(p−1)) coefficient vectors and O(1/ε) candidate short arcs. Sample exactly n indices without replacement. A set of L good indices is missed with probability binom(Q−L,n)/binom(Q,n) ≤ (1−L/Q)ⁿ. Sum the bad-event bounds. It suffices to choose Kₚ so large that 4Kₚ/5 exceeds p(p−1)2^(p−1)+p as well as the discrepancy requirement. Constants in the grid estimates are absorbed by increasing the threshold for n.
4. The resulting one n-element set P hits every candidate pair. Rounding the lower coefficients changes the phase by at most ε/100 modulo 1 for each k ∈ P. Every arc of length ε contains a short grid arc with enough room for that error; this also treats arcs crossing the origin. The same P therefore works simultaneously for all coefficients and arc locations. The published Proposition 5 includes p = 1. Only its p ≥ 2 part is needed here. The uploaded revision states this restricted range.
5. Embed the integer pattern on the first coordinate axis. For even p set F(x) = ∑ᵢ xᵢᵖ and take the points for which F(x) is at distance < (1−ε)/2 from ℤ. For odd p use all 2ᵈ functions Fσ(x) = ∑ᵢ σᵢ xᵢᵖ, with σᵢ = ±1, and intersect the corresponding sets. These are measurable. Lemma 6 gives the length (1−ε)R + Oₚ(1) on any first-coordinate slice, uniformly in the offset from the remaining coordinates. Integration gives actual density 1−ε in the even case. A union bound on the complements gives lower density ≥ 1−2ᵈ ε in the odd case.
6. Make rⱼ = (A+j)^(1/p) positive by discarding finitely many j. It diverges. By strict convexity (Lemma 7), any pairwise scaled copy on this axis would have labels x+rⱼ k v with ℓᵖ-unit direction v. Expand F or Fσ along that line. For odd p choose σᵢ from the sign of vᵢ. The coefficient of kᵖ is A+j. The other nonconstant terms give admissible lower coefficients. Subtract the constant term and the integer j kᵖ. Containment in the chosen set leaves an omitted arc of length ε, contradicting Step 4.
7. The even clause is independent of d with C = Kₚ. For odd p use C = 2ᵈKₚ. Specializing the even clause to p = 2 gives all the witnesses and the absolute constant for Theorem 1.

## Theorem 3

Put m = n−2d+2, so m ≥ 3, and ε = 1/m. Take m consecutive axial points k e₁, −1 ≤ k ≤ n−2d, and the remaining pairs ±eᵢ, 2 ≤ i ≤ d. The pieces are disjoint and give m+2(d−1)=n points. Take E to be the set where the fractional part of ∑ᵢ xᵢ is less than 1−ε. This implements the half-open interval [0,1−ε). Each slice over the first coordinate is 1-periodic. Over an integer side length N its length is exactly N(1−ε), uniformly in the shift. Fubini then gives the exact cube volume (1−ε)Nᵈ. Trapping a real side R between ⌊R⌋ and ⌊R⌋+1 gives the same density limit. This gives the boundary estimate of Section 4.

At rⱼ = j+ε, the axial points of a proposed copy lie on one line by Lemma 7. Normalize their direction and the directions from the center to the other positive endpoints. Opposite endpoints give opposite directions by strict convexity. Every pair of distinct model axes has both p-th powers of the sum and difference norms equal to 2. Lemma 8 implies the normalized images have disjoint supports. Its scalar proof applies strict convexity or strict concavity of the power p/2 to (a+b)² and (a−b)². The sign of every coordinate defect is the same, so equality in the sum forces equality in each coordinate, hence ab = 0. There are d nonempty disjoint supports in d coordinates. All are singletons, and each unit vector is a signed coordinate vector. This conclusion is about the finite configuration and does not assume an extension theorem for ambient isometries.

The fractional parts for the axial block are now a translate of the m equally spaced residues modulo 1, in either order. One lies in [1−1/m,1), including its left endpoint if the boundary aligns. This contradicts containment. The case d=1 needs no auxiliary perpendicular directions. Section 5 of the paper gives a different, weaker logarithm-free construction of order n^(−1/2) and is not used in this deduction.

## References used in the mathematical proof

* Kovač and Santos Sepčić, arXiv:2604.18544v1, §§2–4 and Appendix A. [Paper](https://arxiv.org/abs/2604.18544v1)
* L. Kuipers and H. Niederreiter, *Uniform Distribution of Sequences*, Chapter 2, Theorem 2.5 (Erdős–Turán).
* R. C. Vaughan, *The Hardy–Littlewood Method*, second edition, Lemma 2.4 (Weyl's inequality).
* J. A. Clarkson, *Uniformly convex spaces* (1936), and the self-contained scalar argument in Lemma 8 of the source.

The mathematical account here is a blueprint. The verification report identifies the portion that Lean actually checked.
