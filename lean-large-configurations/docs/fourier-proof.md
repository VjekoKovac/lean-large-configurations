# The Fourier estimates in the proof of Proposition 5

Section 3 of the paper estimates polynomial exponential sums, obtains enough points in every short arc, and thins the original set of indices. The formalization proves the two estimates at the frequencies and arc lengths needed for thinning. The prime denominator can grow by a larger power of the pattern size because the final constant may depend on the degree. [Source, §3](https://arxiv.org/abs/2604.18544v1)

## Cancellation at one denominator

Fix the integer degree $p\ge2$, and write $e(t)=\exp(2\pi i t)$. For large integers $n$, set $M=n^4$ and $T=n^6$. There are an exponent $s=s(p)$, a shift bound $H$, and a prime $Q$ with

$$
n\le Q\le n^s,\qquad (16T)^{2^p}\le H,\qquad 4H^2\le Q,\qquad M p! H^{p-1}<Q.
$$

The exponent $s$ is independent of $n$. The prime and the leading coefficient $1/Q$ are chosen before all lower coefficients. For every real polynomial
$f(t)=t^p/Q+\sum_{i=1}^{p-1} B_i t^i$ and every $1\le h\le M$, the formal estimate is

$$
\left|\sum_{k=0}^{Q-1}e(h f(k))\right|\le Q/T.
$$

The induction takes two shifts $0\le i,j<H$ with $i\ne j$. For a degree $d$ polynomial with leading coefficient $a/Q$, its difference at those shifts has leading coefficient $ad(i-j)/Q$. Each differencing step keeps the new numerator nonzero. At degree one, the numerator has absolute value less than $Q$. Character orthogonality for the prime denominator makes the linear-phase sum exactly zero, including an arbitrary constant phase. At every earlier step, uniform bounds $Q\eta$ for the off-diagonal correlations give a normalized bound
$2H/Q+\sqrt{1/H+\eta}$.
For target accuracy $1/T_0$, the induction asks for $\eta=1/(16T_0^2)$ from the next degree. The hypotheses $H\ge16T_0^2$ and $Q\ge4H^2$ make the resulting bound at most $1/T_0$. [Van der Corput inequality](../Density/VanDerCorput.lean) · [Degree and coefficient identities](../Density/WeylShift.lean) · [Induction](../Density/Weyl.lean) · [Parameter choices](../Density/WeylParameters.lean) · [Uniform sample estimate](../Density/WeylSamples.lean)

## Counting points in a short arc

For $M\ge1$ put

$$
K_M(t)=\frac1{M^2}\left|\sum_{h=0}^{M-1}e(ht)\right|^2.
$$

For any $Q$ real points $X_0,\ldots,X_{Q-1}$, assume
$\left|\sum_{k<Q}e(hX_k)\right|\le Q\delta$ for $1\le h<M$. Expanding the square gives the following estimate and identity.

$$
\left|\sum_{k<Q} K_M(X_k-c)-\frac QM\right|\le Q\delta,\qquad
\sum_{j<M} K_M(x-c-j/M)=1.
$$

The second formula follows by applying the first with $X_j=j/M$ and $\delta=0$. If $x$ lies outside a test arc and $c$ is at distance at least $b>0$ from both of its endpoints inside that arc, the geometric-sum formula gives $K_M(x-c)\le1/(M^2 b^2)$. The proof estimates the chord of the unit circle by the distance to the nearest integer, which also handles arcs crossing zero. [Squared sums and exact partition](../Density/Fejer.lean) · [Tail bound](../Density/FejerTail.lean)

Take $0<\varepsilon\le1$, $M\varepsilon^3\ge10^6$, and $M\delta\le\varepsilon/100$. In an arc starting at $u$ of length $9\varepsilon/10$, choose

$$
c_j=u+\varepsilon/50+j/M,\qquad
0\le j<L=\left\lfloor M(9\varepsilon/10-2\varepsilon/50)\right\rfloor.
$$

The sum of these $L$ weights is at most one for a point in the arc and at most $\varepsilon/100$ for a point outside. Summing over the $Q$ points, then in the opposite order over centers, gives at least $(4\varepsilon/5)Q$ points in the arc. The interval is half-open. The count is over indices, so repeated phase values contribute with their multiplicity. [Short-arc count](../Density/FejerCount.lean)

## Why the logarithmic gap survives

The lower-coefficient grids have resolutions $1/(n^2Q^i)$ for $1\le i<p$. The arc origins have resolution $1/n^2$. Their total number of combinations is at most $n^a$, with $a=2+\sum_{i=1}^{p-1}(2+si)$. For $\varepsilon=L_0\log(n)/n$, where $L_0=10(a+1)$, the union bound for the event that an $n$-element sample misses one grid target is at most $n^a\exp(-4n\varepsilon/5)<1$. The sampling proof counts subsets using binomial coefficients. It gives exactly $n$ distinct indices.

For large $n$ one has $1/n\le\varepsilon\le1$, $n^4\varepsilon^3\ge10^6$, and $n^4/n^6\le\varepsilon/100$. A grid hit persists when the lower coefficients and the arc origin are moved off their grids. Applying this conclusion to the half-open interval with origin $u+\varepsilon/2$ places the hit strictly inside the interval $(u,u+2\varepsilon)$ modulo one. Thus $K_p=2L_0$ is admissible in Proposition 5. Section 2 uses $C_p=K_p$ for even $p$, and $C_{d,p}=2^dK_p$ for odd $p$. [Thinning and coefficient grids](../Density/Polynomial.lean) · [Final constant and endpoint adjustment](../Density/Hitting.lean) · [Density theorems](../Density/IntegerLp.lean)

## Reused Lean proofs

| Step | Mathlib declaration used |
|---|---|
| Select a prime in a polynomial-size interval | `Nat.exists_prime_lt_and_le_two_mul` |
| Bound the square of the finite sum | `sq_sum_le_card_mul_sum_sq` |
| Compute the translated coefficients | `Polynomial.taylor_coeff`, `Polynomial.hasseDeriv_coeff` |
| Identify primitive roots and sum the geometric progression | `Complex.isPrimitiveRoot_exp_of_isCoprime`, `IsPrimitiveRoot.geom_sum_eq_zero` |
| Prove orthogonality on the full Fejér mesh for arbitrary mesh size | `Complex.isPrimitiveRoot_exp`, `IsPrimitiveRoot.pow_eq_one_iff_dvd` |
| Bound the unit-circle chord length | `Real.mul_abs_le_abs_sin`, `Complex.norm_exp_I_mul_ofReal_sub_one` |
| Count subsets of a given size | `Finset.card_powersetCard`, `Nat.choose_succ_right_eq` |

These declarations come from the mathlib revision pinned by [the project manifest](../lake-manifest.json).
