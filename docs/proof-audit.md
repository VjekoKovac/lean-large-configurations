# Independent AI review of selected proofs and their sources

An OpenAI Codex agent reviewed the modules listed below. Other agents wrote these proofs. The reviewer also implemented the build configuration, stripe-volume calculation, finite van der Corput estimate, and parameter bounds. The independent review here concerns the other agents' modules. No human review is claimed.

The comparison source was Kovač and Santos Sepčić, *Near-optimal density theorems for large dilates of large point configurations*, arXiv:2604.18544v1. The Introduction supplies the three public theorems. The discussion below concerns dependencies that could change their mathematical meaning. [Paper](https://arxiv.org/abs/2604.18544v1)

| Step reviewed | What the Lean argument checks |
| --- | --- |
| Appendix, collinear copies | `collinear_copy_coordinates` takes a finite real pattern and the scaled distance equations between every pair of its points. At its first and last labels equality in the triangle inequality gives a common ray. Dividing the endpoint chord by its positive length produces a unit direction, and subtracting the first parameter gives the origin of the affine parametrization. The proof treats empty and singleton patterns separately. |
| Section 4, rigidity for real exponents | `clarkson_eq_iff` treats both $1<p<2$ and $2<p$. The scalar inequality is strict when both coordinates are nonzero. The strict summands have a common sign for each fixed exponent, so equality forces disjoint coordinate supports. `unit_axes_of_cross` then uses the equality of the number of nonempty disjoint supports and the number of coordinates. The result gives signed coordinate axes for a finite distance-preserving labeling. |
| Section 4, counting and exclusion | For ambient dimension $d+1$, `crossPattern d m` has $m+2d$ points. The code maps a disjoint union of labels injectively into the coordinate space, which also handles $d=0$. `fullLp` obtains $m=n-2d$ from the actual lower bound $n\ge 2(d+1)+1$. The excluded scales are $j+1/m$. The complement of the stripe includes its left endpoint, and `grid_hits_last_cell` proves a weak inequality at that endpoint. |
| Section 3, thinning | `exists_hitting_of_sum_choose_lt` counts $n$-element subsets of a finite population. A union of misses of strictly smaller cardinality leaves an actual $n$-element subset. `thin_of_short_arc_count` transfers a uniform estimate on arcs of length $9\varepsilon/10$ to hitting half-open arcs of length $\varepsilon$. The final argument in `Hitting.lean` shifts the tested arc inside an open interval and doubles the constant $K$ to obtain strict interior hitting. Its grid sizes are integral and its conclusion quantifies over every real lower coefficient and every starting point of the arc. |
| Section 2, parity and dimension | `even_obstruction` and `odd_obstruction` take the same polynomial hitting property. In the odd case the set is intersected over all signs before the direction of a hypothetical embedding is known. `oddShell_lowerDensity` bounds the complement by the sum over those $2^d$ signs. In `integerLp_of_hitting`, the even-case constant and cutoff are chosen before the dimension. Its inputs include the entire polynomial hitting property. The declaration `euclidean_of_integerLp` specializes the even branch at $p=2$ and carries forward the same constant and cutoff. |

## Reused results

The reuse above consists of applications of named mathlib declarations. For example, `Polynomial.exists_prime_between` invokes `Nat.exists_prime_lt_and_le_two_mul` for Bertrand's postulate, and `exists_hitting_of_sum_choose_lt` invokes `Finset.card_powersetCard` and `Finset.card_biUnion_le`. The collinearity proof uses `sameRay_iff_norm_sub` and `SameRay.norm_smul_eq`. The Clarkson coordinate proof invokes `Real.strictConcaveOn_rpow` and `strictConvexOn_rpow` at exponent $p/2$, followed by the scalar power inequalities. These results are credited to their mathlib contributors. The pinned mathlib release is v4.35.0, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. [mathlib source tree at that revision](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib)

## Reproducing the dependency inspection

Run the following in a shell at the repository root after building `Density.FullLp` and `Density.IntegerLp`.

```sh
lake env lean --stdin <<'LEAN'
import Density.FullLp
import Density.IntegerLp
#print axioms Density.collinear_copy_coordinates
#print axioms Density.clarkson_eq_iff
#print axioms Density.unit_axes_of_cross
#print axioms Density.card_crossPattern
#print axioms Density.no_scaled_copy_cross
#print axioms Density.Polynomial.exists_hitting_of_sum_choose_lt
#print axioms Density.Polynomial.thin_of_short_arc_count
#print axioms Density.Annular.even_obstruction
#print axioms Density.Annular.odd_obstruction
#print axioms Density.Annular.hasDensity_shell
#print axioms Density.Annular.oddShell_lowerDensity
#print axioms Density.integerLp_of_hitting
#print axioms Density.euclidean_of_integerLp
LEAN
```

Lean 4.35.0 printed the following when checking these declarations. These reports cover the listed proof terms and their dependencies. The comparison evidence for the public statements is recorded separately in the verification logs.

```text
'Density.collinear_copy_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.clarkson_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.unit_axes_of_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.card_crossPattern' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.no_scaled_copy_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.Polynomial.exists_hitting_of_sum_choose_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.Polynomial.thin_of_short_arc_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.Annular.even_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.Annular.odd_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.Annular.hasDensity_shell' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.Annular.oddShell_lowerDensity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.integerLp_of_hitting' depends on axioms: [propext, Classical.choice, Quot.sound]
'Density.euclidean_of_integerLp' depends on axioms: [propext, Classical.choice, Quot.sound]
```
