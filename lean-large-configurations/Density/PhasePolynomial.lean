module

public import Density.Polynomial
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # The real polynomial at a Fourier frequency

The lower-order tuple used for thinning supplies coefficients of degrees
1 through p−1. Multiplying the phase by m gives the leading coefficient m/Q.
-/

public section

open scoped BigOperators Polynomial
open _root_.Polynomial

namespace Density.Polynomial

/-- A polynomial in the coordinates used in the Weyl differencing argument.
No coprimality or frequency size assumption is needed for this identity. -/
theorem exists_frequencyPolynomial {p : ℕ} (hp : 1 ≤ p) (m Q : ℕ)
    (B : Fin (p-1) → ℝ) :
    ∃ f : ℝ[X], f.natDegree ≤ p ∧ f.coeff p = (m : ℝ)/Q ∧
      ∀ k : ℕ, f.eval (k : ℝ) = (m : ℝ) * phase p (1/(Q:ℝ)) B k := by
  let lower := fun i : Fin (p-1) =>
    monomial (i.val+1) ((m : ℝ)*B i)
  let lead := monomial p ((m : ℝ)/Q)
  refine ⟨lead + ∑ i, lower i, ?_, ?_, ?_⟩
  · apply natDegree_add_le_of_degree_le
    · exact natDegree_monomial_le _
    · apply natDegree_sum_le_of_forall_le
      intro i _
      exact (natDegree_monomial_le _).trans (by have := i.isLt; omega)
  · change (monomial p ((m : ℝ)/Q) + ∑ i, lower i).coeff p = _
    rw [coeff_add, finsetSum_coeff]
    have hlow (i : Fin (p-1)) : (lower i).coeff p = 0 := by
      simp [lower, coeff_monomial, show i.val+1 ≠ p by have := i.isLt; omega]
    simp [hlow]
  · intro k
    simp [lead, lower, phase, eval_finsetSum, eval_monomial, Finset.mul_sum,
      mul_add, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]

end Density.Polynomial
