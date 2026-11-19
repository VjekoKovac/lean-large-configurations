module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic

/-! # The polynomial algebra and the base case of Weyl differencing

Two translates of the same polynomial have equal leading coefficients. Their
difference drops by one degree and has the indicated new leading coefficient.
At degree one, summation over the entire prime denominator gives exact
cancellation by the geometric-sum identity.
-/

public section

open scoped BigOperators ComplexConjugate
open Finset

namespace Density.Polynomial

private theorem coeff_taylor_top (P : Polynomial ℝ) {d : ℕ} (h : P.natDegree ≤ d)
    (x : ℝ) : (Polynomial.taylor x P).coeff d = P.coeff d := by
  rcases lt_or_eq_of_le h with hlt | heq
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hlt),
      P.coeff_eq_zero_of_natDegree_lt hlt]
  · rw [← heq, Polynomial.coeff_taylor_natDegree, Polynomial.coeff_natDegree]

private theorem coeff_taylor_next (P : Polynomial ℝ) {d : ℕ} (h : P.natDegree ≤ d+1)
    (x : ℝ) : (Polynomial.taylor x P).coeff d =
      P.coeff d + (d + 1 : ℕ) * P.coeff (d+1) * x := by
  rw [Polynomial.taylor_coeff]
  have hd := Polynomial.natDegree_hasseDeriv_le P d
  rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
  simp [Finset.sum_range_succ, Polynomial.hasseDeriv_coeff, Nat.one_add,
    Nat.choose_succ_self_right]

/-- The finite difference f(X+i)−f(X+j) in ordinary polynomial form. -/
@[expose] noncomputable def shiftedDifference (P : Polynomial ℝ) (i j : ℝ) : Polynomial ℝ :=
  Polynomial.taylor i P - Polynomial.taylor j P

theorem shiftedDifference_eval (P : Polynomial ℝ) (i j x : ℝ) :
    (shiftedDifference P i j).eval x = P.eval (x+i) - P.eval (x+j) := by
  simp [shiftedDifference, Polynomial.taylor_eval]

theorem shiftedDifference_degree (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d+1)
    (i j : ℝ) : (shiftedDifference P i j).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [shiftedDifference, Polynomial.coeff_sub]
  by_cases heq : n = d+1
  · rw [heq, coeff_taylor_top P hd, coeff_taylor_top P hd, sub_self]
  · have hn' : P.natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hn'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hn'), sub_self]

theorem shiftedDifference_coeff (P : Polynomial ℝ) {d : ℕ} (hd : P.natDegree ≤ d+1)
    (i j : ℝ) : (shiftedDifference P i j).coeff d =
      P.coeff (d+1) * (d+1 : ℕ) * (i-j) := by
  rw [shiftedDifference, Polynomial.coeff_sub, coeff_taylor_next P hd, coeff_taylor_next P hd]
  ring

/-- Taking a conjugate in a correlation subtracts the two phases. -/
theorem fourierChar_sub (x y : ℝ) :
    (Real.fourierChar (x-y) : ℂ) =
      (Real.fourierChar x : ℂ) * conj (Real.fourierChar y : ℂ) := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
    Circle.coe_mul, Circle.coe_inv_eq_conj]

/-- A complete nonconstant linear-phase sum with denominator a prime. -/
theorem linear_phase_sum {Q : ℕ} (hQ : Q.Prime) (a : ℤ) (ha : a ≠ 0)
    (haQ : a.natAbs < Q) (P : Polynomial ℝ) (hd : P.natDegree ≤ 1)
    (hc : P.coeff 1 = (a : ℝ) / Q) :
    (∑ k ∈ range Q, (Real.fourierChar (P.eval (k : ℝ)) : ℂ)) = 0 := by
  have hcop : IsCoprime a (Q : ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simp only [Int.natAbs_natCast]
    apply Nat.Coprime.symm
    apply hQ.coprime_iff_not_dvd.mpr
    intro h
    exact (Nat.not_le.mpr haQ) (Nat.le_of_dvd (Int.natAbs_pos.mpr ha) h)
  have hroot : IsPrimitiveRoot (Real.fourierChar ((a : ℝ) / Q) : ℂ) Q := by
    rw [Real.fourierChar_apply]
    convert Complex.isPrimitiveRoot_exp_of_isCoprime a Q hQ.ne_zero hcop using 2
    push_cast
    ring
  have heval (k : ℕ) :
      P.eval (k : ℝ) = P.coeff 0 + k • ((a : ℝ) / Q) := by
    rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
    simp [Finset.sum_range_succ, hc, nsmul_eq_mul, mul_comm]
  simp_rw [heval, AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow,
    Circle.coe_mul, Circle.coe_pow]
  rw [← Finset.mul_sum, hroot.geom_sum_eq_zero hQ.one_lt, mul_zero]

end Density.Polynomial
