module

public import Density.WeylShift
public import Density.VanDerCorput
public import Density.WeylParameters
public import Mathlib.Data.Int.Lemmas

/-! # A short-shift version of Weyl's inequality

For the rational leading coefficient in Section 3, taking a larger prime
denominator allows differencing to stop at an exactly vanishing linear sum.
Every nonzero product of the shifts and the descending degree factors is
strictly smaller than the prime. The error incurred by averaging shifts is
controlled by the finite van der Corput inequality.
-/

public section

open Finset
open scoped ComplexConjugate

namespace Density.Polynomial

/-- Reducing degree d+1 to d introduces the multiplier (d+1)(i-j). -/
private theorem numerator_budget {a : ℤ} {d H i j : ℕ}
    (hd : 0 < d) (hi : i < H) (hj : j < H) :
    (a * ((d+1 : ℕ) : ℤ) * ((i : ℤ)-j)).natAbs * d.factorial * H^(d-1) ≤
      a.natAbs * (d+1).factorial * H^((d+1)-1) := by
  have hdiff := Int.natAbs_coe_sub_coe_le_of_le hi.le hj.le
  calc
    _ = ((a.natAbs * (d+1).factorial) * ((i : ℤ)-j).natAbs) * H^(d-1) := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast, Nat.factorial_succ]
      ring
    _ ≤ ((a.natAbs * (d+1).factorial) * H) * H^(d-1) := by gcongr
    _ = (a.natAbs * (d+1).factorial) * H^((d-1)+1) := by rw [pow_succ]; ring
    _ = _ := by rw [show d-1+1=d by omega]; simp

/-- Large-denominator polynomial cancellation at any prescribed integer
accuracy T, uniform in the real lower coefficients and the numerator a
within the displayed range. -/
theorem short_shift_weyl {Q H d T : ℕ} (hQ : Q.Prime) (hQH : 4 * H^2 ≤ Q)
    (hd : 0 < d) (hT : 0 < T) (hsize : (16*T)^(2^d) ≤ H)
    (a : ℤ) (ha : a ≠ 0) (hnum : a.natAbs * d.factorial * H^(d-1) < Q)
    (P : Polynomial ℝ) (hdeg : P.natDegree ≤ d) (hcoeff : P.coeff d = (a : ℝ) / Q) :
    ‖∑ k ∈ range Q, (Real.fourierChar (P.eval (k : ℝ)) : ℂ)‖ / Q ≤ 1 / (T : ℝ) := by
  induction d generalizing T a P with
  | zero => omega
  | succ d ih =>
    by_cases hd0 : d = 0
    · subst d
      have hsmall : a.natAbs < Q := by simpa using hnum
      rw [linear_phase_sum hQ a ha hsmall P hdeg hcoeff]
      simp
    have hd' : 0 < d := by omega
    have hchild : (16 * (16*T^2))^(2^d) ≤ H := (weyl_child_size d T) ▸ hsize
    have hbase : 0 < 16 * (16*T^2) := by positivity
    have hprec : 16*T^2 ≤ H := by
      calc
        _ ≤ 16*(16*T^2) := by omega
        _ = (16*(16*T^2))^1 := (pow_one _).symm
        _ ≤ _ := (Nat.pow_le_pow_right hbase (show 0 < 2^d by positivity)).trans hchild
    have hH : 0 < H := lt_of_lt_of_le (by positivity) hprec
    let f (k : ℕ) : ℂ := Real.fourierChar (P.eval (k : ℝ))
    have hc (i : ℕ) (hi : i < H) (j : ℕ) (hj : j < H) (hne : i ≠ j) :
        ‖∑ k ∈ range Q, f (k+i) * conj (f (k+j))‖ ≤
        Q * (1 / (16 * (T : ℝ)^2)) := by
      let b : ℤ := a * ((d+1 : ℕ) : ℤ) * ((i : ℤ)-j)
      have hb : b ≠ 0 := by
        dsimp [b]
        exact mul_ne_zero (mul_ne_zero ha (by positivity))
          (sub_ne_zero.mpr (by exact_mod_cast hne))
      have hbudget : b.natAbs * d.factorial * H^(d-1) < Q :=
        (numerator_budget hd' hi hj).trans_lt hnum
      let D := shiftedDifference P i j
      have hcoeff' : D.coeff d = (b : ℝ) / Q := by
        rw [shiftedDifference_coeff P hdeg, hcoeff]
        dsimp [b]
        push_cast
        ring
      have hmean := ih hd' (T := 16*T^2) (by positivity) hchild b hb hbudget
        D (shiftedDifference_degree P hdeg _ _) hcoeff'
      have hcorr (k : ℕ) :
          f (k+i) * conj (f (k+j)) = (Real.fourierChar (D.eval (k : ℝ)) : ℂ) := by
        rw [shiftedDifference_eval, fourierChar_sub]
        simp [f]
      simp_rw [hcorr]
      have hraw := (div_le_iff₀ (by exact_mod_cast hQ.pos : (0 : ℝ) < Q)).mp hmean
      push_cast at hraw
      simpa only [mul_comm (Q : ℝ)] using hraw
    exact (van_der_corput f Q H hQ.pos hH (by positivity) (by simp [f]) hc).trans
      (weyl_step_bound hT hprec hQH)

end Density.Polynomial
