module

public import Density.Polynomial
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.Order.Round
public import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! # A tail bound for the Fejér kernel away from a test arc

A chord on the unit circle has length at least four times the distance to
the nearest integer. Combining this with the finite geometric sum formula
bounds the Fejér mass contributed by a point outside the enlarged arc.
The estimate applies to arcs which wrap around zero as well.
-/

public section
open Finset
open scoped BigOperators

namespace Density.Polynomial

/-- Jordan's inequality for sine in the normalization e(t) = exp(2πit). -/
theorem fourier_chord_lower (t : ℝ) :
    4 * |t - (round t : ℝ)| ≤ ‖(Real.fourierChar t : ℂ) - 1‖ := by
  let z : ℤ := round t
  have hz : |t - (z : ℝ)| ≤ 1 / 2 := abs_sub_round t
  have hang : |(t - (z : ℝ)) * Real.pi| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_right hz Real.pi_pos.le]
  have h := Real.mul_abs_le_abs_sin hang
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  have hf : 2 / Real.pi * (|t - (z : ℝ)| * Real.pi) = 2 * |t - (z : ℝ)| := by
    field_simp
  rw [hf, sub_mul, Real.sin_sub_int_mul_pi, abs_mul] at h
  have hzpow : |(-1 : ℝ) ^ z| = 1 := by simp [abs_zpow]
  rw [hzpow, one_mul] at h
  change 4 * |t - (z : ℝ)| ≤ ‖Complex.exp (↑(2 * Real.pi * t) * Complex.I) - 1‖
  rw [mul_comm (↑(2 * Real.pi * t) : ℂ) Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    show 2 * Real.pi * t / 2 = t * Real.pi by ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

/-- Uniform bound for the unnormalized Fejér numerator. Centers have distance
at least δ to both endpoints. Lengths, centers and sample points are real
representatives, with the integer translates encoded in inArc. -/
theorem fejer_sum_tail {x u length c δ : ℝ} (hδ : 0 < δ) (hl : u + δ ≤ c)
    (hr : c + δ ≤ u + length) (hx : ¬ inArc x u length) (M : ℕ) :
    ‖∑ h ∈ Finset.range M, (Real.fourierChar ((h : ℝ) * (x - c)) : ℂ)‖ ^ 2 ≤ 1 / δ ^ 2 := by
  let t := x - c
  let z : ℤ := round t
  have hd : δ ≤ |t - (z : ℝ)| := by
    by_contra! hsmall
    apply hx
    obtain ⟨hleft, hright⟩ := abs_lt.mp hsmall
    dsimp [t] at hleft hright
    exact ⟨z, by linarith, by linarith⟩
  let w : ℂ := Real.fourierChar t
  have hw : ‖w‖ = 1 := Circle.norm_coe _
  have hgeom : ‖∑ h ∈ range M, w ^ h‖ * ‖w-1‖ ≤ 2 := calc
    _ = ‖w ^ M - 1‖ := by rw [← norm_mul, geom_sum_mul]
    _ ≤ ‖w ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp [norm_pow, hw]; norm_num
  have hchord2 : 2 * δ ≤ ‖w - 1‖ := by
    have h := fourier_chord_lower t
    change 4 * |t - (z : ℝ)| ≤ ‖w - 1‖ at h
    linarith
  have hmul := mul_le_mul_of_nonneg_left hchord2 (norm_nonneg (∑ h ∈ range M, w ^ h))
  have hsum : ‖∑ h ∈ range M, w ^ h‖ ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hterm (h : ℕ) : (Real.fourierChar ((h : ℝ) * (x - c)) : ℂ) = w ^ h := by
    change (Real.fourierChar ((h : ℝ) * t) : ℂ) = (Real.fourierChar t : ℂ) ^ h
    rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
    rfl
  simp_rw [hterm]
  simpa [div_pow] using pow_le_pow_left₀ (norm_nonneg _) hsum 2

end Density.Polynomial
