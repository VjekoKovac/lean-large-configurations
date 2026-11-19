module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-! A finite van der Corput inequality for the polynomial-phase argument of Section 3. -/

public section

namespace Density.Polynomial

open Finset
open scoped ComplexConjugate

private theorem shift_error (f : ℕ → ℂ) (hf : ∀ k, ‖f k‖ ≤ 1) (N i : ℕ) :
    ‖(∑ k ∈ range N, f k) - ∑ k ∈ range N, f (k + i)‖ ≤ 2 * (i : ℝ) := by
  have h : (∑ k ∈ range N, f k) + (∑ k ∈ range i, f (N + k)) =
      (∑ k ∈ range i, f k) + ∑ k ∈ range N, f (i + k) := by
    rw [← sum_range_add, ← sum_range_add, Nat.add_comm]
  have eq : (∑ k ∈ range N, f k) - (∑ k ∈ range N, f (k + i)) =
      (∑ k ∈ range i, f k) - ∑ k ∈ range i, f (N + k) := by
    simp_rw [Nat.add_comm i] at h
    linear_combination h
  have bound (j : ℕ) : ‖∑ k ∈ range i, f (j+k)‖ ≤ (i : ℝ) := by
    calc
      _ ≤ ∑ k ∈ range i, ‖f (j+k)‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ range i, (1 : ℝ) := sum_le_sum fun _ _ => hf _
      _ = _ := by simp
  rw [eq]
  apply (norm_sub_le _ _).trans
  have h₀ := bound 0
  simp only [Nat.zero_add] at h₀
  linarith [bound N]

/-- Shift averaging and Cauchy–Schwarz. The hypothesis only concerns distinct
shifts, so that the constant correlation at a diagonal pair costs exactly 1/H. -/
theorem van_der_corput (f : ℕ → ℂ) (N H : ℕ) (hN : 0 < N) (hH : 0 < H)
    {δ : ℝ} (hδ : 0 ≤ δ) (hf : ∀ k, ‖f k‖ ≤ 1)
    (hc : ∀ i < H, ∀ j < H, i ≠ j →
      ‖∑ k ∈ range N, f (k+i) * conj (f (k+j))‖ ≤ N * δ) :
    ‖∑ k ∈ range N, f k‖ / N ≤ 2 * H / N + Real.sqrt (1 / H + δ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hHr : 0 < (H : ℝ) := by exact_mod_cast hH
  let S := ∑ k ∈ range N, f k
  let g (k : ℕ) := ∑ i ∈ range H, f (k+i)
  let T := ∑ k ∈ range N, g k
  let c (i j : ℕ) := (∑ k ∈ range N, f (k+i) * conj (f (k+j))).re
  have herr : ‖(H : ℂ) * S - T‖ ≤ 2 * (H : ℝ)^2 := by
    have heq : (H : ℂ) * S - T =
        ∑ i ∈ range H, (S - ∑ k ∈ range N, f (k+i)) := by
      simp only [T, g, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      rw [sum_comm (s := range N)]
    rw [heq]
    calc
      _ ≤ _ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ range H, 2 * (H : ℝ) := by
        apply sum_le_sum
        intro i hi
        exact (shift_error f hf N i).trans (by gcongr; exact_mod_cast (mem_range.mp hi).le)
      _ = _ := by simp; ring
  have hcompare : (H : ℝ) * ‖S‖ ≤ 2 * (H : ℝ)^2 + ‖T‖ := by
    calc
      _ = ‖(H : ℂ) * S‖ := by simp
      _ ≤ ‖(H : ℂ) * S - T‖ + ‖T‖ := by simpa using norm_add_le ((H : ℂ) * S - T) T
      _ ≤ _ := by linarith
  have hr (z : ℂ) : (z * conj z).re = ‖z‖ ^ 2 := by rw [Complex.mul_conj']; norm_cast
  have hexpand : ∑ k ∈ range N, ‖g k‖ ^ 2 =
      ∑ i ∈ range H, ∑ j ∈ range H, c i j := by
    simp_rw [← hr, g, c, map_sum, sum_mul, mul_sum, Complex.re_sum]
    rw [sum_comm (s := range N)]
    apply sum_congr rfl
    intro i _
    exact sum_comm
  have hdiag (i : ℕ) : c i i ≤ (N : ℝ) := by
    dsimp [c]
    rw [Complex.re_sum]
    calc
      _ ≤ ∑ _ ∈ range N, (1 : ℝ) := by
        apply sum_le_sum
        intro k _
        rw [hr]
        nlinarith [hf (k+i), norm_nonneg (f (k+i))]
      _ = _ := by simp
  have hrow (i : ℕ) (hi : i ∈ range H) :
      (∑ j ∈ range H, c i j) ≤ (N : ℝ) + H * (N*δ) := by
    calc
      _ ≤ ∑ j ∈ range H, ((if j = i then (N : ℝ) else 0) + N * δ) := by
        apply sum_le_sum
        intro j hj
        by_cases hij : j = i
        · subst j
          simpa using (hdiag i).trans (le_add_of_nonneg_right (mul_nonneg hNr.le hδ))
        · simp only [ite_eq_right, hij, zero_add, not_false_eq_true]
          exact (Complex.re_le_norm _).trans (hc i (mem_range.mp hi) j (mem_range.mp hj) (Ne.symm hij))
      _ = _ := by simp [sum_add_distrib, hi]
  have henergy : (∑ k ∈ range N, ‖g k‖ ^ 2) ≤ H * ((N : ℝ) + H * (N*δ)) := by
    rw [hexpand]
    simpa [mul_add] using sum_le_sum hrow
  have hcs : ‖T‖^2 ≤ (N : ℝ) * (∑ k ∈ range N, ‖g k‖^2) := by
    apply ((sq_le_sq₀ (norm_nonneg _) (sum_nonneg fun _ _ => norm_nonneg _)).mpr
      (norm_sum_le _ _)).trans
    simpa using sq_sum_le_card_mul_sum_sq (s := range N) (f := fun k => ‖g k‖)
  have hroot : ‖T‖ ≤ (H : ℝ) * N * Real.sqrt (1 / H + δ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    apply hcs.trans
    apply (mul_le_mul_of_nonneg_left henergy hNr.le).trans_eq
    field_simp
  change ‖S‖ / N ≤ _
  apply (div_le_iff₀ hNr).2
  rw [add_mul, div_mul_cancel₀ _ hNr.ne']
  apply (le_of_mul_le_mul_left _ hHr)
  nlinarith only [hcompare, hroot]

end Density.Polynomial
