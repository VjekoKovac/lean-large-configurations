module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic

/-! A finite Fourier estimate for short arcs. We expand the square of a
geometric sum. For a uniform mesh all off-diagonal sums vanish exactly. -/

@[expose] public section

open Complex
open scoped BigOperators ComplexConjugate

namespace Density.Polynomial

/-- The standard additive character of the real line, with period one. -/
noncomputable def fourierE (x : ℝ) : ℂ := (Real.fourierChar x : ℂ)

@[simp] theorem fourierE_zero : fourierE 0 = 1 := by simp [fourierE]

@[simp] theorem norm_fourierE (x : ℝ) : ‖fourierE x‖ = 1 := by simp [fourierE]

theorem fourierE_add (x y : ℝ) : fourierE (x+y) = fourierE x * fourierE y := by
  simp [fourierE, AddChar.map_add_eq_mul]

theorem fourierE_nat_mul (h : ℕ) (x : ℝ) :
    fourierE ((h:ℝ)*x) = (fourierE x)^h := by
  unfold fourierE
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  rfl

@[simp] theorem conj_fourierE (x : ℝ) : conj (fourierE x) = fourierE (-x) := by
  simp [fourierE]

/-- The normalized squared geometric sum. Its M equally spaced translates
sum to one. -/
noncomputable def fejerWeight (M : ℕ) (x : ℝ) : ℝ :=
  ‖∑ h ∈ Finset.range M, fourierE ((h:ℝ)*x)‖ ^ 2 / (M:ℝ)^2

theorem fejer_nonneg (M : ℕ) (x : ℝ) : 0 ≤ fejerWeight M x := by
  unfold fejerWeight
  positivity

theorem fejer_neg (M : ℕ) (x : ℝ) : fejerWeight M (-x) = fejerWeight M x := by
  unfold fejerWeight
  simp_rw [mul_neg, ← conj_fourierE, ← map_sum, Complex.norm_conj]

private theorem fejer_numerator (M : ℕ) (x : ℝ) :
    ‖∑ h ∈ Finset.range M, fourierE ((h:ℝ)*x)‖ ^ 2 =
      ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range M,
        (fourierE (((a:ℝ)-b)*x)).re := by
  have he (a b : ℕ) : fourierE ((a:ℝ)*x) * conj (fourierE ((b:ℝ)*x)) =
      fourierE (((a:ℝ)-b)*x) := by
    rw [conj_fourierE, ← fourierE_add]
    congr 1
    ring
  have eqn := Complex.mul_conj (∑ h ∈ Finset.range M, fourierE ((h:ℝ)*x))
  rw [map_sum, Finset.sum_mul] at eqn
  simp_rw [Finset.mul_sum, he] at eqn
  have re := congrArg Complex.re eqn
  simpa only [Complex.re_sum, Complex.ofReal_re, Complex.normSq_eq_norm_sq] using re.symm

/-- Uniform control of the nonzero frequencies up to M−1 bounds the
deviation of each shifted Fejér average from its constant coefficient. -/
theorem fejer_error {M Q : ℕ} (hM : 0 < M) (X : ℕ → ℝ) (c δ : ℝ)
    (hδ : 0 ≤ δ)
    (hW : ∀ h : ℕ, 0 < h → h < M →
      ‖∑ k ∈ Finset.range Q, fourierE ((h:ℝ)*X k)‖ ≤ (Q:ℝ)*δ) :
    |(∑ k ∈ Finset.range Q, fejerWeight M (X k-c)) - (Q:ℝ)/M| ≤ (Q:ℝ)*δ := by
  have hdif (a b : ℕ) (ha : a < M) (hb : b < M) (hne : a ≠ b) :
      ‖∑ k ∈ Finset.range Q, fourierE (((a:ℝ)-b)*X k)‖ ≤ (Q:ℝ)*δ := by
    rcases lt_or_gt_of_ne hne with hab | hba
    · have e : ∀ k, fourierE (((a:ℝ)-b)*X k) = conj (fourierE (((b-a:ℕ):ℝ)*X k)) := by
        intro k
        rw [conj_fourierE, Nat.cast_sub hab.le, ← neg_mul]
        congr 2
        ring
      simp_rw [e, ← map_sum, Complex.norm_conj]
      apply hW <;> omega
    · rw [← Nat.cast_sub hba.le]
      apply hW <;> omega
  let I := Finset.range M
  let T (a b : ℕ) (k : ℕ) := (fourierE (((a:ℝ)-b)*(X k-c))).re
  have hlocal (a : ℕ) (ha : a ∈ I) (b : ℕ) (hb : b ∈ I) :
      |(∑ k ∈ Finset.range Q, T a b k) - (if b=a then (Q:ℝ) else 0)| ≤ (Q:ℝ)*δ := by
    by_cases he : b=a
    · subst b
      simp [T, mul_nonneg (Nat.cast_nonneg _) hδ]
    · have hshift (k : ℕ) : fourierE (((a:ℝ)-b)*(X k-c)) =
          fourierE (-(((a:ℝ)-b)*c)) * fourierE (((a:ℝ)-b)*X k) := by
        rw [← fourierE_add]
        congr 1
        ring
      simp only [T, ite_eq_right he, sub_zero, ← Complex.re_sum]
      apply (Complex.abs_re_le_norm _).trans
      simp_rw [hshift, ← Finset.mul_sum, norm_mul, norm_fourierE, one_mul]
      exact hdif a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) (Ne.symm he)
  let S (a b : ℕ) := (∑ k ∈ Finset.range Q, T a b k) - (if b=a then (Q:ℝ) else 0)
  have habs : |∑ a ∈ I, ∑ b ∈ I, S a b| ≤ (M:ℝ)^2*((Q:ℝ)*δ) := by
    calc
      _ ≤ ∑ a ∈ I, |∑ b ∈ I, S a b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ I, ∑ b ∈ I, |S a b| :=
        Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _a ∈ I, ∑ _b ∈ I, (Q:ℝ)*δ :=
        Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (hlocal a ha))
      _ = _ := by simp [I]; ring
  have hdiag (a : ℕ) (ha : a ∈ I) : (∑ b ∈ I, if b=a then (Q:ℝ) else 0) = Q := by simp [ha]
  have htot : (∑ a ∈ I, ∑ b ∈ I, S a b) =
      (∑ k ∈ Finset.range Q, ∑ a ∈ I, ∑ b ∈ I, T a b k) - M*Q := by
    simp only [S, Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl hdiag]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, I]
    congr 1
    calc
      _ = ∑ a ∈ Finset.range M, ∑ k ∈ Finset.range Q, ∑ b ∈ Finset.range M, T a b k :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [htot] at habs
  have hrM : (0:ℝ) < M := by exact_mod_cast hM
  simp only [fejerWeight, fejer_numerator, ← Finset.sum_div]
  change |(∑ k ∈ Finset.range Q, ∑ a ∈ I, ∑ b ∈ I, T a b k) / (M:ℝ)^2 - Q/M| ≤ _
  rw [show (Q:ℝ)/M = ((M:ℝ)*Q)/M^2 by field_simp, ← sub_div, abs_div, abs_of_nonneg (sq_nonneg (M:ℝ))]
  exact (div_le_iff₀ (sq_pos_of_pos hrM)).mpr (by linarith only [habs, mul_comm ((M:ℝ)^2) ((Q:ℝ)*δ)])

/-- Character orthogonality on the equally spaced M-point mesh. -/
theorem grid_fourier_zero {M h : ℕ} (hM : 0 < M) (hh : 0 < h) (hsmall : h < M) :
    (∑ j ∈ Finset.range M, fourierE ((h:ℝ)*((j:ℝ)/M))) = 0 := by
  let w := fourierE (1/(M:ℝ))
  have hw : IsPrimitiveRoot w M := by
    have e : w = Complex.exp (2 * Real.pi * Complex.I / (M:ℂ)) := by
      unfold w fourierE
      rw [Real.fourierChar_apply]
      push_cast
      congr 1
      ring
    rw [e]
    exact Complex.isPrimitiveRoot_exp _ hM.ne'
  have hne : w ^ h ≠ 1 := by
    intro h1
    exact (not_le.mpr hsmall) (Nat.le_of_dvd hh ((hw.pow_eq_one_iff_dvd h).mp h1))
  have he (k : ℕ) : fourierE ((h:ℝ)*((k:ℝ)/M)) = (w^h)^k := by
    unfold w
    rw [← fourierE_nat_mul, ← fourierE_nat_mul]
    congr 1
    ring
  simp_rw [he]
  rw [geom_sum_eq hne, ← pow_mul, Nat.mul_comm h M, pow_mul, hw.pow_eq_one, one_pow,
    sub_self, zero_div]

/-- Exactly one unit of mass lies in all grid translates, including when
x is itself a grid point. -/
theorem fejer_partition (M : ℕ) (hM : 0 < M) (x c : ℝ) :
    ∑ j ∈ Finset.range M, fejerWeight M (x-(c+(j:ℝ)/M)) = 1 := by
  have h := fejer_error (Q:=M) hM (fun j => (j:ℝ)/M) (x-c) 0 le_rfl (by
    intro h hh hm
    rw [grid_fourier_zero hM hh hm, norm_zero, mul_zero])
  simp only [mul_zero, abs_nonpos_iff, sub_eq_zero] at h
  have he (j : ℕ) : fejerWeight M (x-(c+(j:ℝ)/M)) = fejerWeight M ((j:ℝ)/M-(x-c)) := by
    rw [show x-(c+(j:ℝ)/M) = -((j:ℝ)/M-(x-c)) by ring, fejer_neg]
  simp_rw [he]
  exact h.trans (div_self (by exact_mod_cast hM.ne' : (M:ℝ) ≠ 0))

end Density.Polynomial
