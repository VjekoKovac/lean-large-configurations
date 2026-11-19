module

public import Density.AxialCopy
public import Density.Grid

/-! The finite rigidity argument in Section 4, applied to arbitrary
distance-preserving labelings of the pattern. -/

public section

open scoped BigOperators

namespace Density

private theorem lpDistance_nonneg {d : ℕ} (p : ℝ) (x y : Point d) :
    0 ≤ lpDistance p x y := by
  unfold lpDistance
  positivity

private theorem lpDistance_pow {d : ℕ} {p : ℝ} (hp : 0 < p) (x y : Point d) :
    lpDistance p x y ^ p = powerMass p (x-y) := by
  unfold lpDistance powerMass
  rw [one_div, Real.rpow_inv_rpow (by positivity) hp.ne']
  rfl

private theorem powerMass_smul {d : ℕ} (p r : ℝ) (v : Point d) :
    powerMass p (r • v) = |r| ^ p * powerMass p v := by
  unfold powerMass
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
    Finset.mul_sum]

private theorem cross_distance_pow {d : ℕ} {p : ℝ} (hp : 0 < p) (i j : Fin d)
    (hij : i ≠ j) (a b : ℝ) :
    powerMass p (axisPoint i a - axisPoint j b) = |a| ^ p + |b| ^ p := by
  classical
  have h (k : Fin d) : |axisPoint i a k - axisPoint j b k| ^ p =
      (if k = i then |a| ^ p else 0) + (if k = j then |b| ^ p else 0) := by
    by_cases hk : k = i
    · subst k
      simp [axisPoint, hij]
    by_cases hl : k = j
    · subst k
      simp [axisPoint, hk]
    · simp [axisPoint, hk, hl, Real.zero_rpow hp.ne']
  simp only [powerMass, Pi.sub_apply, h, Finset.sum_add_distrib]
  simp

/-- The normalized directions of any finite scaled copy of the explicit
pattern form a signed permutation of the coordinate directions. -/
theorem axes_of_scaled_pattern {d m : ℕ} {p r : ℝ} (hp : 1 < p) (hp₂ : p ≠ 2)
    (hr : 0 < r) (hm : 3 ≤ m) (F : Point (d+1) → Point (d+1))
    (hF : ∀ x ∈ crossPattern d m, ∀ y ∈ crossPattern d m,
      lpDistance p (F x) (F y) = r * lpDistance p x y) :
    ∃ (v : Fin (d+1) → Point (d+1)) (e : Fin (d+1) ≃ Fin (d+1)),
      (∀ i, |v i (e i)| = 1 ∧ ∀ k, k ≠ e i → v i k = 0) ∧
      ∀ i, ∀ t ∈ arm m i, F (axisPoint i t) = F 0 + (r*t) • v i := by
  classical
  have hp₀ : 0 < p := by linarith
  have hzero (i : Fin (d+1)) : (0:ℝ) ∈ arm m i := by
    simpa only [Int.cast_zero] using small_mem_arm hm i 0 (by norm_num) (by norm_num)
  have hpos (i : Fin (d+1)) : (1:ℝ) ∈ arm m i := by
    simpa only [Int.cast_one] using small_mem_arm hm i 1 (by norm_num) (by norm_num)
  have hneg (i : Fin (d+1)) : (-1:ℝ) ∈ arm m i := by
    simpa only [Int.cast_neg, Int.cast_one] using small_mem_arm hm i (-1) (by norm_num) (by norm_num)
  have hd (i : Fin (d+1)) := affine_axis_of_copy hp hr (crossPattern d m) F hF i (arm m i)
    (hzero i) (axisPoint_mem_crossPattern hm i)
  choose v hu hv using hd
  have hcmp (i k : Fin (d+1)) (a b : ℝ) (ha : a ∈ arm m i) (hb : b ∈ arm m k) :
      powerMass p (a • v i - b • v k) = powerMass p (axisPoint i a - axisPoint k b) := by
    have he := congrArg (fun s : ℝ => s ^ p) (hF _ (axisPoint_mem_crossPattern hm _ _ ha)
      _ (axisPoint_mem_crossPattern hm _ _ hb))
    change lpDistance p _ _ ^ p = (r * lpDistance p _ _) ^ p at he
    rw [Real.mul_rpow hr.le (lpDistance_nonneg ..), lpDistance_pow hp₀, lpDistance_pow hp₀] at he
    have hdiff : F (axisPoint i a) - F (axisPoint k b) = r • (a • v i - b • v k) := by
      rw [hv i a ha, hv k b hb]
      ext l
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hdiff, powerMass_smul, abs_of_pos hr] at he
    exact mul_left_cancel₀ (Real.rpow_pos_of_pos hr p).ne' he
  have hcross (i k : Fin (d+1)) (hik : i ≠ k) :
      powerMass p (v i + v k) = 2 ∧ powerMass p (v i - v k) = 2 := by
    have hs := hcmp i k 1 (-1) (hpos i) (hneg k)
    have ht := hcmp i k 1 1 (hpos i) (hpos k)
    rw [cross_distance_pow hp₀ _ _ hik] at hs ht
    constructor
    · simpa [show (1:ℝ) + 1 = 2 by norm_num] using hs
    · simpa [show (1:ℝ) + 1 = 2 by norm_num] using ht
  obtain ⟨e, he⟩ := unit_axes_of_cross hp hp₂ v hu hcross
  exact ⟨v, e, he, hv⟩

/-- Every finite isometric copy contains at least one point in the omitted
half-open stripe, including copies that reverse the long arm. -/
theorem no_scaled_copy_cross {d m : ℕ} {p : ℝ} (hp : 1 < p) (hp₂ : p ≠ 2)
    (hm : 3 ≤ m) (j : ℕ) :
    ¬HasScaledCopy p ((j : ℝ) + 1 / (m : ℝ)) (crossPattern d m)
      {x | Int.fract (∑ i, x i) < 1 - 1 / (m : ℝ)} := by
  classical
  let r : ℝ := (j : ℝ) + 1 / (m : ℝ)
  have hM : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hr : 0 < r := by dsimp [r]; positivity
  rintro ⟨f, _, hf⟩
  let F (x : Point (d+1)) : Point (d+1) := if h : x ∈ crossPattern d m then (f ⟨x,h⟩).val else 0
  have hF (x) (hx : x ∈ crossPattern d m) (y) (hy : y ∈ crossPattern d m) :
      lpDistance p (F x) (F y) = r * lpDistance p x y := by
    simpa [F, hx, hy, r] using hf ⟨x,hx⟩ ⟨y,hy⟩
  have hE (x) (hx : x ∈ crossPattern d m) :
      Int.fract (∑ i, F x i) < 1 - 1 / (m : ℝ) := by
    simpa [F, hx, Set.mem_ofPred_eq] using (f ⟨x,hx⟩).property
  obtain ⟨v, e, he, hv⟩ := axes_of_scaled_pattern hp hp₂ hr hm F hF
  obtain ⟨s, hs, hsign⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (v 0 (e 0) : ℝ) = s := by
    rcases abs_eq_abs.mp (show |v 0 (e 0)| = |(1 : ℝ)| by simpa using (he 0).1) with h | h
    · exact ⟨1, Or.inl rfl, by exact_mod_cast h⟩
    · exact ⟨-1, Or.inr rfl, by exact_mod_cast h⟩
  have hsv : (∑ i, v 0 i) = (s : ℝ) := by
    rw [← hsign]
    exact Finset.sum_eq_single (e 0) (fun i _ hi => (he 0).2 i hi) (by simp)
  obtain ⟨k, hk₀, hk₁, hhit⟩ := signed_grid_hits_last_cell (m : ℤ) j s (by omega) hs (-1)
    (∑ i, F 0 i)
  have hkm : k < (m : ℤ) - 1 := by omega
  have hmem : (k : ℝ) ∈ arm m (0 : Fin (d+1)) := by
    change (k : ℝ) ∈ firstArm m
    exact int_mem_firstArm k hk₀ hkm
  have hbad := hE _ (axisPoint_mem_crossPattern hm _ _ hmem)
  rw [hv 0 _ hmem] at hbad
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hsv] at hbad
  push_cast at hhit
  dsimp [r] at hbad
  rw [show ((j : ℝ) + 1 / (m : ℝ)) * k * s =
    (s : ℝ) * (j + 1 / (m : ℝ)) * k by ring] at hbad
  exact (not_lt.mpr hhit) hbad

end Density
