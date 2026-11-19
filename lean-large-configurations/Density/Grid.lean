module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

/-! The half-open endpoint in the obstruction is essential: a translate of a
grid always has a point in the last half-open subinterval of length 1/m. -/

public section

namespace Density

/-- One of m consecutive residues belongs to the omitted half-open cell. -/
theorem grid_hits_last_cell (m : ℤ) (hm : 0 < m) (x : ℝ) :
    ∃ k : ℤ, 0 ≤ k ∧ k < m ∧ 1 - 1 / (m : ℝ) ≤ Int.fract (x + k / (m : ℝ)) := by
  let u := Int.fract x
  let b := ⌊(m : ℝ) * u⌋
  let k := m - 1 - b
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  have hu₀ : 0 ≤ u := Int.fract_nonneg _
  have hu₁ : u < 1 := Int.fract_lt_one _
  have hb₀ : 0 ≤ b := Int.floor_nonneg.mpr (mul_nonneg hM.le hu₀)
  have hb₁ : b < m := Int.floor_lt.mpr (by nlinarith [mul_lt_mul_of_pos_left hu₁ hM])
  have hk₀ : 0 ≤ k := by dsimp [k]; omega
  have hk₁ : k < m := by dsimp [k]; omega
  refine ⟨k, hk₀, hk₁, ?_⟩
  have hk : (k : ℝ) = (m : ℝ) - 1 - (b : ℝ) := by simp [k]
  have hlo : (b : ℝ) ≤ m * u := Int.floor_le _
  have hhi : (m : ℝ) * u < b + 1 := Int.lt_floor_add_one _
  have he : u + (k : ℝ) / m = ((m : ℝ) * u + k) / m := by field_simp
  have hr₀ : 0 ≤ u + (k : ℝ) / m := by positivity
  have hr₁ : u + (k : ℝ) / m < 1 := by
    rw [he, div_lt_one hM, hk]
    linarith
  have hre : x + (k : ℝ) / m = (u + k / (m : ℝ)) + (⌊x⌋ : ℝ) := by
    have hu : u = x - (⌊x⌋ : ℝ) := rfl
    rw [hu]
    ring
  rw [hre, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨hr₀, hr₁⟩, he,
      show (1 : ℝ) - 1 / m = (m - 1) / m by field_simp]
  apply (div_le_div_iff_of_pos_right hM).2
  rw [hk]
  linarith

/-- For either orientation of the line and any integral part of the scale,
one point of an integer block hits the omitted cell. -/
theorem signed_grid_hits_last_cell (m j s : ℤ) (hm : 0 < m) (hs : s = 1 ∨ s = -1)
    (a : ℤ) (x : ℝ) :
    ∃ k : ℤ, a ≤ k ∧ k < a + m ∧
      1 - 1 / (m : ℝ) ≤ Int.fract (x + (s : ℝ) * ((j : ℝ) + 1 / m) * k) := by
  rcases hs with rfl | rfl
  · obtain ⟨t, ht₀, ht₁, h⟩ := grid_hits_last_cell m hm (x + (a : ℝ) / m)
    refine ⟨a + t, by omega, by omega, ?_⟩
    have he : x + ((1 : ℤ) : ℝ) * ((j : ℝ) + 1 / m) * ((a + t : ℤ) : ℝ) =
        (x + (a : ℝ) / m + (t : ℝ) / m) + ((j * (a + t) : ℤ) : ℝ) := by
      push_cast
      ring
    rw [he, Int.fract_add_intCast]
    exact h
  · let b := a + m - 1
    obtain ⟨t, ht₀, ht₁, h⟩ := grid_hits_last_cell m hm (x - (b : ℝ) / m)
    refine ⟨b - t, by dsimp [b]; omega, by dsimp [b]; omega, ?_⟩
    have he : x + ((-1 : ℤ) : ℝ) * ((j : ℝ) + 1 / m) * ((b - t : ℤ) : ℝ) =
        (x - (b : ℝ) / m + (t : ℝ) / m) + ((-(j * (b - t)) : ℤ) : ℝ) := by
      push_cast
      ring
    rw [he, Int.fract_add_intCast]
    exact h

end Density
