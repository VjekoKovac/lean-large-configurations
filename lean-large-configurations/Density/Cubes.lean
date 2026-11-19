module

public import Density.Definitions
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

/-! # Centered cubes and the passage from integer to real side lengths -/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace Density

theorem centeredCube_eq_Icc (d : ℕ) (R : ℝ) :
    centeredCube d R = Set.Icc (fun _ : Fin d => -(R / 2)) (fun _ => R / 2) := by
  ext x
  exact forall_and

theorem measurableSet_centeredCube (d : ℕ) (R : ℝ) : MeasurableSet (centeredCube d R) := by
  rw [centeredCube_eq_Icc]
  exact measurableSet_Icc

theorem volume_centeredCube (d : ℕ) (R : ℝ) :
    volume (centeredCube d R) = ENNReal.ofReal R ^ d := by
  rw [centeredCube_eq_Icc, Real.volume_Icc_pi]
  simp [show R / 2 - -(R / 2) = R by ring]

theorem centeredCube_mono (d : ℕ) : Monotone (centeredCube d) := by
  intro r s hrs x hx i
  obtain ⟨h₁, h₂⟩ := hx i
  constructor <;> linarith

theorem cubeVolume_mono {d : ℕ} (E : Set (Point d)) :
    Monotone (fun R => volume.real (E ∩ centeredCube d R)) := by
  intro r s hrs
  refine measureReal_mono (Set.inter_subset_inter_right _ (centeredCube_mono d hrs)) ?_
  exact (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
    (by rw [volume_centeredCube]; finiteness)).ne

/-- An exact integer-side volume formula implies a true density limit over
all real side lengths. Monotonicity places each intermediate volume between
the volumes of two consecutive integer cubes. -/
theorem hasDensity_of_integer_volumes {d : ℕ} (E : Set (Point d)) (a : ℝ)
    (hvol : ∀ N : ℕ, 1 ≤ N → volume.real (E ∩ centeredCube d (N : ℝ)) = a * (N : ℝ) ^ d) :
    HasDensity E a := by
  have hfloor : Tendsto (fun R : ℝ => (⌊R⌋₊ : ℝ) / R) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have hsucc : Tendsto (fun R : ℝ => ((⌊R⌋₊ : ℝ) + 1) / R) atTop (𝓝 1) := by
    simpa only [add_div, add_zero] using hfloor.add
      (tendsto_const_nhds.div_atTop (tendsto_id : Tendsto id atTop (atTop : Filter ℝ)) :
        Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0))
  have hm := cubeVolume_mono E
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun R : ℝ => a * ((⌊R⌋₊ : ℝ) / R) ^ d)
    (h := fun R : ℝ => a * (((⌊R⌋₊ : ℝ) + 1) / R) ^ d)
    (by simpa using tendsto_const_nhds.mul (hfloor.pow d))
    (by simpa using tendsto_const_nhds.mul (hsucc.pow d))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hn : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by simpa using hR)
    have hle := hm (Nat.floor_le (by linarith : 0 ≤ R))
    change volume.real _ ≤ volume.real _ at hle
    rw [hvol _ hn] at hle
    change a * _ ≤ volume.real _ / R ^ d
    rw [div_pow, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hle (pow_nonneg (by linarith) _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hleR : R ≤ ((⌊R⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one R).le
    have hle := hm hleR
    change volume.real _ ≤ volume.real _ at hle
    rw [hvol _ (by omega)] at hle
    push_cast at hle
    change volume.real _ / R ^ d ≤ a * _
    rw [div_pow, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hle (pow_nonneg (by linarith) _)

end Density
