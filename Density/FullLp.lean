module

public import Density.CrossAvoidance
public import Density.StripeMeasure

/-! Section 4: the configuration and all of the obstructed scales for
Theorem 3. For dimension D+1, its first arm has n-2D points. -/

public section

open Filter MeasureTheory

namespace Density

theorem fullLp : FullLpStatement := by
  intro dim p hdim hp hp₂ n hn
  cases dim with
  | zero => omega
  | succ d =>
    let m := n - 2 * d
    have hm : 3 ≤ m := by dsimp [m]; omega
    have hm' : m + 2 * d = n := by dsimp [m]; omega
    have hmr : (m : ℝ) = (n : ℝ) - 2 * ((d + 1 : ℕ) : ℝ) + 2 := by
      have e : (m : ℝ) + 2 * (d : ℝ) = n := by exact_mod_cast hm'
      push_cast
      linarith
    have hM : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hM₀ : (0 : ℝ) < m := by linarith
    let a : ℝ := 1 - 1 / (m : ℝ)
    have h₀ : 0 ≤ a := by
      apply sub_nonneg.mpr
      exact (div_le_one hM₀).mpr hM
    have h₁ : a ≤ 1 := sub_le_self _ (by positivity)
    refine ⟨stripes (d+1) a, crossPattern d m, ?_, ?_⟩
    · refine ⟨(measurableSet_stripes (d+1) a).nullMeasurableSet, (card_crossPattern d m).trans hm',
        fun j => (j : ℝ) + 1 / (m : ℝ), ?_, ?_, ?_⟩
      · intro j
        positivity
      · exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      · intro j
        exact no_scaled_copy_cross hp hp₂ hm j
    · rw [← hmr]
      exact hasDensity_stripes (by omega) h₀ h₁

end Density
