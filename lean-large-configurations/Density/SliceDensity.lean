module

public import Density.Cubes
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Lifting a uniform one-dimensional slice estimate to centered-cube density -/

public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace Density

/-- Slice the cube in its first coordinate. Volume in dimension zero, which
occurs on the right when the original dimension is one, has mass one. -/
theorem volume_cube_by_slices {d : ℕ} {E : Set (Point (d + 1))} (hE : MeasurableSet E) (R : ℝ) :
    volume (E ∩ centeredCube (d+1) R) =
      ∫⁻ y in centeredCube d R, volume (Icc (-(R/2)) (R/2) ∩
        {t : ℝ | Fin.cons t y ∈ E}) := by
  let S := E ∩ centeredCube (d+1) R
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
  have hS : MeasurableSet S := hE.inter (measurableSet_centeredCube _ _)
  have hP := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
  change volume S = _
  rw [← hP.measure_preimage hS.nullMeasurableSet]
  change (volume.prod volume) (e ⁻¹' S) = _
  rw [Measure.prod_apply_symm (e.measurable hS), ← lintegral_indicator (measurableSet_centeredCube _ _)]
  apply lintegral_congr
  intro y
  have hf (t : ℝ) : (t,y) ∈ e ⁻¹' S ↔ Fin.cons t y ∈ E ∧
      t ∈ Icc (-(R/2)) (R/2) ∧ y ∈ centeredCube d R := by
    simp [e, S, centeredCube, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv, Fin.forall_fin_succ, and_assoc]
  by_cases hy : y ∈ centeredCube d R
  · rw [Set.indicator_of_mem hy]
    congr 1
    ext t
    simpa [hy, and_comm] using hf t
  · rw [Set.indicator_of_notMem hy]
    have hempty : (fun t : ℝ => (t,y)) ⁻¹' (e ⁻¹' S) = ∅ := by
      ext t
      simpa [hy] using hf t
    simp [hempty]

/-- A slice error bounded in absolute value by C gives an error at most C/R
in the density ratio, uniformly in the remaining d coordinates. -/
theorem cubeRatio_slice_bound {d : ℕ} {E : Set (Point (d+1))} (hE : MeasurableSet E)
    {R a C : ℝ} (hR : 0 < R) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hs : ∀ y : Point d, |volume.real (Icc (-(R/2)) (R/2) ∩
      {t : ℝ | Fin.cons t y ∈ E}) - a * R| ≤ C) :
    |cubeRatio E R - a| ≤ C / R := by
  let B := centeredCube d R
  let f (y : Point d) := volume (Icc (-(R/2)) (R/2) ∩ {t : ℝ | Fin.cons t y ∈ E})
  have hfin (y) : f y ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt (by simp : volume (Icc (-(R/2)) (R/2)) < ⊤)).ne
  have hfs (y) : a * R - C ≤ (f y).toReal ∧ (f y).toReal ≤ a * R + C := by
    have h := abs_le.mp (hs y)
    change -C ≤ (f y).toReal - a * R ∧ (f y).toReal - a * R ≤ C at h
    constructor <;> linarith
  have hlow (y) : ENNReal.ofReal (a*R-C) ≤ f y := by
    simpa [ENNReal.ofReal_toReal (hfin y)] using ENNReal.ofReal_le_ofReal (hfs y).1
  have hupp (y) : f y ≤ ENNReal.ofReal (a*R+C) := by
    simpa [ENNReal.ofReal_toReal (hfin y)] using ENNReal.ofReal_le_ofReal (hfs y).2
  have hm (b : ℝ) : (∫⁻ _ : Point d in B, ENNReal.ofReal b) =
      ENNReal.ofReal b * ENNReal.ofReal R ^ d := by
    simp [B, volume_centeredCube]
  have hlo := lintegral_mono (μ := volume.restrict B) hlow
  have hhi := lintegral_mono (μ := volume.restrict B) hupp
  rw [hm] at hlo
  rw [hm] at hhi
  have hint : (∫⁻ y in B, f y) ≠ ⊤ := (hhi.trans_lt (by finiteness)).ne
  have hlo' := ENNReal.toReal_mono hint hlo
  have hhi' := ENNReal.toReal_mono (by finiteness) hhi
  have hh : 0 ≤ a * R + C := by positivity
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le,
    ENNReal.toReal_ofReal hh] at hlo' hhi'
  have htr : a*R-C ≤ (ENNReal.ofReal (a*R-C)).toReal := by
    by_cases hx : 0 ≤ a*R-C
    · rw [ENNReal.toReal_ofReal hx]
    · exact (le_of_not_ge hx).trans ENNReal.toReal_nonneg
  have hlo'' := mul_le_mul_of_nonneg_right htr (pow_nonneg hR.le d)
  change |(volume (E ∩ centeredCube (d+1) R)).toReal / R ^ (d+1) - a| ≤ C/R
  rw [volume_cube_by_slices hE]
  change |(∫⁻ y in B, f y).toReal / R ^ (d+1) - a| ≤ C/R
  have hpos := pow_pos hR d
  have hd := pow_pos hR (d+1)
  apply abs_le.mpr
  constructor
  · apply (le_sub_iff_add_le.mpr ?_)
    apply (le_div_iff₀ hd).mpr
    calc
      _ = (a*R-C)*R^d := by rw [pow_succ]; field_simp; ring
      _ ≤ _ := hlo''.trans hlo'
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ hd).mpr
    calc
      _ ≤ _ := hhi'
      _ = _ := by rw [pow_succ]; field_simp; ring

theorem hasDensity_of_uniform_slices {d : ℕ} {E : Set (Point (d+1))}
    (hE : MeasurableSet E) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hs : ∀ R : ℝ, 0 < R → ∀ y : Point d, |volume.real (Icc (-(R/2)) (R/2) ∩
      {t : ℝ | Fin.cons t y ∈ E}) - a * R| ≤ C) : HasDensity E a := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlim : Tendsto (fun R : ℝ => C/R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [hlim.eventually_lt_const hε, eventually_gt_atTop (0:ℝ)] with R hδ hR
  exact (cubeRatio_slice_bound hE hR hC ha (hs _ hR)).trans_lt hδ

end Density
