module

public import Density.Cubes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Density of the stripe set of Theorem 3

We evaluate each one-dimensional slice on a cube of integer side length exactly
using the integral of a periodic function. Fubini then gives its volume as
the width of the stripe times the volume of the cube.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace Density

def stripes (d : ℕ) (a : ℝ) : Set (Point d) :=
  {x | Int.fract (∑ i, x i) < a}

theorem measurableSet_stripes (d : ℕ) (a : ℝ) : MeasurableSet (stripes d a) := by
  apply measurableSet_lt _ measurable_const
  exact measurable_fract.comp (Finset.measurable_fun_sum _ (fun i _ => measurable_pi_apply i))

private def strip (a : ℝ) : Set ℝ := {t | Int.fract t < a}

private theorem strip_measurable (a : ℝ) : MeasurableSet (strip a) :=
  measurableSet_lt measurable_fract measurable_const

private noncomputable def pulse (a : ℝ) : ℝ → ℝ := (strip a).indicator (fun _ => 1)

private theorem pulse_periodic (a : ℝ) : Function.Periodic (pulse a) 1 := by
  intro x
  by_cases h : Int.fract x < a <;> simp [pulse, Set.indicator, strip, Int.fract_add_one, h]

private theorem pulse_intervalIntegrable (a u v : ℝ) :
    IntervalIntegrable (pulse a) volume u v := by
  rw [intervalIntegrable_iff]
  exact (intervalIntegrable_const (c := (1 : ℝ)) (a := u) (b := v) (μ := volume)).def'.integrable.indicator
    (strip_measurable a)

private theorem pulse_unit {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∫ t in (0 : ℝ)..1, pulse a t = a := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Ico_eq_integral_Ioc]
  change ∫ t in Ico (0 : ℝ) 1, (strip a).indicator (fun _ => (1 : ℝ)) t = a
  rw [setIntegral_indicator (strip_measurable a)]
  have h : Ico (0 : ℝ) 1 ∩ strip a = Ico 0 a := by
    ext t
    constructor
    · rintro ⟨ht, hta⟩
      exact ⟨ht.1, by simpa [strip, Int.fract_eq_self.2 ht] using hta⟩
    · intro ht
      have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_le ha₁⟩
      exact ⟨ht', by simpa [strip, Int.fract_eq_self.2 ht'] using ht.2⟩
  simp [h, Real.volume_real_Ico_of_le ha₀]

/-- The slice volume is independent of both the left endpoint and the phase shift. -/
theorem stripe_slice (s L a : ℝ) (N : ℕ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    volume.real (Icc L (L + N) ∩ {t : ℝ | Int.fract (t + s) < a}) = N * a := by
  have hm : MeasurableSet {t : ℝ | Int.fract (t + s) < a} :=
    (strip_measurable a).preimage (measurable_id.add_const s)
  have h₁ : ∫ t in L..L + (N : ℝ), pulse a (t + s) =
      volume.real (Icc L (L + N) ∩ {t : ℝ | Int.fract (t + s) < a}) := by
    rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right (Nat.cast_nonneg N) : L ≤ L + (N : ℝ)),
      ← integral_Icc_eq_integral_Ioc]
    change ∫ t in Icc L (L + N), ({t : ℝ | Int.fract (t + s) < a} : Set ℝ).indicator
      (fun _ => (1 : ℝ)) t = _
    rw [setIntegral_indicator hm, setIntegral_const]
    simp
  rw [← h₁, intervalIntegral.integral_comp_add_right]
  have hg := (pulse_periodic a).intervalIntegral_add_zsmul_eq (N : ℤ) (L + s)
    (pulse_intervalIntegrable a)
  simp only [zsmul_eq_mul, Int.cast_natCast, mul_one] at hg
  rw [show L + (N : ℝ) + s = L + s + N by ring, hg,
    (pulse_periodic a).intervalIntegral_add_eq (L + s) 0, zero_add, pulse_unit ha₀ ha₁]

private theorem volume_stripes_cube (d N : ℕ) (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    volume (stripes (d+1) a ∩ centeredCube (d+1) N) =
      ENNReal.ofReal (N * a) * ENNReal.ofReal N ^ d := by
  let S := stripes (d+1) a ∩ centeredCube (d+1) N
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
  have hS : MeasurableSet S := (measurableSet_stripes _ _).inter (measurableSet_centeredCube _ _)
  have hE := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
  change volume S = _
  rw [← hE.measure_preimage hS.nullMeasurableSet]
  change (volume.prod volume) (e ⁻¹' S) = _
  rw [Measure.prod_apply_symm (e.measurable hS)]
  have hs (y : Point d) :
      volume ((fun t : ℝ => (t,y)) ⁻¹' (e ⁻¹' S)) =
        (centeredCube d N).indicator (fun _ => ENNReal.ofReal (N * a)) y := by
    have hslice (t : ℝ) : (t,y) ∈ e ⁻¹' S ↔
        (Int.fract (t + ∑ i, y i) < a ∧ t ∈ Icc (-((N : ℝ)/2)) (N/2) ∧ y ∈ centeredCube d N) := by
      simp [S, e, stripes, centeredCube, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.sum_univ_succ, Fin.forall_fin_succ, and_assoc]
    by_cases hy : y ∈ centeredCube d N
    · rw [Set.indicator_of_mem hy]
      have heq : ((fun t : ℝ => (t,y)) ⁻¹' (e ⁻¹' S)) =
          Icc (-((N : ℝ)/2)) (N/2) ∩ {t | Int.fract (t + ∑ i, y i) < a} := by
        ext t
        simpa [hy, and_comm] using hslice t
      rw [heq]
      have hvol := stripe_slice (∑ i, y i) (-((N : ℝ)/2)) a N ha₀ ha₁
      have hend : -((N : ℝ)/2) + N = N/2 := by ring
      rw [hend] at hvol
      rw [← hvol, measureReal_def, ENNReal.ofReal_toReal]
      exact (measure_mono Set.inter_subset_left).trans_lt (by simp) |>.ne
    · have hempty : ((fun t : ℝ => (t,y)) ⁻¹' (e ⁻¹' S)) = ∅ := by
        ext t
        simpa [hy] using hslice t
      simp [hempty, hy]
  simp_rw [hs]
  rw [lintegral_indicator_const (measurableSet_centeredCube _ _), volume_centeredCube]

theorem hasDensity_stripes {d : ℕ} (hd : 1 ≤ d) {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    HasDensity (stripes d a) a := by
  cases d with
  | zero => omega
  | succ d =>
    apply hasDensity_of_integer_volumes
    intro N _
    rw [measureReal_def, volume_stripes_cube d N a ha₀ ha₁, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
    ring

end Density
