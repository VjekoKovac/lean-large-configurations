module

public import Density.Annular
public import Density.PowerSlices
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Translated arcs and centered slices

Two intervals in [0,1) suffice for any translated circular arc. Its boundary
has a countable preimage under a nonconstant power on the positive half-line.
-/
@[expose] public noncomputable section
open Set MeasureTheory Filter

namespace Density.PowerSlices

private theorem normalized_arc {a L s : ℝ} (ha : 0 ≤ a) (ha' : a < 1) (hL : L ≤ 1)
    (hs : 0 ≤ s) (hs' : s < 1) :
    (∃ m : ℤ, a + (m : ℝ) ≤ s ∧ s < a + L + m) ↔
      s ∈ Ico a (min 1 (a+L)) ∨ s ∈ Ico 0 (max 0 (a+L-1)) := by
  constructor
  · rintro ⟨m, hm, hm'⟩
    have hm1 : (-2 : ℤ) < m := by exact_mod_cast (show (-2 : ℝ) < (m : ℝ) by linarith)
    have hm2 : m < 1 := by exact_mod_cast (show (m : ℝ) < 1 by linarith)
    rcases (show m = 0 ∨ m = -1 by omega) with rfl | rfl
    · left
      simp only [Int.cast_zero, add_zero] at hm hm'
      exact ⟨hm, lt_min hs' hm'⟩
    · right
      simp only [Int.cast_neg, Int.cast_one] at hm'
      exact ⟨hs, (by linarith : s < a+L-1).trans_le (le_max_right _ _)⟩
  · rintro (h | h)
    · refine ⟨0, ?_, ?_⟩
      · simpa using h.1
      · simpa using lt_of_lt_of_le h.2 (min_le_right _ _)
    · refine ⟨-1, ?_, ?_⟩
      · push_cast; linarith
      · have hf := (lt_max_iff.mp h.2).resolve_left (not_lt.mpr hs)
        push_cast
        linarith

private def part (p : ℕ) (R a b : ℝ) : Set ℝ :=
  Ico 0 R ∩ {t : ℝ | Int.fract (t^p) ∈ Ico a b}

private theorem part_meas (p : ℕ) (R a b : ℝ) : MeasurableSet (part p R a b) :=
  measurableSet_Ico.inter (measurableSet_Ico.preimage (measurable_id.pow_const p).fract)

private theorem part_finite (p : ℕ) (R a b : ℝ) : volume (part p R a b) ≠ ⊤ :=
  measure_ne_top_of_subset inter_subset_left measure_Ico_lt_top.ne

/-- The positive half-line estimate, uniformly in the translate of the arc. -/
theorem positive_band_estimate {p : ℕ} (hp : 1 ≤ p) {ε R : ℝ}
    (hε : 0 < ε) (hε' : ε < 1) (hR : 0 ≤ R) (c : ℝ) :
    |volume.real (Ico 0 R ∩ {t : ℝ | t^p + c ∈ Annular.Band ε}) - (1-ε)*R| ≤ 8 := by
  let L := 1-ε
  let u := -L/2-c
  let a := Int.fract u
  let b := min 1 (a+L)
  let e := max 0 (a+L-1)
  have hL : 0 < L := by dsimp [L]; linarith
  have hL' : L ≤ 1 := by dsimp [L]; linarith
  have ha : 0 ≤ a := Int.fract_nonneg u
  have ha' : a < 1 := Int.fract_lt_one u
  have hab : a ≤ b := le_min ha'.le (by linarith)
  have hb : b ≤ 1 := min_le_left _ _
  have he : 0 ≤ e := le_max_left _ _
  have hea : e ≤ a := max_le ha (by linarith)
  have hlen : b-a+e=L := by
    dsimp [b,e]
    rcases le_total (a+L) 1 with h | h
    · rw [min_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [min_eq_left h, max_eq_right (by linarith)]
      ring
  let boundary : Set ℝ := range (fun m : ℤ => (u+(m : ℝ)) ^ ((p:ℝ)⁻¹))
  have ae : ∀ᵐ t : ℝ ∂volume, t ∉ boundary :=
    compl_mem_ae_iff.mpr ((countable_range _).measure_zero volume)
  have heq : Ico 0 R ∩ {t : ℝ | t^p + c ∈ Annular.Band ε}
      =ᵐ[volume] part p R a b ∪ part p R 0 e := by
    filter_upwards [ae] with t ht
    apply propext
    by_cases hR' : t ∈ Ico 0 R
    · simp only [part, mem_union, mem_inter_iff, hR', true_and, mem_ofPred_eq]
      rw [← normalized_arc ha ha' hL' (Int.fract_nonneg _) (Int.fract_lt_one _)]
      have hu0 : u = a + (⌊u⌋ : ℝ) := (Int.fract_add_floor u).symm
      have ht0 : t^p = Int.fract (t^p) + (⌊t^p⌋ : ℝ) := (Int.fract_add_floor (t^p)).symm
      have huDef : u = -(1-ε)/2-c := rfl
      have hLDef : L = 1-ε := rfl
      constructor
      · rintro ⟨m, hm⟩
        obtain ⟨hl,hu⟩ := abs_lt.mp hm
        refine ⟨m + ⌊u⌋ - ⌊t^p⌋, ?_, ?_⟩ <;>
          simp only [Int.cast_add,Int.cast_sub] <;> linarith only [hu0,ht0,hl,hu,huDef,hLDef]
      · rintro ⟨k, hl,hu⟩
        let m : ℤ := k + ⌊t^p⌋ - ⌊u⌋
        have hml : u + (m : ℝ) ≤ t^p := by dsimp [m]; push_cast; linarith
        have hmu : t^p < u + L + (m : ℝ) := by dsimp [m]; push_cast; linarith
        have hn : u + (m : ℝ) ≠ t^p := by
          intro h
          apply ht
          refine ⟨m, ?_⟩
          change (u + (m : ℝ)) ^ ((p : ℝ)⁻¹) = t
          rw [h, Real.pow_rpow_inv_natCast hR'.1 (by omega)]
        refine ⟨m, abs_lt.mpr ⟨?_, ?_⟩⟩
        · have := lt_of_le_of_ne hml hn
          dsimp [u,L] at this
          linarith
        · dsimp [u,L] at hmu
          linarith
    · simp [part, hR']
  have hd : Disjoint (part p R a b) (part p R 0 e) := by
    apply Set.disjoint_left.mpr
    exact fun t h₁ h₂ => (not_lt_of_ge (hea.trans h₁.2.1)) h₂.2.2
  rw [measureReal_congr heq, measureReal_union hd (part_meas _ _ _ _)
    (part_finite _ _ _ _) (part_finite _ _ _ _)]
  have h₁ := abs_le.mp (interval_slice_estimate hp ha hab hb hR)
  have h₂ := abs_le.mp (interval_slice_estimate hp (le_refl 0) he (hea.trans ha'.le) hR)
  change -4 ≤ volume.real (part p R a b) - (b-a)*R ∧ volume.real (part p R a b) - (b-a)*R ≤ 4 at h₁
  change -4 ≤ volume.real (part p R 0 e) - (e-0)*R ∧ volume.real (part p R 0 e) - (e-0)*R ≤ 4 at h₂
  change |_ - L * R| ≤ 8
  rw [← hlen]
  apply abs_le.mpr
  constructor <;> linarith

private theorem neg_band (ε t : ℝ) : -t ∈ Annular.Band ε ↔ t ∈ Annular.Band ε := by
  have h (v : ℝ) (hv : v ∈ Annular.Band ε) : -v ∈ Annular.Band ε := by
    obtain ⟨m,hm⟩ := hv
    refine ⟨-m, ?_⟩
    rw [Int.cast_neg, show -v - -(m : ℝ) = -(v-(m : ℝ)) by ring, abs_neg]
    exact hm
  exact ⟨fun ht => by simpa using h _ ht, h t⟩

private def half (p : ℕ) (ε R c σ : ℝ) : Set ℝ :=
  Ico 0 R ∩ {t : ℝ | σ*t^p + c ∈ Annular.Band ε}

private theorem half_estimate {p : ℕ} (hp : 1 ≤ p) {ε R : ℝ}
    (hε : 0 < ε) (hε' : ε < 1) (hR : 0 ≤ R) (c : ℝ) {σ : ℝ} (hσ : σ=1 ∨ σ= -1) :
    |volume.real (half p ε R c σ) - (1-ε)*R| ≤ 8 := by
  rcases hσ with rfl | rfl
  · simpa [half] using positive_band_estimate hp hε hε' hR c
  · have eq : half p ε R c (-1) = Ico 0 R ∩ {t : ℝ | t^p + (-c) ∈ Annular.Band ε} := by
      ext t
      simp only [half, mem_inter_iff, mem_ofPred_eq]
      rw [show (-1 : ℝ) * t^p + c = -(t^p + -c) by ring, neg_band]
    rw [eq]
    exact positive_band_estimate hp hε hε' hR (-c)

/-- Lemma 6 for the translated interval used in both parity cases. The
constant 16 is uniform in the real translate, the sign, R and p ≥ 1. -/
theorem centered_band_estimate {p : ℕ} (hp : 1 ≤ p) {ε R : ℝ}
    (hε : 0 < ε) (hε' : ε < 1) (hR : 0 ≤ R) (c : ℝ) (s : Bool) :
    |volume.real (Icc (-(R/2)) (R/2) ∩
        {t : ℝ | Annular.directionSign s * t^p + c ∈ Annular.Band ε}) - (1-ε)*R| ≤ 16 := by
  let H := R / 2
  let σ := Annular.directionSign s
  let U := {t : ℝ | σ * t ^ p + c ∈ Annular.Band ε}
  have meas : MeasurableSet U := (Annular.isOpen_band ε).measurableSet.preimage
    (show Measurable (fun t : ℝ => σ*t^p+c) by fun_prop)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hσ : σ=1 ∨ σ= -1 := by cases s <;> simp [σ, Annular.directionSign]
  have hσ' : σ*(-1)^p=1 ∨ σ*(-1)^p= -1 := by
    rcases hσ with h | h <;> rcases neg_one_pow_eq_or ℝ p with h' | h' <;> simp [h,h']
  have negSlice : (fun t : ℝ => -t) ⁻¹' (Ioc (-H) 0 ∩ U) = half p ε H c (σ*(-1)^p) := by
    ext t
    simp only [mem_preimage, mem_inter_iff, mem_Ioc, U, mem_ofPred_eq, half, mem_Ico]
    rw [neg_lt_neg_iff, neg_nonpos, neg_eq_neg_one_mul t, mul_pow]
    simp only [mul_assoc, and_comm (a := t < H)]
  have negVol : volume.real (Ioc (-H) 0 ∩ U) = volume.real (half p ε H c (σ*(-1)^p)) := by
    rw [←negSlice]
    exact congrArg ENNReal.toReal ((Measure.measurePreserving_neg (volume : Measure ℝ)).measure_preimage
      (measurableSet_Ioc.inter meas).nullMeasurableSet).symm
  have posVol : volume.real (Ioc 0 H ∩ U) = volume.real (half p ε H c σ) :=
    measureReal_congr (ae_eq_set_inter (Ioc_ae_eq_Icc.trans Ico_ae_eq_Icc.symm) .rfl)
  have mid : volume.real (Icc (-H) H ∩ U) =
      volume.real (Ioc (-H) 0 ∩ U) + volume.real (Ioc 0 H ∩ U) := by
    have hIntervals : Icc (-H) H ∩ U =ᵐ[volume] Ioc (-H) H ∩ U :=
      ae_eq_set_inter Ioc_ae_eq_Icc.symm (ae_eq_refl U)
    rw [measureReal_congr hIntervals,
      ← Ioc_union_Ioc_eq_Ioc (neg_nonpos.mpr hH) hH, union_inter_distrib_right]
    apply measureReal_union
    · exact Set.disjoint_left.mpr (fun t ht ht' => (not_lt_of_ge ht.1.2) ht'.1.1)
    · exact measurableSet_Ioc.inter meas
    · exact measure_ne_top_of_subset inter_subset_left measure_Ioc_lt_top.ne
    · exact measure_ne_top_of_subset inter_subset_left measure_Ioc_lt_top.ne
  change |volume.real (Icc (-H) H ∩ U) - (1-ε)*R| ≤ 16
  rw [mid, negVol, posVol]
  have h₁ := abs_le.mp (half_estimate hp hε hε' hH c hσ)
  have h₂ := abs_le.mp (half_estimate hp hε hε' hH c hσ')
  dsimp [H] at h₁ h₂ ⊢
  apply abs_le.mpr
  constructor <;> linarith

end Density.PowerSlices
