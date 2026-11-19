module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

/-! # The positive half-line slice estimate

For a power `p` and a prefix arc `[0,a)`, the m-th component has endpoints
`m^(1/p)` and `(m+a)^(1/p)`. Concavity bounds a component length below by
`a` times the current period length and above by `a` times the preceding
period length. Summing both inequalities telescopes. This implements the
cell decomposition of the appendix with secant inequalities in place of its
mean-value estimate.
-/

@[expose] public noncomputable section
open Finset Set MeasureTheory
open scoped BigOperators

namespace Density.PowerSlices

/-- The union of the first N complete components for the exponent q = 1/p. -/
def cells (q a : ℝ) (N : ℕ) : Set ℝ :=
  ⋃ m ∈ range N, Ico ((m : ℝ) ^ q) (((m : ℝ) + a) ^ q)

theorem cell_lengths {q a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) (ha' : a ≤ 1) (N : ℕ) :
    volume.real (cells q a N) =
      ∑ m ∈ range N, (((m : ℝ) + a) ^ q - (m : ℝ) ^ q) := by
  have hsep {i j : ℕ} (hij : i < j) :
      ((i : ℝ) + a) ^ q ≤ (j : ℝ) ^ q := by
    apply Real.rpow_le_rpow (by positivity) _ hq
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hij)
    linarith
  unfold cells
  rw [measureReal_biUnion_finset (h := fun _ _ => measure_Ico_lt_top.ne) ?_ ?_]
  · apply sum_congr rfl
    intro m _
    apply Real.volume_real_Ico_of_le
    exact Real.rpow_le_rpow (by positivity) (by linarith) hq
  · intro i _ j _ hne
    apply Set.disjoint_left.mpr
    intro t hi hj
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact (not_lt_of_ge (le_trans (hsep hij) hj.1)) hi.2
    · exact (not_lt_of_ge (le_trans (hsep hji) hi.1)) hj.2
  · exact fun _ _ => measurableSet_Ico

private theorem current_period_lower {q a : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (m : ℕ) :
    a * (((m : ℝ) + 1) ^ q - (m : ℝ) ^ q) ≤
      ((m : ℝ) + a) ^ q - (m : ℝ) ^ q := by
  have h := (Real.concaveOn_rpow hq hq').2
    (x := (m : ℝ)) (y := (m : ℝ) + 1)
    (show (m : ℝ) ∈ Set.Ici 0 by exact Nat.cast_nonneg m)
    (show (m : ℝ) + 1 ∈ Set.Ici 0 by change 0 ≤ _; positivity)
    (show 0 ≤ 1-a by linarith) ha (sub_add_cancel 1 a)
  simp only [smul_eq_mul] at h
  rw [show (1-a) * (m : ℝ) + a * ((m : ℝ) + 1) = (m : ℝ) + a by ring] at h
  linarith

private theorem previous_period_upper {q a : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1)
    (ha : 0 < a) (m : ℕ) :
    ((m : ℝ) + 1 + a) ^ q - ((m : ℝ) + 1) ^ q ≤
      a * (((m : ℝ) + 1) ^ q - (m : ℝ) ^ q) := by
  have h := (Real.concaveOn_rpow hq hq').slope_anti_adjacent
    (x := (m : ℝ)) (y := (m : ℝ) + 1) (z := (m : ℝ) + 1 + a)
    (show (m : ℝ) ∈ Set.Ici 0 by exact Nat.cast_nonneg m)
    (show (m : ℝ) + 1 + a ∈ Set.Ici 0 by change 0 ≤ _; positivity) (by linarith) (by linarith)
  simp only [add_sub_cancel_left, div_one] at h
  have ht := (div_le_iff₀ ha).mp h
  linarith

/-- At a full-period endpoint the discrepancy in length is at most one. -/
theorem complete_periods {q a : ℝ} (hq : 0 < q) (hq' : q ≤ 1)
    (ha : 0 < a) (ha' : a ≤ 1) (N : ℕ) :
    a * (N : ℝ) ^ q ≤ volume.real (cells q a N) ∧
    volume.real (cells q a N) ≤ a * (N : ℝ) ^ q + 1 := by
  let S (n : ℕ) := ∑ m ∈ range n, (((m : ℝ) + a) ^ q - (m : ℝ) ^ q)
  have addCell (n : ℕ) : S (n+1) = S n + (((n : ℝ) + a) ^ q - (n : ℝ) ^ q) :=
    sum_range_succ _ _
  have low (n : ℕ) : a * (n : ℝ) ^ q ≤ S n := by
    induction n with
    | zero => simp [S, Real.zero_rpow hq.ne']
    | succ n ih =>
      rw [addCell, Nat.cast_succ]
      linarith [current_period_lower hq.le hq' ha.le ha' n]
  have high (n : ℕ) : S (n+1) ≤ a ^ q + a * (n : ℝ) ^ q := by
    induction n with
    | zero => simp [S, Real.zero_rpow hq.ne']
    | succ n ih =>
      rw [addCell (n+1), Nat.cast_succ]
      linarith [previous_period_upper hq.le hq' ha n]
  rw [cell_lengths hq.le ha.le ha']
  refine ⟨low N, ?_⟩
  cases N with
  | zero => simp [Real.zero_rpow hq.ne']
  | succ n =>
    have h1 : a ^ q ≤ 1 := by simpa using Real.rpow_le_rpow ha.le ha' hq.le
    have h2 : (n : ℝ) ^ q ≤ ((n : ℝ) + 1) ^ q :=
      Real.rpow_le_rpow (by positivity) (by linarith) hq.le
    rw [Nat.cast_succ]
    linarith [high n, mul_le_mul_of_nonneg_left h2 ha.le]

/-- On the positive half-line, the lifted arc [0,a) modulo one. -/
def prefixSlice (p : ℕ) (a R : ℝ) : Set ℝ :=
  {t | t ∈ Ico 0 R ∧ ∃ m : ℕ, (m : ℝ) ≤ t ^ p ∧ t ^ p < (m : ℝ) + a}

/-- The incomplete final period costs at most one in length. -/
theorem prefix_slice_estimate {p : ℕ} (hp : 1 ≤ p) {a R : ℝ}
    (ha : 0 < a) (ha' : a ≤ 1) (hR : 0 ≤ R) :
    |volume.real (prefixSlice p a R) - a * R| ≤ 2 := by
  let q := (p : ℝ)⁻¹
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : 0 < q := by dsimp [q]; positivity
  have hq' : q ≤ 1 := by simpa [q] using inv_le_one_of_one_le₀ hp'
  have invpow (t : ℝ) (ht : 0 ≤ t) : (t ^ p) ^ q = t :=
    Real.pow_rpow_inv_natCast ht (by omega)
  let N := ⌊R ^ p⌋₊
  have floorLo : (N : ℝ) ≤ R ^ p := Nat.floor_le (pow_nonneg hR _)
  have floorHi : R ^ p < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have lo : (N : ℝ) ^ q ≤ R := invpow R hR ▸
    Real.rpow_le_rpow (Nat.cast_nonneg _) floorLo hq.le
  have hi : R ≤ ((N : ℝ) + 1) ^ q := invpow R hR ▸
    Real.rpow_le_rpow (pow_nonneg hR _) floorHi.le hq.le
  have step : ((N : ℝ) + 1) ^ q ≤ (N : ℝ) ^ q + 1 := by
    simpa using Real.rpow_add_le_add_rpow (Nat.cast_nonneg N) (show (0 : ℝ) ≤ 1 by norm_num) hq.le hq'
  have first : cells q a N ⊆ prefixSlice p a R := by
    intro t ht
    obtain ⟨m, hm, hm'⟩ := (by simpa only [cells, mem_iUnion, exists_prop] using ht :
      ∃ m ∈ range N, t ∈ Ico ((m : ℝ) ^ q) (((m : ℝ) + a) ^ q))
    have ht0 : 0 ≤ t := le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hm'.1
    have hmN : (m : ℝ) + 1 ≤ N := by exact_mod_cast mem_range.mp hm
    have end_le : ((m : ℝ) + a) ^ q ≤ (N : ℝ) ^ q :=
      Real.rpow_le_rpow (by positivity) (by linarith) hq.le
    refine ⟨⟨ht0, hm'.2.trans_le (end_le.trans lo)⟩, m, ?_, ?_⟩
    · apply (Real.rpow_le_rpow_iff (Nat.cast_nonneg m) (pow_nonneg ht0 _) hq).mp
      rw [invpow t ht0]
      exact hm'.1
    · apply (Real.rpow_lt_rpow_iff (pow_nonneg ht0 _) (by positivity) hq).mp
      rw [invpow t ht0]
      exact hm'.2
  have last : prefixSlice p a R ⊆ cells q a (N+1) := by
    rintro t ⟨ht, m, hm, hm'⟩
    have hle : (m : ℝ) ≤ R ^ p := hm.trans (pow_le_pow_left₀ ht.1 ht.2.le _)
    have hmN : m < N+1 := by exact_mod_cast hle.trans_lt floorHi
    refine mem_iUnion.mpr ⟨m, mem_iUnion.mpr ⟨mem_range.mpr hmN, ?_⟩⟩
    constructor
    · rw [← invpow t ht.1]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) hm hq.le
    · rw [← invpow t ht.1]
      exact Real.rpow_lt_rpow (pow_nonneg ht.1 _) hm' hq
  have low := (complete_periods hq hq' ha ha' N).1.trans
    (measureReal_mono (μ := volume) first
      (measure_ne_top_of_subset (fun _ h => h.1 : prefixSlice p a R ⊆ Ico 0 R) measure_Ico_lt_top.ne))
  have high := (measureReal_mono (μ := volume) last
    (by
      unfold cells
      apply (measure_biUnion_lt_top (range (N+1)).finite_toSet ?_).ne
      exact fun _ _ => measure_Ico_lt_top)).trans (complete_periods hq hq' ha ha' (N+1)).2
  rw [Nat.cast_add_one] at high
  apply abs_le.mpr
  constructor
  · linarith [mul_le_mul_of_nonneg_left (hi.trans step) ha.le]
  · linarith [mul_le_mul_of_nonneg_left step ha.le, mul_le_mul_of_nonneg_left lo ha.le]

/-- Upper endpoints of test arcs are excluded to allow subtraction of cumulative lengths. -/
theorem prefixSlice_eq_fract {p : ℕ} {a R : ℝ} (ha : a ≤ 1) :
    prefixSlice p a R = Ico 0 R ∩ {t : ℝ | Int.fract (t ^ p) < a} := by
  ext t
  constructor
  · rintro ⟨ht, m, hm, hm'⟩
    have hf : ⌊t ^ p⌋ = (m : ℤ) := Int.floor_eq_iff.mpr (by
      push_cast
      exact ⟨hm, by linarith⟩)
    refine ⟨ht, ?_⟩
    change t ^ p - (⌊t ^ p⌋ : ℝ) < a
    rw [hf]
    push_cast
    linarith
  · rintro ⟨ht, hf⟩
    have ht0 := pow_nonneg ht.1 p
    refine ⟨ht, ⌊t^p⌋₊, Nat.floor_le ht0, ?_⟩
    rw [natCast_floor_eq_intCast_floor ht0]
    change t ^ p - (⌊t ^ p⌋ : ℝ) < a at hf
    linarith

theorem prefix_slice_estimate_nonneg {p : ℕ} (hp : 1 ≤ p) {a R : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hR : 0 ≤ R) :
    |volume.real (prefixSlice p a R) - a * R| ≤ 2 := by
  rcases ha.eq_or_lt with h | h
  · subst a
    rw [prefixSlice_eq_fract (by norm_num)]
    have hempty : {t : ℝ | Int.fract (t ^ p) < 0} = ∅ := by
      ext t
      simp [Int.fract_nonneg]
    simp [hempty]
  · exact prefix_slice_estimate hp h ha' hR

/-- Uniform estimate on every half-open arc staying inside [0,1]. -/
theorem interval_slice_estimate {p : ℕ} (hp : 1 ≤ p) {a b R : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hR : 0 ≤ R) :
    |volume.real (Ico 0 R ∩ {t : ℝ | Int.fract (t ^ p) ∈ Ico a b}) - (b-a) * R| ≤ 4 := by
  have eq : Ico 0 R ∩ {t : ℝ | Int.fract (t ^ p) ∈ Ico a b} =
      prefixSlice p b R \ prefixSlice p a R := by
    rw [prefixSlice_eq_fract hb, prefixSlice_eq_fract (hab.trans hb)]
    ext t
    simp only [mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff]
    change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ ¬ (_ ∧ _))
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact ⟨⟨h1,h3⟩, fun h => (not_lt.mpr h2) h.2⟩
    · rintro ⟨⟨h1,h2⟩, h3⟩
      exact ⟨h1, not_lt.mp (fun h => h3 ⟨h1,h⟩), h2⟩
  have sub : prefixSlice p a R ⊆ prefixSlice p b R := by
    rintro t ⟨ht, m, hl, hu⟩
    exact ⟨ht, m, hl, by linarith⟩
  have meas : MeasurableSet (prefixSlice p a R) := by
    rw [prefixSlice_eq_fract (hab.trans hb)]
    refine measurableSet_Ico.inter ?_
    exact measurableSet_lt ((measurable_id.pow_const p).fract) measurable_const
  rw [eq, measureReal_sdiff sub meas
    (measure_ne_top_of_subset (fun _ h => h.1 : prefixSlice p b R ⊆ Ico 0 R) measure_Ico_lt_top.ne)]
  have ha0 := abs_le.mp (prefix_slice_estimate_nonneg hp ha (hab.trans hb) hR)
  have hb0 := abs_le.mp (prefix_slice_estimate_nonneg hp (ha.trans hab) hb hR)
  apply abs_le.mpr
  constructor <;> linarith

end Density.PowerSlices
