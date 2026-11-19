module

public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Tactic

@[expose] public section

/-!
# Equality in Clarkson's coordinate inequality

This follows the appendix of Kovač and Santos Sepčić. The two scalar inputs
from mathlib are strict Jensen for real powers at a midpoint and the
superadditivity or subadditivity of a nonnegative real power.
-/

open scoped BigOperators

namespace Density

/-- Sum of the p-th powers of absolute coordinates. -/
noncomputable def powerMass {d : ℕ} (p : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ i, |x i| ^ p

private noncomputable def scalarGap (p a b : ℝ) : ℝ :=
  |a + b| ^ p + |a - b| ^ p - 2 * (|a| ^ p + |b| ^ p)

private lemma sq_rpow_half (x p : ℝ) : (x ^ 2) ^ (p / 2) = |x| ^ p := by
  calc
    (x ^ 2) ^ (p / 2) = (|x| ^ (2 : ℝ)) ^ (p / 2) := by rw [Real.rpow_two, sq_abs]
    _ = |x| ^ (2 * (p / 2)) := (Real.rpow_mul (abs_nonneg x) _ _).symm
    _ = |x| ^ p := by rw [show 2 * (p / 2) = p by ring]

private lemma scalarGap_strict {p a b : ℝ} (hp : 1 < p) (hp₂ : p ≠ 2)
    (ha : a ≠ 0) (hb : b ≠ 0) : 0 < (p - 2) * scalarGap p a b := by
  have hd : (a + b) ^ 2 ≠ (a - b) ^ 2 := by
    intro h
    exact (mul_ne_zero ha hb) (by nlinarith only [h])
  have hmid : (1 / 2 : ℝ) * (a + b) ^ 2 + 1 / 2 * (a - b) ^ 2 = a ^ 2 + b ^ 2 := by ring
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hon : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  rcases lt_or_gt_of_ne hp₂ with hsmall | hlarge
  · have hq₀ : 0 < p / 2 := by linarith
    have hq₁ : p / 2 < 1 := by linarith
    have hj := (Real.strictConcaveOn_rpow hq₀ hq₁).2
      (show (a + b) ^ 2 ∈ Set.Ici (0 : ℝ) from sq_nonneg _)
      (show (a - b) ^ 2 ∈ Set.Ici (0 : ℝ) from sq_nonneg _) hd hhalf hhalf hon
    simp only [smul_eq_mul, hmid, sq_rpow_half] at hj
    have hs := Real.rpow_add_le_add_rpow (sq_nonneg a) (sq_nonneg b) hq₀.le hq₁.le
    rw [sq_rpow_half, sq_rpow_half] at hs
    apply mul_pos_of_neg_of_neg (by linarith)
    unfold scalarGap
    linarith
  · have hq : 1 < p / 2 := by linarith
    have hj := (strictConvexOn_rpow hq).2
      (show (a + b) ^ 2 ∈ Set.Ici (0 : ℝ) from sq_nonneg _)
      (show (a - b) ^ 2 ∈ Set.Ici (0 : ℝ) from sq_nonneg _) hd hhalf hhalf hon
    simp only [smul_eq_mul, hmid, sq_rpow_half] at hj
    have hs := Real.add_rpow_le_rpow_add (sq_nonneg a) (sq_nonneg b) hq.le
    rw [sq_rpow_half, sq_rpow_half] at hs
    apply mul_pos (by linarith)
    unfold scalarGap
    linarith

private lemma scalarGap_axis {p a b : ℝ} (hp : 1 < p) (hz : a = 0 ∨ b = 0) :
    scalarGap p a b = 0 := by
  have hp₀ : p ≠ 0 := by linarith
  rcases hz with rfl | rfl <;> simp [scalarGap, Real.zero_rpow hp₀] <;> ring

/-- The vector equality case, including both ranges of the exponent. -/
theorem clarkson_eq_iff {d : ℕ} {p : ℝ} (hp : 1 < p) (hp₂ : p ≠ 2)
    (x y : Fin d → ℝ) :
    powerMass p (x + y) + powerMass p (x - y) = 2 * (powerMass p x + powerMass p y) ↔
      ∀ i, x i = 0 ∨ y i = 0 := by
  classical
  have hsum : (∑ i, scalarGap p (x i) (y i)) =
      powerMass p (x + y) + powerMass p (x - y) - 2 * (powerMass p x + powerMass p y) := by
    simp only [scalarGap, powerMass, Pi.add_apply, Pi.sub_apply, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum]
  constructor
  · intro h i
    have hs : ∑ j, (p - 2) * scalarGap p (x j) (y j) = 0 := by
      rw [← Finset.mul_sum, hsum, h, sub_self, mul_zero]
    have hn (j : Fin d) : 0 ≤ (p - 2) * scalarGap p (x j) (y j) := by
      by_cases hx : x j = 0
      · rw [scalarGap_axis hp (Or.inl hx), mul_zero]
      by_cases hy : y j = 0
      · rw [scalarGap_axis hp (Or.inr hy), mul_zero]
      exact (scalarGap_strict hp hp₂ hx hy).le
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hs i (Finset.mem_univ i)
    by_contra! hh
    exact (scalarGap_strict hp hp₂ hh.1 hh.2).ne' hz
  · intro h
    have hz : ∑ i, scalarGap p (x i) (y i) = 0 :=
      Finset.sum_eq_zero (fun i _ => scalarGap_axis hp (h i))
    exact sub_eq_zero.mp (hsum ▸ hz)

/-- In dimension d, disjoint supports of d nonzero vectors are singletons.
The equivalence records which row uses which coordinate. -/
theorem singleton_supports {d : ℕ} (v : Fin d → Fin d → ℝ)
    (hn : ∀ i, ∃ j, v i j ≠ 0)
    (hd : ∀ i k, i ≠ k → ∀ j, v i j = 0 ∨ v k j = 0) :
    ∃ e : Fin d ≃ Fin d, ∀ i j, v i j ≠ 0 ↔ j = e i := by
  classical
  choose f hf using hn
  have inj : Function.Injective f := by
    intro i k h
    by_contra hik
    rcases hd i k hik (f i) with hz | hz
    · exact hf i hz
    · exact hf k (h ▸ hz)
  let e := Equiv.ofBijective f inj.bijective_of_finite
  refine ⟨e, ?_⟩
  intro i j
  constructor
  · intro hij
    obtain ⟨k, hk⟩ := e.surjective j
    have hik : i = k := by
      by_contra hne
      rcases hd i k hne j with hz | hz
      · exact hij hz
      · rw [← hk] at hz
        exact hf k hz
    simpa [hik] using hk.symm
  · rintro rfl
    exact hf i

/-- A normalized cross consisting of opposite axis pairs has signed coordinate
directions. The hypotheses are the unit and mutual-distance identities obtained
from the copy after centering and dividing by its scale. -/
theorem unit_axes_of_cross {d : ℕ} {p : ℝ} (hp : 1 < p) (hp₂ : p ≠ 2)
    (v : Fin d → Fin d → ℝ) (hu : ∀ i, powerMass p (v i) = 1)
    (hcross : ∀ i k, i ≠ k →
      powerMass p (v i + v k) = 2 ∧ powerMass p (v i - v k) = 2) :
    ∃ e : Fin d ≃ Fin d, ∀ i, |v i (e i)| = 1 ∧ ∀ j, j ≠ e i → v i j = 0 := by
  classical
  have hp₀ : 0 < p := by linarith
  have hn (i : Fin d) : ∃ j, v i j ≠ 0 := by
    by_contra! hz
    have h := hu i
    simp [powerMass, hz, Real.zero_rpow hp₀.ne'] at h
  have hd (i k : Fin d) (hik : i ≠ k) : ∀ j, v i j = 0 ∨ v k j = 0 := by
    apply (clarkson_eq_iff hp hp₂ _ _).mp
    obtain ⟨hs, ht⟩ := hcross i k hik
    rw [hs, ht, hu i, hu k]
    norm_num
  obtain ⟨e, he⟩ := singleton_supports v hn hd
  refine ⟨e, ?_⟩
  intro i
  have hz (j : Fin d) (h : j ≠ e i) : v i j = 0 := by
    by_contra h'
    exact h ((he i j).mp h')
  refine ⟨?_, hz⟩
  have hs : powerMass p (v i) = |v i (e i)| ^ p := by
    unfold powerMass
    apply Finset.sum_eq_single (e i)
    · intro j _ hj
      simp [hz j hj, Real.zero_rpow hp₀.ne']
    · simp
  apply (Real.strictMonoOn_rpow_Ici_of_exponent_pos hp₀).injOn
    (show |v i (e i)| ∈ Set.Ici (0 : ℝ) from abs_nonneg _)
    (show (1 : ℝ) ∈ Set.Ici 0 from zero_le_one)
  simpa only [Real.one_rpow] using hs.symm.trans (hu i)

end Density
