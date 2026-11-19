module

public import Density.Definitions
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

/-! # Finite-dimensional strict convexity for Lemma 7

The proof uses Mathlib's scalar strict convexity of real powers, its sum
formula for the PiLp norm, and its unit-sphere criterion for a strictly
convex space. -/

@[expose] public section
open scoped BigOperators ENNReal

namespace Density

/-- The coordinate formula from the public statements is Mathlib's PiLp distance. -/
theorem lpDistance_eq_piLp_dist {d : ℕ} {p : ℝ} (hp : 0 < p) (x y : Point d) :
    lpDistance p x y =
      dist (WithLp.toLp (ENNReal.ofReal p) x : PiLp (ENNReal.ofReal p) (fun _ : Fin d => ℝ))
           (WithLp.toLp (ENNReal.ofReal p) y) := by
  have hreal := ENNReal.toReal_ofReal hp.le
  rw [PiLp.dist_eq_sum (hreal.symm ▸ hp)]
  simp only [lpDistance, hreal, Real.dist_eq]

private theorem abs_midpoint_rpow_lt {p a b : ℝ} (hp : 1 < p) (hab : a ≠ b) :
    |(1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b| ^ p <
      (1 / 2 : ℝ) * |a| ^ p + (1 / 2 : ℝ) * |b| ^ p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  by_cases h : |a| = |b|
  · have heq := (abs_eq_abs.mp h).resolve_left hab
    have hb : b ≠ 0 := by
      intro hzero
      apply hab
      simpa [hzero] using heq
    rw [heq]
    rw [show (1 / 2 : ℝ) * (-b) + (1 / 2 : ℝ) * b = 0 by ring]
    rw [abs_zero, Real.zero_rpow hp0.ne', abs_neg]
    have hpow := Real.rpow_pos_of_pos (abs_pos.mpr hb) p
    linarith
  · have htri :
        |(1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b| ≤
          (1 / 2 : ℝ) * |a| + (1 / 2 : ℝ) * |b| := by
      simpa [abs_mul] using abs_add_le ((1 / 2 : ℝ) * a) ((1 / 2 : ℝ) * b)
    apply (Real.rpow_le_rpow (abs_nonneg _) htri hp0.le).trans_lt
    have hj := (strictConvexOn_rpow hp).2
      (show |a| ∈ Set.Ici (0 : ℝ) from abs_nonneg a)
      (show |b| ∈ Set.Ici (0 : ℝ) from abs_nonneg b) h
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
      (by norm_num)
    simpa only [smul_eq_mul] using hj

/-- Strict convexity of the finite-dimensional real ℓᵖ space for finite p > 1.
We take p in ENNReal to match the index in Mathlib's type synonym. -/
theorem strictConvex_piLp_real {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p.toReal) (d : ℕ) :
    StrictConvexSpace ℝ (PiLp p (fun _ : Fin d => ℝ)) := by
  apply StrictConvexSpace.of_norm_combo_lt_one
  intro x y hx hy hxy
  have hp0 := lt_trans zero_lt_one hp
  have hunit (z : PiLp p (fun _ : Fin d => ℝ)) (hz : ‖z‖ = 1) :
      ∑ i : Fin d, |z i| ^ p.toReal = 1 := by
    have hpow := congrArg (fun t : ℝ => t ^ p.toReal) hz
    rw [PiLp.norm_eq_sum hp0, one_div, Real.rpow_inv_rpow (by positivity) hp0.ne',
      Real.one_rpow] at hpow
    simpa only [Real.norm_eq_abs] using hpow
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! heq
    exact hxy (PiLp.ext heq)
  let a : ℝ := 1 / 2
  have hsum :
      ∑ j : Fin d, |a * x j + a * y j| ^ p.toReal <
        ∑ j : Fin d, (a * |x j| ^ p.toReal + a * |y j| ^ p.toReal) := by
    apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : x j = y j
      · rw [hj]
        have h (u : ℝ) : a * u + a * u = u := by dsimp [a]; ring
        rw [h, h]
      · exact (abs_midpoint_rpow_lt hp hj).le
    · exact ⟨i, Finset.mem_univ _, abs_midpoint_rpow_lt hp hi⟩
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hunit x hx, hunit y hy] at hsum
  have hlt : ∑ j : Fin d, |a * x j + a * y j| ^ p.toReal < 1 := by
    simpa only [mul_one, show a + a = 1 by norm_num [a]] using hsum
  refine ⟨a, a, by norm_num [a], ?_⟩
  rw [PiLp.norm_eq_sum hp0]
  apply Real.rpow_lt_one (by positivity) _ (by positivity)
  simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs] using hlt

end Density
