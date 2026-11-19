module

public import Density.Pattern
public import Density.CollinearLp
public import Density.Rigidity

/-! # Images of the axes in the pattern of Theorem 3

The paper applies its collinear-copy lemma first to the long arm and then to
each short arm. On an arm containing the origin, the translation vector is
the image of that same origin. This identifies the center across all arms.
-/

@[expose] public section
open scoped BigOperators

namespace Density

/-- In every positive real exponent, the distance along one coordinate axis
is the ordinary absolute difference of the two labels. -/
theorem lpDistance_axis_same {d : ℕ} {p : ℝ} (hp : 0 < p)
    (i : Fin d) (s t : ℝ) :
    lpDistance p (axisPoint i s) (axisPoint i t) = |s - t| := by
  classical
  have hsum : ∑ j : Fin d, |axisPoint i s j - axisPoint i t j| ^ p = |s - t| ^ p := by
    calc
      _ = |axisPoint i s i - axisPoint i t i| ^ p := by
        apply Finset.sum_eq_single i
        · intro j _ hj
          simp [axisPoint, hj, Real.zero_rpow hp.ne']
        · simp
      _ = _ := by simp [axisPoint]
  simpa only [lpDistance, hsum, one_div] using Real.rpow_rpow_inv (abs_nonneg (s - t)) hp.ne'

/-- For a scaled isometry restricted to a point pattern, the images of any
one of its coordinate arms through zero have a common unit direction. -/
theorem affine_axis_of_copy {d : ℕ} {p r : ℝ} (hp : 1 < p) (hr : 0 < r)
    (P : Finset (Point (d+1))) (F : Point (d+1) → Point (d+1))
    (hdist : ∀ x ∈ P, ∀ y ∈ P, lpDistance p (F x) (F y) = r * lpDistance p x y)
    (i : Fin (d+1)) (Q : Finset ℝ) (hzero : 0 ∈ Q)
    (hsub : ∀ t ∈ Q, axisPoint i t ∈ P) :
    ∃ v : Point (d+1), powerMass p v = 1 ∧
      ∀ t ∈ Q, F (axisPoint i t) = F 0 + (r * t) • v := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  let y (t : ℝ) := F (axisPoint i t)
  have hy : ∀ s ∈ Q, ∀ t ∈ Q, lpDistance p (y s) (y t) = r * |s - t| := by
    intro s hs t ht
    exact (hdist _ (hsub s hs) _ (hsub t ht)).trans
      (congrArg (r * ·) (lpDistance_axis_same hp0 i s t))
  obtain ⟨x, v, hv, h⟩ := collinear_copy_coordinates (by omega) hp hr Q y hy
  have hx : x = F 0 := by simpa [y, axisPoint_zero] using (h 0 hzero).symm
  refine ⟨v, ?_, ?_⟩
  · have hpow := congrArg (fun z : ℝ => z ^ p) hv
    simpa only [lpDistance, powerMass, Pi.zero_apply, sub_zero, one_div,
      Real.rpow_inv_rpow (by positivity : 0 ≤ ∑ j, |v j| ^ p) hp0.ne',
      Real.one_rpow] using hpow
  · intro t ht
    simpa only [y, hx] using h t ht

end Density
