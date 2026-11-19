module

public import Density.Collinear
public import Density.LpSpace

/-! # Coordinate form of the collinear-copy lemma -/

public section

namespace Density

/-- Lemma 7 for the explicit distance used by the three public statements. -/
theorem collinear_copy_coordinates {d : ℕ} (hd : 1 ≤ d) {p r : ℝ} (hp : 1 < p) (hr : 0 < r)
    (P : Finset ℝ) (y : ℝ → Point d)
    (h : ∀ s ∈ P, ∀ t ∈ P, lpDistance p (y s) (y t) = r * |s - t|) :
    ∃ x v : Point d, lpDistance p v 0 = 1 ∧ ∀ t ∈ P, y t = x + (r * t) • v := by
  let q := ENNReal.ofReal p
  let V := PiLp q (fun _ : Fin d => ℝ)
  have hp0 := lt_trans zero_lt_one hp
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Fact (1 ≤ q) := ⟨by simpa [q] using ENNReal.ofReal_le_ofReal hp.le⟩
  have : StrictConvexSpace ℝ V := strictConvex_piLp_real (by simpa [q, hp0.le] using hp) d
  let z (t : ℝ) : V := WithLp.toLp q (y t)
  have hz (s : ℝ) (hs : s ∈ P) (t : ℝ) (ht : t ∈ P) :
      ‖z s - z t‖ = r * |s - t| := by
    rw [← dist_eq_norm]
    exact (lpDistance_eq_piLp_dist hp0 _ _).symm.trans (h s hs t ht)
  obtain ⟨x, v, hv, hparam⟩ := collinear_copy P z hr hz
  refine ⟨x.ofLp, v.ofLp, ?_, ?_⟩
  · rw [lpDistance_eq_piLp_dist hp0]
    simpa only [WithLp.toLp_ofLp, WithLp.toLp_zero, dist_zero_right] using hv
  · intro t ht
    exact congrArg WithLp.ofLp (hparam t ht)

end Density
