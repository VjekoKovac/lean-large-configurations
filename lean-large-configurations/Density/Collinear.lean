module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

/-!
# Scaled copies of a finite subset of a line

Lemma 7 of Kovač and Santos Sepčić, arXiv:2604.18544v1. The only geometric
property of the range needed here is strict convexity. We apply Mathlib's
`sameRay_iff_norm_sub` and `SameRay.norm_smul_eq` to the two chords from the
left endpoint. The argument also treats the empty and singleton configurations.
-/

public section

namespace Density

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [StrictConvexSpace ℝ V] [Nontrivial V]

/-- The labels of any scaled isometric copy of a finite real pattern have a
single affine parametrization with a unit direction. Only distances between
labels in the pattern are prescribed. -/
theorem collinear_copy (P : Finset ℝ) (y : ℝ → V) {r : ℝ} (hr : 0 < r)
    (h : ∀ s ∈ P, ∀ t ∈ P, ‖y s - y t‖ = r * |s - t|) :
    ∃ x v : V, ‖v‖ = 1 ∧ ∀ t ∈ P, y t = x + (r * t) • v := by
  classical
  by_cases hcard : 1 < P.card
  · have hP : P.Nonempty := Finset.card_pos.mp (by omega)
    let a := P.min' hP
    let b := P.max' hP
    have ha : a ∈ P := P.min'_mem hP
    have hb : b ∈ P := P.max'_mem hP
    have hab : a < b := P.min'_lt_max'_of_card hcard
    have hD : 0 < r * (b - a) := mul_pos hr (sub_pos.mpr hab)
    have hba : ‖y b - y a‖ = r * (b - a) := by
      rw [h b hb a ha, abs_of_nonneg (sub_nonneg.mpr hab.le)]
    let v := (r * (b - a))⁻¹ • (y b - y a)
    refine ⟨y a - (r * a) • v, v, ?_, ?_⟩
    · change ‖(r * (b - a))⁻¹ • (y b - y a)‖ = 1
      rw [norm_smul_of_nonneg (inv_nonneg.mpr hD.le), hba, inv_mul_cancel₀ hD.ne']
    · intro t ht
      have hat : a ≤ t := P.min'_le t ht
      have htb : t ≤ b := P.le_max' t ht
      have hta : ‖y t - y a‖ = r * (t - a) := by
        rw [h t ht a ha, abs_of_nonneg (sub_nonneg.mpr hat)]
      have hchord : SameRay ℝ (y b - y a) (y t - y a) := by
        apply sameRay_iff_norm_sub.mpr
        rw [sub_sub_sub_cancel_right, h b hb t ht, abs_of_nonneg (sub_nonneg.mpr htb),
          hba, hta, ← mul_sub, abs_of_nonneg (mul_nonneg hr.le (by linarith))]
        ring
      have hratio := hchord.norm_smul_eq
      rw [hba, hta] at hratio
      have htvec : y t - y a = (r * (t - a)) • v := calc
        y t - y a = (r * (b - a))⁻¹ • ((r * (b - a)) • (y t - y a)) :=
          (inv_smul_smul₀ hD.ne' _).symm
        _ = (r * (t - a)) • v := by rw [hratio, smul_comm]
      rw [mul_sub, sub_smul] at htvec
      calc
        y t = y a + (y t - y a) := by abel
        _ = _ := by rw [htvec]; abel
  · obtain ⟨v, hv⟩ := exists_norm_eq V (zero_le_one : (0 : ℝ) ≤ 1)
    obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp (by omega : P.card ≤ 1)
    refine ⟨y a - (r * a) • v, v, hv, ?_⟩
    intro t ht
    have heq : t = a := Finset.mem_singleton.mp (ha ht)
    simp [heq]

end Density
