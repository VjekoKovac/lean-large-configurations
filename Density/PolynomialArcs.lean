module

public import Density.Polynomial
public import Density.Annular

/-! # Passing the polynomial progression to the annular construction

Section 3 samples natural indices and omits the constant coefficient.
Section 2 uses integer indices and allows a constant coefficient. The inclusion
of the naturals into the integers preserves cardinality. Subtracting the
constant coefficient from the test arc reconciles the two polynomials.
-/

public section

open Filter
open scoped BigOperators

namespace Density.Polynomial

/-- The integer configuration used in Section 2. -/
@[expose] def intPattern (P : Finset ℕ) : Finset ℤ :=
  P.map ⟨Int.ofNat, Int.ofNat_injective⟩

@[simp] theorem card_intPattern (P : Finset ℕ) : (intPattern P).card = P.card :=
  Finset.card_map _

theorem annular_hits_of_phase {m : ℕ} {P : Finset ℕ} {A ε : ℝ}
    (h : ∀ (B : Fin m → ℝ) (u : ℝ), ∃ k ∈ P, ∃ z : ℤ,
      u < phase (m + 1) A B k - z ∧ phase (m + 1) A B k - z < u + ε) :
    Annular.HitsArcs (m + 1) (intPattern P) A ε := by
  intro B u
  obtain ⟨k, hk, z, hl, hr⟩ := h (fun i => B (i.val + 1)) (u - B 0)
  refine ⟨(k : ℤ), Finset.mem_map.mpr ⟨k, hk, rfl⟩, z, ?_⟩
  simp only [Int.cast_natCast]
  have hsum : (∑ l ∈ Finset.range (m+1), B l * (k : ℝ) ^ l) =
      (∑ i : Fin m, B (i.val + 1) * (k : ℝ) ^ (i.val + 1)) + B 0 := by
    rw [Finset.sum_range_succ']
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => B (i + 1) * (k : ℝ) ^ (i + 1))]
    simp
  rw [hsum]
  dsimp [phase] at hl hr
  constructor <;> linarith

/-- The uniform discrepancy estimate for positive integer degrees delivers
exactly the polynomial input used by the remainder of the proof. -/
theorem eventual_annular_pattern_of_discrepancy {p s : ℕ} {C : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C)
    (hD : ∀ᶠ n : ℕ in atTop, ∃ (Q : ℕ) (A : ℝ), n ≤ Q ∧ Q ≤ n ^ s ∧
      discrepancyLE (p-1) p Q A (C * (Real.log n / n))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∃ (P : Finset ℤ) (A : ℝ),
      P.card = n ∧ Annular.HitsArcs p P A (K * (Real.log n / n)) := by
  cases p with
  | zero => omega
  | succ m =>
    obtain ⟨K, hK, h⟩ := eventual_hitting_of_discrepancy hC hD
    refine ⟨K, hK, ?_⟩
    filter_upwards [h] with n hn
    obtain ⟨P, A, hcard, hhit⟩ := hn
    exact ⟨intPattern P, A, (card_intPattern P).trans hcard, annular_hits_of_phase hhit⟩

end Density.Polynomial
