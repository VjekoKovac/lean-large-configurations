module

public import Density.Weyl
public import Density.PhasePolynomial

/-! # Uniform cancellation at the chosen prime sample size

The prime denominator and the leading coefficient are chosen before all
lower-order coefficients. The same choice works through the entire Fourier
cutoff used in estimating short arcs.
-/

public section

open Finset Filter

namespace Density.Polynomial

theorem eventual_weyl_samples (p : ℕ) (hp : 1 ≤ p) :
    ∃ s : ℕ, ∀ᶠ n : ℕ in atTop, ∃ Q : ℕ, n ≤ Q ∧ Q ≤ n ^ s ∧
      ∀ (m : ℕ), 1 ≤ m → m ≤ n ^ 4 → ∀ B : Fin (p-1) → ℝ,
        ‖∑ k ∈ range Q, (Real.fourierChar ((m : ℝ) * phase p (1 / (Q : ℝ)) B k) : ℂ)‖ ≤
          (Q : ℝ) * (1 / (n : ℝ) ^ 6) := by
  obtain ⟨s, hs⟩ := weyl_parameters p
  refine ⟨s, ?_⟩
  filter_upwards [hs] with n hn
  obtain ⟨H, Q, hn1, hQ, hnQ, hQs, hsize, hQH, hnum⟩ := hn
  refine ⟨Q, hnQ, hQs, ?_⟩
  intro m hm hm4 B
  obtain ⟨P, hdeg, hc, heval⟩ := exists_frequencyPolynomial hp m Q B
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hbudget : (m : ℤ).natAbs * p.factorial * H ^ (p-1) < Q := by
    simp only [Int.natAbs_natCast]
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hm4)).trans_lt hnum
  have hc' : P.coeff p = ((m : ℤ) : ℝ) / Q := by simpa using hc
  have h := short_shift_weyl hQ hQH hp (T := n^6) (by positivity)
    hsize (m : ℤ) hm' hbudget P hdeg hc'
  have bound := (div_le_iff₀ (by exact_mod_cast hQ.pos : (0 : ℝ) < Q)).mp h
  simp_rw [heval] at bound
  push_cast at bound
  simpa only [mul_comm (Q : ℝ)] using bound

end Density.Polynomial
