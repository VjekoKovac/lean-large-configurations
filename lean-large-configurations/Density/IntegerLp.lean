module

public import Density.AnnularCopies
public import Density.PolynomialArcs
public import Density.ShellDensity

/-! # Section 2, including the dimension-uniform even-exponent conclusion -/

public section

open Filter MeasureTheory
open scoped Topology

namespace Density

/-- The p ≥ 2 part of Proposition 5 which feeds Theorems 1 and 2. -/
@[expose] def PolynomialHitting : Prop :=
  ∀ p : ℕ, 2 ≤ p → ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
    ∃ (P : Finset ℤ) (A : ℝ), P.card = n ∧
      Annular.HitsArcs p P A (K * (Real.log (n : ℝ) / (n : ℝ)))

private theorem gap_eventually {K : ℝ} (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, 0 < K * (Real.log (n : ℝ) / (n : ℝ)) ∧
      K * (Real.log (n : ℝ) / (n : ℝ)) < 1 := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcast
  have h0 : Tendsto (fun n : ℕ => K * (Real.log (n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
    simpa using hlim.const_mul K
  filter_upwards [eventually_gt_atTop 1, h0.eventually_lt_const zero_lt_one] with n hn hsmall
  have hreal : 1 < (n : ℝ) := by exact_mod_cast hn
  exact ⟨mul_pos hK (div_pos (Real.log_pos hreal) (lt_trans zero_lt_one hreal)), hsmall⟩

theorem lowerCase_of_actual {d n : ℕ} {p C : ℝ} (h : ActualCase d n p C) :
    LowerCase d n p C := by
  obtain ⟨E, P, hE, hc, a, ha, hle⟩ := h
  refine ⟨E, P, hE, hc, ?_⟩
  have hlim : lowerDensity E = a := ha.liminf_eq
  rwa [hlim]

/-- Combine the uniform slice estimates, the finite sign intersection, and
Proposition 5. The same p-dependent cutoff works for every even-case dimension. -/
theorem integerLp_of_hitting (hit : PolynomialHitting) :
    IntegralLpStatement := by
  have heven (p : ℕ) (hp : 2 ≤ p) (he : Even p) :
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ d : ℕ, 1 ≤ d →
        ∀ n : ℕ, N ≤ n → ActualCase d n (p : ℝ) C := by
    obtain ⟨K, hK, hpat⟩ := hit p hp
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hpat.and (gap_eventually hK))
    refine ⟨K, hK, N, fun d hd n hn => ?_⟩
    obtain ⟨⟨P, A, hcard, hhit⟩, hpos, hlt⟩ := hN n hn
    obtain ⟨Q, hobs, hcol⟩ := Annular.even_obstruction hd hp he hhit
    rw [hcard] at hobs
    refine ⟨_, Q, hobs, hcol, 1 - K * (Real.log (n : ℝ) / (n : ℝ)), ?_, ?_⟩
    · simpa [Annular.directionSign] using
        Annular.hasDensity_shell hd (by omega : 1 ≤ p) (fun _ => true) hpos hlt
    · rw [mul_div_assoc]
  refine ⟨?_, heven⟩
  intro d p hd hp
  rcases Nat.even_or_odd p with he | ho
  · obtain ⟨K, hK, N, hN⟩ := heven p hp he
    exact ⟨K, hK, N, fun n hn => lowerCase_of_actual (hN d hd n hn)⟩
  · obtain ⟨K, hK, hpat⟩ := hit p hp
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hpat.and (gap_eventually hK))
    refine ⟨(2 : ℝ) ^ d * K, by positivity, N, fun n hn => ?_⟩
    obtain ⟨⟨P, A, hcard, hhit⟩, hpos, hlt⟩ := hN n hn
    obtain ⟨Q, hobs, hcol⟩ := Annular.odd_obstruction hd hp ho hhit
    rw [hcard] at hobs
    refine ⟨_, Q, hobs, hcol, ?_⟩
    simpa only [mul_div_assoc, mul_assoc] using Annular.oddShell_lowerDensity hd (by omega : 1 ≤ p) hpos hlt

/-- Theorem 1 follows from the even case p = 2, including uniformity in d. -/
theorem euclidean_of_integerLp (h : IntegralLpStatement) : EuclideanStatement := by
  simpa only [EuclideanStatement, Nat.cast_ofNat] using h.2 2 (by decide) (by exact ⟨1, rfl⟩)

end Density
