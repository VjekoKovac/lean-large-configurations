module

public import Density.IntegerLp
public import Density.WeylSamples
public import Density.FejerCount

/-! # From Fourier estimates and short-arc counts to Proposition 5

The two analytic inputs are combined with the exact-cardinality thinning
theorem. Widening the final arc by a factor of two makes the endpoint
convention immaterial. The constant and the cutoff depend only on the degree.
-/

public section

open Filter Finset
open scoped Classical
open scoped BigOperators Topology

namespace Density.Polynomial

/-- Proposition 5 in the range p ≥ 2 needed by the three introduction
theorems. The choice of the polynomial phases works for all lower
coefficients and all positions of the test interval simultaneously. -/
theorem polynomial_hitting : Density.PolynomialHitting := by
  intro p hp
  cases p with
  | zero => omega
  | succ m =>
    obtain ⟨s, hsample⟩ := eventual_weyl_samples (m+1) (by omega)
    let a : ℕ := (∑ i : Fin m, (2 + s * (i.val+1))) + 2
    let L : ℝ := 10 * (a+1)
    have ha : 0 ≤ (a:ℝ) := Nat.cast_nonneg _
    have hL : 1 ≤ L := by dsimp [L]; linarith
    have hL₀ : 0 < L := by linarith
    have hK : (a:ℝ) < 4*L/5 := by dsimp [L]; linarith
    have hcast : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hlogs := (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1
    have hlim : Tendsto (fun n : ℕ => L*(Real.log n/(n:ℝ))) atTop (𝓝 0) := by
      simpa using (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcast).const_mul L
    refine ⟨2*L, by positivity, ?_⟩
    filter_upwards [hsample, hlogs, hlim.eventually_lt_const zero_lt_one,
      eventually_ge_atTop 1000000, eventually_ge_atTop (100*(m+1))]
      with n hs hnlog hnsmall hnM hnlarge
    obtain ⟨Q, hnQ, hQs, hW⟩ := hs
    have hnpos : 0 < n := by omega
    have hnr : 0 < (n:ℝ) := by exact_mod_cast hnpos
    change 1 ≤ Real.log (n:ℝ) at hnlog
    let ε := L*(Real.log (n:ℝ)/(n:ℝ))
    have heps : 0 < ε := mul_pos hL₀ (div_pos (by linarith) hnr)
    have hne : (n:ℝ)*ε = L * Real.log n := by dsimp [ε]; field_simp
    have hepsn : 1 ≤ (n:ℝ)*ε := by
      rw [hne]
      simpa only [one_mul] using mul_le_mul hL hnlog zero_le_one hL₀.le
    have ⟨hmesh, herr⟩ := fejer_parameter_bounds hnM hepsn
    have hmesh' : (1000000:ℝ) ≤ (n:ℝ)^4*ε^3 := (div_le_iff₀ (pow_pos heps _)).mp hmesh
    have herr' : (n:ℝ)^4 * (1/(n:ℝ)^6) ≤ ε/100 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 100*(n:ℝ)^4)).mp herr
      apply (le_div_iff₀ (by norm_num : (0:ℝ) < 100)).mpr
      linarith only [hh]
    have hcount (B : Fin m → ℝ) (u : ℝ) :
        4*ε/5*Q ≤ (((range Q).filter (fun k => inArc (phase (m+1) (1/(Q:ℝ)) B k)
          u (9*ε/10))).card : ℝ) := by
      apply short_arc_count_of_fourier (M := n^4) (δ := 1/(n:ℝ)^6) (pow_pos hnpos _) _
        heps hnsmall.le (by positivity) (by exact_mod_cast hmesh') (by exact_mod_cast herr')
      intro h hh hlt
      exact hW h hh hlt.le B
    obtain ⟨P, _, hc, hits⟩ := thin_of_short_arc_count (1/(Q:ℝ)) ε L hnlarge hnQ hQs
      hepsn hne.ge hK hcount
    refine ⟨intPattern P, 1/(Q:ℝ), (card_intPattern P).trans hc, annular_hits_of_phase ?_⟩
    intro B u
    obtain ⟨k, hk, z, hl, hu⟩ := hits B (u+ε/2)
    refine ⟨k, hk, z, by linarith, ?_⟩
    dsimp [ε] at hu heps
    linarith

end Density.Polynomial
