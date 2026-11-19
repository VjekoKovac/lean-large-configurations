module

public import Density.Fejer
public import Density.FejerTail
public import Density.Polynomial

/-! # Counting phases in short arcs

Sum the Fejér weights over the mesh points a little inside the interval. On
the interval their total is at most one, by the exact partition identity.
Outside it every mesh point is separated from the phase, so the total tail
is small. The Fourier estimates give a lower bound for the same sum.
-/

public section
open Finset Classical
open scoped BigOperators

namespace Density.Polynomial

theorem short_arc_count_of_fourier {M Q : ℕ} (hM : 0 < M) (X : ℕ → ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ 1) (hδ : 0 ≤ δ)
    (hmesh : (1000000 : ℝ) ≤ (M : ℝ)*ε^3) (herr : (M : ℝ)*δ ≤ ε/100)
    (hW : ∀ h : ℕ, 0 < h → h < M →
      ‖∑ k ∈ range Q, fourierE ((h : ℝ)*X k)‖ ≤ (Q : ℝ)*δ) (u : ℝ) :
    (4*ε/5)*Q ≤ (((range Q).filter (fun k => inArc (X k) u (9*ε/10))).card : ℝ) := by
  classical
  let w := 9*ε/10 - 2*(ε/50)
  let L : ℕ := ⌊(M : ℝ)*w⌋₊
  let c := u + ε/50
  let t (j : ℕ) := c + (j : ℝ) / M
  have hm : 0 < (M : ℝ) := by exact_mod_cast hM
  have hw0 : 0 ≤ w := by dsimp [w]; linarith
  have hw1 : w ≤ 1 := by dsimp [w]; linarith
  have hLM' : (L : ℝ) ≤ (M : ℝ)*w := Nat.floor_le (mul_nonneg hm.le hw0)
  have hLMr : (L : ℝ) ≤ M :=
    hLM'.trans (by simpa using mul_le_mul_of_nonneg_left hw1 hm.le)
  have hLM : L ≤ M := by exact_mod_cast hLMr
  have hw : (M : ℝ)*w < (L : ℝ)+1 := Nat.lt_floor_add_one _
  have hpow : ε^3 ≤ ε := by
    simpa using pow_le_pow_of_le_one hε.le hε' (show 1 ≤ 3 by decide)
  have hscale : 100 ≤ (M : ℝ)*ε := by linarith [mul_le_mul_of_nonneg_left hpow hm.le]
  have hlow : 9*ε/10 - 2*(ε/50) - ε/100 ≤ (L : ℝ)/M := by
    apply (le_div_iff₀ hm).mpr
    dsimp [w] at hw
    linarith
  have hz (j : ℕ) (hj : j ∈ range L) :
      u + ε/50 ≤ t j ∧ t j + ε/50 ≤ u+9*ε/10 := by
    have hj' : (j : ℝ) ≤ L := by exact_mod_cast (mem_range.mp hj).le
    have hdiv := (div_le_iff₀ hm).2 (by linarith : (j : ℝ) ≤ w * M)
    dsimp [t,c]
    dsimp [w] at hdiv
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j : 0 ≤ (j:ℝ)) hm.le]
    · linarith
  have htailnum : (1/(ε/50)^2)/(M:ℝ)^2 ≤ ε/(100*M) := by
    field_simp
    linarith only [hmesh]
  have htail (k j : ℕ) (hj : j ∈ range L) (hx : ¬ inArc (X k) u (9*ε/10)) :
      fejerWeight M (X k-t j) ≤ ε/(100*M) := by
    have h := fejer_sum_tail (by positivity : 0 < ε/50) (hz j hj).1 (hz j hj).2 hx M
    apply le_trans (div_le_div_of_nonneg_right h (sq_nonneg (M:ℝ))) htailnum
  have sumBound (k : ℕ) :
      ∑ j ∈ range L, fejerWeight M (X k-t j) ≤
        (if inArc (X k) u (9*ε/10) then (1:ℝ) else 0) + ε/100 := by
    by_cases hx : inArc (X k) u (9*ε/10)
    · simp only [hx, ↓reduceIte]
      have h := sum_le_sum_of_subset_of_nonneg (range_mono hLM)
        (fun j _ _ => fejer_nonneg M (X k - t j))
      have hp : ∑ j ∈ range M, fejerWeight M (X k-t j) = 1 := fejer_partition M hM (X k) c
      linarith
    · simp only [hx, ↓reduceIte, zero_add]
      calc
        _ ≤ ∑ _j ∈ range L, ε/(100*(M:ℝ)) := sum_le_sum (fun j hj => htail k j hj hx)
        _ = (L:ℝ) * (ε/(100*M)) := by simp
        _ ≤ (M:ℝ) * (ε/(100*M)) := mul_le_mul_of_nonneg_right hLMr (by positivity)
        _ = ε/100 := by field_simp
  have lowEach (j : ℕ) : (Q : ℝ)/M - (Q:ℝ)*δ ≤
      ∑ k ∈ range Q, fejerWeight M (X k-t j) := by
    have h := (abs_le.mp (fejer_error hM X (t j) δ hδ hW)).1
    linarith
  have lowSum := sum_le_sum (s := range L) (fun j _ => lowEach j)
  have highSum := sum_le_sum (s := range Q) (fun k _ => sumBound k)
  rw [sum_comm] at lowSum
  simp only [sum_const, card_range, nsmul_eq_mul] at lowSum
  simp only [sum_add_distrib, sum_boole, sum_const, card_range, nsmul_eq_mul] at highSum
  have combined := lowSum.trans highSum
  have hLδ : (L : ℝ)*δ ≤ ε/100 := (mul_le_mul_of_nonneg_right hLMr hδ).trans herr
  have hQ : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have mainTerm : (9*ε/10 - 2*(ε/50) - ε/100)*(Q:ℝ) ≤ (L:ℝ)*((Q:ℝ)/M) := by
    calc
      _ ≤ ((L:ℝ)/M)*(Q:ℝ) := mul_le_mul_of_nonneg_right hlow hQ
      _ = _ := by ring
  have errorTerm : (L:ℝ)*((Q:ℝ)*δ) ≤ (ε/100)*(Q:ℝ) := by
    calc
      _ = ((L:ℝ)*δ)*(Q:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLδ hQ
  rw [mul_sub] at combined
  linarith only [combined, mul_nonneg hε.le hQ, mainTerm, errorTerm]

end Density.Polynomial
