module

public import Density.Polynomial
public import Mathlib.Analysis.Real.Sqrt

/-! Quantitative choices for short-shift Weyl differencing. -/

public section

namespace Density.Polynomial

/-- Passing to a difference polynomial squares the old accuracy requirement. -/
theorem weyl_child_size (d T : ℕ) :
    (16 * (16*T^2))^(2^d) = (16*T)^(2^(d+1)) := by
  rw [pow_succ 2 d, Nat.mul_comm (2^d) 2, pow_mul]
  congr 1
  ring

/-- Error budget for one application of the finite van der Corput inequality. -/
theorem weyl_step_bound {H Q T : ℕ} (hT : 0 < T) (hH : 16*T^2 ≤ H) (hQ : 4*H^2 ≤ Q) :
    2*(H:ℝ)/Q + Real.sqrt (1/H + 1/(16*(T:ℝ)^2)) ≤ 1/T := by
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  have ht₁ : 1 ≤ (T : ℝ) := by exact_mod_cast hT
  have hh : 16 * (T : ℝ)^2 ≤ H := by exact_mod_cast hH
  have hq : 4 * (H : ℝ)^2 ≤ Q := by exact_mod_cast hQ
  have hp : 0 < (H : ℝ) := lt_of_lt_of_le (by positivity) hh
  have qp : 0 < (Q : ℝ) := lt_of_lt_of_le (by positivity) hq
  have hth : (T : ℝ) ≤ H := by nlinarith [mul_le_mul_of_nonneg_left ht₁ ht.le]
  have h₁ : 2*(H:ℝ)/Q ≤ 1/(2*T) := by
    apply (div_le_div_iff₀ qp (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hth hp.le]
  have h₂ : Real.sqrt (1/H + 1/(16*(T:ℝ)^2)) ≤ 1/(2*T) := by
    apply (Real.sqrt_le_iff).2 ⟨by positivity, ?_⟩
    have h := one_div_le_one_div_of_le (by positivity : 0 < 16*(T:ℝ)^2) hh
    calc
      _ ≤ 1/(16*(T:ℝ)^2) + 1/(16*(T:ℝ)^2) := by linarith
      _ ≤ _ := by field_simp; nlinarith [sq_nonneg (T : ℝ)]
  calc
    _ ≤ 1/(2*(T:ℝ)) + 1/(2*(T:ℝ)) := add_le_add h₁ h₂
    _ = 1/(T:ℝ) := by field_simp; ring

/-- For all large n a single prime Q and shift bound H work simultaneously
for every one of the first n^4 frequencies; Q has polynomial growth in n. -/
theorem weyl_parameters (p : ℕ) :
    ∃ s : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∃ H Q : ℕ,
      1 ≤ n ∧ Q.Prime ∧ n ≤ Q ∧ Q ≤ n^s ∧
      (16*n^6)^(2^p) ≤ H ∧ 4*H^2 ≤ Q ∧ n^4 * p.factorial * H^(p-1) < Q := by
  let D := 10 * 2^p
  let L := 2*D + D*(p-1) + 6
  refine ⟨L+1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 4, Filter.eventually_ge_atTop p.factorial] with n hn hfac
  have hn₁ : 1 ≤ n := by omega
  let H := (16*n^6)^(2^p)
  have hH : H ≤ n^D := by
    have hn4 : 16 ≤ n^4 := by
      calc
        16 ≤ 4^4 := by decide
        _ ≤ n^4 := Nat.pow_le_pow_left hn _
    calc
      _ ≤ (n^4*n^6)^(2^p) := Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hn4) _
      _ = n^D := by simp [D, ← pow_add, ← pow_mul]
  have hl₁ : 1 ≤ L := by dsimp [L]; omega
  have hnL : n ≤ n^L := by simpa using Nat.pow_le_pow_right hn₁ hl₁
  obtain ⟨Q, hprime, hlo, hup⟩ := exists_prime_between (N := n^L) (by omega)
  refine ⟨H, Q, hn₁, hprime, hnL.trans hlo.le, ?_, le_rfl, ?_, ?_⟩
  · rw [pow_succ]
    exact hup.le.trans (by rw [Nat.mul_comm]; gcongr; omega)
  · apply le_trans _ hlo.le
    calc
      4*H^2 ≤ n * (n^D)^2 := Nat.mul_le_mul hn (Nat.pow_le_pow_left hH _)
      _ = n^(D*2+1) := by rw [pow_succ n (D*2), pow_mul n D 2, Nat.mul_comm n]
      _ ≤ _ := Nat.pow_le_pow_right hn₁ (by dsimp [L]; omega)
  · apply lt_of_le_of_lt _ hlo
    calc
      _ ≤ n^4 * n * (n^D)^(p-1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hfac)
        (Nat.pow_le_pow_left hH _)
      _ = n^(5+D*(p-1)) := by rw [pow_add, Nat.pow_mul]; ring
      _ ≤ _ := Nat.pow_le_pow_right hn₁ (by dsimp [L]; omega)

/-- The polynomial frequency cutoff and accuracy suffice already when ε ≥ 1/n. -/
theorem fejer_parameter_bounds {n : ℕ} {ε : ℝ} (hn : 1000000 ≤ n) (hε : 1 ≤ n*ε) :
    1000000 / ε^3 ≤ (n:ℝ)^4 ∧ 1/(n:ℝ)^6 ≤ ε / (100*(n:ℝ)^4) := by
  have hp : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have he : 0 < ε := by_contra fun h =>
    (not_le_of_gt (by norm_num : (0:ℝ) < 1)) (hε.trans (mul_nonpos_of_nonneg_of_nonpos hp.le (le_of_not_gt h)))
  have hn' : (1000000 : ℝ) ≤ n := by exact_mod_cast hn
  have h₁ : 1 ≤ ((n:ℝ)*ε)^3 := one_le_pow₀ hε
  constructor
  · apply (div_le_iff₀ (pow_pos he 3)).2
    calc
      (1000000:ℝ) ≤ n := hn'
      _ ≤ (n:ℝ)*((n:ℝ)*ε)^3 := le_mul_of_one_le_right hp.le h₁
      _ = _ := by ring
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hu : (100:ℝ) ≤ n * ((n:ℝ)*ε) := (by linarith : (100:ℝ) ≤ n).trans
      (le_mul_of_one_le_right hp.le hε)
    nlinarith only [mul_le_mul_of_nonneg_right hu (pow_nonneg hp.le 4)]

end Density.Polynomial
