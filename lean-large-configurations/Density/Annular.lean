module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Tactic

/-! # The annular obstruction in Section 2

The integer translate in `HitsArcs` is an unwrapped representation of a point of
the unit circle. Allowing the coefficient of order zero makes the definition
translation invariant just as translating the test interval does in Proposition 5.
-/
@[expose] public noncomputable section

open Finset Filter Set
open scoped BigOperators Topology

namespace Density.Annular

/-- The points in the open allowed arc after lifting from the unit circle. -/
def Band (ε : ℝ) : Set ℝ :=
  {t | ∃ m : ℤ, |t - (m : ℝ)| < (1 - ε) / 2}

theorem isOpen_band (ε : ℝ) : IsOpen (Band ε) := by
  have h : Band ε = ⋃ m : ℤ, {t : ℝ | |t - (m : ℝ)| < (1 - ε) / 2} := by
    ext t
    simp [Band]
  rw [h]
  exact isOpen_iUnion (fun m => isOpen_lt ((continuous_id.sub continuous_const).abs)
    continuous_const)

/-- A point in the closed complementary arc cannot lie in the open band.
The endpoint distinction allows the test in `HitsArcs` to use closed intervals. -/
theorem not_mem_band_of_gap {ε t : ℝ} {z : ℤ}
    (hl : (1 - ε) / 2 ≤ t - (z : ℝ)) (hu : t - (z : ℝ) ≤ (1 + ε) / 2) :
    t ∉ Band ε := by
  rintro ⟨m, hm⟩
  have hm' := abs_lt.mp hm
  by_cases h : m ≤ z
  · have h' : (m : ℝ) ≤ z := by exact_mod_cast h
    linarith
  · have h' : z + 1 ≤ m := by omega
    have h'' : (z : ℝ) + 1 ≤ m := by exact_mod_cast h'
    linarith

/-- The uniform polynomial hitting property used in the reduction. -/
def HitsArcs (p : ℕ) (P : Finset ℤ) (A ε : ℝ) : Prop :=
  ∀ (B : ℕ → ℝ) (u : ℝ), ∃ k ∈ P, ∃ z : ℤ,
    u ≤ A * (k : ℝ) ^ p + ∑ l ∈ range p, B l * (k : ℝ) ^ l - (z : ℝ) ∧
    A * (k : ℝ) ^ p + ∑ l ∈ range p, B l * (k : ℝ) ^ l - (z : ℝ) ≤ u + ε

/-- The signed power phase; all signs are positive for even exponents. -/
def phase {d : ℕ} (p : ℕ) (σ x : Fin d → ℝ) : ℝ := ∑ i, σ i * x i ^ p

theorem continuous_phase {d : ℕ} (p : ℕ) (σ : Fin d → ℝ) :
    Continuous (phase p σ) := by
  unfold phase
  fun_prop

/-- The construction for even exponents, or one member of the intersection for odd exponents. -/
def shell {d : ℕ} (p : ℕ) (σ : Fin d → ℝ) (ε : ℝ) : Set (Fin d → ℝ) :=
  phase p σ ⁻¹' Band ε

theorem isOpen_shell {d : ℕ} (p : ℕ) (σ : Fin d → ℝ) (ε : ℝ) :
    IsOpen (shell p σ ε) := (isOpen_band ε).preimage (continuous_phase p σ)

def directionSign (s : Bool) : ℝ := if s then 1 else -1

/-- The intersection over the 2^d sign choices in the proof for odd p. -/
def oddShell {d : ℕ} (p : ℕ) (ε : ℝ) : Set (Fin d → ℝ) :=
  ⋂ s : Fin d → Bool, shell p (fun i => directionSign (s i)) ε

theorem isOpen_oddShell {d : ℕ} (p : ℕ) (ε : ℝ) : IsOpen (oddShell (d := d) p ε) :=
  isOpen_iInter_of_finite fun s => isOpen_shell p (fun i => directionSign (s i)) ε

/-- The binomial expansion on an affine line, including its leading coefficient. -/
theorem phase_line {d : ℕ} (p : ℕ) (σ x v : Fin d → ℝ) (r : ℝ) :
    ∃ B : ℕ → ℝ, ∀ k : ℝ,
      phase p σ (fun i => x i + r * k * v i) =
      (r ^ p * phase p σ v) * k ^ p + ∑ l ∈ range p, B l * k ^ l := by
  let b (i : Fin d) (l : ℕ) : ℝ :=
    σ i * (r * v i) ^ l * x i ^ (p-l) * (p.choose l : ℝ)
  refine ⟨fun l => ∑ i, b i l, fun k => ?_⟩
  have term (i : Fin d) :
      σ i * (x i + r * k * v i) ^ p =
      r ^ p * (σ i * v i ^ p) * k ^ p + ∑ l ∈ range p, b i l * k ^ l := by
    rw [show x i + r * k * v i = ((r * v i) * k) + x i by ring, add_pow,
      sum_range_succ, mul_add, mul_sum]
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
    rw [add_comm]
    congr 1
    · rw [mul_pow, mul_pow]
      ring
    · apply sum_congr rfl
      intro l _
      simp only [b, mul_pow]
      ring
  unfold phase
  simp_rw [term]
  rw [sum_add_distrib, sum_comm (s := (univ : Finset (Fin d))) (t := range p)]
  congr 1
  · simp only [mul_sum, sum_mul]
  · apply sum_congr rfl
    intro l _
    rw [sum_mul]

/-- If the leading coefficient is A plus an integer, a point of the affine
copy misses the allowed shell. This is the same exclusion for both parities. -/
theorem exists_outside_shell {d p : ℕ} {P : Finset ℤ} {A ε r : ℝ} (j : ℤ)
    (σ x v : Fin d → ℝ) (hit : HitsArcs p P A ε)
    (lead : r ^ p * phase p σ v = A + (j : ℝ)) :
    ∃ k ∈ P, (fun i => x i + r * (k : ℝ) * v i) ∉ shell p σ ε := by
  obtain ⟨B, hB⟩ := phase_line p σ x v r
  obtain ⟨k, hk, z, hl, hu⟩ := hit B ((1 - ε) / 2)
  refine ⟨k, hk, ?_⟩
  change phase p σ _ ∉ Band ε
  apply not_mem_band_of_gap (z := z + j * k ^ p)
  · rw [hB, lead]
    push_cast
    linarith only [hl]
  · rw [hB, lead]
    push_cast
    linarith only [hu]

theorem even_phase {d p : ℕ} (hp : Even p) (v : Fin d → ℝ) :
    phase p (fun _ => 1) v = ∑ i, |v i| ^ p := by
  simp [phase, hp.pow_abs]

/-- Choose the sign in each coordinate after the direction of the purported
copy is known. The intersection defining the set itself is fixed in advance. -/
theorem odd_phase {d p : ℕ} (hp : Odd p) (v : Fin d → ℝ) :
    phase p (fun i => directionSign (decide (0 ≤ v i))) v = ∑ i, |v i| ^ p := by
  apply sum_congr rfl
  intro i _
  by_cases h : 0 ≤ v i
  · simp [directionSign, h, abs_of_nonneg h]
  · simp [directionSign, h, abs_of_neg (lt_of_not_ge h), hp.neg_pow]

theorem even_exclusion {d p : ℕ} {P : Finset ℤ} {A ε r : ℝ} (j : ℤ)
    (hp : Even p) (x v : Fin d → ℝ) (hit : HitsArcs p P A ε)
    (unit : ∑ i, |v i| ^ p = 1) (scale : r ^ p = A + (j : ℝ)) :
    ∃ k ∈ P, (fun i => x i + r * (k : ℝ) * v i) ∉ shell p (fun _ => 1) ε := by
  apply exists_outside_shell j _ x v hit
  rwa [even_phase hp, unit, mul_one]

theorem odd_exclusion {d p : ℕ} {P : Finset ℤ} {A ε r : ℝ} (j : ℤ)
    (hp : Odd p) (x v : Fin d → ℝ) (hit : HitsArcs p P A ε)
    (unit : ∑ i, |v i| ^ p = 1) (scale : r ^ p = A + (j : ℝ)) :
    ∃ k ∈ P, (fun i => x i + r * (k : ℝ) * v i) ∉ oddShell p ε := by
  let s : Fin d → Bool := fun i => decide (0 ≤ v i)
  have hlead : r ^ p * phase p (fun i => directionSign (s i)) v = A + (j : ℝ) := by
    rwa [odd_phase hp, unit, mul_one]
  obtain ⟨k, hk, hout⟩ := exists_outside_shell j _ x v hit hlead
  exact ⟨k, hk, fun h => hout ((mem_iInter.mp h) s)⟩

/-- For arbitrary real A, discard finitely many starting indices, as in the paper. -/
theorem exists_scales (A : ℝ) {p : ℕ} (hp : 0 < p) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop atTop ∧
      ∀ n, ∃ j : ℤ, r n ^ p = A + (j : ℝ) := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (-A)
  let r (n : ℕ) := (A + ((J : ℝ) + (n : ℝ))) ^ ((p : ℝ)⁻¹)
  have hpos (n : ℕ) : 0 < A + ((J : ℝ) + (n : ℝ)) := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  refine ⟨r, fun n => Real.rpow_pos_of_pos (hpos n) _, ?_, ?_⟩
  · have hbase : Tendsto (fun n : ℕ => A + ((J : ℝ) + (n : ℝ))) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
    exact (tendsto_rpow_atTop (show 0 < (p : ℝ)⁻¹ by positivity)).comp hbase
  · intro n
    refine ⟨(J : ℤ) + n, ?_⟩
    dsimp [r]
    rw [Real.rpow_inv_natCast_pow (hpos n).le hp.ne']
    push_cast
    rfl

end Density.Annular
