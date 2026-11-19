module

public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

/-!
# Polynomial configurations: the finite thinning argument

This file follows the counting argument in Section 3 of Kovač and Santos
Sepčić, arXiv:2604.18544.  Counting the uniform sample space directly gives a
fixed-cardinality hitting set without introducing probability measures.
-/

public section

namespace Density.Polynomial

open scoped BigOperators Classical

/-- Bertrand's postulate in the strict form used to choose the denominator.
Use `N = n ^ (2 ^ p)` in the application. -/
theorem exists_prime_between {N : ℕ} (hN : 2 ≤ N) :
    ∃ Q : ℕ, Q.Prime ∧ N < Q ∧ Q < 2 * N := by
  obtain ⟨Q, hQ, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul N (by omega)
  refine ⟨Q, hQ, hlt, lt_of_le_of_ne hle ?_⟩
  rintro rfl
  exact Nat.not_prime_mul (by decide : (2 : ℕ) ≠ 1) (by omega : N ≠ 1) hQ

/-- If the missing fraction is at most θ, the probability that an n-subset
misses a target is at most θ^n. The inequality is cross-multiplied. -/
theorem choose_le_fraction_pow (L Q : ℕ) (hLQ : L ≤ Q) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hfrac : (L : ℝ) ≤ θ * Q) (n : ℕ) :
    (L.choose n : ℝ) ≤ (Q.choose n : ℝ) * θ ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    by_cases hk : L ≤ k
    · rw [Nat.choose_eq_zero_of_lt (by omega : L < k + 1), Nat.cast_zero]
      positivity
    have hkL : k ≤ L := by omega
    have hkQ : k ≤ Q := hkL.trans hLQ
    have hstep : ((L - k : ℕ) : ℝ) ≤ θ * ((Q - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hkL, Nat.cast_sub hkQ]
      nlinarith only [hfrac, mul_nonneg (sub_nonneg.mpr hθ1)
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have recL : (L.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
        (L.choose k : ℝ) * ((L - k : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq L k
    have recQ : (Q.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
        (Q.choose k : ℝ) * ((Q - k : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_succ_right_eq Q k
    apply le_of_mul_le_mul_right _ (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))
    calc
      _ = (L.choose k : ℝ) * ((L - k : ℕ) : ℝ) := recL
      _ ≤ ((Q.choose k : ℝ) * θ ^ k) * (θ * ((Q - k : ℕ) : ℝ)) :=
        mul_le_mul ih hstep (by positivity) (by positivity)
      _ = ((Q.choose k : ℝ) * ((Q - k : ℕ) : ℝ)) * (θ ^ k * θ) := by ring
      _ = _ := by rw [← recQ, pow_succ]; ring

/-- The exact union bound on uniformly sampled n-subsets. For each index i
the bad samples are the n-subsets of U minus R i. -/
theorem exists_hitting_of_sum_choose_lt {α ι : Type*} [DecidableEq α]
    (U : Finset α) (I : Finset ι) (R : ι → Finset α) (n : ℕ)
    (hcount : (∑ i ∈ I, (U \ R i).card.choose n) < U.card.choose n) :
    ∃ P ⊆ U, P.card = n ∧ ∀ i ∈ I, ∃ x ∈ P, x ∈ R i := by
  classical
  let bad := I.biUnion fun i => (U \ R i).powersetCard n
  have hbad : bad.card < (U.powersetCard n).card := by
    calc
      bad.card ≤ ∑ i ∈ I, ((U \ R i).powersetCard n).card :=
        Finset.card_biUnion_le
      _ < _ := by simpa only [Finset.card_powersetCard] using hcount
  obtain ⟨P, hP, hgood⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  obtain ⟨hPU, hPn⟩ := Finset.mem_powersetCard.mp hP
  refine ⟨P, hPU, hPn, ?_⟩
  intro i hi
  by_contra! hmiss
  apply hgood
  apply Finset.mem_biUnion.mpr
  refine ⟨i, hi, Finset.mem_powersetCard.mpr ⟨?_, hPn⟩⟩
  intro x hx
  exact Finset.mem_sdiff.mpr ⟨hPU hx, hmiss x hx⟩

/-- If every target contains a fraction δ of the population, a uniform
n-subset simultaneously hits them all provided |I| exp(-δ n) < 1.
The paper takes δ = 4 ε / 5 and indexes the targets by pairs (b,I). -/
theorem exists_hitting_of_exp_lt {α ι : Type*} [DecidableEq α]
    (U : Finset α) (I : Finset ι) (R : ι → Finset α) {n : ℕ}
    (hn : n ≤ U.card) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsub : ∀ i ∈ I, R i ⊆ U)
    (hdense : ∀ i ∈ I, δ * U.card ≤ ((R i).card : ℝ))
    (hsmall : (I.card : ℝ) * Real.exp (-(n : ℝ) * δ) < 1) :
    ∃ P ⊆ U, P.card = n ∧ ∀ i ∈ I, ∃ x ∈ P, x ∈ R i := by
  classical
  let θ := Real.exp (-δ)
  have hθ0 : 0 ≤ θ := (Real.exp_pos _).le
  have hθ1 : θ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hθδ : 1 - δ ≤ θ := by
    dsimp [θ]
    linarith [Real.add_one_le_exp (-δ)]
  have hbound (i : ι) (hi : i ∈ I) :
      ((U \ R i).card.choose n : ℝ) ≤ (U.card.choose n : ℝ) * θ ^ n := by
    have hcard := Finset.card_le_card (hsub i hi)
    apply choose_le_fraction_pow _ _ (Finset.card_le_card (Finset.sdiff_subset)) θ hθ0 hθ1
    rw [Finset.card_sdiff_of_subset (hsub i hi), Nat.cast_sub hcard]
    calc
      _ ≤ (1 - δ) * U.card := by linarith [hdense i hi]
      _ ≤ θ * U.card := mul_le_mul_of_nonneg_right hθδ (by positivity)
  have hcount : (∑ i ∈ I, ((U \ R i).card.choose n : ℝ)) <
      (U.card.choose n : ℝ) := by
    have hpow : θ ^ n = Real.exp (-(n : ℝ) * δ) := by
      dsimp [θ]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc
      _ ≤ ∑ i ∈ I, (U.card.choose n : ℝ) * θ ^ n :=
        Finset.sum_le_sum hbound
      _ = (U.card.choose n : ℝ) * ((I.card : ℝ) * Real.exp (-(n : ℝ) * δ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, hpow]
        ring
      _ < (U.card.choose n : ℝ) * 1 :=
        mul_lt_mul_of_pos_left hsmall (by exact_mod_cast Nat.choose_pos hn)
      _ = _ := mul_one _
  apply exists_hitting_of_sum_choose_lt U I R n
  exact_mod_cast hcount

/-- Changing the lower coefficients by Δ_i changes the polynomial at a
natural index k ≤ Q by at most ∑ Δ_i Q^i. Choose representatives on the
real line before applying this estimate to classes modulo one. -/
theorem coefficient_perturbation {ι : Type*} (s : Finset ι) (deg : ι → ℕ)
    (B b Δ : ι → ℝ) (k Q : ℕ) (hk : k ≤ Q)
    (hΔ : ∀ i ∈ s, |B i - b i| ≤ Δ i) :
    |(∑ i ∈ s, B i * (k : ℝ) ^ deg i) - ∑ i ∈ s, b i * (k : ℝ) ^ deg i| ≤
    ∑ i ∈ s, Δ i * (Q : ℝ) ^ deg i := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, |B i * (k : ℝ) ^ deg i - b i * (k : ℝ) ^ deg i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← sub_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) ^ deg i)]
      exact mul_le_mul (hΔ i hi)
        (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hk) _) (by positivity)
        ((abs_nonneg _).trans (hΔ i hi))

/-- A uniform grid on the circle, represented in [0,1). -/
noncomputable def meshPoint {M : ℕ} (b : Fin M) : ℝ := b.val / (M : ℝ)

/-- Rounding down after subtracting an integer part works at the seam of the circle. -/
theorem exists_meshPoint {M : ℕ} (hM : 0 < M) (x : ℝ) :
    ∃ b : Fin M, 0 ≤ Int.fract x - meshPoint b ∧
      Int.fract x - meshPoint b ≤ 1 / (M : ℝ) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hnonneg : 0 ≤ Int.fract x * (M : ℝ) := mul_nonneg (Int.fract_nonneg x) hM'.le
  let j := ⌊Int.fract x * (M : ℝ)⌋₊
  have hj : j < M := by
    apply (Nat.floor_lt hnonneg).mpr
    simpa using mul_lt_mul_of_pos_right (Int.fract_lt_one x) hM'
  have hlo : (j : ℝ) ≤ Int.fract x * (M : ℝ) := Nat.floor_le hnonneg
  have hhi : Int.fract x * (M : ℝ) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨⟨j, hj⟩, ?_, ?_⟩
  · change 0 ≤ Int.fract x - (j : ℝ) / (M : ℝ)
    exact sub_nonneg.mpr ((div_le_iff₀ hM').mpr hlo)
  · change Int.fract x - (j : ℝ) / (M : ℝ) ≤ 1 / (M : ℝ)
    apply (le_div_iff₀ hM').mpr
    rw [sub_mul, div_mul_cancel₀ _ hM'.ne']
    linarith

/-- The leading degree is p. For the source polynomial take m = p - 1. -/
@[expose] noncomputable def phase {m : ℕ} (p : ℕ) (A : ℝ) (B : Fin m → ℝ) (k : ℕ) : ℝ :=
  A * (k : ℝ) ^ p + ∑ i, B i * (k : ℝ) ^ (i.val + 1)

/-- Membership of x modulo one in the half-open arc starting at u. -/
@[expose] def inArc (x u length : ℝ) : Prop :=
  ∃ z : ℤ, u ≤ x - z ∧ x - z < u + length

/-- Shifting lower coefficients by integers has no effect on a phase modulo one. -/
theorem phase_fract {m : ℕ} (p : ℕ) (A : ℝ) (B : Fin m → ℝ) (k : ℕ) :
    phase p A B k - (↑(∑ i, ⌊B i⌋ * (k : ℤ) ^ (i.val + 1)) : ℝ) =
    phase p A (fun i => Int.fract (B i)) k := by
  simp only [phase, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [add_sub_assoc, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_mul]
  rfl

/-- Finite reduction of the polynomial interval problem. The inputs are
(a) a lower point count for the prescribed grid of short arcs and coefficient tuples,
(b) grid resolutions, and (c) the scalar union-bound inequality. The conclusion
quantifies over all real coefficients and all arc origins at once. -/
theorem thin_polynomial_grid {m n Q p H : ℕ} (A ε : ℝ) (M : Fin m → ℕ)
    (hε : 0 < ε) (hn : n ≤ Q) (hH : 0 < H) (hM : ∀ i, 0 < M i)
    (hinterval : 1 / (H : ℝ) ≤ ε / 100)
    (hcoeff : (∑ i, (1 / (M i : ℝ)) * (Q : ℝ) ^ (i.val + 1)) ≤ ε / 100)
    (hcount : ∀ (b : (i : Fin m) → Fin (M i)) (a : Fin H),
      (4 * ε / 5) * Q ≤
      (((Finset.range Q).filter (fun k => inArc
        (phase p A (fun i => meshPoint (b i)) k) (meshPoint a) (9 * ε / 10))).card : ℝ))
    (hsmall : (((∏ i, M i) * H : ℕ) : ℝ) * Real.exp (-(n : ℝ) * (4 * ε / 5)) < 1) :
    ∃ P ⊆ Finset.range Q, P.card = n ∧ ∀ (B : Fin m → ℝ) (u : ℝ),
      ∃ k ∈ P, inArc (phase p A B k) u ε := by
  classical
  let R := fun g : ((i : Fin m) → Fin (M i)) × Fin H =>
    (Finset.range Q).filter fun k =>
      inArc (phase p A (fun i => meshPoint (g.1 i)) k) (meshPoint g.2) (9 * ε / 10)
  have hsub (g) (_ : g ∈ (Finset.univ : Finset (((i : Fin m) → Fin (M i)) × Fin H))) :
      R g ⊆ Finset.range Q := Finset.filter_subset _ _
  have hsize (g) (_ : g ∈ (Finset.univ : Finset (((i : Fin m) → Fin (M i)) × Fin H))) :
      (4 * ε / 5) * ((Finset.range Q).card : ℝ) ≤ ((R g).card : ℝ) := by
    simpa only [Finset.card_range] using hcount g.1 g.2
  obtain ⟨P, hP, hcard, hhit⟩ :=
    exists_hitting_of_exp_lt (Finset.range Q) Finset.univ R
      (by simpa using hn) (4 * ε / 5) (by positivity) hsub hsize
      (by simpa [Fintype.card_pi] using hsmall)
  refine ⟨P, hP, hcard, ?_⟩
  intro B u
  choose b hb0 hb1 using fun i => exists_meshPoint (hM i) (B i)
  let v := u + ε / 20
  obtain ⟨a, ha0, ha1⟩ := exists_meshPoint hH v
  obtain ⟨k, hk, hR⟩ := hhit (b, a) (Finset.mem_univ _)
  refine ⟨k, hk, ?_⟩
  obtain ⟨z, hz0, hz1⟩ := (Finset.mem_filter.mp hR).2
  have hkQ := (Finset.mem_range.mp (hP hk)).le
  have hpert := coefficient_perturbation Finset.univ (fun i : Fin m => i.val + 1)
    (fun i => Int.fract (B i)) (fun i => meshPoint (b i)) (fun i => 1 / (M i : ℝ))
    k Q hkQ (fun i _ => by rw [abs_of_nonneg (hb0 i)]; exact hb1 i)
  have hphase :
      |phase p A (fun i => Int.fract (B i)) k -
        phase p A (fun i => meshPoint (b i)) k| ≤ ε / 100 := by
    simpa only [phase, add_sub_add_left_eq_sub] using hpert.trans hcoeff
  have hphase' := abs_le.mp hphase
  let w : ℤ := ∑ i, ⌊B i⌋ * (k : ℤ) ^ (i.val + 1)
  have hw : phase p A B k - (w : ℝ) = phase p A (fun i => Int.fract (B i)) k :=
    phase_fract p A B k
  have hv : (⌊v⌋ : ℝ) + Int.fract v = u + ε / 20 := Int.floor_add_fract v
  refine ⟨z + w - ⌊v⌋, ?_, ?_⟩
  · push_cast
    linarith only [hz0, hw, hv, ha1, hinterval, hphase'.1, hε]
  · push_cast
    linarith only [hz1, hw, hv, ha0, hphase'.2, hε]


/-- The logarithm in the final scale comes from a polynomial-size family of
bad events. With N ≤ n^a, the upper bound N exp(-4 ε n / 5) is strictly below
one as soon as ε ≥ K log(n)/n and 4K/5 > a. -/
theorem exp_small_of_polynomial_card {n N a : ℕ} (hn : 1 < n) (hN : N ≤ n ^ a)
    {K ε : ℝ} (hK : (a : ℝ) < 4 * K / 5)
    (hε : K * Real.log (n : ℝ) ≤ (n : ℝ) * ε) :
    (N : ℝ) * Real.exp (-(n : ℝ) * (4 * ε / 5)) < 1 := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_pos hn'
  have hp : (n : ℝ) ^ a = Real.exp ((a : ℝ) * Real.log (n : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith : (0 : ℝ) < n)]
  calc
    _ ≤ (n : ℝ) ^ a * Real.exp (-(n : ℝ) * (4 * ε / 5)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (Real.exp_pos _).le
    _ = Real.exp ((a : ℝ) * Real.log n - (n : ℝ) * (4 * ε / 5)) := by
      rw [hp, ← Real.exp_add]
      congr 1
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr (by
      nlinarith only [mul_lt_mul_of_pos_right hK hlog, hε])


/-- Once a uniform short-arc count is available for the full sample, working
with explicit integer grid sizes reduces the rest of Proposition 5 to
polynomial growth of Q and a numerical lower bound on K. The ith grid has
n² Q^(i+1) points and the grid of arc origins has n² points. -/
theorem thin_of_short_arc_count {m n Q p s : ℕ} (A ε K : ℝ)
    (hn : 100 * (m + 1) ≤ n) (hnQ : n ≤ Q) (hQ : Q ≤ n ^ s)
    (hε : 1 ≤ (n : ℝ) * ε) (hlog : K * Real.log (n : ℝ) ≤ (n : ℝ) * ε)
    (hK : (((∑ i : Fin m, (2 + s * (i.val + 1))) + 2 : ℕ) : ℝ) < 4 * K / 5)
    (hcount : ∀ (B : Fin m → ℝ) (a : ℝ), (4 * ε / 5) * Q ≤
      (((Finset.range Q).filter (fun k => inArc (phase p A B k) a (9 * ε / 10))).card : ℝ)) :
    ∃ P ⊆ Finset.range Q, P.card = n ∧ ∀ (B : Fin m → ℝ) (u : ℝ),
      ∃ k ∈ P, inArc (phase p A B k) u ε := by
  let M (i : Fin m) := n ^ 2 * Q ^ (i.val + 1)
  have hn1 : 1 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hQpos : 0 < Q := by omega
  have hεpos : 0 < ε := by
    by_contra! h
    linarith [mul_nonpos_of_nonneg_of_nonpos hnpos.le h]
  have hres (x : ℝ) (hx : 100 * x ≤ n) : x * (1 / (n : ℝ) ^ 2) ≤ ε / 100 := by
    rw [← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [hx, mul_le_mul_of_nonneg_right hε hnpos.le]
  have hmesh (i : Fin m) :
      (1 / (M i : ℝ)) * (Q : ℝ) ^ (i.val + 1) = 1 / (n : ℝ) ^ 2 := by
    dsimp [M]
    push_cast
    field_simp
  have hsize : (∏ i, M i) * n^2 ≤
      n ^ ((∑ i : Fin m, (2 + s * (i.val + 1))) + 2) := by
    rw [pow_add, ← Finset.prod_pow_eq_pow_sum]
    apply Nat.mul_le_mul_right
    apply Finset.prod_le_prod
    intro i _
    dsimp [M]
    rw [pow_add n 2, pow_mul n s]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _)
  apply thin_polynomial_grid A ε M hεpos hnQ (H := n^2)
  · positivity
  · intro i
    dsimp [M]
    positivity
  · have hx : (100 : ℝ) * 1 ≤ n := by
      exact_mod_cast (show 100 * 1 ≤ n by omega)
    simpa using hres 1 hx
  · simp_rw [hmesh]
    simpa using hres m (by exact_mod_cast (show 100 * m ≤ n by omega))
  · intro b a
    exact hcount _ _
  · exact exp_small_of_polynomial_card hn1 hsize hK hlog


open Filter
open scoped Topology

/-- Discrepancy of a full collection, with an explicit comparison to the
length of each test interval. Neither B nor the interval is fixed in advance. -/
@[expose] def discrepancyLE (m p Q : ℕ) (A D : ℝ) : Prop :=
  ∀ (B : Fin m → ℝ) (u ℓ : ℝ), 0 ≤ ℓ → ℓ ≤ 1 →
    |(((Finset.range Q).filter (fun k => inArc (phase p A B k) u ℓ)).card : ℝ) / Q - ℓ| ≤ D

/-- The deduction of the polynomial hitting property of Proposition 5 from
the uniform discrepancy estimate. The exponent s bounds the growth of Q.
The conclusion hits even the interior of every length-ε interval. -/
theorem eventual_hitting_of_discrepancy {m p s : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hD : ∀ᶠ n : ℕ in atTop, ∃ (Q : ℕ) (A : ℝ),
      n ≤ Q ∧ Q ≤ n ^ s ∧ discrepancyLE m p Q A (C * (Real.log n / n))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∃ (P : Finset ℕ) (A : ℝ),
      P.card = n ∧ ∀ (B : Fin m → ℝ) (u : ℝ), ∃ k ∈ P, ∃ z : ℤ,
        u < phase p A B k - z ∧ phase p A B k - z < u + K * (Real.log n / n) := by
  let a : ℕ := (∑ i : Fin m, (2 + s * (i.val + 1))) + 2
  let L : ℝ := 10 * (C + a + 1)
  have ha : (0 : ℝ) ≤ a := by positivity
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := by linarith
  have hC' : 10 * C ≤ L := by dsimp [L]; linarith
  have ha' : (a : ℝ) < 4 * L / 5 := by dsimp [L]; linarith
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlogs : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1
  have hlim : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hcast
  have hsmall : ∀ᶠ n : ℕ in atTop, L * (Real.log n / (n : ℝ)) < 1 := by
    have ht := (tendsto_const_nhds (x := L)).mul hlim
    exact (show Tendsto _ _ (𝓝 (0 : ℝ)) by simpa using ht).eventually_lt_const zero_lt_one
  refine ⟨2 * L, by positivity, ?_⟩
  filter_upwards [hD, hlogs, hsmall, eventually_ge_atTop (100 * (m + 1))]
    with n hDn hnlog hnsmall hnlarge
  obtain ⟨Q, A, hnQ, hQ, hdisc⟩ := hDn
  have hnpos : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  let ε : ℝ := L * (Real.log n / (n : ℝ))
  have hε : 0 < ε := mul_pos hL (div_pos (by linarith) hn')
  have hnε : (n : ℝ) * ε = L * Real.log n := by dsimp [ε]; field_simp
  have hlarge : 1 ≤ (n : ℝ) * ε := by
    rw [hnε]
    calc
      1 = (1 : ℝ) * 1 := by norm_num
      _ ≤ _ := mul_le_mul hL1 hnlog zero_le_one hL.le
  have herr : C * (Real.log n / (n : ℝ)) ≤ ε / 10 := by
    have hh := mul_le_mul_of_nonneg_right hC' (div_nonneg (by linarith : 0 ≤ Real.log n) hn'.le)
    dsimp [ε]
    linarith
  have hcount (B : Fin m → ℝ) (u : ℝ) : (4 * ε / 5) * Q ≤
      (((Finset.range Q).filter (fun k => inArc (phase p A B k) u (9 * ε / 10))).card : ℝ) := by
    have hl : 9 * ε / 10 ≤ 1 := by change ε < 1 at hnsmall; linarith
    have hfrac := (abs_le.mp ((hdisc B u (9 * ε / 10) (by positivity) hl).trans herr)).1
    apply (le_div_iff₀ hQ').mp
    linarith
  obtain ⟨P, _, hPc, hhit⟩ := thin_of_short_arc_count A ε L hnlarge hnQ hQ hlarge
    (le_of_eq hnε.symm) ha' hcount
  refine ⟨P, A, hPc, ?_⟩
  intro B u
  obtain ⟨k, hk, z, hlow, hupp⟩ := hhit B (u + ε / 2)
  refine ⟨k, hk, z, by linarith, ?_⟩
  dsimp [ε] at hupp hε
  linarith

end Density.Polynomial
