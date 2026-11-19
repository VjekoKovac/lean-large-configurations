module

public import Density.CollinearLp
public import Density.Annular

/-! # From polynomial hitting to forbidden finite metric copies

The integer pattern from Proposition 5 is placed on one coordinate axis.
Lemma 7 applies to the distance-preserving labeling of any alleged copy.
The normalized affine direction can then be passed to the even or odd
polynomial exclusion from Section 2.
-/

@[expose] public noncomputable section

open Finset Filter MeasureTheory

namespace Density.Annular

/-- The point with coordinate t on the i-th axis and zero elsewhere. -/
def axial {d : ℕ} (i : Fin d) (t : ℝ) : Point d := fun j => if j = i then t else 0

theorem lpDistance_axial {d : ℕ} (i : Fin d) (s t : ℝ) {p : ℝ} (hp : 0 < p) :
    lpDistance p (axial i s) (axial i t) = |s - t| := by
  have hsum : ∑ j, |axial i s j - axial i t j| ^ p = |s-t| ^ p := by
    rw [Finset.sum_eq_single i]
    · simp [axial]
    · intro j _ hji
      simp [axial, hji, Real.zero_rpow hp.ne']
    · simp
  rw [lpDistance, hsum, one_div, Real.rpow_rpow_inv (abs_nonneg _) hp.ne']

/-- Place the integer labels on an axis without changing their cardinality. -/
def integerPattern {d : ℕ} (i : Fin d) (P : Finset ℤ) : Finset (Point d) :=
  P.map ⟨fun k : ℤ => axial i k, fun a b h => by
    have ha := congrFun h i
    simp only [axial] at ha
    exact_mod_cast ha⟩

@[simp] theorem card_integerPattern {d : ℕ} (i : Fin d) (P : Finset ℤ) :
    (integerPattern i P).card = P.card := by simp [integerPattern]

theorem axial_mem_integerPattern {d : ℕ} (i : Fin d) {k : ℤ} {P : Finset ℤ}
    (hk : k ∈ P) : axial i (k : ℝ) ∈ integerPattern i P :=
  Finset.mem_map.mpr ⟨k, hk, rfl⟩

theorem collinear_integerPattern {d : ℕ} (i : Fin d) (P : Finset ℤ) :
    IsCollinear (integerPattern i P) := by
  refine ⟨0, axial i 1, ?_, ?_⟩
  · intro hz
    have h := congrFun hz i
    simp [axial] at h
  · intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hx
    refine ⟨(k : ℝ), ?_⟩
    change axial i (k : ℝ) = 0 + (k : ℝ) • axial i 1
    ext j
    by_cases h : j = i <;> simp [axial, h, Pi.smul_apply]

/-- Every scaled finite metric copy of the axial integer pattern has the
affine form needed by the polynomial argument. -/
theorem affine_of_copy {d : ℕ} (i : Fin d) {P : Finset ℤ} {E : Set (Point d)}
    {p r : ℝ} (hp : 1 < p) (hr : 0 < r) (hc : HasScaledCopy p r (integerPattern i P) E) :
    ∃ x v : Point d, lpDistance p v 0 = 1 ∧
      ∀ k ∈ P, x + (r * (k : ℝ)) • v ∈ E := by
  classical
  obtain ⟨f, _, hf⟩ := hc
  let T := P.image (fun k : ℤ => (k : ℝ))
  let y (t : ℝ) : Point d :=
    if ht : axial i t ∈ integerPattern i P then (f ⟨axial i t, ht⟩).val else 0
  have hT (t : ℝ) (ht : t ∈ T) : axial i t ∈ integerPattern i P := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    exact axial_mem_integerPattern i hk
  have hy (s : ℝ) (hs : s ∈ T) (t : ℝ) (ht : t ∈ T) :
      lpDistance p (y s) (y t) = r * |s-t| := by
    have h := hf ⟨axial i s, hT s hs⟩ ⟨axial i t, hT t ht⟩
    simpa [y, hT s hs, hT t ht, lpDistance_axial i s t (lt_trans zero_lt_one hp)] using h
  obtain ⟨x, v, hv, hline⟩ :=
    collinear_copy_coordinates (Nat.zero_lt_of_lt i.isLt) hp hr T y hy
  refine ⟨x, v, hv, fun k hk => ?_⟩
  have hx := axial_mem_integerPattern i hk
  rw [← hline _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)]
  simpa only [y, dite_eq_left hx] using (f ⟨axial i (k : ℝ), hx⟩).property

private theorem sum_pow_of_unit {d p : ℕ} {v : Point d}
    (hp : 0 < p) (hv : lpDistance (p : ℝ) v 0 = 1) : ∑ i, |v i| ^ p = 1 := by
  have hn : 0 ≤ ∑ i, |v i| ^ p :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (abs_nonneg _) _)
  have hx := congrArg (fun z : ℝ => z ^ (p : ℝ)) hv
  simp only [lpDistance, Pi.zero_apply, sub_zero, one_div, Real.rpow_natCast,
    Real.rpow_inv_natCast_pow hn hp.ne', one_pow] at hx
  exact hx

private theorem obstruction_of_exclusion {d p : ℕ} (hd : 1 ≤ d) (hp : 2 ≤ p)
    {P : Finset ℤ} (A : ℝ) (E : Set (Point d)) (hE : MeasurableSet E)
    (hex : ∀ (j : ℤ) (r : ℝ) (x v : Point d), (∑ i, |v i| ^ p) = 1 →
      r ^ p = A + (j : ℝ) → ∃ k ∈ P, (fun i => x i + r * (k : ℝ) * v i) ∉ E) :
    ∃ Q : Finset (Point d), IsObstruction (p : ℝ) P.card E Q ∧ IsCollinear Q := by
  let i : Fin d := ⟨0, hd⟩
  have hp0 : 0 < p := by omega
  obtain ⟨r, hr, hdiv, hscale⟩ := exists_scales A hp0
  refine ⟨integerPattern i P, ⟨hE.nullMeasurableSet, card_integerPattern i P,
    r, hr, hdiv, ?_⟩, collinear_integerPattern i P⟩
  intro m hc
  obtain ⟨x, v, hunit, hcopy⟩ := affine_of_copy i (by exact_mod_cast (show 1 < p by omega))
    (hr m) hc
  obtain ⟨j, hj⟩ := hscale m
  obtain ⟨k, hk, hbad⟩ := hex j (r m) x v (sum_pow_of_unit hp0 hunit) hj
  exact hbad (hcopy k hk)

/-- The even-exponent annulus omits every copy on the scale sequence. -/
theorem even_obstruction {d p : ℕ} (hd : 1 ≤ d) (hp : 2 ≤ p) (he : Even p)
    {P : Finset ℤ} {A ε : ℝ} (hit : HitsArcs p P A ε) :
    ∃ Q : Finset (Point d), IsObstruction (p : ℝ) P.card (shell p (fun _ => 1) ε) Q ∧
      IsCollinear Q := by
  apply obstruction_of_exclusion hd hp A _ (isOpen_shell p (fun _ => 1) ε).measurableSet
  exact fun j r x v hunit hscale => even_exclusion j he x v hit hunit hscale

/-- The intersection of signed shells omits every copy on the scale sequence. -/
theorem odd_obstruction {d p : ℕ} (hd : 1 ≤ d) (hp : 2 ≤ p) (ho : Odd p)
    {P : Finset ℤ} {A ε : ℝ} (hit : HitsArcs p P A ε) :
    ∃ Q : Finset (Point d), IsObstruction (p : ℝ) P.card (oddShell p ε) Q ∧ IsCollinear Q := by
  apply obstruction_of_exclusion hd hp A _ (isOpen_oddShell p ε).measurableSet
  exact fun j r x v hunit hscale => odd_exclusion j ho x v hit hunit hscale

end Density.Annular
