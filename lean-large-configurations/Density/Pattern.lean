module

public import Density.Definitions
public import Mathlib.Tactic

/-! The explicit finite configuration in Section 4. Write the dimension as
d+1 and the size of the long arm as m. Its m+2d labels are distinct. -/

@[expose] public section

namespace Density

/-- The vector with value a in coordinate i and zero in the other coordinates. -/
def axisPoint {d : ℕ} (i : Fin d) (a : ℝ) : Point d :=
  fun j => if j = i then a else 0

def signValue (b : Bool) : ℝ := if b then 1 else -1

private lemma signValue_ne (b : Bool) : signValue b ≠ 0 := by
  cases b <;> norm_num [signValue]

private lemma signValue_inj : Function.Injective signValue := by
  intro b c h
  cases b <;> cases c <;> norm_num [signValue] at *

/-- Labels for the m points on the first axis and the two points on each
remaining axis. Lean numbers the first axis 0. -/
def crossLabel {d m : ℕ} : Fin m ⊕ (Fin d × Bool) → Point (d + 1)
  | .inl k => axisPoint 0 ((k.val : ℝ) - 1)
  | .inr (i, b) => axisPoint i.succ (signValue b)

theorem crossLabel_injective (d m : ℕ) : Function.Injective (@crossLabel d m) := by
  intro x y h
  cases x with
  | inl k =>
    cases y with
    | inl l =>
      have h' := congrFun h 0
      simp [crossLabel, axisPoint] at h'
      have hv : (k.val : ℝ) = (l.val : ℝ) := by exact_mod_cast h'
      exact congrArg Sum.inl (Fin.ext (by exact_mod_cast hv))
    | inr z =>
      obtain ⟨i, b⟩ := z
      have h' := congrFun h i.succ
      simp [crossLabel, axisPoint, Fin.succ_ne_zero] at h'
      exact False.elim (signValue_ne b h'.symm)
  | inr z =>
    obtain ⟨i, b⟩ := z
    cases y with
    | inl k =>
      have h' := congrFun h i.succ
      simp [crossLabel, axisPoint, Fin.succ_ne_zero] at h'
      exact False.elim (signValue_ne b h')
    | inr w =>
      obtain ⟨j, c⟩ := w
      have h' := congrFun h i.succ
      have hij : i = j := by
        by_contra hne
        have hne' : i.succ ≠ j.succ := fun he => hne (Fin.succ_inj.mp he)
        simp [crossLabel, axisPoint, hne'] at h'
        exact signValue_ne b h'
      subst j
      have hbc : b = c := signValue_inj (by simpa [crossLabel, axisPoint] using h')
      subst c
      rfl

/-- The pattern with first-axis indices -1, 0, ..., m-2. -/
noncomputable def crossPattern (d m : ℕ) : Finset (Point (d + 1)) :=
  Finset.univ.map ⟨crossLabel, crossLabel_injective d m⟩

theorem card_crossPattern (d m : ℕ) : (crossPattern d m).card = m + 2 * d := by
  simp [crossPattern, Nat.mul_comm]

theorem crossLabel_mem {d m : ℕ} (i : Fin m ⊕ (Fin d × Bool)) :
    crossLabel i ∈ crossPattern d m := by
  apply Finset.mem_map.mpr
  exact ⟨i, Finset.mem_univ _, rfl⟩

@[simp] theorem axisPoint_zero {d : ℕ} (i : Fin d) : axisPoint i 0 = 0 := by
  ext j
  simp [axisPoint]

/-- The arm of length m, with offsets -1 through m-2. -/
noncomputable def firstArm (m : ℕ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun k : Fin m => (k.val : ℝ) - 1)

theorem int_mem_firstArm {m : ℕ} (k : ℤ) (hk₀ : -1 ≤ k) (hk₁ : k < (m : ℤ) - 1) :
    (k : ℝ) ∈ firstArm m := by
  classical
  let l : Fin m := ⟨(k+1).toNat, by omega⟩
  have hl : (l.val : ℤ) = k + 1 := by dsimp [l]; omega
  have hr : (l.val : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hl
  exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, by linarith⟩

/-- For each axis, all model parameters needed to determine its image. -/
noncomputable def arm {d : ℕ} (m : ℕ) (i : Fin (d + 1)) : Finset ℝ := by
  classical
  exact if i = 0 then firstArm m else {-1, 0, 1}

theorem small_mem_arm {d m : ℕ} (hm : 3 ≤ m) (i : Fin (d + 1)) (t : ℤ)
    (ht₀ : -1 ≤ t) (ht₁ : t ≤ 1) : (t : ℝ) ∈ arm m i := by
  classical
  by_cases hi : i = 0
  · simp [arm, hi]
    apply int_mem_firstArm t ht₀
    omega
  · simp [arm, hi]
    interval_cases t <;> norm_num

theorem axisPoint_mem_crossPattern {d m : ℕ} (hm : 3 ≤ m) (i : Fin (d + 1))
    (t : ℝ) (ht : t ∈ arm m i) : axisPoint i t ∈ crossPattern d m := by
  classical
  induction i using Fin.cases with
  | zero =>
    change t ∈ firstArm m at ht
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    exact crossLabel_mem (Sum.inl k)
  | succ i =>
    simp [arm, Fin.succ_ne_zero] at ht
    rcases ht with rfl | rfl | rfl
    · exact @crossLabel_mem d m (Sum.inr (i, false))
    · have hzero : axisPoint (0 : Fin (d + 1)) (0 : ℝ) ∈ crossPattern d m := by
        let l : Fin m := ⟨1, by omega⟩
        have h := @crossLabel_mem d m (Sum.inl l)
        simpa [crossLabel, l] using h
      simpa using hzero
    · exact @crossLabel_mem d m (Sum.inr (i, true))

end Density
