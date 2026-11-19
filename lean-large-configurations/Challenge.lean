module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Point configurations and centered-cube densities

Definitions for Theorems 1–3 of Kovač and Santos Sepčić, arXiv:2604.18544v1.
The same definitions occur verbatim in the standalone Challenge.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology BigOperators

namespace Density

/-- Coordinate space equipped with product Lebesgue measure. We specify the
distance explicitly to avoid using the supremum metric on the function space. -/
abbrev Point (d : ℕ) := Fin d → ℝ

/-- The distance for a finite real exponent, used only when `1 < p`. -/
noncomputable def lpDistance {d : ℕ} (p : ℝ) (x y : Point d) : ℝ :=
  (∑ i : Fin d, |x i - y i| ^ p) ^ (1 / p : ℝ)

/-- The closed cube of side length R centered at the origin. -/
def centeredCube (d : ℕ) (R : ℝ) : Set (Point d) :=
  {x | ∀ i, -(R / 2) ≤ x i ∧ x i ≤ R / 2}

/-- The ratio in the definition of asymptotic density, used as R tends
to positive infinity. Every centered cube of finite side length is bounded. -/
noncomputable def cubeRatio {d : ℕ} (E : Set (Point d)) (R : ℝ) : ℝ :=
  (volume (E ∩ centeredCube d R)).toReal / R ^ d

/-- The actual density exists and equals a. The side length is real. -/
def HasDensity {d : ℕ} (E : Set (Point d)) (a : ℝ) : Prop :=
  Tendsto (cubeRatio E) atTop (𝓝 a)

/-- Lower asymptotic density using the same centered cubes. -/
noncomputable def lowerDensity {d : ℕ} (E : Set (Point d)) : ℝ :=
  Filter.liminf (cubeRatio E) atTop

/-- Membership in one affine line with a nonzero direction vector. -/
def IsCollinear {d : ℕ} (P : Finset (Point d)) : Prop :=
  ∃ a v : Point d, v ≠ 0 ∧ ∀ x ∈ P, ∃ t : ℝ, x = a + t • v

/-- An injective labeling of a subset of E by P. The labeling is a
bijection onto its image, so every pairwise scaled isometric copy is included. -/
def HasScaledCopy {d : ℕ} (p r : ℝ) (P : Finset (Point d)) (E : Set (Point d)) : Prop :=
  ∃ f : P → E, Function.Injective f ∧
    ∀ u v : P, lpDistance p (f u).val (f v).val = r * lpDistance p u.val v.val

/-- A Lebesgue-measurable E, an n-element P, and a positive sequence of
forbidden scales diverging to infinity. The same E and P work for every j. -/
def IsObstruction {d : ℕ} (p : ℝ) (n : ℕ) (E : Set (Point d)) (P : Finset (Point d)) : Prop :=
  NullMeasurableSet E volume ∧ P.card = n ∧
    ∃ r : ℕ → ℝ, (∀ j, 0 < r j) ∧ Tendsto r atTop atTop ∧
      ∀ j, ¬HasScaledCopy p (r j) P E

/-- Collinear obstruction with an actual density at least the logarithmic bound. -/
def ActualCase (d n : ℕ) (p C : ℝ) : Prop :=
  ∃ (E : Set (Point d)) (P : Finset (Point d)), IsObstruction p n E P ∧ IsCollinear P ∧
    ∃ a : ℝ, HasDensity E a ∧ 1 - C * Real.log (n : ℝ) / (n : ℝ) ≤ a

/-- Collinear obstruction with the lower asymptotic density bound. -/
def LowerCase (d n : ℕ) (p C : ℝ) : Prop :=
  ∃ (E : Set (Point d)) (P : Finset (Point d)), IsObstruction p n E P ∧ IsCollinear P ∧
    1 - C * Real.log (n : ℝ) / (n : ℝ) ≤ lowerDensity E

/-- Theorem 1. The proof supplies both a constant and a cutoff independent of d. -/
def EuclideanStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ d : ℕ, 1 ≤ d →
    ∀ n : ℕ, N ≤ n → ActualCase d n 2 C

/-- Theorem 2. The second conjunct quantifies the constant before the
dimension, and asks for the actual density for the same obstruction.
The cutoff for the even case comes from Proposition 5 and depends only on p. -/
def IntegralLpStatement : Prop :=
  (∀ (d p : ℕ), 1 ≤ d → 2 ≤ p →
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → LowerCase d n (p : ℝ) C) ∧
  (∀ p : ℕ, 2 ≤ p → Even p →
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ d : ℕ, 1 ≤ d →
      ∀ n : ℕ, N ≤ n → ActualCase d n (p : ℝ) C)

/-- Theorem 3. The exponent is real. The denominator uses real subtraction. -/
def FullLpStatement : Prop :=
  ∀ (d : ℕ) (p : ℝ), 1 ≤ d → 1 < p → p ≠ 2 →
    ∀ n : ℕ, 2 * d + 1 ≤ n →
      ∃ (E : Set (Point d)) (P : Finset (Point d)), IsObstruction p n E P ∧
        HasDensity E (1 - 1 / ((n : ℝ) - 2 * (d : ℝ) + 2))

/-- Theorem 1 of arXiv:2604.18544v1. Challenge declaration only. -/
theorem euclidean : EuclideanStatement := by sorry

/-- Theorem 2, including its uniform even-exponent clause. Challenge declaration only. -/
theorem integerLp : IntegralLpStatement := by sorry

/-- Theorem 3, with the exact density for every allowed n. Challenge declaration only. -/
theorem nonEuclideanLp : FullLpStatement := by sorry

end Density
