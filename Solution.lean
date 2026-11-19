module

public import Density.FullLp
public import Density.Hitting

/-! # The three introduction theorems of arXiv:2604.18544v1

These declarations import only the proof development. The separate Challenge
fixes the same types independently for Lean Comparator.
-/

public section

namespace Density

/-- Theorem 2, including the uniform even-exponent conclusion. -/
theorem integerLp : IntegralLpStatement :=
  integerLp_of_hitting Polynomial.polynomial_hitting

/-- Theorem 1. Specialize the even-exponent conclusion to p = 2. -/
theorem euclidean : EuclideanStatement :=
  euclidean_of_integerLp integerLp

/-- Theorem 3, with exact density for arbitrary real p > 1 different from 2. -/
theorem nonEuclideanLp : FullLpStatement :=
  fullLp

end Density
