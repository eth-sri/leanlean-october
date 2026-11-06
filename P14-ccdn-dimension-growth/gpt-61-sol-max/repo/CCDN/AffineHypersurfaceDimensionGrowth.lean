/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

public import CCDN.Statements
import CCDN.Hypersurface.AffineHypersurfaceCount

/-! CCDN Theorem 4 with the corrected degree exponent of Remark 4.3.8.
In `N = n + 3` variables the exponent is `18 + 3n = 3N + 9`: the corrected surface
bound `d^18` and a cost of `d^3` for each bounded good hyperplane slice
(`affineHypersurfaceGrowth`, in `CCDN.Hypersurface.AffineHypersurfaceCount`). -/

public section
namespace CCDN
open MvPolynomial

/-- CCDN Theorem 4 for integer equations in all affine ambient dimensions
at least three. The constant depends only on dimension, and the explicit
degree exponent is 18 + 3n in n+3 variables. -/
theorem affine_hypersurface_dimension_growth (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : CCDN.IntegerPolynomial (n + 3),
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus (CCDN.rationalPolynomial f)) B : ℝ) ≤
        C * ↑f.totalDegree ^ (18 + 3 * n) * B ^ (n + 1) :=
  affineHypersurfaceGrowth n

/-- CCDN Theorem 4 for rational equations, with the degree exponent 18 + 3n in
n+3 variables. -/
theorem affine_hypersurface_dimension_growth_rat (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : CCDN.CoordinatePolynomial (n + 3),
      HasAbsIrreducibleTopFormRat f →
      5 ≤ f.totalDegree → ∀ B : ℝ, 1 ≤ B →
      (count (zeroLocus f) B : ℝ) ≤
        C * ↑f.totalDegree ^ (18 + 3 * n) * B ^ (n + 1) :=
  (affineHypersurfaceGrowth n).rational

end CCDN
