/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.Hilbert.FilteredIntersection

/-!
# The affine Hilbert degree of a curve

An affine algebraic set is represented by an ideal in `ℚ[x₁,…,xₙ]`. For an integral curve,
its degree is the slope of the eventually linear affine Hilbert function: the dimension
of polynomials of total degree at most `M` in its coordinate ring is `d*M + c` for large `M`.
The slope of an eventually linear function is unique, and a pointwise inequality between two
eventually linear functions compares their slopes (`eventual_linear_slope_le`).
-/

@[expose] public section

namespace CCDN

section

variable {n : ℕ} (I : Ideal (CoordinatePolynomial n))

/-- The affine Hilbert function: the dimension of the polynomials of total degree at
most `M` in the coordinate ring. -/
noncomputable def affineHilbertFunction
    (M : ℕ) : ℕ := Module.finrank ℚ (filteredCoordinateSpace I M)

/-- Degree via the eventual affine Hilbert polynomial. This condition is mathematical
data about the coordinate ring, and contains no point-counting estimate. -/
def HasAffineCurveDegree (d : ℕ) : Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M : ℕ, N ≤ M →
    (affineHilbertFunction I M) = d * M + c

/-- The affine Hilbert degree of a curve is unique: if `I` has affine curve degree `d` and `e`, then
`d = e`. -/
theorem affineCurveDegree_unique {I : Ideal (CoordinatePolynomial n)} {d e : ℕ}
    (hd : HasAffineCurveDegree I d) (he : HasAffineCurveDegree I e) : d = e := by
  obtain ⟨N, c, hN⟩ := hd
  obtain ⟨P, k, hP⟩ := he
  have hN1 := hN (max N P + 1) (by omega)
  grind

end

end CCDN
