/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ArithmeticHeights.BombieriVaaler
import CCDN.Determinant.GramDeterminant

/-!
# Determinant divisibility from filtered factorizations

Cauchy–Binet turns a weighted factorization into a determinant valuation bound. The
univariate specialization gives the quadratic exponent `s*(s-1)/2` for polynomial
evaluations in one residue class. The passage from a curve's local ring to such a
factorization is proved in `FilteredDeterminant` in arbitrary ambient dimension.
`HypersurfaceResidue` supplies the sharp singular hypersurface bound.
-/

@[expose] public section

namespace CCDN

open Matrix

/-- Cauchy–Binet valuation bound: if `p ^ weight i` divides the `i`-th row of `V`, and every choice
of `s` increasing row indices has total weight at least `e`, then `p ^ e` divides `det (U * V)`. -/
theorem pow_dvd_det_of_weighted_factorization {R : Type*} [CommRing R] {s N : ℕ}
    (U : Matrix (Fin s) (Fin N) R) (V : Matrix (Fin N) (Fin s) R)
    (p : R) (weight : Fin N → ℕ) (e : ℕ)
    (hV : ∀ i j, p ^ weight i ∣ V i j)
    (he : ∀ t : Fin s ↪o Fin N, e ≤ ∑ i, weight (t i)) :
    p ^ e ∣ (U * V).det := by
  rw [Matrix.det_mul_eq_sum_det_submatrix]
  refine Finset.dvd_sum fun t _ => ?_
  have hminor := prod_row_factors_dvd_det (V.submatrix t id)
    (fun i => p ^ weight (t i)) (fun i j => hV (t i) j)
  rw [Finset.prod_pow_eq_pow_sum] at hminor
  exact dvd_mul_of_dvd_right ((pow_dvd_pow p (he t)).trans hminor) _

end CCDN
