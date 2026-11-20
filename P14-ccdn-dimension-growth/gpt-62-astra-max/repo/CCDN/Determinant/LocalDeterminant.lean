/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CCDN.Determinant.MinorGcd
import Mathlib.Data.Fin.Tuple.Sort
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
of `s` distinct row indices has total weight at least `e`, then `p ^ e` divides `det (U * V)`. -/
theorem pow_dvd_det_of_weighted_factorization {R ι : Type*} [CommRing R] [Fintype ι] {s : ℕ}
    (U : Matrix (Fin s) ι R) (V : Matrix ι (Fin s) R) (p : R) (weight : ι → ℕ) (e : ℕ)
    (hV : ∀ i j, p ^ weight i ∣ V i j) (he : ∀ t : Fin s ↪ ι, e ≤ ∑ i, weight (t i)) :
    p ^ e ∣ (U * V).det := by
  apply dvd_det_mul_of_row_minors
  intro t
  have h := prod_row_factors_dvd_det (V.submatrix t id) _ (fun i j => hV (t i) j)
  rw [Finset.prod_pow_eq_pow_sum] at h
  exact (pow_dvd_pow p (he t)).trans h

end CCDN
