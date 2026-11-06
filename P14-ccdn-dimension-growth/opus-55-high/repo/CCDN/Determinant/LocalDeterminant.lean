/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

namespace CCDN

open Matrix

section
variable {s N : ℕ}

/-- Cauchy–Binet valuation bound: if `p ^ weight i` divides the `i`-th row of `V`, and every choice
of `s` increasing row indices has total weight at least `e`, then `p ^ e` divides `det (U * V)`. -/
theorem pow_dvd_det_of_weighted_factorization {R : Type*} [CommRing R]
    (U : Matrix (Fin s) (Fin N) R) (V : Matrix (Fin N) (Fin s) R)
    (p : R) (weight : Fin N → ℕ) (e : ℕ)
    (hV : ∀ i j, p ^ weight i ∣ V i j)
    (he : ∀ t : Fin s ↪o Fin N, e ≤ ∑ i, weight (t i)) :
    p ^ e ∣ (U * V).det := by
  rw [Matrix.det_mul_eq_sum_det_submatrix]
  apply Finset.dvd_sum
  intro S _
  let t := (S : Finset (Fin N)).orderEmbOfFin (Set.powersetCard.card_eq S)
  have hminor : (∏ i, (fun i => p ^ weight (t i)) i) ∣ (V.submatrix t id).det := by
    choose Q hQ using (fun i j => hV (t i) j)
    have hA : (V.submatrix t id) = Matrix.of (fun i j => (fun i => p ^ weight (t i)) i * Q i j) := by aesop
    rw [hA]
    exact ⟨(Matrix.of Q).det, Matrix.det_mul_column (fun i => p ^ weight (t i)) (Matrix.of Q)⟩
  rw [Finset.prod_pow_eq_pow_sum] at hminor
  exact dvd_mul_of_dvd_right ((pow_dvd_pow p (he t)).trans hminor) _

end

