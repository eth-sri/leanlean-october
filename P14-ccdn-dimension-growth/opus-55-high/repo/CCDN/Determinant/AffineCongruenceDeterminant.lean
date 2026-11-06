/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.PolynomialPredicates
import CCDN.Algebra.ScaledHomogenization
import CCDN.Determinant.HypersurfaceDeterminantRank
import CCDN.Height.CountingHypotheses
import CCDN.AuxiliaryPolynomial.UnscaledHypersurfaceBadPrimes
import CCDN.Determinant.SmoothCongruenceDeterminant

/-! Congruence-refined determinant estimates for affine zeros and
arbitrary bounded-degree polynomial evaluation columns. -/

namespace CCDN
section
open MvPolynomial Finset

/-- The homogeneous coordinates `(1, x)` of an integer point `x` are primitive: their gcd is `1`. -/
lemma primitive_affine_integer_coordinates {n : ℕ} (x : Fin n → ℤ) :
    Finset.univ.gcd (Fin.cons 1 x) = 1 := by
  have he : insert (0 : Fin (n + 1)) univ = univ := insert_eq_of_mem (mem_univ _)
  have hh := congrArg (fun S : Finset (Fin (n + 1)) => S.gcd (Fin.cons 1 x)) he
  simpa only [Finset.gcd_insert, Fin.cons_zero, gcd_one_left] using hh.symm
