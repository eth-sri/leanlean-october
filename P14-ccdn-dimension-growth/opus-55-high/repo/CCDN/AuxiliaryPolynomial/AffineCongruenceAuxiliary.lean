/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.AffineCongruenceHeight
import CCDN.ForMathlib.StandardExponents
import CCDN.AuxiliaryPolynomial.StandardMonomialAuxiliary
import CCDN.AuxiliaryPolynomial.WeightedMonomialDeterminant

/-! Auxiliary polynomials from the competing congruence determinant
lower bound and weighted archimedean upper bound. -/

namespace CCDN
noncomputable section
open MvPolynomial Finset

theorem square_minorGcd_eq_abs_det {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) :
    Int.Matrix.minorGcd A = |A.det| := by
  let : Nonempty (Set.powersetCard (Fin s) s) :=
    ⟨⟨univ, by simp⟩⟩
  rw [Int.Matrix.minorGcd]
  have hp : exteriorPower.plucker s A.row = fun _ => A.det :=
    funext (fun S => exteriorPower.plucker_fin_eq_det A.row S)
  rw [hp, Finset.gcd_eq_gcd_image, Finset.image_const univ_nonempty]
  simp [Finset.gcd_singleton, id_eq, ← Int.abs_eq_normalize]

/-- The lower bound for the logarithm of a nonzero `s × s` determinant of monomials evaluated
at integral zeros of an absolutely irreducible affine equation of degree `d` in `n + 2`
variables with coefficient height at most `H`, when the zeros lie in smooth residue classes
modulo primes whose logarithms sum to `Q`. -/
def affineCongruenceDeterminantLower (n d s : ℕ) (H Q : ℝ) : ℝ :=
  ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
    (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
      (Real.log s - (n + 1 : ℝ) * (4 * Real.log d +
        congruenceHeightCharge (n + 3) d H Q) - hypersurfaceDeterminantError n) +
    (hypersurfaceDeterminantMain n s - (n + 2 : ℝ) * s) * Q

variable {B : ℝ}
