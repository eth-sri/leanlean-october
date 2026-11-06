/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.EulerPairBasis
import CCDN.Noether.EulerPairBasisValues
import CCDN.Noether.ShearNormalization

/-! Euler columns and their coefficient minors commute with every coefficient
ring homomorphism, including specialization and reduction in any characteristic. -/

namespace CCDN
section
open MvPolynomial Module

section
variable {R : Type*} [CommRing R] (k : ℕ)

/-- The basis vector of `EulerPairSpace R k` from the first low block corresponds to the pair
`(m, 0)` for the associated monomial `m` of degree at most `k`. -/
lemma eulerPairCoordinates_basis_left (i : EulerLowIndex k) :
    eulerPairCoordinates R k (eulerPairBasis R k (.inl i)) =
      (monomial ((Finsupp.degreeLeEquivSym (Fin 2) k).symm i).val 1, 0) := by
  simp [eulerPairCoordinates, eulerPairBasis, Basis.prod_apply, eulerLowBasis_apply]

/-- The basis vector of `EulerPairSpace R k` from the second low block corresponds to the pair
`(0, m)` for the associated monomial `m` of degree at most `k`. -/
lemma eulerPairCoordinates_basis_right (i : EulerLowIndex k) :
    eulerPairCoordinates R k (eulerPairBasis R k (.inr (.inl i))) =
      (0, monomial ((Finsupp.degreeLeEquivSym (Fin 2) k).symm i).val 1) := by
  simp [eulerPairCoordinates, eulerPairBasis, Basis.prod_apply, eulerLowBasis_apply]

/-- The basis vector of `EulerPairSpace R k` from the homogeneous block corresponds to the radial
pair `(y * m, -(x * m))` for the associated monomial `m` of degree `k`. -/
lemma eulerPairCoordinates_basis_radial (i : EulerTopIndex k) :
    eulerPairCoordinates R k (eulerPairBasis R k (.inr (.inr i))) =
      (X 1 * monomial ((degreeEqEquivSym (Fin 2) k).symm i).val 1,
        -(X 0 * monomial ((degreeEqEquivSym (Fin 2) k).symm i).val 1)) := by
  simp [eulerPairCoordinates, eulerPairBasis, Basis.prod_apply, eulerTopBasis_apply]

end

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

lemma eulerBivariatePair_basis_map
    (k : ℕ) (i : EulerColumns k) :
    (bivariateMap φ (eulerBivariatePair R k (eulerPairBasis R k i)).1,
      bivariateMap φ (eulerBivariatePair R k (eulerPairBasis R k i)).2) =
      eulerBivariatePair S k (eulerPairBasis S k i) := by
  simp only [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
    AlgEquiv.toLinearMap_apply, bivariatePolynomialEquiv_map]
  have hh : (map φ (eulerPairCoordinates R k (eulerPairBasis R k i)).1,
      map φ (eulerPairCoordinates R k (eulerPairBasis R k i)).2) =
      eulerPairCoordinates S k (eulerPairBasis S k i) := by
    rcases i with i | i | i
    · rw [eulerPairCoordinates_basis_left, eulerPairCoordinates_basis_left]
      simp
    · rw [eulerPairCoordinates_basis_right, eulerPairCoordinates_basis_right]
      simp
    · rw [eulerPairCoordinates_basis_radial, eulerPairCoordinates_basis_radial]
      simp
  apply Prod.ext
  · grind
  · grind

/-- The exact-order coefficient matrix specializes entry by entry over any
commutative coefficient ring. -/
theorem eulerClosedFormCoefficientMatrix_map
    (k : ℕ) (f : Polynomial (Polynomial R)) :
    (eulerClosedFormCoefficientMatrix k f).map φ =
      eulerClosedFormCoefficientMatrix k (bivariateMap φ f) := by
  ext i j
  change φ (((closedFormOperator f
    (eulerBivariatePair R k (eulerPairBasis R k j))).coeff i.1).coeff i.2) = _
  rw [← bivariateMap_coeff, bivariateMap_closedFormOperator, eulerBivariatePair_basis_map]
  rfl

/-- Every minor of the Euler closed-form coefficient matrix commutes with applying a coefficient
ring homomorphism `φ` to the equation. -/
theorem eulerClosedForm_minor_map
    (k r : ℕ) (f : Polynomial (Polynomial R))
    (a : Fin r → ℕ × ℕ) (c : Fin r → EulerColumns k) :
    φ (((eulerClosedFormCoefficientMatrix k f).submatrix a c).det) =
      ((eulerClosedFormCoefficientMatrix k (bivariateMap φ f)).submatrix a c).det := by
  rw [φ.map_det]
  change (((eulerClosedFormCoefficientMatrix k f).map φ).submatrix a c).det = _
  rw [eulerClosedFormCoefficientMatrix_map]

