/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Noether.EulerUniversalForms
import CCDN.Noether.EulerMonomialColumns
import CCDN.Noether.EulerPairSpecialization
import CCDN.Noether.ShearNormalization

/-! Each row and Euler column uses at most one coefficient of the defining
equation, with integer multiplier bounded by its degree. -/

namespace CCDN
noncomputable section
open Polynomial

section
variable (k : ℕ)

def eulerLowExponent (i : EulerLowIndex k) : Fin 2 →₀ ℕ :=
  ((Finsupp.degreeLeEquivSym (Fin 2) k).symm i).val

def eulerTopExponent (i : EulerTopIndex k) : Fin 2 →₀ ℕ :=
  ((degreeEqEquivSym (Fin 2) k).symm i).val

lemma eulerLowExponent_degree (i : EulerLowIndex k) :
    eulerLowExponent k i 0 + eulerLowExponent k i 1 ≤ k := by
  have hh := ((Finsupp.degreeLeEquivSym (Fin 2) k).symm i).property
  change (eulerLowExponent k i).sum (fun _ e => e) ≤ k at hh
  rwa [bivariate_exponent_eq (eulerLowExponent k i), bivariate_exponent_sum] at hh

lemma eulerTopExponent_degree (i : EulerTopIndex k) :
    eulerTopExponent k i 0 + eulerTopExponent k i 1 = k := by
  have hh := ((degreeEqEquivSym (Fin 2) k).symm i).property
  change (eulerTopExponent k i).sum (fun _ e => e) = k at hh
  rwa [bivariate_exponent_eq (eulerTopExponent k i), bivariate_exponent_sum] at hh

lemma eulerLowExponent_injective : Function.Injective (eulerLowExponent k) :=
  Subtype.val_injective.comp (Finsupp.degreeLeEquivSym (Fin 2) k).symm.injective

end

section
variable (k : ℕ) (col : EulerColumns k) (i : EulerLowIndex (k + 2))

def eulerMonomialOutput
    : ℕ × ℕ :=
  let s := eulerLowExponent (k + 2) i 0
  let t := eulerLowExponent (k + 2) i 1
  match col with
  | .inl j => (eulerLowExponent k j 0 + s, eulerLowExponent k j 1 + t - 1)
  | .inr (.inl j) => (eulerLowExponent k j 0 + s - 1, eulerLowExponent k j 1 + t)
  | .inr (.inr j) => (eulerTopExponent k j 0 + s, eulerTopExponent k j 1 + t)

def eulerMonomialWeight : ℤ :=
  let s := eulerLowExponent (k + 2) i 0
  let t := eulerLowExponent (k + 2) i 1
  match col with
  | .inl j => (eulerLowExponent k j 1 : ℤ) - t
  | .inr (.inl j) => (s : ℤ) - eulerLowExponent k j 0
  | .inr (.inr _) => (k + 2 : ℕ) - (s : ℤ) - t

end

section
variable {R : Type*} [CommRing R] (k : ℕ)

lemma eulerBivariatePair_basis_left (i : EulerLowIndex k) :
    eulerBivariatePair R k (eulerPairBasis R k (.inl i)) =
      (monomial (eulerLowExponent k i 0) (monomial (eulerLowExponent k i 1) (1 : R)), 0) := by
  simp [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
    AlgEquiv.toLinearMap_apply, eulerPairCoordinates_basis_left, bivariatePolynomialEquiv_monomial,
    map_zero, eulerLowExponent]

lemma eulerBivariatePair_basis_right
    (i : EulerLowIndex k) :
    eulerBivariatePair R k (eulerPairBasis R k (.inr (.inl i))) =
      (0, monomial (eulerLowExponent k i 0) (monomial (eulerLowExponent k i 1) (1 : R))) := by
  simp [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
    AlgEquiv.toLinearMap_apply, eulerPairCoordinates_basis_right, bivariatePolynomialEquiv_monomial,
    map_zero, eulerLowExponent]

lemma eulerBivariatePair_basis_radial
    (i : EulerTopIndex k) :
    eulerBivariatePair R k (eulerPairBasis R k (.inr (.inr i))) =
      (monomial (eulerTopExponent k i 0) (monomial (eulerTopExponent k i 1 + 1) (1 : R)),
       -(monomial (eulerTopExponent k i 0 + 1) (monomial (eulerTopExponent k i 1) (1 : R)))) := by
  simp [eulerBivariatePair, LinearMap.comp_apply, LinearMap.prodMap_apply,
    AlgEquiv.toLinearMap_apply, eulerPairCoordinates_basis_radial, map_mul, map_neg,
    bivariatePolynomialEquiv_monomial, bivariatePolynomialEquiv_X_zero,
    bivariatePolynomialEquiv_X_one, C_mul_monomial, X_mul_monomial, eulerTopExponent]

end

section
variable (k : ℕ) (col : EulerColumns k) (i : EulerLowIndex (k + 2))

theorem eulerClosedForm_monomial_output
    :
    eulerClosedFormOperator k (eulerCoefficientMonomial ℤ (k + 2) i)
      (eulerPairBasis ℤ k col) =
      monomial (eulerMonomialOutput k col i).1
        (monomial (eulerMonomialOutput k col i).2 (eulerMonomialWeight k col i)) := by
  change closedFormOperator _ (eulerBivariatePair ℤ k (eulerPairBasis ℤ k col)) = _
  rw [eulerCoefficientMonomial, bivariatePolynomialEquiv_monomial]
  rcases col with j | j | j
  · rw [eulerBivariatePair_basis_left, closedFormOperator_monomial_left]
    rfl
  · rw [eulerBivariatePair_basis_right, closedFormOperator_monomial_right]
    rfl
  · rw [eulerBivariatePair_basis_radial, closedFormOperator_monomial_radial,
      eulerTopExponent_degree]
    rfl

end

variable (k : ℕ)

theorem eulerClosedForm_monomial_entry (row : ℕ × ℕ)
    (col : EulerColumns k) (i : EulerLowIndex (k + 2)) :
    eulerClosedFormCoefficientMatrix k (eulerCoefficientMonomial ℤ (k + 2) i) row col =
      if eulerMonomialOutput k col i = row then eulerMonomialWeight k col i else 0 := by
  change ((eulerClosedFormOperator k (eulerCoefficientMonomial ℤ (k + 2) i)
    (eulerPairBasis ℤ k col)).coeff row.1).coeff row.2 = _
  rw [eulerClosedForm_monomial_output]
  by_cases h₀ : (eulerMonomialOutput k col i).1 = row.1 <;>
    by_cases h₁ : (eulerMonomialOutput k col i).2 = row.2 <;>
    simp [coeff_monomial, Prod.ext_iff, h₀, h₁]

