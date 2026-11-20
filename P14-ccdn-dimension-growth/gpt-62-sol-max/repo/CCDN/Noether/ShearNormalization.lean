/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.ConstantLeadingBadReduction
public import CCDN.Noether.BivariateTotalDegree
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.Fin.VecNotation

/-! Bounded integral shears give full outer degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

section

variable {R : Type*} [CommRing R]
include R

/-- Variable zero corresponds to the outer variable of the nested polynomial ring. -/
lemma bivariatePolynomialEquiv_X_zero :
    bivariatePolynomialEquiv R (MvPolynomial.X 0) = (X : R[X][X]) := by
  simp [bivariatePolynomialEquiv, MvPolynomial.finSuccEquiv_X_zero]

/-- Variable one corresponds to the inner variable of the nested polynomial ring. -/
lemma bivariatePolynomialEquiv_X_one :
    bivariatePolynomialEquiv R (MvPolynomial.X 1) = (C X : R[X][X]) := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X (Fin.succ (0 : Fin 1)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp

/-- Constants correspond to constants of the nested polynomial ring. -/
lemma bivariatePolynomialEquiv_C (a : R) :
    bivariatePolynomialEquiv R (MvPolynomial.C a) = C (C a) := by
  exact (bivariatePolynomialEquiv R).commutes a

end

/-- The identification of two-variable polynomials with nested polynomials commutes with applying a
coefficient ring homomorphism. -/
lemma bivariatePolynomialEquiv_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : MvPolynomial (Fin 2) R) :
    bivariateMap φ (bivariatePolynomialEquiv R f) =
      bivariatePolynomialEquiv S (MvPolynomial.map φ f) := by
  ext i j
  grind [bivariateMap_coeff, bivariatePolynomialEquiv_coeff, MvPolynomial.coeff_map]

end
end CCDN
