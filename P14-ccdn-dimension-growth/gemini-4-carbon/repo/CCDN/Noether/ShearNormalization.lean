/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateTotalDegree
public import CCDN.Noether.ClosedFormHeight
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Basic equivalences for nested bivariate polynomials. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

lemma bivariatePolynomialEquiv_X_zero {R : Type*} [CommRing R] :
    bivariatePolynomialEquiv R (MvPolynomial.X 0) = (X : R[X][X]) := by
  simp [bivariatePolynomialEquiv, MvPolynomial.finSuccEquiv_X_zero]

lemma bivariatePolynomialEquiv_X_one {R : Type*} [CommRing R] :
    bivariatePolynomialEquiv R (MvPolynomial.X 1) = (C X : R[X][X]) := by
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv R 1 (MvPolynomial.X (Fin.succ (0 : Fin 1)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  simp

lemma bivariatePolynomialEquiv_C {R : Type*} [CommRing R] (a : R) :
    bivariatePolynomialEquiv R (MvPolynomial.C a) = C (C a) :=
  (bivariatePolynomialEquiv R).commutes a

lemma bivariatePolynomialEquiv_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : MvPolynomial (Fin 2) R) :
    bivariateMap φ (bivariatePolynomialEquiv R f) =
      bivariatePolynomialEquiv S (MvPolynomial.map φ f) := by
  ext i j
  simp only [bivariateMap_coeff, bivariatePolynomialEquiv_coeff, MvPolynomial.coeff_map]

lemma bivariate_leadingCoeff_eq_constant {R : Type*} [CommRing R]
    (f : R[X][X]) (htotal : bivariateTotalDegree f ≤ f.natDegree) :
    f.leadingCoeff = C (f.leadingCoeff.coeff 0) := by
  by_cases hc : f.leadingCoeff = 0
  · simp [hc]
  have h := bivariateTotalDegree_coeff_le f f.natDegree f.leadingCoeff.natDegree
    (Polynomial.leadingCoeff_ne_zero.mpr hc)
  exact eq_C_of_natDegree_eq_zero (by omega)

end
end CCDN
