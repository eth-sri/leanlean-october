/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.ScaledHomogenization
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Algebra.HomogeneousSlice
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Algebra.ScaledHomogenizationPrimitive
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Irreducibility and coefficient maps of scaled homogeneous models in
arbitrary dimension, including reduction modulo primes. -/

public section
namespace CCDN
open MvPolynomial

/-- Scaled homogenization commutes with mapping the coefficients along a ring homomorphism
`φ`, the scaling factor `h` being replaced by `φ h`. -/
lemma scaledHomogenize_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (d : ℕ) (h : R) (f : MvPolynomial (Fin n) R) :
    map φ (scaledHomogenize d h f) = scaledHomogenize d (φ h) (map φ f) := by
  grind [map_sum, map_monomial,   coeff_map, Finset.sum_subset, support_map_subset, mul_zero, monomial_zero, scaledHomogenize]

/-- Over a field, every nonzero scaling of an irreducible affine equation
has an irreducible homogeneous model. -/
theorem scaledHomogenize_irreducible {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (hir : Irreducible f) {h : K} (hh : h ≠ 0) :
    Irreducible (scaledHomogenize f.totalDegree h f) := by
  let F := scaledHomogenize f.totalDegree h f
  have hF0 : F ≠ 0 := scaledHomogenize_ne_zero _ hh hir.ne_zero
  have hFhom := scaledHomogenize_homogeneous h f le_rfl
  let G := firstCoordinateScale K h hh F
  have hG0 := (firstCoordinateScale K h hh).injective.ne (by simpa using hF0)
  have hGhom : G.IsHomogeneous f.totalDegree := firstCoordinateScaleHom_homogeneous h hFhom
  have hchart : affineChart n G = C (h ^ f.totalDegree) * f := by
    rw [show affineChart n G = homogeneousSlice n h F from
      (homogeneousSlice_eq_chart_scale h F).symm]
    exact homogeneousSlice_scaledHomogenize h f le_rfl
  have hunit : IsUnit (C (h ^ f.totalDegree) : MvPolynomial (Fin n) K) :=
    (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hh)).map C
  have hchartir : Irreducible (affineChart n G) := by
    simp_all [irreducible_isUnit_mul]
  have hchartdeg : (affineChart n G).totalDegree = G.totalDegree := by
    rw [hchart, totalDegree_mul_of_isDomain (C_eq_zero.not.mpr (pow_ne_zero _ hh)) hir.ne_zero,
      totalDegree_C, zero_add, hGhom.totalDegree hG0]
  exact (MulEquiv.irreducible_iff (firstCoordinateScale K h hh)).mp
    (irreducible_of_affineChart_irreducible G hchartdeg hchartir)

/-- Prime scaling preserves integer irreducibility whenever it preserves
primitivity; avoiding the constant coefficient discharges that condition. -/
theorem scaledHomogenize_integer_irreducible {n : ℕ}
    (f : CCDN.IntegerPolynomial n) (hprim : PrimitiveIntegerPolynomial f)
    (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {p : ℕ} (hp : p.Prime) (hp0 : ¬ ↑p ∣ f.coeff 0) :
    Irreducible (scaledHomogenize f.totalDegree ↑p f) := by
  apply (hprim.scaledHomogenize f.totalDegree hp hp0).irreducible_of_rational_map
  rw [scaledHomogenize_map]
  have hdeg : (CCDN.rationalPolynomial f).totalDegree = f.totalDegree :=
      totalDegree_map_of_injective Int.cast_injective _
  rw [← hdeg]
  exact scaledHomogenize_irreducible _ (rational_map_irreducible_of_integer f hir hd)
    (by aesop)

end CCDN
