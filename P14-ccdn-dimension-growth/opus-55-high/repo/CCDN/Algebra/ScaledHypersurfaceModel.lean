/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.ScaledHomogenization
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Algebra.HomogeneousSlice
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Algebra.ScaledHomogenizationPrimitive
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Irreducibility and coefficient maps of scaled homogeneous models in
arbitrary dimension, including reduction modulo primes. -/

namespace CCDN
section
open MvPolynomial

variable {n : ℕ}

/-- Scaled homogenization commutes with mapping the coefficients along a ring homomorphism
`φ`, the scaling factor `h` being replaced by `φ h`. -/
lemma scaledHomogenize_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (d : ℕ) (h : R) (f : MvPolynomial (Fin n) R) :
    map φ (scaledHomogenize d h f) = scaledHomogenize d (φ h) (map φ f) := by
  simp [scaledHomogenize, map_sum, map_monomial, map_mul, map_pow, coeff_map]
  symm
  apply Finset.sum_subset (support_map_subset _ _)
  intro m _ hm
  have hz : φ (f.coeff m) = 0 := by aesop
  simp [hz, mul_zero, monomial_zero]

/-- Over a field, every nonzero scaling of an irreducible affine equation
has an irreducible homogeneous model. -/
theorem scaledHomogenize_irreducible {K : Type*} [Field K]
    (f : MvPolynomial (Fin n) K) (hir : Irreducible f) {h : K} (hh : h ≠ 0) :
    Irreducible (scaledHomogenize f.totalDegree h f) := by
  let F := scaledHomogenize f.totalDegree h f
  have hF0 : F ≠ 0 := scaledHomogenize_ne_zero _ hh hir.ne_zero
  have hFhom := scaledHomogenize_homogeneous h f le_rfl
  let G := firstCoordinateScale K h hh F
  have hG0 := (firstCoordinateScale K h hh).injective.ne (by positivity)
  have hGhom : G.IsHomogeneous f.totalDegree := firstCoordinateScaleHom_homogeneous h hFhom
  have hchart : affineChart n G = C (h ^ f.totalDegree) * f := by
    rw [show affineChart n G = homogeneousSlice n h F from
      (homogeneousSlice_eq_chart_scale h F).symm]
    exact homogeneousSlice_scaledHomogenize h f le_rfl
  have hunit : IsUnit (C (h ^ f.totalDegree) : MvPolynomial (Fin n) K) :=
    (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hh)).map C
  have hchartir : Irreducible (affineChart n G) := by
    rw [hchart]
    exact (irreducible_isUnit_mul hunit).mpr hir
  have hchartdeg : (affineChart n G).totalDegree = G.totalDegree := by
    rw [hchart, totalDegree_mul_of_isDomain (C_eq_zero.not.mpr (pow_ne_zero _ hh)) hir.ne_zero,
      totalDegree_C, zero_add, hGhom.totalDegree hG0]
  exact (MulEquiv.irreducible_iff (f := firstCoordinateScale K h hh)).mp
    (irreducible_of_affineChart_irreducible G hchartdeg hchartir)

