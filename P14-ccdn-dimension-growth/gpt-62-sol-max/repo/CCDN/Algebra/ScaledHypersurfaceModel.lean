/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousChart
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Algebra.HomogeneousSlice
import CCDN.Algebra.IntegerRationalIrreducibility
import CCDN.Algebra.ScaledHomogenizationPrimitive
import CCDN.ForMathlib.MvPolynomial
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Irreducibility and coefficient maps of scaled homogeneous models in
arbitrary dimension, including reduction modulo primes. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Scaled homogenization commutes with mapping the coefficients along a ring homomorphism
`φ`, the scaling factor `h` being replaced by `φ h`. -/
lemma scaledHomogenize_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (φ : R →+* S) (d : ℕ) (h : R) (f : MvPolynomial (Fin n) R) :
    map φ (scaledHomogenize d h f) = scaledHomogenize d (φ h) (map φ f) := by
  classical
  simp only [scaledHomogenize, map_sum, map_monomial, map_mul, map_pow, coeff_map]
  symm
  apply Finset.sum_subset (support_map_subset _ _)
  intro m _ hm
  have hz : φ (f.coeff m) = 0 := by aesop
  simp_all

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
  have hchartir : Irreducible (affineChart n G) := by
    rw [hchart]
    exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr (pow_ne_zero _ hh)).map C)).mpr hir
  have hchartdeg : (affineChart n G).totalDegree = G.totalDegree := by
    rw [hchart, totalDegree_mul_of_isDomain (C_eq_zero.not.mpr (pow_ne_zero _ hh)) hir.ne_zero,
      totalDegree_C, zero_add, hGhom.totalDegree hG0]
  exact (MulEquiv.irreducible_iff (firstCoordinateScale K h hh)).mp (irreducible_of_affineChart_irreducible G hchartdeg hchartir)

/-- A primitive scaled homogenization of a nonconstant irreducible polynomial is irreducible. -/
theorem scaledHomogenize_integer_irreducible {n : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hir : Irreducible f) (hd : 0 < f.totalDegree)
    {a : ℤ} (ha : a ≠ 0) (hprim : PrimitiveIntegerPolynomial (scaledHomogenize f.totalDegree a f)) :
    Irreducible (scaledHomogenize f.totalDegree a f) := by
  apply hprim.irreducible_of_rational_map
  have he : (map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
    totalDegree_map_of_injective Int.cast_injective _
  rw [scaledHomogenize_map, ← he]
  exact scaledHomogenize_irreducible _ (rational_map_irreducible_of_integer f hir hd)
    (Int.cast_ne_zero.mpr ha)

end
end CCDN
