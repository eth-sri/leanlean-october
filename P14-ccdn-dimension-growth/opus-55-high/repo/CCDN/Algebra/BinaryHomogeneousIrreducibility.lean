/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.Algebra.HomogeneousChartIrreducible

/-! Over an algebraically closed field, an irreducible homogeneous binary
form has degree one. The affine chart reduces this to a univariate polynomial. -/

namespace CCDN
section
open MvPolynomial

theorem uniqueAlgEquiv_natDegree {R σ : Type*} [CommRing R] [Unique σ]
    (f : MvPolynomial σ R) :
    ((uniqueAlgEquiv R σ) f).natDegree = f.totalDegree := by
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_uniqueAlgEquiv]
    apply coeff_eq_zero_of_totalDegree_lt
    change f.totalDegree < (Finsupp.single default k).degree
    simp_all
  · unfold totalDegree
    apply Finset.sup_le
    intro m hm
    have hc : ((uniqueAlgEquiv R σ) f).coeff (m default) ≠ 0 := by
      rw [coeff_uniqueAlgEquiv, ← Finsupp.unique_single m]
      grind
    have hle := Polynomial.le_natDegree_of_ne_zero hc
    have he : m.degree = m default := by
      calc
        _ = (Finsupp.single default (m default)).degree :=
          congrArg Finsupp.degree (Finsupp.unique_single m)
        _ = _ := Finsupp.degree_single _ _
    change m.degree ≤ _
    grind

/-- Over an algebraically closed field, an irreducible homogeneous polynomial in two variables
has degree at most `1`. -/
theorem binary_homogeneous_irreducible_degree_le_one
    {K : Type*} [Field K] [IsAlgClosed K] {d : ℕ}
    (f : MvPolynomial (Fin 2) K) (hf : f.IsHomogeneous d)
    (hir : Irreducible f) : d ≤ 1 := by
  by_contra h
  have hX := variable_not_dvd_irreducible_homogeneous f hf hir (by omega) 0
  have hdeg := affineChart_degree_of_not_variable_dvd f hf hX
  have hc := affineChart_irreducible_of_not_variable_dvd f hf hir hX
  have hu :=
    (MulEquiv.irreducible_iff (f := (uniqueAlgEquiv K (Fin 1)).toMulEquiv)).mpr hc
  have hh : ((uniqueAlgEquiv K (Fin 1)) (affineChart 1 f)).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (IsAlgClosed.degree_eq_one_of_irreducible K hu)
  rw [uniqueAlgEquiv_natDegree, hdeg] at hh
  omega

