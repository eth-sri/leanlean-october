/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import CCDN.Algebra.HomogeneousChartIrreducible

/-! Over an algebraically closed field, an irreducible homogeneous binary
form has degree one. The affine chart reduces this to a univariate polynomial. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

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
  have hu : Irreducible ((uniqueAlgEquiv K (Fin 1)) (affineChart 1 f)) :=
    (MulEquiv.irreducible_iff (f := (uniqueAlgEquiv K (Fin 1)).toMulEquiv)).mpr hc
  have hh : ((uniqueAlgEquiv K (Fin 1)) (affineChart 1 f)).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (IsAlgClosed.degree_eq_one_of_irreducible K hu)
  have hle : (affineChart 1 f).totalDegree ≤
      ((uniqueAlgEquiv K (Fin 1)) (affineChart 1 f)).natDegree :=
    Finset.sup_le fun m hm => by
      have hc0 : ((uniqueAlgEquiv K (Fin 1)) (affineChart 1 f)).coeff (m default) ≠ 0 := by
        rw [coeff_uniqueAlgEquiv, ← Finsupp.unique_single m]
        exact mem_support_iff.mp hm
      have he : m.degree = m default :=
        (congrArg Finsupp.degree (Finsupp.unique_single m)).trans (Finsupp.degree_single _ _)
      exact he.trans_le (Polynomial.le_natDegree_of_ne_zero hc0)
  omega

end
end CCDN
