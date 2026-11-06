/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.ForMathlib.Matrix
import CCDN.Noether.EulerPairBasis

/-! Explicit monomial values of the Euler basis and nonzero minors of the
correct Noether order d^2-1. -/

namespace CCDN
section
open MvPolynomial Module

section
variable {R : Type*} [CommRing R]

lemma euler_restrict_basis_val
    (S : Set (Fin 2 →₀ ℕ)) (i : S) :
    (basisRestrictSupport R S i).val = monomial i.val 1 := by
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp S).symm
      (Finsupp.single i 1)).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- The basis vector of `eulerLowBasis R k` indexed by `i` is the monomial with exponent vector
corresponding to `i` and coefficient one. -/
lemma eulerLowBasis_apply (k : ℕ) (i : EulerLowIndex k) :
    (eulerLowBasis R k i).val =
      monomial ((Finsupp.degreeLeEquivSym (Fin 2) k).symm i).val 1 := by
  have h := Basis.reindex_apply (basisRestrictSupport R {p : Fin 2 →₀ ℕ | p.degree ≤ k})
    (Finsupp.degreeLeEquivSym (Fin 2) k) i
  exact (congrArg Subtype.val h).trans (euler_restrict_basis_val _ _)

/-- The basis vector of `eulerTopBasis R k` indexed by `i` is the monomial of degree `k` with
exponent vector corresponding to `i` and coefficient one. -/
lemma eulerTopBasis_apply (k : ℕ) (i : EulerTopIndex k) :
    (eulerTopBasis R k i).val =
      monomial ((degreeEqEquivSym (Fin 2) k).symm i).val 1 := by
  simp [eulerTopBasis, Basis.map_apply, Basis.reindex_apply]
  exact euler_restrict_basis_val _ _

end

variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] (k : ℕ) (f : Polynomial (Polynomial F)) (hf : Irreducible f) (a : F) (ha : a ≠ 0) (hl : f.leadingCoeff = Polynomial.C a) (hdeg : f.natDegree = k + 2)
include hf ha hl hdeg

theorem eulerClosedFormCoefficientMatrix_rank
    :
    (eulerClosedFormCoefficientMatrix k f).rank = (k + 2) ^ 2 - 1 := by
  have hi : LinearIndependent F (eulerClosedFormCoefficientMatrix k f).col := by
    have hi := eulerClosedFormOperator_injective_of_constant_leading k f hf a ha hl hdeg
    have h := ((eulerPairBasis F k).linearIndependent.map' (eulerClosedFormOperator k f)
      (LinearMap.ker_eq_bot.mpr hi)).map' (bivariateCoefficients F)
        (LinearMap.ker_eq_bot.mpr bivariateCoefficients_injective)
    exact h
  have hr : (eulerClosedFormCoefficientMatrix k f).rank = Fintype.card (EulerColumns k) := by
    rw [Matrix.rank_eq_finrank_span_cols, linearIndependent_iff_card_eq_finrank_span.mp hi,
      Set.finrank]
  rw [hr, card_eulerColumns]

