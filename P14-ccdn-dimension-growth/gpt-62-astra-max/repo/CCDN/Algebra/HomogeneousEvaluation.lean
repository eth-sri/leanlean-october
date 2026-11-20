/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.HomogeneousMonomials
import CCDN.Algebra.RowSelection

/-! Homogeneous equations give nonzero relations on the complete
homogeneous evaluation matrix and hence strictly deficient row rank. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

/-- A homogeneous polynomial of degree `M` in `n + 1` variables is the sum of its terms over
the degree-`M` monomials enumerated by `homogeneousMonomials n M`. -/
lemma homogeneous_eq_sum_coeff {K : Type*} [CommSemiring K] {n M : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M) :
    f = ∑ j, monomial (homogeneousMonomials n M j) (f.coeff (homogeneousMonomials n M j)) := by
  classical
  ext p
  by_cases hp : p.degree = M
  · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective n M p hp
    simp [(homogeneousMonomials_injective n M).eq_iff]
  · rw [(hf.coeff_eq_zero hp), coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_monomial, ite_eq_right]
    grind [homogeneousMonomials_degree]

end
end CCDN
