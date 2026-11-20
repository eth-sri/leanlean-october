/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.MonomialEvaluationMatrix
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import CCDN.ForMathlib.MvPolynomial

/-! Complete homogeneous monomial lists, their exact cardinalities, and the
corresponding polynomial-space dimensions. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A finite indexing of all degree-`M` monomials in `n+1` variables. -/
def homogeneousExponentEquiv (n M : ℕ) :
    Fin ((n + M).choose M) ≃ {p : Fin (n + 1) →₀ ℕ // p.degree = M} := by
  letI := Fintype.ofEquiv _ (Finsupp.degreeEqEquivSym (Fin (n + 1)) M).symm
  refine (Fintype.equivFinOfCardEq ?_).symm
  rw [← Nat.card_eq_fintype_card, Finsupp.card_degree_eq]
  simp

/-- The list of all exponent vectors of total degree `M` in `n + 1` variables, indexed by
`Fin ((n + M).choose M)` via `homogeneousExponentEquiv`. -/
def homogeneousMonomials (n M : ℕ) : Fin ((n + M).choose M) → (Fin (n + 1) →₀ ℕ) :=
  fun j => (homogeneousExponentEquiv n M j).val

section

variable (n M : ℕ)
include n M

/-- Distinct indices give distinct monomials in `homogeneousMonomials n M`. -/
lemma homogeneousMonomials_injective : Function.Injective (homogeneousMonomials n M) :=
  Subtype.val_injective.comp (homogeneousExponentEquiv n M).injective

/-- Every monomial in `homogeneousMonomials n M` has total degree `M`. -/
lemma homogeneousMonomials_degree (j : Fin ((n + M).choose M)) :
    (homogeneousMonomials n M j).degree = M :=
  (homogeneousExponentEquiv n M j).property

/-- Every exponent vector of total degree `M` in `n + 1` variables occurs in
`homogeneousMonomials n M`. -/
lemma homogeneousMonomials_surjective (p : Fin (n + 1) →₀ ℕ)
    (hp : p.degree = M) : ∃ j, homogeneousMonomials n M j = p := by
  obtain ⟨j, hj⟩ := (homogeneousExponentEquiv n M).surjective ⟨p, hp⟩
  exact ⟨j, congrArg Subtype.val hj⟩

/-- An integer combination of the degree-`M` monomials `homogeneousMonomials n M` is a
homogeneous polynomial of degree `M`. -/
theorem polynomialOfCoefficients_homogeneous
    (v : Fin ((n + M).choose M) → ℤ) :
    (polynomialOfCoefficients (homogeneousMonomials n M) v).IsHomogeneous M := by
  apply IsHomogeneous.sum
  intro j _
  apply isHomogeneous_monomial
  exact homogeneousMonomials_degree n M j

end

/-- A homogeneous polynomial of degree `M` in `n + 1` variables is the sum of its terms over
the degree-`M` monomials enumerated by `homogeneousMonomials n M`. -/
lemma homogeneous_eq_sum_coeff {K : Type*} [CommSemiring K] {n M : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M) :
    f = ∑ j, monomial (homogeneousMonomials n M j) (f.coeff (homogeneousMonomials n M j)) := by
  classical
  ext p
  by_cases hp : p.degree = M
  · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective n M p hp
    simp [coeff_monomial, (homogeneousMonomials_injective n M).eq_iff]
  · have hc := hf.coeff_eq_zero hp
    simp_all

end
end CCDN
