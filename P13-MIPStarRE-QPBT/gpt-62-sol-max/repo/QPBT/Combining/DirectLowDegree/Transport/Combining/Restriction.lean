module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.Linearity
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Restricting a polynomial in the combined variables to a point

The recovery step of the combining reduction reads a polynomial `p` in the
`m + k` combined variables as a polynomial in the `k` combining variables whose
coefficients are polynomials in the `m` point variables, and asks whether the
restriction `p(u, ·)` obtained by substituting a point `u` for the point
variables is a linear form in the combining variables.  This module introduces
that restriction and records its elementary properties: it computes the
combined polynomial of a tuple to the linear form of the tuple of values of the
tuple at the point, and, when it is a linear form, its coefficients are forced
to be the values at the point of the components recovered by the substitution
of `lem:ld-combining-split`.  Consequently a restriction which is a linear form
agrees with the restriction of the combined polynomial of those components,
which is the first half of `lem:ld-combining-exact-linearity`.

## Main statements

* `eval_combinedRestrict` — evaluating `p(u, ·)` at `α` evaluates `p` at the
  combined point with parts `u` and `α`.
* `combinedRestrict_combinePolyTuple` — the restriction of a combined
  polynomial is the linear form of the tuple of values of its components.
* `combinedRestrict_eq_of_eq_combiningLinearForm` — a restriction which is a
  linear form agrees with the restriction of the combined polynomial of the
  components of `p`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1470`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:575-600`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## The two coordinate blocks -/

/-- Every coordinate of the combined dimension is either a point coordinate or
a combining coordinate. -/
theorem combinedVar_cases {m k : ℕ} (i : Fin (m + k)) :
    (∃ j : Fin m, i = combinedPointVar m k j) ∨
      ∃ r : Fin k, i = combinedCoefficientVar m k r := by
  rcases h : finSumFinEquiv.symm i with j | r
  · exact Or.inl ⟨j, by rw [combinedPointVar, ← h, Equiv.apply_symm_apply]⟩
  · exact Or.inr ⟨r, by rw [combinedCoefficientVar, ← h, Equiv.apply_symm_apply]⟩

@[simp] theorem combinedPoint_combinedPointVar {K : Type*} {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) (j : Fin m) :
    combinedPoint u α (combinedPointVar m k j) = u j := by
  simp [combinedPoint, combinedPointVar]

@[simp] theorem combinedPoint_combinedCoefficientVar {K : Type*} {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) (r : Fin k) :
    combinedPoint u α (combinedCoefficientVar m k r) = α r := by
  simp [combinedPoint, combinedCoefficientVar]

/-- Order the combining variables before the point variables when currying. -/
def combinedVariableEquiv (m k : ℕ) : Fin (m + k) ≃ Fin k ⊕ Fin m :=
  finSumFinEquiv.symm.trans (Equiv.sumComm _ _)

/-- Read the combining-variable polynomial with point-variable polynomial coefficients. -/
def combinedCoefEquiv (K : Type*) [CommSemiring K] (m k : ℕ) :
    MvPolynomial (Fin (m + k)) K ≃ₐ[K] MvPolynomial (Fin k) (MvPolynomial (Fin m) K) :=
  (MvPolynomial.renameEquiv K (combinedVariableEquiv m k)).trans
    (MvPolynomial.sumAlgEquiv K (Fin k) (Fin m))

@[simp] theorem combinedCoefEquiv_X_point (K : Type*) [CommSemiring K] {m k : ℕ} (j : Fin m) :
    combinedCoefEquiv K m k (MvPolynomial.X (combinedPointVar m k j)) =
      MvPolynomial.C (MvPolynomial.X j) := by
  simp [combinedCoefEquiv, combinedVariableEquiv, combinedPointVar]

@[simp] theorem combinedCoefEquiv_X_coefficient (K : Type*) [CommSemiring K]
    {m k : ℕ} (r : Fin k) :
    combinedCoefEquiv K m k (MvPolynomial.X (combinedCoefficientVar m k r)) =
      MvPolynomial.X r := by
  simp [combinedCoefEquiv, combinedVariableEquiv, combinedCoefficientVar]

/-- Restriction evaluates each point-variable coefficient at `u`. -/
def combinedRestrictHom {K : Type*} [CommSemiring K] {m k : ℕ} (u : Fin m → K) :
    MvPolynomial (Fin (m + k)) K →ₐ[K] MvPolynomial (Fin k) K :=
  (MvPolynomial.mapAlgHom (MvPolynomial.aeval u)).comp (combinedCoefEquiv K m k).toAlgHom

section

variable {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K)
include K m k p u

/-- The partially evaluated polynomial `p(u, ·)`. -/
def combinedRestrict : MvPolynomial (Fin k) K :=
  combinedRestrictHom u p

/-- Partial evaluation followed by evaluation of the combining variables is full evaluation. -/
theorem eval_combinedRestrict (α : Fin k → K) :
    MvPolynomial.eval α (combinedRestrict p u) =
      MvPolynomial.eval (combinedPoint u α) p := by
  have h : (MvPolynomial.aeval α).comp (combinedRestrictHom u) =
      MvPolynomial.aeval (combinedPoint u α) := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;>
      simp [combinedRestrictHom, MvPolynomial.algebraMap_eq]
  exact DFunLike.congr_fun h p

end

end

end MIPStarRE.QPBT
