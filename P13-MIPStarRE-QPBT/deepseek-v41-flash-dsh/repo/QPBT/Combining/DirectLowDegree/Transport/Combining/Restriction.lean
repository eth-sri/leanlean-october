module

public import QPBT.Combining.DirectLowDegree.Transport.Combining.Linearity

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
variable {K : Type*}


@[simp] theorem combinedPoint_combinedPointVar  {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) (j : Fin m) :
    combinedPoint u α (combinedPointVar m k j) = u j := by
  simp [combinedPoint, combinedPointVar]

@[simp] theorem combinedPoint_combinedCoefficientVar  {m k : ℕ}
    (u : Fin m → K) (α : Fin k → K) (r : Fin k) :
    combinedPoint u α (combinedCoefficientVar m k r) = α r := by
  simp [combinedPoint, combinedCoefficientVar]

/-! ## The restriction to a point -/

/-- The substitution replacing the point coordinates by the coordinates of `u`
and keeping the combining coordinates as variables. -/
def combinedRestrictSubstitution {K : Type*} [CommSemiring K] {m : ℕ} (k : ℕ)
    (u : Fin m → K) : Fin (m + k) → MvPolynomial (Fin k) K :=
  fun i => Sum.elim (fun j : Fin m => MvPolynomial.C (u j))
    (fun r : Fin k => MvPolynomial.X r) (finSumFinEquiv.symm i)

@[simp] theorem combinedRestrictSubstitution_point  [CommSemiring K]
    {m k : ℕ} (u : Fin m → K) (j : Fin m) :
    combinedRestrictSubstitution k u (combinedPointVar m k j) =
      MvPolynomial.C (u j) := by
  simp [combinedRestrictSubstitution, combinedPointVar]

@[simp] theorem combinedRestrictSubstitution_coefficient  [CommSemiring K]
    {m k : ℕ} (u : Fin m → K) (r : Fin k) :
    combinedRestrictSubstitution k u (combinedCoefficientVar m k r) =
      (MvPolynomial.X r : MvPolynomial (Fin k) K) := by
  simp [combinedRestrictSubstitution, combinedCoefficientVar]

/-- The polynomial `p(u, ·)` in the combining variables obtained from `p` by
substituting the point `u` for the point variables. -/
def combinedRestrict {K : Type*} [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) : MvPolynomial (Fin k) K :=
  MvPolynomial.aeval (combinedRestrictSubstitution k u) p

/-- Evaluating the restriction of `p` at `u` at a combining vector `α`
evaluates `p` at the combined point with parts `u` and `α`. -/
theorem eval_combinedRestrict  [CommSemiring K] {m k : ℕ}
    (p : MvPolynomial (Fin (m + k)) K) (u : Fin m → K) (α : Fin k → K) :
    MvPolynomial.eval α (combinedRestrict p u) =
      MvPolynomial.eval (combinedPoint u α) p := by
  have hcomp : (MvPolynomial.aeval (R := K) α).comp
        (MvPolynomial.aeval (combinedRestrictSubstitution k u)) =
      MvPolynomial.aeval (combinedPoint u α) := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases combinedVar_cases i with ⟨j, rfl⟩ | ⟨r, rfl⟩ <;> simp
  show MvPolynomial.aeval α (MvPolynomial.aeval (combinedRestrictSubstitution k u) p) = _
  rw [← AlgHom.comp_apply, hcomp]
  rfl

end

end MIPStarRE.QPBT
