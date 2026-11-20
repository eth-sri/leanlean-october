module

public import QPBT.Observables.ExpandedPlacement

/-!
# Square-root error bounds for placed measurement families

The consistency conclusions of `lem:qld-comm-line-cons` are stated with the
common error `deltaLine ε = √ε`, while the individual estimates of the proof
are linear in `ε` or already of square-root form. This module records the two
elementary facts that convert those estimates into the common form: the
state-dependent distance between two placed complete measurements never
exceeds `4`, and a quantity bounded by both `a * ε` and `4` is bounded by
`(a + 4) * √ε`.

## References

`lem:qld-comm-line-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:527-545`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

/-- A nonnegative quantity bounded by a linear error `a * ε` with `1 ≤ a` and
by the trivial bound `4` is bounded by `(a + 4) * √ε`: for `ε ≤ 1` the linear
bound dominates, and for `ε ≥ 1` the trivial bound does. Formalization-only
auxiliary: this is the passage to the common square-root error of
`lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:527-545`. -/
theorem le_mul_sqrt_of_le_mul_of_le_four {x ε a : ℝ} (ha : 1 ≤ a) (hx0 : 0 ≤ x)
    (hxa : x ≤ a * ε) (hx4 : x ≤ 4) : x ≤ (a + 4) * Real.sqrt ε := by
  have hε : 0 ≤ ε := by
    by_contra hneg
    have hlt : ε < 0 := lt_of_not_ge hneg
    nlinarith
  have hsqrt := Real.sqrt_nonneg ε
  by_cases hε1 : ε ≤ 1
  · have hle : ε ≤ Real.sqrt ε := by
      rw [Real.le_sqrt hε hε]
      nlinarith
    nlinarith
  · have hone := Real.one_le_sqrt.mpr (lt_of_not_ge hε1).le
    nlinarith

end MIPStarRE.QPBT
