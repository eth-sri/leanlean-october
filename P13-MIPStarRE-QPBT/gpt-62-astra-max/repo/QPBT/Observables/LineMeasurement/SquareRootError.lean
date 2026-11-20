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

namespace DistanceCalculus

variable {X α ιA ιB : Type*} [Fintype α] [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
  [DecidableEq ιB]

/-- The state-dependent distance between two complete measurements placed on
opposite tensor factors is at most four. Formalization-only auxiliary: this is
the trivial bound used to pass from a linear error to the common square-root
error of `lem:qld-comm-line-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:527-545`. -/
theorem opFamilyDistSq_placed_le_four
    {μ : Distribution X} (hμ : μ.IsProbability)
    (A : X → MIPStarRE.Quantum.Measurement α ιA)
    (B : X → MIPStarRE.Quantum.Measurement α ιB)
    {ψ : EuclideanSpace ℂ (ιA × ιB)} (hψ : ‖ψ‖ = 1) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 4 := by
  rw [← avgOver_const_of_isProbability μ hμ 4]
  apply avgOver_mono
  intro x
  exact sum_norm_sub_apply_sq_le_four hψ
    ((MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
       (leftPlacedMeasurement (A x))))
    ((MIPStarRE.QPBT.measurement_sum_adjoint_mul_le_one
       (rightPlacedMeasurement (B x))))

end DistanceCalculus

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
    nlinarith
  by_cases hε1 : ε ≤ 1
  · have hle : ε ≤ Real.sqrt ε := by
      simp
      nlinarith
    apply le_trans
    gcongr
    nlinarith
  · have hone :=
      Real.one_le_sqrt.mpr (lt_of_not_ge hε1).le
    calc
      x ≤ 4 := hx4
      _ ≤ 4 * Real.sqrt ε := by nlinarith
      _ ≤ _ := by nlinarith

end MIPStarRE.QPBT
