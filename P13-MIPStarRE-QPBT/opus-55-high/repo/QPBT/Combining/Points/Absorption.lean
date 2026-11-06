module

public import QPBT.Combining.Points.Closeness
public import QPBT.Combining.Witnesses

/-!
# Absorption estimates for combined point measurements

This module proves the first projection step used to compare a joint point
measurement with the corresponding marginal point measurement.  Projectivity
makes the complementary projection contractive, and the two ordered
consistency fields of `CombinedPointsWitness` supply the resulting averaged
bounds.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:902-915`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Removing the component outside a projective effect is a contraction.
This is the projection step preceding `eq:qqm`, paper
`14_analysis_of_the_pauli_basis_test.tex:902-915`. No commutation of the
two operators being compared is required. -/
theorem norm_sub_projective_mul_sq_le {α ι : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] (M : Quantum.Measurement α ι)
    (hM : Measurement.IsProjective M) (a : α) (A D : Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (A - M.effect a * A) ψ‖ ^ 2 ≤
      ‖applyOperatorToState (A - M.effect a * D) ψ‖ ^ 2 := by
  have hidem := (hM a).isIdempotentElem.eq
  have hgram : (1 - M.effect a)ᴴ * (1 - M.effect a) ≤ 1 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      (hM a).isSelfAdjoint.isHermitian.eq]
    calc
      (1 - M.effect a) * (1 - M.effect a) = 1 - M.effect a := by
        simp_all [sub_mul, mul_sub, one_mul, mul_one]
      _ ≤ 1 := sub_le_self _ (M.pos a)
  have heq : A - M.effect a * A =
      (1 - M.effect a) * (A - M.effect a * D) := by
    simp only [sub_mul, mul_sub, one_mul, ← mul_assoc, hidem]
    abel
  simp_all [DistanceCalculus.applyOperatorToState_mul, pow_le_pow_left₀, norm_nonneg, MagicSquareRigidity.norm_applyOperatorToState_le]

end

end MIPStarRE.QPBT
