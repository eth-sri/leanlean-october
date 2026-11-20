module

public import QPBT.Test.SoundnessDefs

/-!
# Scalar absorption of the Naimark transfer constants

Transferring the Pauli operator distances from a Naimark dilation back to the
original spaces produces bounds of the shape `3 * δ + 6 * δ ^ 2`, where `δ` is
the Pauli soundness error `deltaQld`. This module records the purely scalar
fact that such a combination is again a Pauli soundness error, after enlarging
the universal prefactor. No strategy, measurement, or state content enters
here; the module only depends on `MIPStarRE.QPBT.Test.SoundnessDefs`.

## References

Blueprint `lem:delta-qld-scalar-absorption-support`. The source performs the
same constant bookkeeping inline when it records the error form of
`thm:pauli` at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
The companion constant adjustments are `deltaQld_mono`
(`MIPStarRE/QPBT/Test/SoundnessDefs.lean`) and `sqrt_deltaQld_le`
(`MIPStarRE/QPBT/Combining/RootErrorBounds.lean`).
-/

@[expose] public section

namespace MIPStarRE.QPBT

/-- **Scalar absorption.** On the source parameter domain the combination
`3 * δ + 6 * δ ^ 2` of the Pauli soundness error `δ = deltaQld a b ε m d q` is
again a Pauli soundness error, with the universal prefactor enlarged from `a`
to `21 * a ^ 2` and the exponent `b` unchanged.

This is the arithmetic step that returns the Naimark operator-transfer bound
`3 * dilatedDistance + 6 * stateError ^ 2` to the source error form. It is a
Lean-only constant-bookkeeping helper, not an additional hypothesis of
`thm:pauli`: the source absorbs the same universal constants inline at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
It is stated as blueprint `lem:delta-qld-scalar-absorption-support`. -/
theorem three_add_six_sq_deltaQld_le {P : AdmissibleParams} {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    3 * P.qldError a b epsilon +
        6 * P.qldError a b epsilon ^ 2 ≤
      P.qldError (21 * a ^ 2) b epsilon := by
  let s := P.degreeBudget
  let t := P.qldTail b epsilon
  let k := a * s ^ a
  let δ := P.qldError a b epsilon
  have hs : 1 ≤ s := P.degreeBudget_ge_one
  have hs' := zero_lt_one.trans_le hs
  have kt : δ = k * t := rfl
  have hk : 1 ≤ k := one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hs (by linarith))
  have ht : 0 ≤ t := P.qldTail_nonneg b hepsilon
  have hδ : 0 ≤ δ := deltaQld_nonneg (by linarith) hepsilon
  have hδ' : δ ≤ 3 * k := by
    rw [kt, mul_comm 3]
    exact mul_le_mul_of_nonneg_left (P.qldTail_le_three hb.le hepsilon hepsilon1) (by linarith)
  calc
    3 * δ + 6 * δ ^ 2 ≤ 21 * k * δ := by nlinarith
    _ = (21 * a ^ 2) * s ^ (a + a) * t := by
      rw [kt, Real.rpow_add hs']; dsimp only [k]; ring
    _ ≤ (21 * a ^ 2) * s ^ (21 * a ^ 2) * t := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hs (by nlinarith)) (by positivity)) ht

end MIPStarRE.QPBT
