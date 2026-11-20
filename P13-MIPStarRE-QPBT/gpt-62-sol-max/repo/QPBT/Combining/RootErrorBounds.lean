module

public import QPBT.Test.SoundnessDefs

/-!
# Square roots of the Pauli soundness error

The state-extraction estimate bounds a squared norm. Taking its square root
preserves the Pauli soundness error family after halving the exponent.

## References

Blueprint `rem:pauli-robustness-form`; the source states the squared bound at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1868-1876`,
whereas `thm:pauli` bounds the unsquared norm.
-/

@[expose] public section

namespace MIPStarRE.QPBT

/-- Every power between zero and one preserves the error envelope, rescaling
its noise exponent. -/
theorem rpow_deltaQld_le {P : AdmissibleParams} {a b ε r : ℝ}
    (ha : 1 ≤ a) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr₁ : r ≤ 1) :
    P.qldError a b ε ^ r ≤ P.qldError a (b * r) ε :=
  rpow_soundnessEnvelope_le P.q P.degreeBudget b
    (P.degreeBudget_ge_one.trans (P.degreeBudget_le_prefactor ha)) hε hr hr₁

theorem sqrt_deltaQld_le {P : AdmissibleParams} {a b ε : ℝ}
    (ha : 1 ≤ a) (hε : 0 ≤ ε) : Real.sqrt (P.qldError a b ε) ≤ P.qldError a (b / 2) ε := by
  simpa only [Real.sqrt_eq_rpow, div_eq_mul_inv, one_mul] using
    rpow_deltaQld_le (P := P) (b := b) ha hε (r := 1 / 2) (by norm_num) (by norm_num)

end MIPStarRE.QPBT
