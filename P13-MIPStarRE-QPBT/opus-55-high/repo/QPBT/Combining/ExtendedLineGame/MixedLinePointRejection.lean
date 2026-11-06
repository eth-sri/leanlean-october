module

public import QPBT.Combining.ExtendedLineGame.LinePointRejection

/-!
# Mixed line/point rejection bounds for the extended direct game

This module identifies the remaining reversed point/diagonal-line branch with
its completed line-point defect and bounds the sum of all four mixed
line/point rejection probabilities. These are exact supplied-witness
consequences used before the soundness step in the proof of `lem:qld-4-7`;
they do not establish a complete passing-value bound or construct a witness.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issues #302, #305, #307, #309, and #311.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

-- The six-register products use the same instance-search budget as StateTransport.

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

variable (lines : ExtendedLinesWitness setting points deltaL)

/-- The sum of the four mixed point/line rejection probabilities is at most
`4 * deltaL`. This combines only the exact branch identities with the two
oriented completed-defect bounds supplied by `lines`. Paper
`14_analysis_of_the_pauli_basis_test.tex:1279-1288`; blueprint `lem:qld-4-7`. -/
theorem mixed_line_point_rejections_le_four_mul
    :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .dline) ≤ 4 * deltaL := by
  rw [aline_point_rejection_eq_completedLinePointDefect lines,
    dline_point_rejection_eq_completedLinePointDefect lines,
    point_aline_rejection_eq_completedLinePointDefect lines,
    point_dline_rejection_eq_completedLinePointDefect lines]
  have hbounds := completedLinePointDefect_sums_le lines
  linarith

end ExtendedLineGame

end

end MIPStarRE.QPBT
