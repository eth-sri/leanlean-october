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
set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The `BB'`--`AB''` completed diagonal-line/point defect is the consistency
defect of the reversed completed direct-game readouts on `pairState`. -/
theorem reversed_diagonal_completed_defect_eq_read_defect
    (lines : ExtendedLinesWitness setting points deltaL) :
    completedLinePointDefect lines .BB' .AB''
        (directDLinePointDist P.extendedDirectLd) =
      branchReadDefect lines .point .dline (fun _ => pointGameRead) diagonalGameRead := by
  unfold branchReadDefect readMeasurement branchQ completedLinePointDefect consistencyDefect
  rw [directDLinePointDist, Distribution.avgOver_map]
  apply avgOver_congr
  intro sample
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a = b
  · simp [h]
  · simp only [h, Ne.symm h, if_false, DistanceCalculus.consistency_term_eq_stateQForm]
    rw [diagonal_read_effect lines .bob, point_read_effect lines .alice,
      DistanceCalculus.placed_product_stateQForm_eq, place_BB'_mul_AB''_comm]
    symm
    apply stateQForm_pairState_eq_AB''_BB' <;> apply measurement_effect_hermitian

/-- The point/diagonal-line branch rejection is exactly the `BB'`--`AB''`
completed diagonal-line/point defect. Zero directions and failed completed
evaluation retain their `none` outcome. Paper
`14_analysis_of_the_pauli_basis_test.tex:1279-1288`; blueprint `lem:qld-4-7`. -/
theorem point_dline_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability (strategy lines)
        (.point, .dline) =
      completedLinePointDefect lines .BB' .AB''
        (directDLinePointDist P.extendedDirectLd) := by
  exact (rejection_eq_readDefect lines diagonalPointReadLaw.swap).trans
    (reversed_diagonal_completed_defect_eq_read_defect lines).symm

/-- The sum of the four mixed point/line rejection probabilities is at most
`4 * deltaL`. This combines only the exact branch identities with the two
oriented completed-defect bounds supplied by `lines`. Paper
`14_analysis_of_the_pauli_basis_test.tex:1279-1288`; blueprint `lem:qld-4-7`. -/
theorem mixed_line_point_rejections_le_four_mul
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability (strategy lines)
          (.aline, .point) +
        directLdBranchRejectionProbability (strategy lines)
          (.dline, .point) +
        directLdBranchRejectionProbability (strategy lines)
          (.point, .aline) +
        directLdBranchRejectionProbability (strategy lines)
          (.point, .dline) ≤ 4 * deltaL := by
  rw [aline_point_rejection_eq_completedLinePointDefect,
    dline_point_rejection_eq_completedLinePointDefect,
    point_aline_rejection_eq_completedLinePointDefect,
    point_dline_rejection_eq_completedLinePointDefect]
  have hbounds := completedLinePointDefect_sums_le lines
  linarith [hbounds.1, hbounds.2]

end ExtendedLineGame

end

end MIPStarRE.QPBT
