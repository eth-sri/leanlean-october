module

public import QPBT.Combining.ExtendedLineGame.ParameterEvaluatedLineBound
public import QPBT.Combining.WitnessErrorNonneg

/-!
# Passing value of the supplied extended-line strategy

This module assembles the seven potentially rejecting branches of the directly
indexed low-degree strategy constructed from an `ExtendedLinesWitness`.  It
then transports the resulting lower bound through the explicit Naimark
dilation.  These are formalization-only supplied-witness consequences; they do
not construct the witness or establish source theorem `lem:qld-4-7`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`
- Issue Dengnifer/MIPStarRE-QPBT-bak#348
-/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The supplied directly indexed strategy passes with error bounded by the
concrete polynomial envelope in `deltaQ + deltaL` and `m*d/q`. -/
theorem strategy_value_ge_directPassingErrorEnvelope
    (lines : ExtendedLinesWitness setting points deltaL) :
    1 - directPassingErrorEnvelope (deltaQ + deltaL)
        ((P.m * P.d : Real) / (P.q : Real)) ≤
      (strategy lines).value := by
  have h : 1 - (strategy lines).value ≤
      min 1 ((deltaQ + 16 * deltaL + 4 * Real.sqrt (deltaQ + 2 * deltaL) +
        5 * ((P.m * P.d : ℝ) / P.q)) / 9) := by
    refine le_min (by linarith [(strategy lines).value_nonneg]) ?_
    rw [strategy_value_eq]
    have hA := sameLine_rejection_le .axis lines
    have hD := sameLine_rejection_le .diagonal lines
    dsimp only [rejection, lineTag, lineDegree] at hA hD
    have hcollision := extendedDirectLd_coefficientCollisionLoss_le_five_mul P
    rw [add_div] at hcollision
    dsimp only [AdmissibleParams.extendedDirectLd] at hcollision
    push_cast at hD hcollision
    linarith [lines.delta_nonneg, point_point_rejection_le lines, mixed_line_point_rejections_le_four_mul lines]
  have := h.trans (seven_branch_capped_error_le_directPassingErrorEnvelope _ _ _
    points.delta_nonneg lines.delta_nonneg (by positivity))
  linarith

end ExtendedLineGame

end

end MIPStarRE.QPBT
