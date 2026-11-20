module

public import QPBT.Combining.ExtendedLineGame.LinePointRejection

/-!
# Same-line branch rejection for the extended direct game

The axis-axis and diagonal-diagonal verifier branches compare the complete
typed coefficient answers returned by the two line measurements. This module
identifies each branch rejection exactly with the corresponding coefficient-
answer consistency defect, averaged over the marginal law of the supplied
line. These are exact transport identities, not numerical passing bounds.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#317.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

local notation "D" => P.extendedDirectLd

/-- Embed the restricted coefficient alphabet into the game's answer type. -/
abbrev lineCoefficientAnswer (P : AdmissibleParams) (kind : LineKind) :=
  match kind with
  | .axis => axisAnswer P
  | .diagonal => diagonalAnswer P

section

variable (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LineKind)
include lines kind

/-- The coefficient-answer consistency of the two line measurements. -/
def coefficientAnswerDefect : ℝ :=
  bipartiteDefect ((linePointLaw P kind).map Prod.fst)
    (fun l => (lines.Qline .alice l).postprocess (lineCoefficientAnswer P kind))
    (fun l => (lines.Qline .bob l).postprocess (lineCoefficientAnswer P kind))
    (pairState setting)

private theorem sampleLine_answerMeasurement (side : PlayerSide) (s : DirectLdSpace D) :
    answerMeasurement lines side (sampleQuestion (lineTag kind) s) =
      (lines.Qline side (sampleLine kind s)).postprocess (lineCoefficientAnswer P kind) := by
  cases kind
  · exact congrArg (fun l => (lines.Qline side l).postprocess (axisAnswer P))
      (axis_description_canonical D s)
  · exact congrArg (fun l => (lines.Qline side l).postprocess (diagonalAnswer P))
      (diagonal_description_canonical D s)

/-- Same-line rejection is exactly disagreement of the coefficient answers. -/
theorem sameLine_rejection_eq_coefficientAnswerDefect :
    directLdBranchRejectionProbability D (strategy lines) (lineTag kind, lineTag kind) =
      coefficientAnswerDefect lines kind := by
  rw [directLdBranchRejectionProbability_eq_avgOver, coefficientAnswerDefect, linePointLaw,
    Distribution.map_map, bipartiteDefect, consistencyDefect, Distribution.avgOver_map]
  apply avgOver_congr
  intro s
  have h := rejectedMass_eq_of_valid_reads lines (sampleQuestion (lineTag kind) s)
    (sampleQuestion (lineTag kind) s) id id
    (fun a b ha hb => by
      cases kind <;> cases a <;> cases b <;>
        simp [lineTag, sampleQuestion, validDirectLdAnswer] at ha hb <;>
        simp [directLdWinPredicate, validDirectLdAnswer])
  rw [h]
  unfold outcomeEventWeight
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Function.comp_def, id, ite_not, DistanceCalculus.placed_product_stateQForm_eq]
  rw [← sampleLine_answerMeasurement lines kind .alice, ← sampleLine_answerMeasurement lines kind .bob]
  rfl

end

end ExtendedLineGame

end

end MIPStarRE.QPBT
