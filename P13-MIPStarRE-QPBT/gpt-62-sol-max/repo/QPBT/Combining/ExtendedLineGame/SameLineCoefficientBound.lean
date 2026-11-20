module

public import QPBT.Combining.DirectLowDegree.CoefficientConsistency
public import QPBT.Combining.ExtendedLineGame.SameLineRejection

/-!
# Coefficient bounds for same-line rejection

The exact axis-axis and diagonal-diagonal rejection identities are bounded by
evaluating the corresponding coefficient measurements at an independent
uniform affine parameter. The losses are the direct univariate collision terms
`d / q` and `md / q`.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1595-1603`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#328.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

section

variable (lines : ExtendedLinesWitness setting points deltaL)
include lines

/-- The defect after reading a coefficient vector and evaluating it at an
independent uniform parameter. -/
def evaluatedLineDefect
    (μ : Distribution (DirectLineDesc P.extendedDirectLd)) {d : ℕ}
    (read : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1) → DirectDegPoly P.extendedDirectLd d) :
    ℝ :=
  bipartiteDefect (Distribution.prod μ (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
    (fun s => ((lines.Qline .alice s.1).postprocess read).postprocess
      (fun c => evalCoefficient c s.2))
    (fun s => ((lines.Qline .bob s.1).postprocess read).postprocess
      (fun c => evalCoefficient c s.2)) (pairState setting)

abbrev axisParameterEvaluatedCoefficientDefect :=
  evaluatedLineDefect lines ((directALinePointDist P.extendedDirectLd).map Prod.fst) (axisRead P)

abbrev diagonalParameterEvaluatedCoefficientDefect :=
  evaluatedLineDefect lines ((directDLinePointDist P.extendedDirectLd).map Prod.fst) (diagonalRead P)

/-- Wrapping a coefficient vector in an answer tag cannot increase the
coefficient defect, which itself is controlled by the collision estimate. -/
private theorem coefficientAnswerDefect_le_evaluated
    (μ : Distribution (DirectLineDesc P.extendedDirectLd)) (hμ : μ.IsProbability) {d : ℕ}
    (read : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1) → DirectDegPoly P.extendedDirectLd d)
    (wrap : DirectDegPoly P.extendedDirectLd d → DirectLdAnswer P.extendedDirectLd) :
    bipartiteDefect μ
      (fun l => (lines.Qline .alice l).postprocess (fun c => wrap (read c)))
      (fun l => (lines.Qline .bob l).postprocess (fun c => wrap (read c)))
      (pairState setting) ≤ evaluatedLineDefect lines μ read + (d : ℝ) / P.extendedDirectLd.q := by
  let A := fun l => (lines.Qline .alice l).postprocess read
  let B := fun l => (lines.Qline .bob l).postprocess read
  have h := consistencyDefect_postprocess_le μ A B (pairState setting) wrap
  simp only [A, B, Measurement.postprocess_comp] at h
  exact h.trans (consistencyDefect_directCoefficients_le_evaluated_add P.extendedDirectLd d μ
    A B (pairState setting) hμ (pairState_norm setting))

/-- The axis-axis rejection is bounded by evaluated coefficient defect plus `d / q`. -/
theorem aline_aline_rejection_le_axisParameterEvaluatedCoefficientDefect_add :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.aline, .aline) ≤
      axisParameterEvaluatedCoefficientDefect lines + (P.d : ℝ) / P.extendedDirectLd.q := by
  rw [sameLine_rejection_eq_coefficientAnswerDefect lines .axis]
  exact coefficientAnswerDefect_le_evaluated lines _
    ((directALinePointDist_isProbability P.extendedDirectLd).map _) (axisRead P)
    (fun c => .alinePolys (fun _ => c))

/-- The diagonal-diagonal rejection is bounded by evaluated coefficient defect plus `md / q`. -/
theorem dline_dline_rejection_le_diagonalParameterEvaluatedCoefficientDefect_add :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.dline, .dline) ≤
      diagonalParameterEvaluatedCoefficientDefect lines +
        (P.extendedDirectLd.m * P.extendedDirectLd.d : ℝ) / P.extendedDirectLd.q := by
  rw [sameLine_rejection_eq_coefficientAnswerDefect lines .diagonal, ← Nat.cast_mul]
  exact coefficientAnswerDefect_le_evaluated lines _
    ((directDLinePointDist_isProbability P.extendedDirectLd).map _) (diagonalRead P)
    (fun c => .dlinePolys (fun _ => c))

end

end ExtendedLineGame

end

end MIPStarRE.QPBT
