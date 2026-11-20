module

public import QPBT.Combining.ExtendedLineGame.ParameterEvaluatedLineBound
public import QPBT.Combining.ExtendedLineGame.SameLineCoefficientBound

/-! # Transport of line parameter-evaluation defects

The strategy answer map and coefficient extraction compose to the same
readout as reading the line measurement directly. The independent parameter
and the actual line marginal are unchanged.
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

private theorem evaluatedLineDefect_eq_avg_parameter {d : ℕ}
    (lineOf : DirectLdSpace P.extendedDirectLd → DirectLineDesc P.extendedDirectLd)
    (q : DirectLdSpace P.extendedDirectLd → DirectLdQuestion P.extendedDirectLd)
    (read : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1) → DirectDegPoly P.extendedDirectLd d)
    (coeff : DirectLdAnswer P.extendedDirectLd → DirectDegPoly P.extendedDirectLd d)
    (hread : ∀ side s, (answerMeasurement lines side (q s)).postprocess coeff =
      (lines.Qline side (lineOf s)).postprocess read) :
    evaluatedLineDefect lines ((uniformDistribution _).map lineOf) read =
      avgOver (uniformDistribution _) (fun s =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) (fun t =>
          parameterEvalDefect (strategy lines) (q s) (q s) coeff coeff t)) := by
  let μ := Distribution.prod (uniformDistribution (DirectLdSpace P.extendedDirectLd))
    (uniformDistribution (DirectScalarQ P.extendedDirectLd))
  let S := strategy lines
  let f : DirectLdSpace P.extendedDirectLd × DirectScalarQ P.extendedDirectLd →
      DirectLdAnswer P.extendedDirectLd → DirectScalarQ P.extendedDirectLd :=
    fun s a => evalCoefficient (coeff a) s.2
  have hA s t : (((lines.Qline .alice (lineOf s)).postprocess read).postprocess
      (fun c => evalCoefficient c t)) = (S.A (q s)).postprocess (f (s, t)) := by
    rw [← hread .alice s, Measurement.postprocess_comp]
    rfl
  have hB s t : (((lines.Qline .bob (lineOf s)).postprocess read).postprocess
      (fun c => evalCoefficient c t)) = (S.B (q s)).postprocess (f (s, t)) := by
    rw [← hread .bob s, Measurement.postprocess_comp]
    rfl
  calc
    _ = bipartiteDefect μ
        (fun s => (S.A (q s.1)).postprocess (f s))
        (fun s => (S.B (q s.1)).postprocess (f s)) S.ψ := by
      simp only [evaluatedLineDefect, consistencyDefect, μ,
        SandwichProduct.avgOver_distribution_prod, Distribution.avgOver_map]
      apply avgOver_congr
      intro s
      apply avgOver_congr
      intro t
      rw [hA, hB]
      rfl
    _ = _ := by
      rw [WinImplications.consistencyDefect_postprocess_eq_mismatch]
      simp only [μ, SandwichProduct.avgOver_distribution_prod, parameterEvalDefect]
      rfl

/-- Coefficient and strategy readouts agree on the same-axis branch. -/
theorem axis_parameter_evaluated_coefficient_defect_eq :
    axisParameterEvaluatedCoefficientDefect lines = parameterEvaluationDefect lines .axis := by
  simp only [axisParameterEvaluatedCoefficientDefect, parameterEvaluationDefect, linePointLaw, sampleLine,
    directALinePointDist, Distribution.map_map, Distribution.avgOver_map]
  refine evaluatedLineDefect_eq_avg_parameter lines (directALineDescOf _) _ (axisRead P)
    (lineCoefficients .axis) fun side s => ?_
  change (((lines.Qline side (directALineDescOf _ (directLdMap _ .aline s))).postprocess
    (axisAnswer P)).postprocess (lineCoefficients .axis)) = _
  rw [axis_description_canonical, Measurement.postprocess_comp]
  rfl

/-- Coefficient and strategy readouts agree on the same-diagonal branch. -/
theorem diagonal_parameter_evaluated_coefficient_defect_eq :
    diagonalParameterEvaluatedCoefficientDefect lines = parameterEvaluationDefect lines .diagonal := by
  simp only [diagonalParameterEvaluatedCoefficientDefect, parameterEvaluationDefect, linePointLaw, sampleLine,
    directDLinePointDist, Distribution.map_map, Distribution.avgOver_map]
  refine evaluatedLineDefect_eq_avg_parameter lines (directDLineDescOf _) _ (diagonalRead P)
    (lineCoefficients .diagonal) fun side s => ?_
  change (((lines.Qline side (directDLineDescOf _ (directLdMap _ .dline s))).postprocess
    (diagonalAnswer P)).postprocess (lineCoefficients .diagonal)) = _
  rw [diagonal_description_canonical, Measurement.postprocess_comp]
  rfl

end

end ExtendedLineGame

end

end MIPStarRE.QPBT
