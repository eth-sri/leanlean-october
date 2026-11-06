module

public import QPBT.Combining.ExtendedLineGame.ParameterEvaluatedLineBound
public import QPBT.Combining.ExtendedLineGame.SameLineCoefficientBound

/-!
# Transport of the axis parameter-evaluation defect

The coefficient-evaluation defect for the same-axis branch equals the
parameter-evaluation defect of the supplied direct-game strategy. Both sample
the actual axis-line marginal and an independent uniform affine parameter.
Composing the strategy's answer map with coefficient extraction gives
`axisRead`. The degree-support field of the supplied line measurements also
identifies this truncated evaluation with the original coefficient evaluation.

These are formalization-only identities for the construction in the proof of
`lem:qld-4-7`; they neither construct the supplied witness nor prove the source
theorem.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#351.
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

/-- The axis coefficient-evaluation defect is exactly the parameter-evaluation
defect of the supplied strategy. The identity uses finite postprocessing and
the unchanged product of the axis-line marginal with a uniform parameter;
it introduces no degree, projectivity, or passing-value hypothesis. -/
theorem axis_parameter_evaluated_coefficient_defect_eq
    (lines : ExtendedLinesWitness setting points deltaL) :
    axisParameterEvaluatedCoefficientDefect lines =
      axisParameterEvaluationDefect lines := by
  classical
  let readAxis : DirectLdAnswer P.extendedDirectLd →
      DirectDegPoly P.extendedDirectLd P.d := fun answer =>
    match answer with
    | .alinePolys coefficients => coefficients ⟨0, by change 0 < 1; decide⟩
    | _ => 0
  let law := Distribution.prod (uniformDistribution (DirectLdSpace P.extendedDirectLd))
    (uniformDistribution (DirectScalarQ P.extendedDirectLd))
  have heffect (side : PlayerSide) (sample : DirectLdSpace P.extendedDirectLd)
      (parameter value : DirectScalarQ P.extendedDirectLd) :
       (((lines.Qline side (directALineDescOf P.extendedDirectLd sample)).postprocess
          (axisRead P)).postprocess
             fun coefficients => evalCoefficient coefficients parameter ).effect value  =
         ((answerMeasurement lines side
          (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
             fun answer => evalCoefficient (readAxis answer) parameter ).effect value  := by
    unfold answerMeasurement
    rw [axis_description_canonical]
    rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
      MIPStarRE.Quantum.Measurement.postprocess_comp]
    rfl
  have hmeasurement : axisParameterEvaluatedCoefficientDefect lines =
      consistencyDefect law
        (fun sample value => heteroKron
          (((answerMeasurement lines .alice
            (.aline, directLdMap P.extendedDirectLd .aline sample.1)).postprocess
               fun answer => evalCoefficient (readAxis answer) sample.2 ).effect value) 1)
        (fun sample value => heteroKron 1
          (((answerMeasurement lines .bob
            (.aline, directLdMap P.extendedDirectLd .aline sample.1)).postprocess
               fun answer => evalCoefficient (readAxis answer) sample.2 ).effect value))
        (pairState setting) := by
    unfold axisParameterEvaluatedCoefficientDefect consistencyDefect
    dsimp only [law]
    simp only [SandwichProduct.avgOver_distribution_prod, directALinePointDist,
      Distribution.avgOver_map]
    apply avgOver_congr
    intro sample
    apply avgOver_congr
    intro parameter
    apply Finset.sum_congr rfl
    intro valueA _
    apply Finset.sum_congr rfl
    intro valueB _
    rw [heffect .alice sample parameter valueA, heffect .bob sample parameter valueB]
  rw [hmeasurement]
  change consistencyDefect law
      (fun sample value => heteroKron
        ((((strategy lines).A
          (.aline, directLdMap P.extendedDirectLd .aline sample.1)).postprocess
             fun answer => evalCoefficient (readAxis answer) sample.2 ).effect value) 1)
      (fun sample value => heteroKron 1
        ((((strategy lines).B
          (.aline, directLdMap P.extendedDirectLd .aline sample.1)).postprocess
             fun answer => evalCoefficient (readAxis answer) sample.2 ).effect value))
      (strategy lines).ψ = _
  rw [WinImplications.consistencyDefect_postprocess_eq_mismatch]
  unfold axisParameterEvaluationDefect
  simp only [law, SandwichProduct.avgOver_distribution_prod, directALinePointDist,
    Distribution.avgOver_map]
  rfl

end ExtendedLineGame

end

end MIPStarRE.QPBT
