module

public import QPBT.Combining.PassingError
public import QPBT.Combining.DirectLowDegree.CoefficientConsistency
public import QPBT.Combining.DirectLowDegree.ExtendedCoefficientLoss
public import QPBT.Combining.DirectLowDegree.RejectionBounds
public import QPBT.Combining.ExtendedLineGame.ParameterEvaluatedLineBound
public import QPBT.Combining.WitnessErrorNonneg

/-!
# Passing value of the supplied extended-line strategy
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

private theorem sameLine_rejectedMass_eq_answer_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LdType) (hkind : kind = .aline ∨ kind = .dline)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (kind, directLdMap P.extendedDirectLd kind sample) =
      outcomeEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (fun answerA answerB => answerA ≠ answerB) := by
  classical
  unfold directRejectedMass outcomeEventWeight
  refine Finset.sum_congr rfl fun answerA _ => Finset.sum_congr rfl fun answerB _ => ?_
  by_cases heq : answerA = answerB
  · subst answerB
    by_cases hvalid : validDirectLdAnswer kind answerA = true
    · have hwin : directLdWinPredicate P.extendedDirectLd
          (kind, directLdMap P.extendedDirectLd kind sample)
          (kind, directLdMap P.extendedDirectLd kind sample)
          answerA answerA = true := by
        rcases hkind with rfl | rfl <;> cases answerA <;>
          simp_all [directLdWinPredicate, validDirectLdAnswer]
      simp [hwin]
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ answerA answerA
        (Or.inl (Bool.eq_false_of_not_eq_true hvalid))]
      simp
  · have hwinFalse : directLdWinPredicate P.extendedDirectLd
        (kind, directLdMap P.extendedDirectLd kind sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        answerA answerB = false :=
      Bool.eq_false_of_not_eq_true fun hwin => heq <| by
        rcases hkind with rfl | rfl <;> cases answerA <;> cases answerB <;>
          simp_all [directLdWinPredicate, validDirectLdAnswer]
    simp [hwinFalse, heq]

private theorem same_line_rejection_le_eval_defect_add
    (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LdType) (hkind : kind = .aline ∨ kind = .dline) (deg : ℕ)
    (coeffs : DirectLdAnswer P.extendedDirectLd → DirectDegPoly P.extendedDirectLd deg)
    (wrap : DirectDegPoly P.extendedDirectLd deg → DirectLdAnswer P.extendedDirectLd)
    (hretractA : ∀ s a,
      ((((strategy lines).A (kind, directLdMap P.extendedDirectLd kind s)).postprocess
        coeffs).postprocess wrap).effect a =
        ((strategy lines).A (kind, directLdMap P.extendedDirectLd kind s)).effect a)
    (hretractB : ∀ s a,
      ((((strategy lines).B (kind, directLdMap P.extendedDirectLd kind s)).postprocess
        coeffs).postprocess wrap).effect a =
        ((strategy lines).B (kind, directLdMap P.extendedDirectLd kind s)).effect a) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (kind, kind) ≤
      (avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
          parameterEvalDefect (strategy lines)
            (kind, directLdMap P.extendedDirectLd kind sample)
            (kind, directLdMap P.extendedDirectLd kind sample)
            coeffs coeffs parameter) +
      (deg : Real) / (P.extendedDirectLd.q : Real) := by
  classical
  let μ := uniformDistribution (DirectLdSpace P.extendedDirectLd)
  let q (s : DirectLdSpace P.extendedDirectLd) : DirectLdQuestion P.extendedDirectLd :=
    (kind, directLdMap P.extendedDirectLd kind s)
  let A (s : DirectLdSpace P.extendedDirectLd) := ((strategy lines).A (q s)).postprocess coeffs
  let B (s : DirectLdSpace P.extendedDirectLd) := ((strategy lines).B (q s)).postprocess coeffs
  have h1 : directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (kind, kind) =
      consistencyDefect μ
        (fun s a => heteroKron (((A s).postprocess wrap).effect a) 1)
        (fun s a => heteroKron 1 (((B s).postprocess wrap).effect a))
        (strategy lines).ψ := by
    rw [directLdBranchRejectionProbability_eq_avgOver,
      avgOver_congr _ _ _ (sameLine_rejectedMass_eq_answer_mismatch lines kind hkind)]
    unfold consistencyDefect outcomeEventWeight
    refine avgOver_congr _ _ _ fun s => ?_
    simp only [A, B, q, hretractA s, hretractB s,
      DistanceCalculus.consistency_term_eq_stateQForm,
      DistanceCalculus.placed_product_stateQForm_eq]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a = b <;> simp [hab, outcomeWeight, DistanceCalculus.stateQForm]
  have h2 := consistencyDefect_postprocess_le μ A B (strategy lines).ψ wrap
  have h3 := consistencyDefect_directCoefficients_le_evaluated_add
    P.extendedDirectLd deg μ A B (strategy lines).ψ
    (uniformDistribution_isProbability _) (pairState_norm setting)
  have h4 : consistencyDefect
      (Distribution.prod μ (uniformDistribution (DirectScalarQ P.extendedDirectLd)))
      (fun st value => heteroKron
        (((A st.1).postprocess (fun c => evalCoefficient c st.2)).effect value) 1)
      (fun st value => heteroKron 1
        (((B st.1).postprocess (fun c => evalCoefficient c st.2)).effect value))
      (strategy lines).ψ =
      avgOver μ fun sample =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
          parameterEvalDefect (strategy lines) (q sample) (q sample)
            coeffs coeffs parameter := by
    simp only [A, B, Measurement.postprocess_comp]
    rw [WinImplications.consistencyDefect_postprocess_eq_mismatch,
      SandwichProduct.avgOver_distribution_prod]
    rfl
  linarith

/-- The sum of the seven potentially rejecting branches of the supplied
strategy is bounded by the scalar expression used by the direct passing-error
envelope. -/
theorem seven_branch_rejections_le
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .dline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .dline) ≤
      deltaQ + 16 * deltaL + 4 * Real.sqrt (deltaQ + 2 * deltaL) +
        5 * ((P.m * P.d : Real) / (P.q : Real)) := by
  have hpoint := point_point_rejection_le lines
  have hmixed := mixed_line_point_rejections_le_four_mul lines
  have haxis := same_line_rejection_le_eval_defect_add lines .aline (Or.inl rfl) P.d
    axisCoefficients (fun c => .alinePolys fun _ => c)
    (fun s a => by
      change (((answerMeasurement lines .alice _).postprocess _).postprocess _).effect a =
        (answerMeasurement lines .alice _).effect a
      unfold answerMeasurement
      rw [axis_description_canonical, Measurement.postprocess_comp, Measurement.postprocess_comp]
      rfl)
    (fun s a => by
      change (((answerMeasurement lines .bob _).postprocess _).postprocess _).effect a =
        (answerMeasurement lines .bob _).effect a
      unfold answerMeasurement
      rw [axis_description_canonical, Measurement.postprocess_comp, Measurement.postprocess_comp]
      rfl)
  have hdiagonal := same_line_rejection_le_eval_defect_add lines .dline (Or.inr rfl)
    (P.extendedDirectLd.m * P.extendedDirectLd.d)
    diagonalCoefficients (fun c => .dlinePolys fun _ => c)
    (fun s a => by
      change (((answerMeasurement lines .alice _).postprocess _).postprocess _).effect a =
        (answerMeasurement lines .alice _).effect a
      unfold answerMeasurement
      rw [diagonal_description_canonical, Measurement.postprocess_comp,
        Measurement.postprocess_comp]
      rfl)
    (fun s a => by
      change (((answerMeasurement lines .bob _).postprocess _).postprocess _).effect a =
        (answerMeasurement lines .bob _).effect a
      unfold answerMeasurement
      rw [diagonal_description_canonical, Measurement.postprocess_comp,
        Measurement.postprocess_comp]
      rfl)
  have haxisEq : (avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
        parameterEvalDefect (strategy lines)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          (.aline, directLdMap P.extendedDirectLd .aline sample)
          axisCoefficients axisCoefficients parameter) =
      axisParameterEvaluationDefect lines := by
    unfold axisParameterEvaluationDefect directALinePointDist
    rw [Distribution.avgOver_map]
    rfl
  have hdiagonalEq : (avgOver (uniformDistribution (DirectLdSpace P.extendedDirectLd)) fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
        parameterEvalDefect (strategy lines)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          (.dline, directLdMap P.extendedDirectLd .dline sample)
          diagonalCoefficients diagonalCoefficients parameter) =
      diagonalParameterEvaluationDefect lines := by
    unfold diagonalParameterEvaluationDefect directDLinePointDist
    rw [Distribution.avgOver_map]
    rfl
  have haxisEval := axis_parameter_evaluation_defect_le lines
  have hdiagonalEval := diagonal_parameter_evaluation_defect_le lines
  have hcollision :
      (P.d : Real) / (P.extendedDirectLd.q : Real) +
          ((P.extendedDirectLd.m * P.extendedDirectLd.d : ℕ) : Real) /
            (P.extendedDirectLd.q : Real) ≤
        5 * ((P.m * P.d : Real) / (P.q : Real)) := by
    refine le_trans (le_of_eq ?_) (extendedDirectLd_coefficientCollisionLoss_le_five_mul P)
    push_cast
    ring
  linarith

/-- The supplied directly indexed strategy passes with error bounded by the
concrete polynomial envelope in `deltaQ + deltaL` and `m*d/q`. -/
theorem strategy_value_ge_directPassingErrorEnvelope
    (lines : ExtendedLinesWitness setting points deltaL) :
    1 - directPassingErrorEnvelope (deltaQ + deltaL)
        ((P.m * P.d : Real) / (P.q : Real)) ≤
      (strategy lines).value := by
  let rejection :=
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .dline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .dline)
  have hsum := seven_branch_rejections_le lines
  have hcap : rejection / 9 ≤ 1 := by
    have h := directLdRejectionProbability_le_one P.extendedDirectLd (strategy lines)
    rw [directLdRejectionProbability_eq_one_sub_value, strategy_value_eq lines] at h
    change rejection / 9 ≤ 1
    linarith
  have henvelope := seven_branch_capped_error_le_directPassingErrorEnvelope
    deltaQ deltaL ((P.m * P.d : Real) / (P.q : Real))
    points.delta_nonneg lines.delta_nonneg (by positivity)
  have hrejection : rejection / 9 ≤
      directPassingErrorEnvelope (deltaQ + deltaL)
        ((P.m * P.d : Real) / (P.q : Real)) :=
    (le_min hcap (by linarith)).trans henvelope
  rw [strategy_value_eq lines]
  change 1 - _ ≤ 1 - rejection / 9
  linarith

end ExtendedLineGame

end

end MIPStarRE.QPBT
