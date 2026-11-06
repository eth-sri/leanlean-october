module

public import QPBT.Combining.DirectLowDegree.Transport.LineResampling
public import QPBT.Combining.ExtendedLineGame.PointPointRejection
public import QPBT.Combining.ExtendedLineGame.ParameterCompletion

/-!
# Bounds for independently parameter-evaluated line answers
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- Read the axis coefficient vector from a direct-game answer. -/
def axisCoefficients (answer : DirectLdAnswer P.extendedDirectLd) :
    DirectDegPoly P.extendedDirectLd P.d :=
  match answer with
  | .alinePolys coefficients => coefficients onlyCoordinate
  | _ => 0

/-- Read the diagonal coefficient vector from a direct-game answer. -/
def diagonalCoefficients (answer : DirectLdAnswer P.extendedDirectLd) :
    DirectDegPoly P.extendedDirectLd (P.extendedDirectLd.m * P.extendedDirectLd.d) :=
  match answer with
  | .dlinePolys coefficients => coefficients onlyCoordinate
  | _ => 0

/-- The canonical direct-game axis question represented by an axis line. -/
def axisQuestion (line : DirectLineDesc P.extendedDirectLd) :
    DirectLdQuestion P.extendedDirectLd :=
  (.aline, ⟨line.base, line.index, 0⟩)

/-- The canonical direct-game diagonal question represented by a diagonal line. -/
def diagonalQuestion (line : DirectLineDesc P.extendedDirectLd) :
    DirectLdQuestion P.extendedDirectLd :=
  (.dline, ⟨line.base, line.index, line.direction⟩)

/-- The axis parameter-evaluation defect under the actual axis-line marginal
and an independent uniform affine parameter. -/
noncomputable def axisParameterEvaluationDefect
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (directALinePointDist P.extendedDirectLd) fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
      parameterEvalDefect (strategy lines) (axisQuestion sample.1)
        (axisQuestion sample.1) axisCoefficients axisCoefficients parameter

/-- The diagonal parameter-evaluation defect under the actual diagonal-line
marginal and an independent uniform affine parameter. -/
noncomputable def diagonalParameterEvaluationDefect
    (lines : ExtendedLinesWitness setting points deltaL) : ℝ :=
  avgOver (directDLinePointDist P.extendedDirectLd) fun sample =>
    avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
      parameterEvalDefect (strategy lines) (diagonalQuestion sample.1)
        (diagonalQuestion sample.1) diagonalCoefficients diagonalCoefficients parameter

private theorem point_read_defect_on_direct_samples_eq_rejection
    (lines : ExtendedLinesWitness setting points deltaL) :
    consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer))
        (pairState setting) =
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .point) := by
  rw [point_branch_rejection_eq_consistencyDefect lines]
  refine (consistencyDefect_congr _ _ _ _ _ _
    (fun sample answer => by rw [point_read_effect lines .alice])
    (fun sample answer => by rw [point_read_effect lines .bob])).trans ?_
  let A (point : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) answer :=
    heteroKron (((points.Q .alice (projX (directPointToPauli P point))
      (projZ (directPointToPauli P point))).postprocess fun values =>
        some (directPointToPauli P point (alphaVar P.m) * values.1 +
          directPointToPauli P point (betaVar P.m) * values.2)).effect answer)
      (1 : Op (setting.ExpandedLocalSpace .bob))
  let B (point : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) answer :=
    heteroKron (1 : Op (setting.ExpandedLocalSpace .alice))
      (((points.Q .bob (projX (directPointToPauli P point))
        (projZ (directPointToPauli P point))).postprocess fun values =>
          some (directPointToPauli P point (alphaVar P.m) * values.1 +
            directPointToPauli P point (betaVar P.m) * values.2)).effect answer)
  exact avgOver_uniform_equiv_fst (directLdSpacePointEquiv P.extendedDirectLd)
    (fun x => ∑ a, ∑ b, if a = b then 0 else
      (inner ℂ (pairState setting)
        ((EuclideanSpace.equiv _ ℂ).symm ((A x a * B x b).mulVec (pairState setting)))).re)

private theorem pointGameRead_eq_none_iff_invalid
    (answer : DirectLdAnswer P.extendedDirectLd) :
    pointGameRead answer = none ↔
      validDirectLdAnswer (D := P.extendedDirectLd) .point answer = false := by
  cases answer <;> simp [pointGameRead, validDirectLdAnswer]

private theorem alice_none_mass_at_le_rejectedMass
    (lines : ExtendedLinesWitness setting points deltaL) (kind : LdType)
    (read : DirectLdSpace P.extendedDirectLd → DirectLdAnswer P.extendedDirectLd →
      Option (PauliScalar P))
    (sample : DirectLdSpace P.extendedDirectLd)
    (hrej : directRejectedMass P.extendedDirectLd (strategy lines)
      (kind, directLdMap P.extendedDirectLd kind sample)
      (.point, directLdMap P.extendedDirectLd .point sample) =
      outcomeEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun a b => read sample a ≠ pointGameRead b)) :
    aliceEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (fun answer => read sample answer = none) ≤
      directRejectedMass P.extendedDirectLd (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (.point, directLdMap P.extendedDirectLd .point sample) := by
  classical
  rw [← outcome_event_weight_left_eq (strategy lines)
    (kind, directLdMap P.extendedDirectLd kind sample)
    (.point, directLdMap P.extendedDirectLd .point sample), hrej]
  unfold outcomeEventWeight
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  by_cases hline : read sample a = none
  · by_cases hpoint : pointGameRead b = none
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ a b
        (Or.inr ((pointGameRead_eq_none_iff_invalid b).1 hpoint))]
      simp
    · simp [hline, Ne.symm hpoint]
  · simp only [hline, ↓reduceIte]
    split_ifs
    · exact outcomeWeight_nonneg (strategy lines) _ _ a b
    · exact le_rfl

private theorem bob_none_mass_at_le_rejectedMass
    (lines : ExtendedLinesWitness setting points deltaL) (kind : LdType)
    (read : DirectLdSpace P.extendedDirectLd → DirectLdAnswer P.extendedDirectLd →
      Option (PauliScalar P))
    (sample : DirectLdSpace P.extendedDirectLd)
    (hrej : directRejectedMass P.extendedDirectLd (strategy lines)
      (.point, directLdMap P.extendedDirectLd .point sample)
      (kind, directLdMap P.extendedDirectLd kind sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (fun a b => pointGameRead a ≠ read sample b)) :
    bobEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind sample)
        (fun answer => read sample answer = none) ≤
      directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (kind, directLdMap P.extendedDirectLd kind sample) := by
  classical
  rw [← outcome_event_weight_right_eq (strategy lines)
    (.point, directLdMap P.extendedDirectLd .point sample)
    (kind, directLdMap P.extendedDirectLd kind sample), hrej]
  unfold outcomeEventWeight
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  by_cases hline : read sample b = none
  · by_cases hpoint : pointGameRead a = none
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ a b
        (Or.inl ((pointGameRead_eq_none_iff_invalid a).1 hpoint))]
      simp
    · simp [hline, hpoint]
  · simp only [hline, ↓reduceIte]
    split_ifs
    · exact outcomeWeight_nonneg (strategy lines) _ _ a b
    · exact le_rfl

private theorem parameter_evaluation_defect_le_aux
    (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LdType) (deg : ℕ)
    (descOf : DirectLdSpace P.extendedDirectLd → DirectLineDesc P.extendedDirectLd)
    (qOf : DirectLineDesc P.extendedDirectLd → DirectLdQuestion P.extendedDirectLd)
    (dist : Distribution (DirectLineDesc P.extendedDirectLd ×
      (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)))
    (coeffs : DirectLdAnswer P.extendedDirectLd → DirectDegPoly P.extendedDirectLd deg)
    (read : DirectLdSpace P.extendedDirectLd → DirectLdAnswer P.extendedDirectLd →
      Option (PauliScalar P))
    (hdist : dist = (uniformDistribution (DirectLdSpace P.extendedDirectLd)).map
      (fun s => (descOf s, s.point)))
    (hq : ∀ s, qOf (descOf s) = (kind, directLdMap P.extendedDirectLd kind s))
    (hresample : ∀ F : DirectLineDesc P.extendedDirectLd ×
        (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) → ℝ,
      avgOver (dist.map Prod.fst) (fun line =>
        avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
          F (line, line.base + parameter • line.direction)) =
        avgOver dist F)
    (hread : ∀ s a, validDirectLdAnswer (D := P.extendedDirectLd) kind a = true →
      read s a = (directEvalOpt (descOf s) s.point (coeffs a)).map
        (extendedDirectScalarEquiv P))
    (hrejA : ∀ s, directRejectedMass P.extendedDirectLd (strategy lines)
      (kind, directLdMap P.extendedDirectLd kind s)
      (.point, directLdMap P.extendedDirectLd .point s) =
      outcomeEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind s)
        (.point, directLdMap P.extendedDirectLd .point s)
        (fun a b => read s a ≠ pointGameRead b))
    (hrejB : ∀ s, directRejectedMass P.extendedDirectLd (strategy lines)
      (.point, directLdMap P.extendedDirectLd .point s)
      (kind, directLdMap P.extendedDirectLd kind s) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point s)
        (kind, directLdMap P.extendedDirectLd kind s)
        (fun a b => pointGameRead a ≠ read s b)) :
    (avgOver dist fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
        parameterEvalDefect (strategy lines) (qOf sample.1) (qOf sample.1)
          coeffs coeffs parameter) ≤
      2 * directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (kind, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, kind) +
        2 * Real.sqrt (deltaQ +
          directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
            (.point, kind)) := by
  classical
  let μ := uniformDistribution (DirectLdSpace P.extendedDirectLd)
  let qL (s : DirectLdSpace P.extendedDirectLd) : DirectLdQuestion P.extendedDirectLd :=
    (kind, directLdMap P.extendedDirectLd kind s)
  let qP (s : DirectLdSpace P.extendedDirectLd) : DirectLdQuestion P.extendedDirectLd :=
    (.point, directLdMap P.extendedDirectLd .point s)
  let F : DirectLineDesc P.extendedDirectLd ×
      (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd) → ℝ := fun sample =>
    outcomeEventWeight (strategy lines) (qOf sample.1) (qOf sample.1)
        (fun a b => directEvalOpt sample.1 sample.2 (coeffs a) ≠
          directEvalOpt sample.1 sample.2 (coeffs b)) +
      aliceEventWeight (strategy lines) (qOf sample.1)
        (fun a => directEvalOpt sample.1 sample.2 (coeffs a) = none) +
      bobEventWeight (strategy lines) (qOf sample.1)
        (fun a => directEvalOpt sample.1 sample.2 (coeffs a) = none)
  have hstep1 : (avgOver dist fun sample =>
      avgOver (uniformDistribution (DirectScalarQ P.extendedDirectLd)) fun parameter =>
        parameterEvalDefect (strategy lines) (qOf sample.1) (qOf sample.1)
          coeffs coeffs parameter) ≤ avgOver dist F := by
    rw [← hresample F, Distribution.avgOver_map]
    refine avgOver_mono _ _ _ fun sample => avgOver_mono _ _ _ fun parameter => ?_
    exact parameterEvalDefect_le_completed_add_none (strategy lines)
      (qOf sample.1) (qOf sample.1) coeffs coeffs sample.1 parameter
  have hmismatch (s : DirectLdSpace P.extendedDirectLd) :
      outcomeEventWeight (strategy lines) (kind, directLdMap P.extendedDirectLd kind s)
        (kind, directLdMap P.extendedDirectLd kind s)
        (fun a b => directEvalOpt (descOf s) s.point (coeffs a) ≠
          directEvalOpt (descOf s) s.point (coeffs b)) =
      outcomeEventWeight (strategy lines) (qL s) (qL s)
        (fun a b => read s a ≠ read s b) := by
    unfold outcomeEventWeight
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    by_cases hinv : validDirectLdAnswer (D := P.extendedDirectLd) kind a = false ∨
        validDirectLdAnswer (D := P.extendedDirectLd) kind b = false
    · rw [outcomeWeight_eq_zero_of_invalid lines (qL s) (qL s) a b hinv]; simp
    · rw [not_or] at hinv
      simp only [qL, hread s a (Bool.eq_true_of_not_eq_false hinv.1),
        hread s b (Bool.eq_true_of_not_eq_false hinv.2),
        (Option.map_injective (extendedDirectScalarEquiv P).injective).ne_iff]
  have hnoneA (s : DirectLdSpace P.extendedDirectLd) :
      aliceEventWeight (strategy lines) (kind, directLdMap P.extendedDirectLd kind s)
        (fun a => directEvalOpt (descOf s) s.point (coeffs a) = none) =
      aliceEventWeight (strategy lines) (qL s) (fun a => read s a = none) := by
    rw [← outcome_event_weight_left_eq (strategy lines) (qL s) (qL s),
      ← outcome_event_weight_left_eq (strategy lines) (qL s) (qL s)]
    unfold outcomeEventWeight
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    by_cases hinv : validDirectLdAnswer (D := P.extendedDirectLd) kind a = false
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ a b (Or.inl hinv)]; simp
    · simp only [hread s a (Bool.eq_true_of_not_eq_false hinv), Option.map_eq_none_iff]
  have hnoneB (s : DirectLdSpace P.extendedDirectLd) :
      bobEventWeight (strategy lines) (kind, directLdMap P.extendedDirectLd kind s)
        (fun a => directEvalOpt (descOf s) s.point (coeffs a) = none) =
      bobEventWeight (strategy lines) (qL s) (fun a => read s a = none) := by
    rw [← outcome_event_weight_right_eq (strategy lines) (qL s) (qL s),
      ← outcome_event_weight_right_eq (strategy lines) (qL s) (qL s)]
    unfold outcomeEventWeight
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    by_cases hinv : validDirectLdAnswer (D := P.extendedDirectLd) kind b = false
    · rw [outcomeWeight_eq_zero_of_invalid lines _ _ a b (Or.inr hinv)]; simp
    · simp only [hread s b (Bool.eq_true_of_not_eq_false hinv), Option.map_eq_none_iff]
  let A (s : DirectLdSpace P.extendedDirectLd) :=
    DistanceCalculus.leftPlacedMeasurement (ιB := setting.ExpandedLocalSpace .bob)
      ((answerMeasurement lines .alice (qL s)).postprocess (read s))
  let B (s : DirectLdSpace P.extendedDirectLd) :=
    DistanceCalculus.rightPlacedMeasurement (ιA := setting.ExpandedLocalSpace .alice)
      ((answerMeasurement lines .bob (qP s)).postprocess pointGameRead)
  let C (s : DirectLdSpace P.extendedDirectLd) :=
    DistanceCalculus.leftPlacedMeasurement (ιB := setting.ExpandedLocalSpace .bob)
      ((answerMeasurement lines .alice (qP s)).postprocess pointGameRead)
  let D (s : DirectLdSpace P.extendedDirectLd) :=
    DistanceCalculus.rightPlacedMeasurement (ιA := setting.ExpandedLocalSpace .alice)
      ((answerMeasurement lines .bob (qL s)).postprocess (read s))
  have hF : avgOver dist F =
      consistencyDefect μ (fun s a => (A s).effect a) (fun s a => (D s).effect a)
        (pairState setting) +
      avgOver μ (fun s => aliceEventWeight (strategy lines) (qL s)
        (fun a => read s a = none)) +
      avgOver μ (fun s => bobEventWeight (strategy lines) (qL s)
        (fun a => read s a = none)) := by
    rw [hdist, Distribution.avgOver_map]
    simp only [F, hq, hmismatch, hnoneA, hnoneB, avgOver_add]
    congr 2
    exact (WinImplications.consistencyDefect_postprocess_eq_mismatch
      μ (strategy lines) qL qL read read).symm
  have hAB : consistencyDefect μ (fun s a => (A s).effect a) (fun s a => (B s).effect a)
      (pairState setting) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (kind, .point) := by
    refine le_of_eq ((WinImplications.consistencyDefect_postprocess_eq_mismatch
      μ (strategy lines) qL qP read (fun _ => pointGameRead)).trans ?_)
    rw [directLdBranchRejectionProbability_eq_avgOver]
    exact avgOver_congr _ _ _ fun s => (hrejA s).symm
  have hCB : consistencyDefect μ (fun s a => (C s).effect a) (fun s a => (B s).effect a)
      (pairState setting) ≤ deltaQ :=
    (le_of_eq (point_read_defect_on_direct_samples_eq_rejection lines)).trans
      (point_point_rejection_le lines)
  have hCD : consistencyDefect μ (fun s a => (C s).effect a) (fun s a => (D s).effect a)
      (pairState setting) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, kind) := by
    refine le_of_eq ((WinImplications.consistencyDefect_postprocess_eq_mismatch
      μ (strategy lines) qP qL (fun _ => pointGameRead) read).trans ?_)
    rw [directLdBranchRejectionProbability_eq_avgOver]
    exact avgOver_congr _ _ _ fun s => (hrejB s).symm
  have htrans := consistencyDefect_trans_le μ A B C D (pairState setting) _ _ _
    (uniformDistribution_isProbability _) (pairState_norm setting) hAB hCB hCD
  have hnoneA_le : avgOver μ (fun s => aliceEventWeight (strategy lines) (qL s)
      (fun a => read s a = none)) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (kind, .point) := by
    rw [directLdBranchRejectionProbability_eq_avgOver]
    exact avgOver_mono _ _ _ fun s => alice_none_mass_at_le_rejectedMass lines kind read s (hrejA s)
  have hnoneB_le : avgOver μ (fun s => bobEventWeight (strategy lines) (qL s)
      (fun a => read s a = none)) ≤
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, kind) := by
    rw [directLdBranchRejectionProbability_eq_avgOver]
    exact avgOver_mono _ _ _ fun s => bob_none_mass_at_le_rejectedMass lines kind read s (hrejB s)
  linarith

/-- Independently evaluating the supplied axis-line measurements has defect at
most `6 * deltaL + 2 * sqrt (deltaQ + 2 * deltaL)`. -/
theorem axis_parameter_evaluation_defect_le
    (lines : ExtendedLinesWitness setting points deltaL) :
    axisParameterEvaluationDefect lines ≤
      6 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  have h := parameter_evaluation_defect_le_aux lines .aline P.d
    (directALineDescOf P.extendedDirectLd) axisQuestion
    (directALinePointDist P.extendedDirectLd) axisCoefficients axisGameRead
    rfl (fun _ => rfl) (avgOver_directALinePointDist_resample P.extendedDirectLd)
    (fun s a ha => by
      cases a <;> simp [validDirectLdAnswer] at ha
      rfl)
    (rejectedMass_eq_read_mismatch lines)
    (point_axis_rejectedMass_eq_read_mismatch lines)
  have hforward := (completedLinePointDefect_sums_le lines).1
  rw [← aline_point_rejection_eq_completedLinePointDefect lines,
    ← dline_point_rejection_eq_completedLinePointDefect lines] at hforward
  have hreverse := (completedLinePointDefect_sums_le lines).2
  rw [← point_aline_rejection_eq_completedLinePointDefect lines,
    ← point_dline_rejection_eq_completedLinePointDefect lines] at hreverse
  have hfn := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.dline, .point)
  have hrn := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.point, .dline)
  have hsqrt : Real.sqrt (deltaQ +
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .aline)) ≤
      Real.sqrt (deltaQ + 2 * deltaL) :=
    Real.sqrt_le_sqrt (by linarith)
  unfold axisParameterEvaluationDefect
  linarith

/-- Independently evaluating the supplied diagonal-line measurements has
defect at most `6 * deltaL + 2 * sqrt (deltaQ + 2 * deltaL)`. -/
theorem diagonal_parameter_evaluation_defect_le
    (lines : ExtendedLinesWitness setting points deltaL) :
    diagonalParameterEvaluationDefect lines ≤
      6 * deltaL + 2 * Real.sqrt (deltaQ + 2 * deltaL) := by
  have h := parameter_evaluation_defect_le_aux lines .dline
    (P.extendedDirectLd.m * P.extendedDirectLd.d)
    (directDLineDescOf P.extendedDirectLd) diagonalQuestion
    (directDLinePointDist P.extendedDirectLd) diagonalCoefficients diagonalGameRead
    rfl (fun _ => rfl) (avgOver_directDLinePointDist_resample P.extendedDirectLd)
    (fun s a ha => by
      cases a <;> simp [validDirectLdAnswer] at ha
      rfl)
    (diagonal_rejectedMass_eq_read_mismatch lines)
    (point_diagonal_rejectedMass_eq_read_mismatch lines)
  have hforward := (completedLinePointDefect_sums_le lines).1
  rw [← aline_point_rejection_eq_completedLinePointDefect lines,
    ← dline_point_rejection_eq_completedLinePointDefect lines] at hforward
  have hreverse := (completedLinePointDefect_sums_le lines).2
  rw [← point_aline_rejection_eq_completedLinePointDefect lines,
    ← point_dline_rejection_eq_completedLinePointDefect lines] at hreverse
  have hfn := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.aline, .point)
  have hrn := directLdBranchRejectionProbability_nonneg
    P.extendedDirectLd (strategy lines) (.point, .aline)
  have hsqrt : Real.sqrt (deltaQ +
      directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .dline)) ≤
      Real.sqrt (deltaQ + 2 * deltaL) :=
    Real.sqrt_le_sqrt (by linarith)
  unfold diagonalParameterEvaluationDefect
  linarith

end ExtendedLineGame

end

end MIPStarRE.QPBT
