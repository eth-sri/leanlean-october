module
public import QPBT.Combining.ExtendedLineGame.StateTransport

/-!
# Line/point and mixed rejection for the extended direct game
-/
@[expose] public section
open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

/-- The unique coordinate of the one-coordinate extended direct low-degree game. -/
def onlyCoordinate : Fin P.extendedDirectLd.k :=
  ⟨0, by change 0 < 1; decide⟩

/-- Read an axis-line answer by completed evaluation at the sampled point. -/
def axisGameRead
    (sample : DirectLdSpace P.extendedDirectLd) :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .alinePolys coeffs =>
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | _ => none

/-- Read a diagonal-line answer by completed evaluation at the sampled point. -/
def diagonalGameRead
    (sample : DirectLdSpace P.extendedDirectLd) :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .dlinePolys coeffs =>
      (directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | _ => none

/-- Read the unique point coordinate as an optional Pauli scalar. -/
def pointGameRead :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .pointVals values => some (extendedDirectScalarEquiv P (values onlyCoordinate))
  | _ => none

private theorem line_point_cond_iff_evalOpt_eq
    {deg : ℕ} (line : DirectLineDesc P.extendedDirectLd)
    (pt : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
    (hmem : pt ∈ line.pointSet)
    (coeffs : Fin P.extendedDirectLd.k → Fin (deg + 1) → DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    decide (∀ t : DirectScalarQ P.extendedDirectLd, pt = line.base + t • line.direction →
      ∀ i : Fin P.extendedDirectLd.k, evalCoefficient (coeffs i) t = values i) = true ↔
      (directEvalOpt line pt (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P) =
        some (extendedDirectScalarEquiv P (values onlyCoordinate)) := by
  have honly (i : Fin P.extendedDirectLd.k) : i = onlyCoordinate := by
    ext; have := i.isLt; change i.val < 1 at this; change i.val = 0; omega
  rw [decide_eq_true_eq, ← Option.map_some,
    (Option.map_injective (extendedDirectScalarEquiv P).injective).eq_iff, directEvalOpt_eq_some_iff]
  exact ⟨fun h => ⟨hmem, fun t ht => h t ht onlyCoordinate⟩,
    fun h t ht i => honly i ▸ h.2 t ht⟩

private theorem axis_point_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.d + 1) → DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.alinePolys coeffs) (.pointVals values) = true ↔
      axisGameRead sample (.alinePolys coeffs) = pointGameRead (.pointVals values) := by
  simpa [directLdWinPredicate, validDirectLdAnswer, directAlinePointCondition,
    directALineDescOf, directLdMap, DirectLineDesc.base, DirectLineDesc.direction,
    axisGameRead, pointGameRead] using
    line_point_cond_iff_evalOpt_eq (directALineDescOf P.extendedDirectLd sample) sample.point
      (by simpa [DirectLineDesc.pointSet, directALineDescOf, DirectLineDesc.base,
            DirectLineDesc.direction] using
            mem_linePoints_lineRepMap (coordinateDirection sample.index) sample.point)
      coeffs values

theorem diagonal_point_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.m * P.extendedDirectLd.d + 1) →
        DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dlinePolys coeffs) (.pointVals values) = true ↔
      diagonalGameRead sample (.dlinePolys coeffs) = pointGameRead (.pointVals values) := by
  simpa [directLdWinPredicate, validDirectLdAnswer, directDlinePointCondition,
    directDLineDescOf, directLdMap, DirectLineDesc.base, DirectLineDesc.direction,
    diagonalGameRead, pointGameRead] using
    line_point_cond_iff_evalOpt_eq (directDLineDescOf P.extendedDirectLd sample) sample.point
      (by simpa [DirectLineDesc.pointSet, directDLineDescOf, DirectLineDesc.base,
            DirectLineDesc.direction] using
            mem_linePoints_lineRepMap
              (directPrefixProjection sample.index sample.direction) sample.point)
      coeffs values

private theorem directEvalOpt_eq_of_evalCoefficient_eq {d1 d2 : ℕ}
    (line : DirectLineDesc P.extendedDirectLd)
    (pt : Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)
    (c1 : DirectDegPoly P.extendedDirectLd d1)
    (c2 : DirectDegPoly P.extendedDirectLd d2)
    (heval : ∀ t, evalCoefficient c1 t = evalCoefficient c2 t) :
    directEvalOpt line pt c1 = directEvalOpt line pt c2 := by
  refine Option.ext fun v => ?_
  simp only [directEvalOpt_eq_some_iff, DirectEvaluatesTo, heval]

private theorem axis_read_effect_side
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    (((answerMeasurement lines side
        (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
      (axisGameRead sample)).effect answer) =
      (((lines.Qline side (directALineDescOf P.extendedDirectLd sample)).postprocess
        (fun coeffs => (directEvalOpt
          (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
            (extendedDirectScalarEquiv P))).effect answer) := by
  classical
  unfold answerMeasurement
  rw [axis_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp]
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  refine Finset.sum_congr rfl fun coeffs _ => ?_
  by_cases heffect : (lines.Qline side
      (directALineDescOf P.extendedDirectLd sample)).effect coeffs = 0
  · simp [heffect]
  · have hread : axisGameRead sample (axisAnswer P coeffs) =
        (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
          (extendedDirectScalarEquiv P) :=
      congrArg (Option.map (extendedDirectScalarEquiv P))
        (directEvalOpt_eq_of_evalCoefficient_eq _ _ _ _
          (axisRead_eval_of_effect_ne_zero lines side _ rfl coeffs heffect))
    rw [hread]

theorem diagonalGameRead_diagonalAnswer_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1)) :
    diagonalGameRead sample (diagonalAnswer P coeffs) =
      (directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (extendedDirectScalarEquiv P) :=
  congrArg (Option.map (extendedDirectScalarEquiv P))
    (directEvalOpt_eq_of_evalCoefficient_eq _ _ _ _ (diagonalRead_eval P coeffs))

private theorem diagonal_read_effect_side
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    (((answerMeasurement lines side
        (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
      (diagonalGameRead sample)).effect answer) =
      (((lines.Qline side (directDLineDescOf P.extendedDirectLd sample)).postprocess
        (fun coeffs => (directEvalOpt
          (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
            (extendedDirectScalarEquiv P))).effect answer) := by
  classical
  unfold answerMeasurement
  rw [diagonal_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp]
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  refine Finset.sum_congr rfl fun coeffs _ => ?_
  rw [diagonalGameRead_diagonalAnswer_eq]

/-- The completed point read of the direct-game answer measurement is the
corresponding scalar coarse-graining of the supplied joint point measurement. -/
theorem point_read_effect
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    (((answerMeasurement lines side
        (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
      pointGameRead).effect answer) =
      (((points.Q side
        (projX (directPointToPauli P sample.point))
        (projZ (directPointToPauli P sample.point))).postprocess fun values =>
          some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
            directPointToPauli P sample.point (betaVar P.m) * values.2)).effect answer) := by
  classical
  unfold answerMeasurement CombinedPointsWitness.extendedQ
  rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
    MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl

theorem rejectedMass_eq_read_mismatch_of_win_iff
    (lines : ExtendedLinesWitness setting points deltaL)
    (qA qB : DirectLdQuestion P.extendedDirectLd)
    (rA rB : DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P))
    (hiff : ∀ a b, validDirectLdAnswer qA.1 a = true → validDirectLdAnswer qB.1 b = true →
      (directLdWinPredicate P.extendedDirectLd qA qB a b = true ↔ rA a = rB b)) :
    directRejectedMass P.extendedDirectLd (strategy lines) qA qB =
      outcomeEventWeight (strategy lines) qA qB (fun a b => rA a ≠ rB b) := by
  classical
  unfold directRejectedMass outcomeEventWeight
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hinv : validDirectLdAnswer qA.1 a = false ∨ validDirectLdAnswer qB.1 b = false
  · rw [outcomeWeight_eq_zero_of_invalid lines qA qB a b hinv]; simp
  · rw [not_or] at hinv
    have h := hiff a b (Bool.eq_true_of_not_eq_false hinv.1) (Bool.eq_true_of_not_eq_false hinv.2)
    by_cases hr : rA a = rB b
    · simp [hr, h.mpr hr]
    · have hnw : directLdWinPredicate P.extendedDirectLd qA qB a b = false :=
        Bool.eq_false_of_not_eq_true (mt h.mp hr)
      simp [hr, hnw]

/-- Fixed-sample axis-line/point rejection equals completed-read mismatch mass. -/
theorem rejectedMass_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) =
      outcomeEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => axisGameRead sample answerA ≠ pointGameRead answerB) :=
  rejectedMass_eq_read_mismatch_of_win_iff lines _ _ _ _ fun a b ha hb => by
    cases a <;> cases b <;> try contradiction
    exact axis_point_win_iff_read_eq sample _ _

/-- Fixed-sample diagonal-line/point rejection equals completed-read mismatch mass. -/
theorem diagonal_rejectedMass_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) =
      outcomeEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => diagonalGameRead sample answerA ≠ pointGameRead answerB) :=
  rejectedMass_eq_read_mismatch_of_win_iff lines _ _ _ _ fun a b ha hb => by
    cases a <;> cases b <;> try contradiction
    exact diagonal_point_win_iff_read_eq sample _ _

/-- Fixed-sample point/axis-line rejection equals completed-read mismatch mass. -/
theorem point_axis_rejectedMass_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB => pointGameRead answerA ≠ axisGameRead sample answerB) :=
  rejectedMass_eq_read_mismatch_of_win_iff lines _ _ _ _ fun a b ha hb => by
    cases a <;> cases b <;> try contradiction
    exact (axis_point_win_iff_read_eq sample _ _).trans eq_comm

/-- Fixed-sample point/diagonal-line rejection equals completed-read mismatch mass. -/
theorem point_diagonal_rejectedMass_eq_read_mismatch
    (lines : ExtendedLinesWitness setting points deltaL)
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answerA answerB => pointGameRead answerA ≠ diagonalGameRead sample answerB) :=
  rejectedMass_eq_read_mismatch_of_win_iff lines _ _ _ _ fun a b ha hb => by
    cases a <;> cases b <;> try contradiction
    exact (diagonal_point_win_iff_read_eq sample _ _).trans eq_comm

/-- The opposite `BB'` and `AB''` placements commute. -/
theorem place_BB'_mul_AB''_comm
    (A : Op (setting.ExpandedLocalSpace .alice))
    (B : Op (setting.ExpandedLocalSpace .bob)) :
    setting.place .BB' B * setting.place .AB'' A =
      setting.place .AB'' A * setting.place .BB' B := by
  change Op (setting.toStrategy.ιA × PauliRegister P) at A
  change Op (setting.toStrategy.ιB × PauliRegister P) at B
  let e := ProjectiveSetting.abBbBipartition P
    setting.toStrategy.ιA setting.toStrategy.ιB
  let C := heteroKron B (1 : Op (PauliRegister P × PauliRegister P))
  let L := heteroKron A (1 : Op ((setting.toStrategy.ιB × PauliRegister P) ×
    (PauliRegister P × PauliRegister P)))
  let R := heteroKron (1 : Op (setting.toStrategy.ιA × PauliRegister P)) C
  have hleft : reindexOp e L = setting.place .AB'' A :=
    ProjectiveSetting.reindexOp_abBbBipartition_left setting A
  have hright : reindexOp e R = setting.place .BB' B :=
    ProjectiveSetting.reindexOp_abBbBipartition_right setting B
  rw [← hleft, ← hright, ← WinImplications.reindexOp_mul, ← WinImplications.reindexOp_mul,
    show R * L = L * R from (WinImplications.heteroKron_left_right_comm A C).symm]

private theorem forward_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LdType)
    (descOf : DirectLdSpace P.extendedDirectLd → DirectLineDesc P.extendedDirectLd)
    (dist : Distribution (DirectLineDesc P.extendedDirectLd ×
      (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)))
    (read : DirectLdSpace P.extendedDirectLd → DirectLdAnswer P.extendedDirectLd →
      Option (PauliScalar P))
    (hdist : dist = (uniformDistribution (DirectLdSpace P.extendedDirectLd)).map
      (fun s => (descOf s, s.point)))
    (hrej : ∀ s, directRejectedMass P.extendedDirectLd (strategy lines)
      (kind, directLdMap P.extendedDirectLd kind s)
      (.point, directLdMap P.extendedDirectLd .point s) =
      outcomeEventWeight (strategy lines)
        (kind, directLdMap P.extendedDirectLd kind s)
        (.point, directLdMap P.extendedDirectLd .point s)
        (fun a b => read s a ≠ pointGameRead b))
    (heff : ∀ s ans,
      (((answerMeasurement lines .alice
        (kind, directLdMap P.extendedDirectLd kind s)).postprocess (read s)).effect ans) =
      (((lines.Qline .alice (descOf s)).postprocess
        (fun coeffs => (directEvalOpt (descOf s) s.point coeffs).map
          (extendedDirectScalarEquiv P))).effect ans)) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (kind, .point) =
      completedLinePointDefect lines .AA' .BA'' dist := by
  rw [directLdBranchRejectionProbability_eq_avgOver,
    avgOver_congr _ _ _ hrej,
    ← WinImplications.consistencyDefect_postprocess_eq_mismatch
      (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
      (fun s => (kind, directLdMap P.extendedDirectLd kind s))
      (fun s => (.point, directLdMap P.extendedDirectLd .point s))
      read (fun _ => pointGameRead)]
  unfold completedLinePointDefect consistencyDefect
  rw [hdist, Distribution.avgOver_map]
  refine avgOver_congr _ _ _ fun sample =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, ite_false, DistanceCalculus.consistency_term_eq_stateQForm,
      DistanceCalculus.placed_product_stateQForm_eq]
    change DistanceCalculus.stateQForm (pairState setting)
      (heteroKron (((answerMeasurement lines .alice
          (kind, directLdMap P.extendedDirectLd kind sample)).postprocess
            (read sample)).effect a)
        (((answerMeasurement lines .bob
          (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
            pointGameRead).effect b)) = _
    rw [heff sample a, point_read_effect lines .bob sample b]
    exact stateQForm_pairState_eq_AA'_BA'' setting _ _
      (Matrix.nonneg_iff_posSemidef.mp
        (((lines.Qline .alice (descOf sample)).postprocess _).pos a)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        (((points.Q .bob _ _).postprocess _).pos b)).isHermitian

private theorem reverse_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL)
    (kind : LdType)
    (descOf : DirectLdSpace P.extendedDirectLd → DirectLineDesc P.extendedDirectLd)
    (dist : Distribution (DirectLineDesc P.extendedDirectLd ×
      (Fin P.extendedDirectLd.m → DirectScalarQ P.extendedDirectLd)))
    (read : DirectLdSpace P.extendedDirectLd → DirectLdAnswer P.extendedDirectLd →
      Option (PauliScalar P))
    (hdist : dist = (uniformDistribution (DirectLdSpace P.extendedDirectLd)).map
      (fun s => (descOf s, s.point)))
    (hrej : ∀ s, directRejectedMass P.extendedDirectLd (strategy lines)
      (.point, directLdMap P.extendedDirectLd .point s)
      (kind, directLdMap P.extendedDirectLd kind s) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point s)
        (kind, directLdMap P.extendedDirectLd kind s)
        (fun a b => pointGameRead a ≠ read s b))
    (heff : ∀ s ans,
      (((answerMeasurement lines .bob
        (kind, directLdMap P.extendedDirectLd kind s)).postprocess (read s)).effect ans) =
      (((lines.Qline .bob (descOf s)).postprocess
        (fun coeffs => (directEvalOpt (descOf s) s.point coeffs).map
          (extendedDirectScalarEquiv P))).effect ans)) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, kind) =
      completedLinePointDefect lines .BB' .AB'' dist := by
  rw [directLdBranchRejectionProbability_eq_avgOver,
    avgOver_congr _ _ _ hrej,
    ← WinImplications.consistencyDefect_postprocess_eq_mismatch
      (uniformDistribution (DirectLdSpace P.extendedDirectLd)) (strategy lines)
      (fun s => (.point, directLdMap P.extendedDirectLd .point s))
      (fun s => (kind, directLdMap P.extendedDirectLd kind s))
      (fun _ => pointGameRead) read]
  unfold completedLinePointDefect consistencyDefect
  rw [hdist, Distribution.avgOver_map]
  refine avgOver_congr _ _ _ fun sample => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : a = b
  · simp [hab]
  · have hba : b ≠ a := Ne.symm hab
    simp only [hab, hba, ite_false, DistanceCalculus.consistency_term_eq_stateQForm,
      DistanceCalculus.placed_product_stateQForm_eq]
    change DistanceCalculus.stateQForm (pairState setting)
      (heteroKron (((answerMeasurement lines .alice
          (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
            pointGameRead).effect a)
        (((answerMeasurement lines .bob
          (kind, directLdMap P.extendedDirectLd kind sample)).postprocess
            (read sample)).effect b)) =
      DistanceCalculus.stateQForm setting.psiHat (setting.place .BB' _ * setting.place .AB'' _)
    rw [point_read_effect lines .alice sample a, heff sample b, place_BB'_mul_AB''_comm]
    exact stateQForm_pairState_eq_AB''_BB' setting _ _
      (Matrix.nonneg_iff_posSemidef.mp
        (((points.Q .alice _ _).postprocess _).pos a)).isHermitian
      (Matrix.nonneg_iff_posSemidef.mp
        (((lines.Qline .bob (descOf sample)).postprocess _).pos b)).isHermitian

theorem aline_point_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.aline, .point) =
      completedLinePointDefect lines .AA' .BA'' (directALinePointDist P.extendedDirectLd) :=
  forward_rejection_eq_completedLinePointDefect lines .aline
    (directALineDescOf P.extendedDirectLd) (directALinePointDist P.extendedDirectLd)
    axisGameRead rfl (rejectedMass_eq_read_mismatch lines) (axis_read_effect_side lines .alice)

theorem dline_point_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.dline, .point) =
      completedLinePointDefect lines .AA' .BA'' (directDLinePointDist P.extendedDirectLd) :=
  forward_rejection_eq_completedLinePointDefect lines .dline
    (directDLineDescOf P.extendedDirectLd) (directDLinePointDist P.extendedDirectLd)
    diagonalGameRead rfl (diagonal_rejectedMass_eq_read_mismatch lines)
    (diagonal_read_effect_side lines .alice)

theorem point_aline_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .aline) =
      completedLinePointDefect lines .BB' .AB'' (directALinePointDist P.extendedDirectLd) :=
  reverse_rejection_eq_completedLinePointDefect lines .aline
    (directALineDescOf P.extendedDirectLd) (directALinePointDist P.extendedDirectLd)
    axisGameRead rfl (point_axis_rejectedMass_eq_read_mismatch lines)
    (axis_read_effect_side lines .bob)

theorem point_dline_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (.point, .dline) =
      completedLinePointDefect lines .BB' .AB'' (directDLinePointDist P.extendedDirectLd) :=
  reverse_rejection_eq_completedLinePointDefect lines .dline
    (directDLineDescOf P.extendedDirectLd) (directDLinePointDist P.extendedDirectLd)
    diagonalGameRead rfl (point_diagonal_rejectedMass_eq_read_mismatch lines)
    (diagonal_read_effect_side lines .bob)

/-- The sum of the four mixed point/line rejection probabilities is at most
`4 * deltaL`. -/
theorem mixed_line_point_rejections_le_four_mul
    (lines : ExtendedLinesWitness setting points deltaL) :
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
  linarith [hbounds.1, hbounds.2]

end ExtendedLineGame
end

end MIPStarRE.QPBT
