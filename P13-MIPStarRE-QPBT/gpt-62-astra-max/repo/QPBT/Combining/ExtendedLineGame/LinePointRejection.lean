module
public import QPBT.Combining.ExtendedLineGame.StateTransport

/-!
# Line/point rejection for the extended direct game

This module identifies the axis-line/point, diagonal-line/point, and reversed
point/axis-line branch rejections of the strategy constructed from an
`ExtendedLinesWitness` with the corresponding completed line-point defects.
These are finite postprocessing and state-transport steps in the first
paragraph of the proof of `lem:qld-4-7`; they do not establish a passing-value
bound or construct the supplied witness.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issues #302, #305, #307, and #309.
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

/-- The two questions on a branch use the same geometric sample. -/
abbrev branchQ (i : LdType) (s : DirectLdSpace P.extendedDirectLd) :
    DirectLdQuestion P.extendedDirectLd := (i, directLdMap i s)

abbrev Readout (P : AdmissibleParams) :=
  DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)

/-- Rejection on valid answers is mismatch of the two decoded answers. Invalid
answers can be ignored since their Born weight is zero. -/
theorem rejectedMass_of_readout (lines : ExtendedLinesWitness setting points deltaL)
    {β : Type*} [DecidableEq β] (x y : DirectLdQuestion P.extendedDirectLd)
    (f g : DirectLdAnswer P.extendedDirectLd → β)
    (h : ∀ a b, validDirectLdAnswer x.1 a = true → validDirectLdAnswer y.1 b = true →
      (directLdWinPredicate _ x y a b = true ↔ f a = g b)) :
    directRejectedMass _ (strategy lines) x y =
      outcomeEventWeight (strategy lines) x y (fun a b => f a ≠ g b) := by
  classical
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hv : validDirectLdAnswer x.1 a = true ∧ validDirectLdAnswer y.1 b = true
  · simp_all
  · simp [(outcomeWeight_eq_zero_of_invalid lines x y a b (by grind))]

/-- The actual branch measurement followed by a completed readout. -/
noncomputable abbrev readMeasurement (lines : ExtendedLinesWitness setting points deltaL)
    (side : PlayerSide) (i : LdType) (f : DirectLdSpace P.extendedDirectLd → Readout P)
    (s : DirectLdSpace P.extendedDirectLd) :=
  (answerMeasurement lines side (branchQ i s)).postprocess (f s)

/-- Consistency of the two postprocessed branch measurements. -/
noncomputable abbrev branchReadDefect (lines : ExtendedLinesWitness setting points deltaL)
    (i j : LdType) (f g : DirectLdSpace P.extendedDirectLd → Readout P) :=
  consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
    (fun s a => heteroKron ((readMeasurement lines .alice i f s).effect a) 1)
    (fun s a => heteroKron 1 ((readMeasurement lines .bob j g s).effect a))
    (pairState setting)

/-- Correctness of the readouts on well-formed verifier answers. -/
def BranchReadLaw (i j : LdType) (f g : DirectLdSpace P.extendedDirectLd → Readout P) : Prop :=
  ∀ s a b, validDirectLdAnswer i a = true → validDirectLdAnswer j b = true →
      (directLdWinPredicate _ (branchQ i s) (branchQ j s) a b = true ↔ f s a = g s b)

theorem BranchReadLaw.swap {i j : LdType} {f g : DirectLdSpace P.extendedDirectLd → Readout P}
    (h : BranchReadLaw i j f g) : BranchReadLaw j i g f := by
  intro s a b ha hb
  rw [directLdWinPredicate_swap]
  exact (h s b a hb ha).trans eq_comm

theorem rejection_eq_readDefect (lines : ExtendedLinesWitness setting points deltaL)
    {i j : LdType} {f g : DirectLdSpace P.extendedDirectLd → Readout P}
    (h : BranchReadLaw i j f g) :
    directLdBranchRejectionProbability (strategy lines) (i, j) =
      branchReadDefect lines i j f g := by
  refine Eq.trans ?_ (WinImplications.consistencyDefect_postprocess_eq_mismatch _
    (strategy lines) (branchQ i) (branchQ j) f g).symm
  apply avgOver_congr
  exact fun s => rejectedMass_of_readout lines _ _ _ _ (h s)

/-- The unique coordinate of the one-coordinate extended direct low-degree game. -/
def onlyCoordinate : Fin P.extendedDirectLd.k :=
  ⟨0, by change 0 < 1; decide⟩

/-- Read an axis-line answer by completed evaluation at the sampled point.
Failed completed evaluation, including a zero-direction ambiguity, remains
the `none` outcome. -/
def axisGameRead
    (sample : DirectLdSpace P.extendedDirectLd) :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .alinePolys coeffs =>
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | _ => none

/-- Read the unique point coordinate as an optional Pauli scalar. Support for
`lem:qld-4-7`, paper `14_analysis_of_the_pauli_basis_test.tex:1279-1288`. -/
def pointGameRead :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .pointVals values => some (extendedDirectScalarEquiv P (values onlyCoordinate))
  | _ => none

private theorem axis_point_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.d + 1) → DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.aline, directLdMap .aline sample)
        (.point, directLdMap .point sample)
        (.alinePolys coeffs) (.pointVals values) = true ↔
      axisGameRead sample (.alinePolys coeffs) = pointGameRead (.pointVals values) := by
  let line := directALineDescOf P.extendedDirectLd sample
  have hmem := (mem_linePoints_lineRepMap (coordinateDirection sample.index) sample.point)
  constructor
  · intro hwin
    have heval : DirectEvaluatesTo line (coeffs onlyCoordinate) sample.point
        (values onlyCoordinate) := by
      refine ⟨hmem, ?_⟩
      have hcondition : directAlinePointCondition P.extendedDirectLd
          (directLdMap .aline sample)
          (directLdMap .point sample) coeffs values := by
        simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
      solve_by_elim [hcondition]
    simp [axisGameRead, pointGameRead, line, ((directEvalOpt_eq_some_iff line sample.point (coeffs onlyCoordinate)
        (values onlyCoordinate)).2 heval)]
  · intro hread
    have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) =
        some (values onlyCoordinate) := by
      cases h : directEvalOpt line sample.point (coeffs onlyCoordinate) with
      | none => simp_all [axisGameRead, pointGameRead, line, h]
      | some value =>
          simp_all [axisGameRead, pointGameRead, line, h]
    simp [directLdWinPredicate, validDirectLdAnswer, decide_eq_true_eq]
    intro parameter hparameter index
    have hindex : index = onlyCoordinate := by
      have hlt : index.val < 1 := index.isLt
      have hzero : (onlyCoordinate (P := P)).val = 0 := rfl
      omega
    subst index
    exact ((directEvalOpt_eq_some_iff line sample.point
      (coeffs onlyCoordinate) (values onlyCoordinate)).1 hopt).2 parameter (hparameter)

private theorem axisGameRead_axisAnswer_eq_of_effect_ne_zero
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1))
    (heffect : (lines.Qline side
      (directALineDescOf P.extendedDirectLd sample)).effect coeffs ≠ 0) :
    axisGameRead sample (axisAnswer P coeffs) =
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (extendedDirectScalarEquiv P) := by
  change (directEvalOpt _ sample.point
      (axisRead P coeffs)).map (extendedDirectScalarEquiv P) = _
  have heval (parameter : DirectScalarQ P.extendedDirectLd)  :=
    axisRead_eval_of_effect_ne_zero lines side _ rfl coeffs heffect parameter
  cases hfull : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
      sample.point coeffs with
  | none =>
      cases haxis : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
          sample.point (axisRead P coeffs) with
      | none => rfl
      | some answer =>
          have hspec := (directEvalOpt_eq_some_iff _ _ _ _).1 haxis
          have hfull' : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
              sample.point coeffs = some answer := by
            apply (directEvalOpt_eq_some_iff _ _ _ _).2
            exact ⟨hspec.1, fun parameter hparameter =>
              (heval parameter).symm.trans (hspec.2 parameter hparameter)⟩
          aesop
  | some answer =>
      have hspec := (directEvalOpt_eq_some_iff _ _ _ _).1 hfull
      have haxis : directEvalOpt (directALineDescOf P.extendedDirectLd sample)
          sample.point (axisRead P coeffs) = some answer := by
        apply (directEvalOpt_eq_some_iff _ _ _ _).2
        exact ⟨hspec.1, fun parameter hparameter =>
          (heval parameter).trans (hspec.2 parameter hparameter)⟩
      rw [haxis]

private theorem axis_read_effect
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    ((((answerMeasurement lines side
        (.aline, directLdMap .aline sample)).postprocess
      (axisGameRead sample)).effect answer)) =
      (((lines.Qline side (directALineDescOf P.extendedDirectLd sample)).postprocess
        (fun coeffs => (directEvalOpt
          (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
            (extendedDirectScalarEquiv P))).effect answer) := by
  classical
  unfold answerMeasurement
  rw [axis_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp]
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  congr 1 with coeffs
  by_cases heffect : (lines.Qline side
      (directALineDescOf P.extendedDirectLd sample)).effect coeffs = 0
  · simp [heffect]
  · rw [axisGameRead_axisAnswer_eq_of_effect_ne_zero lines side sample coeffs heffect]

/-- The completed point read of the direct-game answer measurement is the
corresponding scalar coarse-graining of the supplied joint point measurement. -/
theorem point_read_effect
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    (((answerMeasurement lines side
        (.point, directLdMap .point sample)).postprocess
      pointGameRead).effect answer) =
      ((points.Q side
        (projX (directPointToPauli sample.point))
        (projZ (directPointToPauli sample.point))).postprocess fun values =>
          some (directPointToPauli sample.point (alphaVar P.m) * values.1 +
            directPointToPauli sample.point (betaVar P.m) * values.2)).effect answer := by
  classical
  unfold answerMeasurement CombinedPointsWitness.extendedQ
  simp [MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl

/-- The `AA'`--`BA''` completed axis-line/point defect is the consistency
defect of the corresponding completed direct-game readouts on `pairState`. -/
theorem completed_defect_eq_read_defect
    (lines : ExtendedLinesWitness setting points deltaL) :
    completedLinePointDefect lines .AA' .BA''
        (directALinePointDist P.extendedDirectLd) =
      branchReadDefect lines .aline .point axisGameRead (fun _ => pointGameRead) := by
  unfold branchReadDefect readMeasurement branchQ completedLinePointDefect consistencyDefect
  rw [directALinePointDist, Distribution.avgOver_map]
  apply avgOver_congr
  intro sample
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a = b
  · simp [h]
  · simp only [h, Ne.symm h, if_false, DistanceCalculus.consistency_term_eq_stateQForm]
    rw [axis_read_effect lines .alice, point_read_effect lines .bob,
      DistanceCalculus.placed_product_stateQForm_eq]
    symm
    apply stateQForm_pairState_eq_AA'_BA'' <;> apply measurement_effect_hermitian

theorem axisPointReadLaw : BranchReadLaw (P := P) .aline .point axisGameRead (fun _ => pointGameRead) := by
  intro sample a b ha hb
  cases a <;> cases b <;> simp [validDirectLdAnswer] at ha hb
  apply axis_point_win_iff_read_eq

/-- The axis-line/point branch rejection of the supplied strategy is exactly
the `AA'`--`BA''` completed line-point defect.  This uses only the supplied
measurement witness, its degree support, finite postprocessing, and the
state-correlation identity from issue Dengnifer/MIPStarRE-QPBT-bak#302. -/
theorem aline_point_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability (strategy lines)
        (.aline, .point) =
      completedLinePointDefect lines .AA' .BA''
        (directALinePointDist P.extendedDirectLd) := (rejection_eq_readDefect lines axisPointReadLaw).trans
    (completed_defect_eq_read_defect lines).symm

/-- Read a diagonal-line answer by completed evaluation at the sampled point.
Other answer formats and undefined evaluations return `none`.
Support for `lem:qld-4-7`, paper `14_analysis_of_the_pauli_basis_test.tex:1279-1288`. -/
def diagonalGameRead
    (sample : DirectLdSpace P.extendedDirectLd) :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .dlinePolys coeffs =>
      (directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | _ => none

/-- The diagonal-line/point verifier is equality of the completed reads.
Support for `lem:qld-4-7`, paper `14_analysis_of_the_pauli_basis_test.tex:1279-1288`. -/
theorem diagonal_point_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.m * P.extendedDirectLd.d + 1) →
        DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.dline, directLdMap .dline sample)
        (.point, directLdMap .point sample)
        (.dlinePolys coeffs) (.pointVals values) = true ↔
      diagonalGameRead sample (.dlinePolys coeffs) = pointGameRead (.pointVals values) := by
  let line := directDLineDescOf P.extendedDirectLd sample
  have hmem : sample.point ∈ line.pointSet := by
    solve_by_elim [mem_linePoints_lineRepMap]
  constructor
  · intro hwin
    have heval : DirectEvaluatesTo line (coeffs onlyCoordinate) sample.point
        (values onlyCoordinate) := by
      refine ⟨hmem, ?_⟩
      have hcondition : directDlinePointCondition P.extendedDirectLd
          (directLdMap .dline sample)
          (directLdMap .point sample) coeffs values := by
        simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
      solve_by_elim [hcondition]
    simp [diagonalGameRead, pointGameRead, line, ((directEvalOpt_eq_some_iff line sample.point (coeffs onlyCoordinate)
        (values onlyCoordinate)).2 heval)]
  · intro hread
    have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) =
        some (values onlyCoordinate) := by
      cases h : directEvalOpt line sample.point (coeffs onlyCoordinate) with
      | none => simp_all [diagonalGameRead, pointGameRead, line, h]
      | some value =>
          simp_all [diagonalGameRead, pointGameRead, line, h]
    simp [directLdWinPredicate, validDirectLdAnswer, decide_eq_true_eq]
    intro parameter hparameter index
    have hindex : index = onlyCoordinate := by
      have hlt : index.val < 1 := index.isLt
      have hzero : (onlyCoordinate (P := P)).val = 0 := rfl
      omega
    subst index
    exact ((directEvalOpt_eq_some_iff line sample.point
      (coeffs onlyCoordinate) (values onlyCoordinate)).1 hopt).2 parameter (hparameter)

/-- Reading a diagonal strategy answer agrees with completed polynomial evaluation.
Support for `lem:qld-4-7`, paper `14_analysis_of_the_pauli_basis_test.tex:1279-1288`. -/
theorem diagonalGameRead_diagonalAnswer_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1)) :
    diagonalGameRead sample (diagonalAnswer P coeffs) =
      (directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (extendedDirectScalarEquiv P) := by
  change (directEvalOpt _ sample.point
      (diagonalRead P coeffs)).map (extendedDirectScalarEquiv P) = _
  have heval (parameter : DirectScalarQ P.extendedDirectLd) :
      evalCoefficient (diagonalRead P coeffs) parameter = evalCoefficient coeffs parameter := by
      have hdeg : P.m * P.d + 2 ≤ P.extendedDirectLd.m * P.extendedDirectLd.d + 1 := by
        have := P.hd
        nlinarith
      symm
      apply Fintype.sum_of_injective (Fin.castLE hdeg)
        (Fin.castLE_injective _) _ _ ?_ ?_
      · intro index hindex
        have hlarge : ¬index.val < P.m * P.d + 2 := fun h =>
          hindex ⟨⟨_, h⟩, Fin.ext rfl⟩
        simp [diagonalRead, hlarge]
      · intro index
        simp [diagonalRead]
  cases hfull : directEvalOpt (directDLineDescOf P.extendedDirectLd sample)
      sample.point coeffs with
  | none =>
      cases hdiagonal : directEvalOpt (directDLineDescOf P.extendedDirectLd sample)
          sample.point (diagonalRead P coeffs) with
      | none => rfl
      | some answer =>
          have hspec := (directEvalOpt_eq_some_iff _ _ _ _).1 hdiagonal
          have hfull' : directEvalOpt (directDLineDescOf P.extendedDirectLd sample)
              sample.point coeffs = some answer := by
            apply (directEvalOpt_eq_some_iff _ _ _ _).2
            exact ⟨hspec.1, fun parameter hparameter =>
              (heval parameter).symm.trans (hspec.2 parameter hparameter)⟩
          grind
  | some answer =>
      have hspec := (directEvalOpt_eq_some_iff _ _ _ _).1 hfull
      have hdiagonal : directEvalOpt (directDLineDescOf P.extendedDirectLd sample)
          sample.point (diagonalRead P coeffs) = some answer := by
        apply (directEvalOpt_eq_some_iff _ _ _ _).2
        exact ⟨hspec.1, fun parameter hparameter =>
          (heval parameter).trans (hspec.2 parameter hparameter)⟩
      rw [hdiagonal]

theorem diagonal_read_effect
    (lines : ExtendedLinesWitness setting points deltaL) (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    ((((answerMeasurement lines side
        (.dline, directLdMap .dline sample)).postprocess
      (diagonalGameRead sample)).effect answer)) =
      (((lines.Qline side (directDLineDescOf P.extendedDirectLd sample)).postprocess
        (fun coeffs => (directEvalOpt
          (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
            (extendedDirectScalarEquiv P))).effect answer) := by
  simp [answerMeasurement, diagonal_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp, diagonalGameRead_diagonalAnswer_eq]

/-- The `AA'`--`BA''` completed diagonal-line/point defect is the consistency
defect of the corresponding completed direct-game readouts on `pairState`. -/
theorem diagonal_completed_defect_eq_read_defect
    (lines : ExtendedLinesWitness setting points deltaL) :
    completedLinePointDefect lines .AA' .BA''
        (directDLinePointDist P.extendedDirectLd) =
      branchReadDefect lines .dline .point diagonalGameRead (fun _ => pointGameRead) := by
  unfold branchReadDefect readMeasurement branchQ completedLinePointDefect consistencyDefect
  rw [directDLinePointDist, Distribution.avgOver_map]
  apply avgOver_congr
  intro sample
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a = b
  · simp [h]
  · simp only [h, Ne.symm h, if_false, DistanceCalculus.consistency_term_eq_stateQForm]
    rw [diagonal_read_effect lines .alice, point_read_effect lines .bob,
      DistanceCalculus.placed_product_stateQForm_eq]
    symm
    apply stateQForm_pairState_eq_AA'_BA'' <;> apply measurement_effect_hermitian

theorem diagonalPointReadLaw : BranchReadLaw (P := P) .dline .point diagonalGameRead (fun _ => pointGameRead) := by
  intro sample a b ha hb
  cases a <;> cases b <;> simp [validDirectLdAnswer] at ha hb
  apply diagonal_point_win_iff_read_eq

/-- The diagonal-line/point branch rejection of the supplied strategy is exactly
the `AA'`--`BA''` completed line-point defect. This includes zero diagonal
directions: failed completed evaluation remains the `none` outcome and
contributes to rejection rather than being replaced by a scalar value. -/
theorem dline_point_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability (strategy lines)
        (.dline, .point) =
      completedLinePointDefect lines .AA' .BA''
        (directDLinePointDist P.extendedDirectLd) := (rejection_eq_readDefect lines diagonalPointReadLaw).trans
    (diagonal_completed_defect_eq_read_defect lines).symm

/-- The opposite `BB'` and `AB''` placements commute. Formalization-only support
for `lem:qld-4-7`, paper `14_analysis_of_the_pauli_basis_test.tex:1279-1288`. -/
theorem place_BB'_mul_AB''_comm
    (A : Op (setting.ExpandedLocalSpace .alice))
    (B : Op (setting.ExpandedLocalSpace .bob)) :
    setting.place .BB' B * setting.place .AB'' A =
      setting.place .AB'' A * setting.place .BB' B := setting.place_comm _ _ (by trivial) _ _

/-- The `BB'`--`AB''` completed axis-line/point defect is the consistency
defect of the reversed completed direct-game readouts on `pairState`. -/
theorem reversed_axis_completed_defect_eq_read_defect
    (lines : ExtendedLinesWitness setting points deltaL) :
    completedLinePointDefect lines .BB' .AB''
        (directALinePointDist P.extendedDirectLd) =
      branchReadDefect lines .point .aline (fun _ => pointGameRead) axisGameRead := by
  unfold branchReadDefect readMeasurement branchQ completedLinePointDefect consistencyDefect
  rw [directALinePointDist, Distribution.avgOver_map]
  apply avgOver_congr
  intro sample
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a = b
  · simp [h]
  · simp only [h, Ne.symm h, if_false, DistanceCalculus.consistency_term_eq_stateQForm]
    rw [axis_read_effect lines .bob, point_read_effect lines .alice,
      DistanceCalculus.placed_product_stateQForm_eq, place_BB'_mul_AB''_comm]
    symm
    apply stateQForm_pairState_eq_AB''_BB' <;> apply measurement_effect_hermitian

/-- The point/axis-line branch rejection of the supplied strategy is exactly
the `BB'`--`AB''` completed line-point defect. The proof uses the second
expanded-state correlation and does not identify the two player spaces or
assume a symmetry of the strategy. -/
theorem point_aline_rejection_eq_completedLinePointDefect
    (lines : ExtendedLinesWitness setting points deltaL) :
    directLdBranchRejectionProbability (strategy lines)
        (.point, .aline) =
      completedLinePointDefect lines .BB' .AB''
        (directALinePointDist P.extendedDirectLd) := (rejection_eq_readDefect lines axisPointReadLaw.swap).trans
    (reversed_axis_completed_defect_eq_read_defect lines).symm

end ExtendedLineGame
end

end MIPStarRE.QPBT
