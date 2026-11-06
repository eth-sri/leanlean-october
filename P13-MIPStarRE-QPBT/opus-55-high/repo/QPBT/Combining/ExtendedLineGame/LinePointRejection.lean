module
public import QPBT.Combining.ExtendedLineGame.StateTransport
public import QPBT.Combining.Lines.PairStateConsistencyTransport

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
  ⟨0, by simp⟩

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

theorem axis_point_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.d + 1) → DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.alinePolys coeffs) (.pointVals values) = true ↔
      axisGameRead sample (.alinePolys coeffs) = pointGameRead (.pointVals values) := by
  let line := directALineDescOf P.extendedDirectLd sample
  have hmem : sample.point ∈ line.pointSet := by
    simpa [line, DirectLineDesc.pointSet, directALineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction] using
      (mem_linePoints_lineRepMap (coordinateDirection sample.index) sample.point)
  constructor
  · intro hwin
    have heval : DirectEvaluatesTo line (coeffs onlyCoordinate) sample.point
        (values onlyCoordinate) := by
      refine ⟨hmem, ?_⟩
      intro parameter hparameter
      have hcondition : directAlinePointCondition P.extendedDirectLd
          (directLdMap P.extendedDirectLd .aline sample)
          (directLdMap P.extendedDirectLd .point sample) coeffs values := by
        simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
      exact hcondition parameter (by
        grind [directALineDescOf, directLdMap, DirectLineDesc.base, DirectLineDesc.direction]) onlyCoordinate
    have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) =
        some (values onlyCoordinate) :=
      (directEvalOpt_eq_some_iff line sample.point (coeffs onlyCoordinate)
        (values onlyCoordinate)).2 heval
    grind [axisGameRead, pointGameRead]
  · intro hread
    have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) =
        some (values onlyCoordinate) := by
      cases h : directEvalOpt line sample.point (coeffs onlyCoordinate) with
      | none => grind [axisGameRead, pointGameRead]
      | some value =>
          have hvalue : value = values onlyCoordinate := by
            apply (extendedDirectScalarEquiv P).injective
            simpa [axisGameRead, pointGameRead, line, h] using hread
          simp_all
    have heval := (directEvalOpt_eq_some_iff line sample.point
      (coeffs onlyCoordinate) (values onlyCoordinate)).1 hopt
    simp only [directLdWinPredicate, validDirectLdAnswer, Bool.and_self,
      ↓reduceIte, decide_eq_true_eq]
    intro parameter hparameter index
    have hindex : index = onlyCoordinate := by
      have hlt : index.val < 1 :=
        index.isLt
      have hzero : (onlyCoordinate (P := P)).val = 0 := rfl
      apply Fin.ext
      rw [hzero]
      omega
    subst index
    exact heval.2 parameter (by
      grind [directALineDescOf, directLdMap, DirectLineDesc.base, DirectLineDesc.direction])

theorem directEvalOpt_congr {D : DirectLdParams} {c c' : ℕ} (line : DirectLineDesc D)
    (u : Fin D.m → DirectScalarQ D) (f : DirectDegPoly D c) (f' : DirectDegPoly D c')
    (h : ∀ t, evalCoefficient f' t = evalCoefficient f t) :
    directEvalOpt line u f' = directEvalOpt line u f :=
  Option.ext fun a => by simp only [directEvalOpt_eq_some_iff, DirectEvaluatesTo, h]

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
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dlinePolys coeffs) (.pointVals values) = true ↔
      diagonalGameRead sample (.dlinePolys coeffs) = pointGameRead (.pointVals values) := by
  let line := directDLineDescOf P.extendedDirectLd sample
  have hmem : sample.point ∈ line.pointSet := by
    simpa [line, DirectLineDesc.pointSet, directDLineDescOf,
      DirectLineDesc.base, DirectLineDesc.direction] using
      (mem_linePoints_lineRepMap
        (directPrefixProjection sample.index sample.direction) sample.point)
  constructor
  · intro hwin
    have heval : DirectEvaluatesTo line (coeffs onlyCoordinate) sample.point
        (values onlyCoordinate) := by
      refine ⟨hmem, ?_⟩
      intro parameter hparameter
      have hcondition : directDlinePointCondition P.extendedDirectLd
          (directLdMap P.extendedDirectLd .dline sample)
          (directLdMap P.extendedDirectLd .point sample) coeffs values := by
        simpa [directLdWinPredicate, validDirectLdAnswer] using hwin
      exact hcondition parameter (by
        grind [directDLineDescOf, directLdMap, DirectLineDesc.base, DirectLineDesc.direction]) onlyCoordinate
    have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) =
        some (values onlyCoordinate) :=
      (directEvalOpt_eq_some_iff line sample.point (coeffs onlyCoordinate)
        (values onlyCoordinate)).2 heval
    grind [diagonalGameRead, pointGameRead]
  · intro hread
    have hopt : directEvalOpt line sample.point (coeffs onlyCoordinate) =
        some (values onlyCoordinate) := by
      cases h : directEvalOpt line sample.point (coeffs onlyCoordinate) with
      | none => grind [diagonalGameRead, pointGameRead]
      | some value =>
          have hvalue : value = values onlyCoordinate := by
            apply (extendedDirectScalarEquiv P).injective
            simpa [diagonalGameRead, pointGameRead, line, h] using hread
          simp_all
    have heval := (directEvalOpt_eq_some_iff line sample.point
      (coeffs onlyCoordinate) (values onlyCoordinate)).1 hopt
    simp only [directLdWinPredicate, validDirectLdAnswer, Bool.and_self,
      ↓reduceIte, decide_eq_true_eq]
    intro parameter hparameter index
    have hindex : index = onlyCoordinate := by
      have hlt : index.val < 1 := index.isLt
      have hzero : (onlyCoordinate (P := P)).val = 0 := rfl
      apply Fin.ext
      rw [hzero]
      omega
    subst index
    exact heval.2 parameter (by
      grind [directDLineDescOf, directLdMap, DirectLineDesc.base, DirectLineDesc.direction])

variable (lines : ExtendedLinesWitness setting points deltaL)

/-- At a fixed question pair, rejected Born mass is the mass of unequal reads,
provided that on valid answers the verifier accepts exactly when the reads agree. -/
theorem rejectedMass_eq_mismatch_of (x y : DirectLdQuestion P.extendedDirectLd)
    (rA rB : DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P))
    (h : ∀ a b, validDirectLdAnswer x.1 a = true → validDirectLdAnswer y.1 b = true →
      (directLdWinPredicate P.extendedDirectLd x y a b = true ↔ rA a = rB b)) :
    directRejectedMass P.extendedDirectLd (strategy lines) x y =
      outcomeEventWeight (strategy lines) x y (fun a b => rA a ≠ rB b) := by
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases ha : validDirectLdAnswer x.1 a = true
  · by_cases hb : validDirectLdAnswer y.1 b = true
    · by_cases hw : directLdWinPredicate P.extendedDirectLd x y a b = true <;> simp_all
    · simp [outcomeWeight_eq_zero_of_invalid lines x y a b (Or.inr (by simpa using hb))]
  · simp [outcomeWeight_eq_zero_of_invalid lines x y a b (Or.inl (by simpa using ha))]

/-- A branch rejection probability equals a read defect once the fixed-sample
rejected masses are read mismatches. -/
theorem branch_rejection_eq_of (tA tB : LdType)
    (rA rB : DirectLdSpace P.extendedDirectLd → DirectLdAnswer P.extendedDirectLd →
      Option (PauliScalar P)) {D : ℝ}
    (hmass : ∀ s, directRejectedMass P.extendedDirectLd (strategy lines)
        (tA, directLdMap P.extendedDirectLd tA s) (tB, directLdMap P.extendedDirectLd tB s) =
      outcomeEventWeight (strategy lines) (tA, directLdMap P.extendedDirectLd tA s)
        (tB, directLdMap P.extendedDirectLd tB s) (fun a b => rA s a ≠ rB s b))
    (hD : consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
      (fun s c => heteroKron (((answerMeasurement lines .alice
        (tA, directLdMap P.extendedDirectLd tA s)).postprocess (rA s)).effect c) 1)
      (fun s c => heteroKron 1 (((answerMeasurement lines .bob
        (tB, directLdMap P.extendedDirectLd tB s)).postprocess (rB s)).effect c))
      (pairState setting) = D) :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines) (tA, tB) = D :=
  ((avgOver_congr _ _ _ hmass).trans (WinImplications.consistencyDefect_postprocess_eq_mismatch
    _ (strategy lines) (fun s => (tA, directLdMap P.extendedDirectLd tA s))
    (fun s => (tB, directLdMap P.extendedDirectLd tB s)) rA rB).symm).trans hD

/-- The completed point read of the direct-game answer measurement is the
corresponding scalar coarse-graining of the supplied joint point measurement. -/
theorem point_read_effect
    (side : PlayerSide)
    (sample : DirectLdSpace P.extendedDirectLd) (answer : Option (PauliScalar P)) :
    (((answerMeasurement lines side
        (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
      pointGameRead).effect answer) =
      ((points.Q side
        (projX (directPointToPauli P sample.point))
        (projZ (directPointToPauli P sample.point))).postprocess fun values =>
          some (directPointToPauli P sample.point (alphaVar P.m) * values.1 +
            directPointToPauli P sample.point (betaVar P.m) * values.2)).effect answer := by
  unfold answerMeasurement CombinedPointsWitness.extendedQ
  rw [MIPStarRE.Quantum.Measurement.postprocess_comp,
    MIPStarRE.Quantum.Measurement.postprocess_comp]
  rfl

/-- The `AA'`--`BA''` completed line-point defect of a line family is the
consistency defect of the completed direct-game readouts on `pairState`. -/
theorem completed_defect_eq_read_defect_of (t : LdType)
    (L : DirectLdSpace P.extendedDirectLd → DirectLineDesc P.extendedDirectLd)
    (r : DirectLdSpace P.extendedDirectLd → DirectLdAnswer P.extendedDirectLd →
      Option (PauliScalar P))
    (hr : ∀ s a, ((answerMeasurement lines .alice
        (t, directLdMap P.extendedDirectLd t s)).postprocess (r s)).effect a =
      ((lines.Qline .alice (L s)).postprocess fun c =>
        (directEvalOpt (L s) s.point c).map (extendedDirectScalarEquiv P)).effect a) :
    completedLinePointDefect lines .AA' .BA''
        ((uniformDistribution (DirectLdSpace P.extendedDirectLd)).map fun s => (L s, s.point)) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun s a => heteroKron (((answerMeasurement lines .alice
          (t, directLdMap P.extendedDirectLd t s)).postprocess (r s)).effect a) 1)
        (fun s a => heteroKron 1 (((answerMeasurement lines .bob
          (.point, directLdMap P.extendedDirectLd .point s)).postprocess pointGameRead).effect a))
        (pairState setting) := by
  refine Eq.trans ?_ (placed_consistency_pairState setting _
    (fun s => (answerMeasurement lines .alice (t, directLdMap _ t s)).postprocess (r s))
    (fun s => (answerMeasurement lines .bob (.point, directLdMap _ .point s)).postprocess
      pointGameRead)).1
  unfold completedLinePointDefect consistencyDefect
  rw [Distribution.avgOver_map]
  simp only [hr, point_read_effect lines]

/-- The `BB'`--`AB''` completed line-point defect of a line family is the
consistency defect of the reversed completed direct-game readouts on `pairState`. -/
theorem reversed_completed_defect_eq_read_defect_of (t : LdType)
    (L : DirectLdSpace P.extendedDirectLd → DirectLineDesc P.extendedDirectLd)
    (r : DirectLdSpace P.extendedDirectLd → DirectLdAnswer P.extendedDirectLd →
      Option (PauliScalar P))
    (hr : ∀ s a, ((answerMeasurement lines .bob
        (t, directLdMap P.extendedDirectLd t s)).postprocess (r s)).effect a =
      ((lines.Qline .bob (L s)).postprocess fun c =>
        (directEvalOpt (L s) s.point c).map (extendedDirectScalarEquiv P)).effect a) :
    completedLinePointDefect lines .BB' .AB''
        ((uniformDistribution (DirectLdSpace P.extendedDirectLd)).map fun s => (L s, s.point)) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun s a => heteroKron (((answerMeasurement lines .alice
          (.point, directLdMap P.extendedDirectLd .point s)).postprocess pointGameRead).effect a) 1)
        (fun s a => heteroKron 1 (((answerMeasurement lines .bob
          (t, directLdMap P.extendedDirectLd t s)).postprocess (r s)).effect a))
        (pairState setting) := by
  refine Eq.trans ?_ (placed_consistency_pairState setting _
    (fun s => (answerMeasurement lines .alice (.point, directLdMap _ .point s)).postprocess
      pointGameRead)
    (fun s => (answerMeasurement lines .bob (t, directLdMap _ t s)).postprocess (r s))).2
  unfold completedLinePointDefect consistencyDefect
  rw [Distribution.avgOver_map]
  simp only [hr, point_read_effect lines]

theorem axisGameRead_axisAnswer_eq_of_effect_ne_zero
    (sample : DirectLdSpace P.extendedDirectLd) (side : PlayerSide)
    (coeffs : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1))
    (heffect : (lines.Qline side
      (directALineDescOf P.extendedDirectLd sample)).effect coeffs ≠ 0) :
    axisGameRead sample (axisAnswer P coeffs) =
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (extendedDirectScalarEquiv P) :=
  congrArg (Option.map _) (directEvalOpt_congr _ _ _ _
    (axisRead_eval_of_effect_ne_zero lines side _ rfl coeffs heffect))

theorem axis_read_effect (sample : DirectLdSpace P.extendedDirectLd) (side : PlayerSide)
    (answer : Option (PauliScalar P)) :
    ((((answerMeasurement lines side
        (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
      (axisGameRead sample)).effect answer)) =
      (((lines.Qline side (directALineDescOf P.extendedDirectLd sample)).postprocess
        (fun coeffs => (directEvalOpt
          (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
            (extendedDirectScalarEquiv P))).effect answer) := by
  unfold answerMeasurement
  rw [axis_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp]
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_filter]
  grind [directALineDescOf, axisGameRead_axisAnswer_eq_of_effect_ne_zero]

theorem diagonal_read_effect (sample : DirectLdSpace P.extendedDirectLd) (side : PlayerSide)
    (answer : Option (PauliScalar P)) :
    ((((answerMeasurement lines side
        (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
      (diagonalGameRead sample)).effect answer)) =
      (((lines.Qline side (directDLineDescOf P.extendedDirectLd sample)).postprocess
        (fun coeffs => (directEvalOpt
          (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
            (extendedDirectScalarEquiv P))).effect answer) := by
  unfold answerMeasurement
  rw [diagonal_description_canonical, MIPStarRE.Quantum.Measurement.postprocess_comp]
  simp
  simp [diagonalGameRead, diagonalAnswer, directEvalOpt_congr _ _ _ _ (diagonalRead_eval P _)]

/-- Fixed-sample axis-line/point rejection equals completed-read mismatch mass. -/
theorem rejectedMass_eq_read_mismatch (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) =
      outcomeEventWeight (strategy lines)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => axisGameRead sample answerA ≠ pointGameRead answerB) :=
  rejectedMass_eq_mismatch_of lines _ _ _ _ fun a b ha hb => by
    cases a <;> cases b <;> simp [validDirectLdAnswer] at ha hb
    exact axis_point_win_iff_read_eq sample _ _

/-- Fixed-sample diagonal-line/point rejection equals completed-read mismatch mass. -/
theorem diagonal_rejectedMass_eq_read_mismatch (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample) =
      outcomeEventWeight (strategy lines)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => diagonalGameRead sample answerA ≠ pointGameRead answerB) :=
  rejectedMass_eq_mismatch_of lines _ _ _ _ fun a b ha hb => by
    cases a <;> cases b <;> simp [validDirectLdAnswer] at ha hb
    exact diagonal_point_win_iff_read_eq sample _ _

/-- Fixed-sample point/axis-line rejection equals completed-read mismatch mass. -/
theorem point_axis_rejectedMass_eq_read_mismatch (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (fun answerA answerB => pointGameRead answerA ≠ axisGameRead sample answerB) :=
  rejectedMass_eq_mismatch_of lines _ _ _ _ fun a b ha hb => by
    cases a <;> cases b <;> simp [validDirectLdAnswer] at ha hb
    exact (axis_point_win_iff_read_eq sample _ _).trans eq_comm

/-- At a fixed point/diagonal-line question pair, rejected Born mass is
exactly the mass of unequal completed readouts. -/
theorem point_diagonal_rejectedMass_eq_read_mismatch (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (fun answerA answerB => pointGameRead answerA ≠ diagonalGameRead sample answerB) :=
  rejectedMass_eq_mismatch_of lines _ _ _ _ fun a b ha hb => by
    cases a <;> cases b <;> simp [validDirectLdAnswer] at ha hb
    exact (diagonal_point_win_iff_read_eq sample _ _).trans eq_comm

/-- The `AA'`--`BA''` completed axis-line/point defect is the consistency
defect of the corresponding completed direct-game readouts on `pairState`. -/
theorem completed_defect_eq_read_defect :
    completedLinePointDefect lines .AA' .BA''
        (directALinePointDist P.extendedDirectLd) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
              (axisGameRead sample)).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer))
        (pairState setting) :=
  completed_defect_eq_read_defect_of lines .aline _ _ fun s => axis_read_effect lines s .alice

/-- The `AA'`--`BA''` completed diagonal-line/point defect is the consistency
defect of the corresponding completed direct-game readouts on `pairState`. -/
theorem diagonal_completed_defect_eq_read_defect :
    completedLinePointDefect lines .AA' .BA''
        (directDLinePointDist P.extendedDirectLd) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
              (diagonalGameRead sample)).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer))
        (pairState setting) :=
  completed_defect_eq_read_defect_of lines .dline _ _ fun s => diagonal_read_effect lines s .alice

/-- The `BB'`--`AB''` completed axis-line/point defect is the consistency
defect of the reversed completed direct-game readouts on `pairState`. -/
theorem reversed_axis_completed_defect_eq_read_defect :
    completedLinePointDefect lines .BB' .AB''
        (directALinePointDist P.extendedDirectLd) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.aline, directLdMap P.extendedDirectLd .aline sample)).postprocess
              (axisGameRead sample)).effect answer))
        (pairState setting) :=
  reversed_completed_defect_eq_read_defect_of lines .aline _ _ fun s => axis_read_effect lines s .bob

/-- The `BB'`--`AB''` completed diagonal-line/point defect is the consistency
defect of the reversed completed direct-game readouts on `pairState`. -/
theorem reversed_diagonal_completed_defect_eq_read_defect :
    completedLinePointDefect lines .BB' .AB''
        (directDLinePointDist P.extendedDirectLd) =
      consistencyDefect (uniformDistribution (DirectLdSpace P.extendedDirectLd))
        (fun sample answer => heteroKron
          (((answerMeasurement lines .alice
            (.point, directLdMap P.extendedDirectLd .point sample)).postprocess
              pointGameRead).effect answer) 1)
        (fun sample answer => heteroKron 1
          (((answerMeasurement lines .bob
            (.dline, directLdMap P.extendedDirectLd .dline sample)).postprocess
              (diagonalGameRead sample)).effect answer))
        (pairState setting) :=
  reversed_completed_defect_eq_read_defect_of lines .dline _ _ fun s =>
    diagonal_read_effect lines s .bob

/-- The axis-line/point branch rejection of the supplied strategy is exactly
the `AA'`--`BA''` completed line-point defect. -/
theorem aline_point_rejection_eq_completedLinePointDefect :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.aline, .point) =
      completedLinePointDefect lines .AA' .BA''
        (directALinePointDist P.extendedDirectLd) :=
  branch_rejection_eq_of lines .aline .point _ _ (rejectedMass_eq_read_mismatch lines)
    (completed_defect_eq_read_defect lines).symm

/-- The diagonal-line/point branch rejection of the supplied strategy is exactly
the `AA'`--`BA''` completed line-point defect. Failed completed evaluation remains
the `none` outcome. -/
theorem dline_point_rejection_eq_completedLinePointDefect :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.dline, .point) =
      completedLinePointDefect lines .AA' .BA''
        (directDLinePointDist P.extendedDirectLd) :=
  branch_rejection_eq_of lines .dline .point _ _ (diagonal_rejectedMass_eq_read_mismatch lines)
    (diagonal_completed_defect_eq_read_defect lines).symm

/-- The point/axis-line branch rejection of the supplied strategy is exactly
the `BB'`--`AB''` completed line-point defect. -/
theorem point_aline_rejection_eq_completedLinePointDefect :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .aline) =
      completedLinePointDefect lines .BB' .AB''
        (directALinePointDist P.extendedDirectLd) :=
  branch_rejection_eq_of lines .point .aline (fun _ => pointGameRead) axisGameRead
    (point_axis_rejectedMass_eq_read_mismatch lines)
    (reversed_axis_completed_defect_eq_read_defect lines).symm

/-- The point/diagonal-line branch rejection is exactly the `BB'`--`AB''`
completed diagonal-line/point defect. -/
theorem point_dline_rejection_eq_completedLinePointDefect :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .dline) =
      completedLinePointDefect lines .BB' .AB''
        (directDLinePointDist P.extendedDirectLd) :=
  branch_rejection_eq_of lines .point .dline (fun _ => pointGameRead) diagonalGameRead
    (point_diagonal_rejectedMass_eq_read_mismatch lines)
    (reversed_diagonal_completed_defect_eq_read_defect lines).symm

end ExtendedLineGame
end

end MIPStarRE.QPBT
