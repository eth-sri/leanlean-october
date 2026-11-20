module
public import QPBT.Combining.Lines.PairStateConsistencyTransport
public import QPBT.Observables.LineMeasurement.LinePointOverlap

/-! Completed readouts and mixed line/point rejection for the extended low-degree game. -/

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

open DistanceCalculus

local notation "D" => P.extendedDirectLd
local notation "Sample" => DirectLdSpace D
local notation "Read" => Sample → DirectLdAnswer D → Option (PauliScalar P)

def onlyCoordinate : Fin P.extendedDirectLd.k :=
  ⟨0, by change 0 < 1; decide⟩

def axisGameRead
    (sample : DirectLdSpace P.extendedDirectLd) :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .alinePolys coeffs =>
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | _ => none

def diagonalGameRead
    (sample : DirectLdSpace P.extendedDirectLd) :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .dlinePolys coeffs =>
      (directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point
        (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P)
  | _ => none

def pointGameRead :
    DirectLdAnswer P.extendedDirectLd → Option (PauliScalar P)
  | .pointVals values => some (extendedDirectScalarEquiv P (values onlyCoordinate))
  | _ => none

private theorem linePointRead_iff {c : ℕ} (line : DirectLineDesc P.extendedDirectLd)
    (u : DirectPoint P.extendedDirectLd) (hu : u ∈ line.pointSet)
    (coeffs : Fin P.extendedDirectLd.k → DirectDegPoly P.extendedDirectLd c)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    (∀ t, u = line.base + t • line.direction → ∀ j, evalCoefficient (coeffs j) t = values j) ↔
      (directEvalOpt line u (coeffs onlyCoordinate)).map (extendedDirectScalarEquiv P) =
        some (extendedDirectScalarEquiv P (values onlyCoordinate)) := by
  rw [← Option.map_some (f := extendedDirectScalarEquiv P),
    (Option.map_injective (extendedDirectScalarEquiv P).injective).eq_iff,
    directEvalOpt_eq_some_iff]
  letI : Subsingleton (Fin P.extendedDirectLd.k) := inferInstanceAs (Subsingleton (Fin 1))
  refine ⟨fun h => ⟨hu, fun t ht => h t ht _⟩, ?_⟩
  intro h t ht j
  rw [Subsingleton.elim j onlyCoordinate]
  exact h.2 t ht

private theorem directEvalOpt_congr {c c' : ℕ} (line : DirectLineDesc P.extendedDirectLd)
    (u : DirectPoint P.extendedDirectLd)
    (f : DirectDegPoly P.extendedDirectLd c) (g : DirectDegPoly P.extendedDirectLd c')
    (h : ∀ t, evalCoefficient f t = evalCoefficient g t) :
    directEvalOpt line u f = directEvalOpt line u g := by
  apply Option.ext
  intro a
  simp only [directEvalOpt_eq_some_iff, DirectEvaluatesTo, LineEvaluation.Determines, h]

section

variable (sample : DirectLdSpace P.extendedDirectLd)

private theorem axis_point_win_iff_read_eq
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.d + 1) → DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.aline, directLdMap P.extendedDirectLd .aline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.alinePolys coeffs) (.pointVals values) = true ↔
      axisGameRead sample (.alinePolys coeffs) = pointGameRead (.pointVals values) := by
  simp only [directLdWinPredicate, validDirectLdAnswer, Bool.and_self, ↓reduceIte,
    decide_eq_true_eq]
  exact linePointRead_iff (directALineDescOf P.extendedDirectLd sample) sample.point
    (mem_linePoints_lineRepMap (coordinateDirection sample.index) sample.point) coeffs values

private theorem diagonal_point_win_iff_read_eq
    (coeffs : Fin P.extendedDirectLd.k →
      Fin (P.extendedDirectLd.m * P.extendedDirectLd.d + 1) →
        DirectScalarQ P.extendedDirectLd)
    (values : Fin P.extendedDirectLd.k → DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.dline, directLdMap P.extendedDirectLd .dline sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.dlinePolys coeffs) (.pointVals values) = true ↔
      diagonalGameRead sample (.dlinePolys coeffs) = pointGameRead (.pointVals values) := by
  simp only [directLdWinPredicate, validDirectLdAnswer, Bool.and_self, ↓reduceIte,
    decide_eq_true_eq]
  exact linePointRead_iff (directDLineDescOf P.extendedDirectLd sample) sample.point
    (mem_linePoints_lineRepMap
      (directPrefixProjection sample.index sample.direction) sample.point) coeffs values

private theorem axisGameRead_axisAnswer_eq_of_effect_ne_zero
    (lines : ExtendedLinesWitness setting points deltaL)
    (side : PlayerSide) (sample : DirectLdSpace P.extendedDirectLd)
    (coeffs : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1))
    (heffect : (lines.Qline side
      (directALineDescOf P.extendedDirectLd sample)).effect coeffs ≠ 0) :
    axisGameRead sample (axisAnswer P coeffs) =
      (directEvalOpt (directALineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (extendedDirectScalarEquiv P) := congrArg (Option.map (extendedDirectScalarEquiv P))
  (directEvalOpt_congr _ _ _ _ (axisRead_eval_of_effect_ne_zero lines side _ rfl coeffs heffect))

theorem diagonalGameRead_diagonalAnswer_eq
    (coeffs : DirectDegPoly P.extendedDirectLd (P.m * P.d + 1)) :
    diagonalGameRead sample (diagonalAnswer P coeffs) =
      (directEvalOpt (directDLineDescOf P.extendedDirectLd sample) sample.point coeffs).map
        (extendedDirectScalarEquiv P) := congrArg (Option.map (extendedDirectScalarEquiv P))
  (directEvalOpt_congr _ _ _ _ (diagonalRead_eval P coeffs))

end

/-- The direct question tag for each line kind. -/
abbrev lineTag : LineKind → LdType
  | .axis => .aline
  | .diagonal => .dline

/-- The line generated by a common direct sample. -/
abbrev sampleLine (kind : LineKind) : Sample → DirectLineDesc D :=
  match kind with
  | .axis => directALineDescOf D
  | .diagonal => directDLineDescOf D

/-- The line read selected by the question kind. -/
abbrev lineGameRead (kind : LineKind) : Read :=
  match kind with
  | .axis => axisGameRead
  | .diagonal => diagonalGameRead

/-- Joint law of the sampled line and its point. -/
abbrev linePointLaw (P : AdmissibleParams) (kind : LineKind) :=
  (uniformDistribution (DirectLdSpace P.extendedDirectLd)).map fun s => (sampleLine kind s, s.point)

abbrev sampleQuestion (tag : LdType) (s : Sample) : DirectLdQuestion D :=
  (tag, directLdMap D tag s)

section

variable (lines : ExtendedLinesWitness setting points deltaL)

/-- The postprocessed answer measurement on a common direct sample. -/
abbrev sampleReadout
    (side : PlayerSide) (tag : LdType) (read : Read) (s : Sample) :
    Measurement (Option (PauliScalar P)) (setting.ExpandedLocalSpace side) :=
  (answerMeasurement lines side (sampleQuestion tag s)).postprocess (read s)

/-- Consistency defect of two completed readouts in the extended strategy. -/
abbrev readoutDefect
    (tagA tagB : LdType) (readA readB : Read) : ℝ :=
  bipartiteDefect (uniformDistribution Sample)
    (sampleReadout lines .alice tagA readA)
    (sampleReadout lines .bob tagB readB)
    (pairState setting)

abbrev branchRejection (tagA tagB : LdType) :=
  directLdBranchRejectionProbability D (strategy lines) (tagA, tagB)

/-- Answer predicates agreeing on all valid tags have the same Born mass. -/
theorem outcomeEventWeight_congr_valid
    (x y : DirectLdQuestion D) (e f : DirectLdAnswer D → DirectLdAnswer D → Prop)
    [DecidableRel e] [DecidableRel f]
    (h : ∀ a b, validDirectLdAnswer x.1 a = true → validDirectLdAnswer y.1 b = true →
      (e a b ↔ f a b)) :
    outcomeEventWeight (strategy lines) x y e = outcomeEventWeight (strategy lines) x y f := by
  unfold outcomeEventWeight
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  cases ha : validDirectLdAnswer x.1 a
  · simp [outcomeWeight_eq_zero_of_invalid lines x y a b (.inl ha)]
  cases hb : validDirectLdAnswer y.1 b
  · simp [outcomeWeight_eq_zero_of_invalid lines x y a b (.inr hb)]
  exact if_congr (h a b ha hb) rfl rfl

/-- Inclusion on valid answer pairs suffices for monotonicity of Born mass. -/
theorem outcomeEventWeight_mono_valid
    (x y : DirectLdQuestion D) (e f : DirectLdAnswer D → DirectLdAnswer D → Prop)
    [DecidableRel e] [DecidableRel f]
    (h : ∀ a b, validDirectLdAnswer x.1 a = true → validDirectLdAnswer y.1 b = true →
      e a b → f a b) :
    outcomeEventWeight (strategy lines) x y e ≤ outcomeEventWeight (strategy lines) x y f := by
  rw [outcomeEventWeight_congr_valid lines x y e (fun a b => e a b ∧ f a b)
    (fun a b ha hb => ⟨fun he => ⟨he, h a b ha hb he⟩, And.left⟩)]
  exact outcome_event_weight_mono _ _ _ _ _ fun _ _ => And.right

/-- Under the constructed strategy only valid answer tags have weight. -/
theorem rejectedMass_eq_of_valid_reads {α : Type*} [DecidableEq α]
    (lines : ExtendedLinesWitness setting points deltaL)
    (x y : DirectLdQuestion D) (readX readY : DirectLdAnswer D → α)
    (h : ∀ a b, validDirectLdAnswer x.1 a = true → validDirectLdAnswer y.1 b = true →
      (directLdWinPredicate D x y a b = true ↔ readX a = readY b)) :
    directRejectedMass D (strategy lines) x y =
      outcomeEventWeight (strategy lines) x y (fun a b => readX a ≠ readY b) := by
  rw [directRejectedMass_eq_event]
  apply outcomeEventWeight_congr_valid
  intro a b ha hb
  rw [Bool.eq_false_iff]
  exact not_congr (h a b ha hb)

private theorem line_point_win_iff_read_eq (kind : LineKind) (s : Sample)
    (a b : DirectLdAnswer D) (ha : validDirectLdAnswer (lineTag kind) a = true)
    (hb : validDirectLdAnswer .point b = true) :
    directLdWinPredicate D (sampleQuestion (lineTag kind) s) (sampleQuestion .point s) a b = true ↔
      lineGameRead kind s a = pointGameRead b := by
  cases kind <;> cases a <;> cases b <;> simp [lineTag, validDirectLdAnswer] at ha hb
  · exact axis_point_win_iff_read_eq s _ _
  · exact diagonal_point_win_iff_read_eq s _ _

/-- On a mixed line/point question, rejection is disagreement of completed reads. -/
theorem line_point_rejectedMass_eq_read_mismatch (kind : LineKind) (s : Sample) :
    directRejectedMass D (strategy lines) (sampleQuestion (lineTag kind) s) (sampleQuestion .point s) =
      outcomeEventWeight (strategy lines) (sampleQuestion (lineTag kind) s) (sampleQuestion .point s)
        (fun a b => lineGameRead kind s a ≠ pointGameRead b) :=
  rejectedMass_eq_of_valid_reads lines _ _ _ _ (line_point_win_iff_read_eq kind s)

/-- The same mismatch identity with the line on Bob's side. -/
theorem point_line_rejectedMass_eq_read_mismatch (kind : LineKind) (s : Sample) :
    directRejectedMass D (strategy lines) (sampleQuestion .point s) (sampleQuestion (lineTag kind) s) =
      outcomeEventWeight (strategy lines) (sampleQuestion .point s) (sampleQuestion (lineTag kind) s)
        (fun a b => pointGameRead a ≠ lineGameRead kind s b) := by
  apply rejectedMass_eq_of_valid_reads
  intro a b ha hb
  rw [directLdWinPredicate_symm]
  exact (line_point_win_iff_read_eq kind s b a hb ha).trans eq_comm

/-- Compare a fixed pair of tags by reading their answers on the common sample. -/
theorem readoutDefect_eq_branchRejection (tagA tagB : LdType) (readA readB : Read)
    (h : ∀ s, directRejectedMass D (strategy lines) (sampleQuestion tagA s) (sampleQuestion tagB s) =
      outcomeEventWeight (strategy lines) (sampleQuestion tagA s) (sampleQuestion tagB s)
        (fun a b => readA s a ≠ readB s b)) :
    readoutDefect lines tagA tagB readA readB = branchRejection lines tagA tagB := by
  rw [branchRejection, directLdBranchRejectionProbability_eq_avgOver]
  exact (WinImplications.consistencyDefect_postprocess_eq_mismatch _ (strategy lines) _ _
    readA readB).trans (avgOver_congr _ _ _ fun s => (h s).symm)

/-- The strategy's point readout is the scalar coarse-graining of the point witness. -/
theorem point_read_effect (side : PlayerSide)
    (s : Sample) (a : Option (PauliScalar P)) :
    (sampleReadout lines side .point (fun _ => pointGameRead) s).effect a =
      (completedPointReadout points side s.point).effect a := by
  classical
  unfold sampleReadout answerMeasurement completedPointReadout
  rw [Measurement.postprocess_comp]
  rfl

private theorem line_read_effect
    (side : PlayerSide) (kind : LineKind) (s : Sample) (a : Option (PauliScalar P)) :
    (sampleReadout lines side (lineTag kind) (lineGameRead kind) s).effect a =
      (completedLineReadout lines side (sampleLine kind s) s.point).effect a := by
  classical
  cases kind
  · unfold sampleReadout answerMeasurement lineTag
    rw [axis_description_canonical, Measurement.postprocess_comp]
    simp only [Measurement.postprocess_effect, Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : (lines.Qline side (directALineDescOf D s)).effect c = 0
    · simp [h, sampleLine]
    · rw [show lineGameRead .axis s (axisAnswer P c) = _ from
        axisGameRead_axisAnswer_eq_of_effect_ne_zero lines side s c h]
  · unfold sampleReadout answerMeasurement lineTag
    rw [diagonal_description_canonical, Measurement.postprocess_comp]
    simp only [Measurement.postprocess_effect, Finset.sum_filter]
    exact Finset.sum_congr rfl fun c _ => by
      rw [show lineGameRead .diagonal s (diagonalAnswer P c) = _ from
        diagonalGameRead_diagonalAnswer_eq s c]

/-- Identifying the strategy readouts on the first opposite register pair. -/
theorem completed_line_point_defect_eq_readout (kind : LineKind) :
    completedLinePointDefect lines .AA' .BA'' (linePointLaw P kind) =
      readoutDefect lines (lineTag kind) .point (lineGameRead kind) (fun _ => pointGameRead) := by
  unfold completedLinePointDefect completedDefect ProjectiveSetting.placedDefect
    measurementDefect consistencyDefect
  simp only [linePointLaw, Distribution.avgOver_map]
  refine avgOver_congr _ _ _ fun s =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  dsimp only
  simp only [placed_product_stateQForm_eq, ProjectiveSetting.placedMeasurement_effect]
  rw [stateQForm_pairState_eq_AA'_BA'',
    line_read_effect lines .alice kind s a, point_read_effect lines .bob s b]

/-- Identifying the strategy readouts on the second opposite register pair. -/
theorem completed_point_line_defect_eq_readout (kind : LineKind) :
    completedLinePointDefect lines .BB' .AB'' (linePointLaw P kind) =
      readoutDefect lines .point (lineTag kind) (fun _ => pointGameRead) (lineGameRead kind) := by
  unfold completedLinePointDefect completedDefect ProjectiveSetting.placedDefect
    measurementDefect consistencyDefect
  simp only [linePointLaw, Distribution.avgOver_map]
  refine avgOver_congr _ _ _ fun s => Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  dsimp only
  simp only [placed_product_stateQForm_eq, ProjectiveSetting.placedMeasurement_effect]
  rw [stateQForm_pairState_eq_AB''_BB',
    ProjectiveSetting.placedCorrelation,
    ProjectiveSetting.place_AB''_mul_place_BB'_comm,
    line_read_effect lines .bob kind s b, point_read_effect lines .alice s a]
  simp only [eq_comm]

/-- Mixed line/point rejection equals the supplied completed consistency defect. -/
theorem line_point_rejection_eq_completedLinePointDefect (kind : LineKind) :
    branchRejection lines (lineTag kind) .point =
      completedLinePointDefect lines .AA' .BA'' (linePointLaw P kind) := by
  rw [completed_line_point_defect_eq_readout, readoutDefect_eq_branchRejection]
  exact line_point_rejectedMass_eq_read_mismatch lines kind

/-- Mixed point/line rejection equals the supplied completed consistency defect. -/
theorem point_line_rejection_eq_completedLinePointDefect (kind : LineKind) :
    branchRejection lines .point (lineTag kind) =
      completedLinePointDefect lines .BB' .AB'' (linePointLaw P kind) := by
  rw [completed_point_line_defect_eq_readout, readoutDefect_eq_branchRejection]
  exact point_line_rejectedMass_eq_read_mismatch lines kind

/-- The forward and reverse sums of mixed-line branch errors have the same bound. -/
theorem mixed_line_branch_bounds :
    branchRejection lines .aline .point + branchRejection lines .dline .point ≤ 2 * deltaL ∧
    branchRejection lines .point .aline + branchRejection lines .point .dline ≤ 2 * deltaL := by
  rw [line_point_rejection_eq_completedLinePointDefect lines .axis,
    line_point_rejection_eq_completedLinePointDefect lines .diagonal,
    point_line_rejection_eq_completedLinePointDefect lines .axis,
    point_line_rejection_eq_completedLinePointDefect lines .diagonal]
  exact ⟨completedLinePointDefect_sum_le lines .alice, completedLinePointDefect_sum_le lines .bob⟩

/-- Every line/point branch satisfies the forward bound. -/
theorem line_point_rejection_le
    (kind : LineKind) : branchRejection lines (lineTag kind) .point ≤ 2 * deltaL := by
  have h := (mixed_line_branch_bounds lines).1
  have hA := directLdBranchRejectionProbability_nonneg D (strategy lines) (.aline, .point)
  have hD := directLdBranchRejectionProbability_nonneg D (strategy lines) (.dline, .point)
  cases kind <;> dsimp only [lineTag] <;> linarith

/-- Every point/line branch satisfies the reverse bound. -/
theorem point_line_rejection_le
    (kind : LineKind) : branchRejection lines .point (lineTag kind) ≤ 2 * deltaL := by
  have h := (mixed_line_branch_bounds lines).2
  have hA := directLdBranchRejectionProbability_nonneg D (strategy lines) (.point, .aline)
  have hD := directLdBranchRejectionProbability_nonneg D (strategy lines) (.point, .dline)
  cases kind <;> dsimp only [lineTag] <;> linarith

theorem mixed_line_point_rejections_le_four_mul :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.aline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.dline, .point) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .aline) +
        directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
          (.point, .dline) ≤ 4 * deltaL := by
  obtain ⟨h, h'⟩ := mixed_line_branch_bounds lines
  linarith

end

end ExtendedLineGame

end

end MIPStarRE.QPBT
