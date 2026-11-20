module

public import QPBT.Combining.DirectLowDegree.Transport.Strategy
public import QPBT.Combining.DirectLowDegree.GameValue
public import QPBT.Games.DistanceTheorems.LdtBridge
public import MIPStarRE.LDT.Test.StrategyBiProj.Measurements

/-!
# Branch comparison for the coordinate strategies of the direct low-degree game

Every branch of the low individual degree failure probability of a coordinate
strategy `directCoordinateProjStrat` is compared with the ordered type-pair
branch of the direct game asking the same questions.  An accepted direct
answer pair reads out to equal LDT answers: the line answer, rebased to the
LDT line and evaluated at the LDT base point, is the point answer, and the
zero-direction convention reads the constant value at the base point.  Hence
the LDT inconsistency mass at a question pair is at most the rejected direct
Born mass there.  The point-agreement and axis-line branches then compare
exactly after the coordinate reindexing of `directPointEquiv`; the diagonal
branches are treated in `Transport.DiagonalRecursion`.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:214-458`
- `references/ldt-paper/test_definition.tex:130-151`
- Blueprint `def:ld-question-distribution`, `lem:ld-aline-level`,
  `lem:ld-dline-level`, `lem:ld-question-typed-cl`, `lem:alnf`, `lem:dlnf`,
  `def:ld-win-predicate`, `rem:ld-win-zero-direction`, and `def:ld-meas`
- `MIPStarRE/LDT/Test/StrategyFailures.lean:18-130`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

/-- Admissible field sizes are positive, so LDT points over a direct
parameter tuple form a nonempty type. -/
instance instNeZeroNatQ (D : DirectLdParams) : NeZero D.q :=
  ⟨Nat.ne_of_gt D.toLDTParameters.hq⟩

/-! ## Rejected Born mass at a fixed question pair -/

section

variable (D : DirectLdParams) (S : Strategy (directLdGame D))
include D S

section

variable (x y : DirectLdQuestion D)
include x y

/-- The Born mass of the rejected answer pairs at a fixed pair of direct
questions.  Its uniform average over the common direct sample of an ordered
type pair is `directLdBranchRejectionProbability`. -/
def directRejectedMass : ℝ :=
  ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
    if directLdWinPredicate D x y a b then 0 else outcomeWeight S x y a b

theorem directRejectedMass_eq_event :
    directRejectedMass D S x y =
      outcomeEventWeight S x y (fun a b => directLdWinPredicate D x y a b = false) := by
  unfold directRejectedMass outcomeEventWeight
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Bool.eq_false_iff, ite_not]

theorem directRejectedMass_nonneg :
    0 ≤ directRejectedMass D S x y := by
  rw [directRejectedMass_eq_event]
  exact outcome_event_weight_nonneg S x y _

end

/-- The branch rejection probability of an ordered type pair is the uniform
average of the rejected Born mass at the canonical questions of the common
direct sample. -/
theorem directLdBranchRejectionProbability_eq_avgOver (types : LdType × LdType) :
    directLdBranchRejectionProbability D S types =
      avgOver (uniformDistribution (DirectLdSpace D)) fun sample =>
        directRejectedMass D S
          (types.1, directLdMap D types.1 sample)
          (types.2, directLdMap D types.2 sample) :=
  rfl

/-- When every accepted direct answer pair reads out to equal LDT answers,
the bipartite consistency defect of the two readouts at a fixed question pair
is at most the rejected direct Born mass there.  The matched mass of the
readouts is the Born mass of the pairs with equal readouts, and the total
overlap is the full Born mass, which is one. -/
theorem qBipartiteConsDefect_le_directRejectedMass
    (hS : S.IsProjective)
    {Outcome : Type*} [Fintype Outcome]
    (x y : DirectLdQuestion D)
    (readA readB : DirectLdAnswer D → Outcome)
    (hwin : ∀ a b, directLdWinPredicate D x y a b = true → readA a = readB b) :
    qBipartiteConsDefect (strategyQuantumState S)
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas ≤
      directRejectedMass D S x y := by
  classical
  letI := (strategyQuantumState_isNormalized S).nonempty
  let A := (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toMeasurement
  let B := (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toMeasurement
  change qBipartiteConsDefect ((strategyPureState S : PureState _) : QuantumState _)
    A.toSubMeas B.toSubMeas ≤ _
  rw [ldt_qBipartiteConsDefect_eq]
  change (∑ a, ∑ b, if a = b then 0 else stateQForm S.ψ
    (heteroKron (((S.A x).postprocess readA).effect a) (((S.B y).postprocess readB).effect b))) ≤ _
  rw [DistanceCalculus.point_placed_defect_postprocess, directRejectedMass_eq_event]
  simpa only [outcomeEventWeight, ite_not, outcomeWeight, stateQForm] using
    outcome_event_weight_mono S x y (fun a b => readA a ≠ readB b)
      (fun a b => directLdWinPredicate D x y a b = false) fun a b hab =>
        Bool.eq_false_iff.mpr (fun hw => hab (hwin a b hw))

end

section

variable (D : DirectLdParams) (r : Fin D.k)
include D r

/-- On the point-agreement branch, an accepted pair of point answers has
equal readouts in every simultaneous coordinate. -/
theorem directPointAnswerReadout_eq_of_win
    (p : DirectPoint D) (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directLdPointQuestionOf D p)
      (directLdPointQuestionOf D p) a b = true) :
    letI := D.toLDTFieldModel
    directPointAnswerReadout D r a = directPointAnswerReadout D r b := by
  letI := D.toLDTFieldModel
  cases a <;> cases b <;>
    simp [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer] at hwin
  subst_vars
  rfl

/-- The axis-line acceptance clause at the canonical rebase parameter gives
the rebased polynomial its point value at the LDT base point. -/
private theorem axis_readout_of_condition
    (line : AxisParallelLine D.toLDTParameters)
    (f : Fin D.k → Fin (D.d + 1) → DirectScalarQ D)
    (c : Fin D.k → DirectScalarQ D)
    (hcond : directAlinePointCondition D
      ⟨lineRepMap (coordinateDirection (Fin.rev line.direction))
          (ldtPointToDirect D line.base),
        Fin.rev line.direction, 0⟩
      ⟨ldtPointToDirect D line.base, D.firstIndex, 0⟩ f c) :
    letI := D.toLDTFieldModel
    directAxisAnswerReadout D r line (.alinePolys f) zeroCoord =
      directScalarEquiv D (c r) := by
  letI := D.toLDTFieldModel
  have heval :=
    hcond (directAxisRebaseParameter D line)
      (directLineRepParameter_spec
        (coordinateDirection (Fin.rev line.direction))
        (ldtPointToDirect D line.base)) r
  simp only [directAxisAnswerReadout]
  rw [AxisLinePolynomial.reparamAt_apply_zero, directAxisAnswerEquiv_apply, heval]

/-- The diagonal-line acceptance clause gives the readout its point value at
the LDT base point, using the canonical rebase parameter for a nonzero
direction and the parameter zero for the zero direction. -/
private theorem diagonal_readout_of_condition
    (line : DiagonalLine D.toLDTParameters)
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
    (c : Fin D.k → DirectScalarQ D)
    (hcond : directDlinePointCondition D
      ⟨lineRepMap (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base),
        directDiagonalIndexOf D (ldtPointToDirect D line.direction),
        ldtPointToDirect D line.direction⟩
      ⟨ldtPointToDirect D line.base, D.firstIndex, 0⟩ f c) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerReadout D r line (.dlinePolys f) zeroCoord =
      directScalarEquiv D (c r) := by
  letI := D.toLDTFieldModel
  by_cases hdir : ldtPointToDirect D line.direction = 0
  · have hbase : ldtPointToDirect D line.base =
        lineRepMap (0 : DirectPoint D) (ldtPointToDirect D line.base) := by
      simpa only [hdir, smul_zero, add_zero] using directLineRepParameter_spec
        (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base)
    rw [hdir] at hcond
    have heval := hcond 0 (by simpa only [smul_zero, add_zero] using hbase) r
    simp only [directDiagonalAnswerReadout, hdir, if_true, constantDiagonalAnswer_apply, heval]
  · have heval :=
      hcond (directDiagonalRebaseParameter D line)
        (directLineRepParameter_spec
          (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base)) r
    simp only [directDiagonalAnswerReadout, hdir, if_false]
    rw [DiagonalLinePolynomial.reparamAt_apply_zero,
      directDiagonalAnswerEquiv_apply, heval]

/-- On the axis-line branch with the line on the left, an accepted direct
answer pair has the rebased line answer, evaluated at the LDT base point,
equal to the point readout. -/
theorem directAxisAnswerReadout_zeroCoord_eq_of_win (line : AxisParallelLine D.toLDTParameters)
    (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directAxisQuestionOf D line)
      (directPointQuestionOf D line.base) a b = true) :
    letI := D.toLDTFieldModel
    directAxisAnswerReadout D r line a zeroCoord =
      directPointAnswerReadout D r b := by
  letI := D.toLDTFieldModel
  cases a <;> cases b <;>
    simp only [directLdWinPredicate, directAxisQuestionOf, directPointQuestionOf,
      directLdPointQuestionOf, validDirectLdAnswer, Bool.and_self, Bool.true_and,
      Bool.false_and, Bool.and_false, ↓reduceIte, Bool.false_eq_true] at hwin
  exact axis_readout_of_condition D r line _ _ (@of_decide_eq_true _ (Classical.propDecidable _) hwin)

/-- On the diagonal-line branch with the line on the left, an accepted direct
answer pair has the rebased line answer, evaluated at the LDT base point,
equal to the point readout. -/
theorem directDiagonalAnswerReadout_zeroCoord_eq_of_win (line : DiagonalLine D.toLDTParameters)
    (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directDiagonalQuestionOf D line)
      (directPointQuestionOf D line.base) a b = true) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerReadout D r line a zeroCoord =
      directPointAnswerReadout D r b := by
  letI := D.toLDTFieldModel
  cases a <;> cases b <;>
    simp only [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf,
      directLdPointQuestionOf, validDirectLdAnswer, Bool.and_self, Bool.true_and,
      Bool.false_and, Bool.and_false, ↓reduceIte, Bool.false_eq_true] at hwin
  exact diagonal_readout_of_condition D r line _ _ (@of_decide_eq_true _ (Classical.propDecidable _) hwin)

end

/-- A direct question with a postprocessing of its answers. -/
abbrev DirectReadout (D : DirectLdParams) (α : Type*) :=
  DirectLdQuestion D × (DirectLdAnswer D → α)

/-- Use the line/point or point/line ordering in a two-player quantity. -/
def linePointOrder {α β : Type*} (lineFirst : Bool) (F : α → α → β) (line point : α) : β :=
  bif lineFirst then F line point else F point line

section

variable (D : DirectLdParams) (S : Strategy (directLdGame D))
    (hS : S.IsProjective) {α : Type*} [Fintype α]
include D S hS α

noncomputable def directReadoutDefect (A B : DirectReadout D α) : ℝ :=
  qBipartiteConsDefect (strategyQuantumState S)
    (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.A A.1) (hS.1 A.1)) A.2).toSubMeas
    (ProjMeas.postprocess (matrixMeasurementToLDTProjMeas (S.B B.1) (hS.2 B.1)) B.2).toSubMeas

/-- A readout agreement implication bounds the defect in either order. -/
theorem linePointReadoutDefect_le (line point : DirectReadout D α)
    (hwin : ∀ a b, directLdWinPredicate D line.1 point.1 a b = true → line.2 a = point.2 b)
    (lineFirst : Bool) :
    linePointOrder lineFirst (directReadoutDefect D S hS) line point ≤
      linePointOrder lineFirst (directRejectedMass D S) line.1 point.1 := by
  cases lineFirst
  · exact qBipartiteConsDefect_le_directRejectedMass D S hS point.1 line.1 point.2 line.2
      fun a b h => (hwin b a ((directLdWinPredicate_symm D _ _ _ _).trans h)).symm
  · exact qBipartiteConsDefect_le_directRejectedMass D S hS line.1 point.1 line.2 point.2 hwin

end

abbrev coordinatePointReadout (D : DirectLdParams) (r : Fin D.k) (u : Point D.toLDTParameters) :
    letI := D.toLDTFieldModel; DirectReadout D (Fq D.toLDTParameters) :=
  ⟨directPointQuestionOf D u, directPointAnswerReadout D r⟩

/-! ## Direct samples as products -/

/-- A direct sample as its point-index pair together with its direction.
Formalization-only reindexing of the direct sample space. -/
def directLdSpaceSplitEquiv (D : DirectLdParams) :
    DirectLdSpace D ≃
      ((DirectPoint D) × Fin D.m) × (DirectPoint D) where
  toFun s := ((s.point, s.index), s.direction)
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv s := rfl
  right_inv x := rfl

/-! ## The point-agreement and axis-line branches -/

section PointAxisBranches

variable (D : DirectLdParams) (S : Strategy (directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)

/-- Point-agreement defect at an LDT point is at most the rejected direct
mass at the direct point question. -/
private theorem point_defect_le (u : Point D.toLDTParameters) :
    letI := D.toLDTFieldModel
    qBipartiteConsDefect (directCoordinateProjStrat D S hS r).state
        ((directCoordinateProjStrat D S hS r).pointMeasurementA u).toSubMeas
        ((directCoordinateProjStrat D S hS r).pointMeasurementB u).toSubMeas ≤
      directRejectedMass D S
        (directLdPointQuestionOf D (ldtPointToDirect D u))
        (directLdPointQuestionOf D (ldtPointToDirect D u)) := qBipartiteConsDefect_le_directRejectedMass D S hS (directPointQuestionOf D u) (directPointQuestionOf D u)   (directPointAnswerReadout D r) (directPointAnswerReadout D r) fun a b hab ↦   directPointAnswerReadout_eq_of_win D r (ldtPointToDirect D u) a b hab

/-- The point-agreement failure of the coordinate strategy is at most the
point-point branch rejection of the direct game. -/
theorem directCoordinate_point_agreement_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).pointAgreementFailureProbability ≤
      directLdBranchRejectionProbability D S (.point, .point) := by
  letI := D.toLDTFieldModel
  unfold ProjStrat.pointAgreementFailureProbability bipartiteConsError
  refine (avgOver_mono _ _ _ (point_defect_le D S hS r)).trans_eq ?_
  rw [directLdBranchRejectionProbability_eq_avgOver]
  let f := fun p => directRejectedMass D S (directLdPointQuestionOf D p) (directLdPointQuestionOf D p)
  exact (avgOver_uniform_equiv (directPointEquiv D) f).symm.trans
    (avgOver_uniform_equiv_fst (directLdSpacePointEquiv D) f).symm

/-- Reindex a uniform average over LDT axis samples to the direct sample
space; the averaged function depends only on the decoded point and the
reversed coordinate index. -/
private theorem avgOver_axis_sample_eq
    (f : (DirectPoint D) × Fin D.m → ℝ) :
    avgOver (uniformDistribution (AxisParallelTestSample D.toLDTParameters))
        (fun s => f (ldtPointToDirect D s.1, Fin.rev s.2)) =
      avgOver (uniformDistribution (DirectLdSpace D))
        (fun sample => f (sample.point, sample.index)) := by
  exact (avgOver_uniform_equiv ((directPointEquiv D).prodCongr Fin.revPerm) f).symm.trans
    (avgOver_uniform_equiv_fst (directLdSpaceSplitEquiv D) f).symm

private abbrev axisPointReadout (s : AxisParallelTestSample D.toLDTParameters) :
    letI := D.toLDTFieldModel; DirectReadout D (Fq D.toLDTParameters) := by
  letI := D.toLDTFieldModel
  exact ⟨directAxisQuestionOf D ⟨s.1, s.2⟩, fun a => directAxisAnswerReadout D r ⟨s.1, s.2⟩ a zeroCoord⟩

set_option maxHeartbeats 600000 in
/-- In either orientation the axis failure is bounded by the corresponding direct branch. -/
private theorem directCoordinate_axis_le (lineFirst : Bool) :
    letI := D.toLDTFieldModel
    (bif lineFirst then
      (directCoordinateProjStrat D S hS r).axisParallelLineLeftPointRightFailureProbability
    else (directCoordinateProjStrat D S hS r).axisParallelPointLeftLineRightFailureProbability) ≤
      directLdBranchRejectionProbability D S (linePointOrder lineFirst Prod.mk .aline .point) := by
  letI := D.toLDTFieldModel
  let F (s : AxisParallelTestSample D.toLDTParameters) :=
    linePointOrder lineFirst (directReadoutDefect D S hS)
      (axisPointReadout D r s) (coordinatePointReadout D r s.1)
  have hF : (bif lineFirst then
      (directCoordinateProjStrat D S hS r).axisParallelLineLeftPointRightFailureProbability
    else (directCoordinateProjStrat D S hS r).axisParallelPointLeftLineRightFailureProbability) =
      avgOver (uniformDistribution _) F := by
    cases lineFirst <;> apply avgOver_congr <;> intro s <;>
      simp only [F, linePointOrder, Bool.cond_true, Bool.cond_false, directReadoutDefect,   ProjStrat.axisParallelLineAnswerFamilyA, ProjStrat.axisParallelLineAnswerFamilyB,   ProjStrat.axisParallelPointAnswerFamilyA, ProjStrat.axisParallelPointAnswerFamilyB, directCoordinateProjStrat,   directCoordinateReadout, directCoordinateAxisMeasurement, directCoordinatePointMeasurement,   ProjMeas.postprocess_toSubMeas, SubMeas.postprocess_comp]
  rw [hF, directLdBranchRejectionProbability_eq_avgOver]
  refine (avgOver_mono _ _ _ fun s => linePointReadoutDefect_le D S hS
    (axisPointReadout D r s) (coordinatePointReadout D r s.1)
    (directAxisAnswerReadout_zeroCoord_eq_of_win D r ⟨s.1, s.2⟩) lineFirst).trans_eq ?_
  cases lineFirst <;> exact avgOver_axis_sample_eq D (fun pi =>
    linePointOrder _ (directRejectedMass D S)
      (.aline, ⟨lineRepMap (coordinateDirection pi.2) pi.1, pi.2, 0⟩)
      (directLdPointQuestionOf D pi.1))

theorem directCoordinate_axis_line_point_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).axisParallelLineLeftPointRightFailureProbability ≤
      directLdBranchRejectionProbability D S (.aline, .point) :=
  directCoordinate_axis_le D S hS r true

theorem directCoordinate_axis_point_line_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat D S hS r).axisParallelPointLeftLineRightFailureProbability ≤
      directLdBranchRejectionProbability D S (.point, .aline) :=
  directCoordinate_axis_le D S hS r false

end PointAxisBranches

end

end MIPStarRE.QPBT
