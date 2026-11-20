module

public import QPBT.Combining.DirectLowDegree.Transport.Strategy
public import QPBT.Combining.DirectLowDegree.GameValue
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
open MIPStarRE.Quantum

noncomputable section

section

variable (D : DirectLdParams)

/-- Admissible field sizes are positive, so LDT points over a direct
parameter tuple form a nonempty type. -/
instance instNeZeroNatQ : NeZero D.q :=
  ⟨Nat.ne_of_gt D.toLDTParameters.hq⟩

/-! ## Rejected Born mass at a fixed question pair -/

section

variable (S : Strategy (directLdGame D))

/-- The Born mass of the rejected answer pairs at a fixed pair of direct
questions.  Its uniform average over the common direct sample of an ordered
type pair is `directLdBranchRejectionProbability`. -/
def directRejectedMass
    (x y : DirectLdQuestion D) : ℝ :=
  ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
    if directLdWinPredicate D x y a b then 0 else outcomeWeight S x y a b

theorem directRejectedMass_nonneg (x y : DirectLdQuestion D) :
    0 ≤ directRejectedMass D S x y := by
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  split_ifs
  · exact le_rfl
  · apply outcomeWeight_nonneg

/-- The branch rejection probability of an ordered type pair is the uniform
average of the rejected Born mass at the canonical questions of the common
direct sample. -/
theorem directLdBranchRejectionProbability_eq_avgOver (types : LdType × LdType) :
    directLdBranchRejectionProbability S types =
      avgOver (uniformDistribution (DirectLdSpace D)) fun sample =>
        directRejectedMass D S
          (types.1, directLdMap types.1 sample)
          (types.2, directLdMap types.2 sample) :=
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
  have hmatch :
      qBipartiteMatchMass (strategyQuantumState S)
          (ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas
          (ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas =
        ∑ a : DirectLdAnswer D, ∑ b : DirectLdAnswer D,
          if readA a = readB b then outcomeWeight S x y a b else 0 := by
    calc
      _ =
          ∑ c : Outcome,
            ∑ a ∈ Finset.univ.filter (fun a => readA a = c),
              ∑ b ∈ Finset.univ.filter (fun b => readB b = c),
                outcomeWeight S x y a b := by
        refine Finset.sum_congr rfl ?_
        solve_by_elim [directPostprocessBornWeight]
      _ = ∑ c : Outcome, ∑ a : DirectLdAnswer D,
            if readA a = c then
              ∑ b : DirectLdAnswer D,
                if readB b = c then outcomeWeight S x y a b else 0
            else 0 := by
        simp only [Finset.sum_filter]
      _ = _ := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl ?_
        intro a _
        simp
        refine Finset.sum_congr rfl ?_
        intro b _
        by_cases hab : readA a = readB b
        · simp [hab]
        · grind
  have htotal :
      ev (strategyQuantumState S)
        (opTensor
          (ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.A x) (hS.1 x)) readA).toSubMeas.total
          (ProjMeas.postprocess
            (matrixMeasurementToLDTProjMeas (S.B y) (hS.2 y)) readB).toSubMeas.total) =
        1 := by
    change ev (strategyQuantumState S)
      (Matrix.kroneckerMap (fun x1 x2 => x1 * x2) 1 1) = 1
    simp
    exact ev_one_of_isNormalized _ (strategyQuantumState_isNormalized S)
  refine max_le (directRejectedMass_nonneg D S x y) ?_
  rw [htotal, hmatch, ← (outcomeWeight_sum_eq_one S x y), ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  have hw := outcomeWeight_nonneg S x y a b
  by_cases hacc : directLdWinPredicate D x y a b = true
  · simp [hacc, (hwin a b hacc)]
  · split_ifs <;> linarith

end

/-! ## Accepted answer pairs read out consistently

An accepted answer pair of the direct game consists of well-formed answers
satisfying the line-versus-point clause or the consistency clause of
`def:ld-win-predicate`.  The readouts of `Transport.Questions` evaluate the
rebased line polynomial at the LDT base point, which is the direct point
at the canonical rebase parameter; the accepted clause forces this value to
be the point answer.  Zero directions use the constant readout at the base
point, where the universal clause of `rem:ld-win-zero-direction` gives the
value at parameter zero. -/

section

variable (r : Fin D.k)

/-- On the point-agreement branch, an accepted pair of point answers has
equal readouts in every simultaneous coordinate. -/
theorem directPointAnswerReadout_eq_of_win
    {p : DirectPoint D} (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directLdPointQuestionOf D p)
      (directLdPointQuestionOf D p) a b = true) :
    letI := D.toLDTFieldModel
    directPointAnswerReadout r a = directPointAnswerReadout r b := by
  letI := D.toLDTFieldModel
  cases a with
  | pointVals u =>
      cases b with
      | pointVals v =>
          simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer]
      | alinePolys _ =>
          simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer]
      | dlinePolys _ =>
          simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer]
  | alinePolys _ =>
      simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer]
  | dlinePolys _ =>
      simp_all [directLdWinPredicate, directLdPointQuestionOf, validDirectLdAnswer]

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
  simp only [directAxisAnswerReadout]
  rw [AxisLinePolynomial.reparamAt_apply_zero, directAxisAnswerEquiv_apply, (hcond (directAxisRebaseParameter D line)
      (directLineRepParameter_spec
        _
        _) r)]

/-- The diagonal-line acceptance clause gives the readout its point value at
the LDT base point, using the canonical rebase parameter for a nonzero
direction and the parameter zero for the zero direction. -/
private theorem diagonal_readout_of_condition
    (line : DiagonalLine D.toLDTParameters)
    (f : Fin D.k → Fin (D.m * D.d + 1) → DirectScalarQ D)
    (c : Fin D.k → DirectScalarQ D)
    (hcond : directDlinePointCondition D
      ⟨lineRepMap (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base),
        directDiagonalIndexOf (ldtPointToDirect D line.direction),
        ldtPointToDirect D line.direction⟩
      ⟨ldtPointToDirect D line.base, D.firstIndex, 0⟩ f c) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerReadout D r line (.dlinePolys f) zeroCoord =
      directScalarEquiv D (c r) := by
  letI := D.toLDTFieldModel
  by_cases hdir : ldtPointToDirect D line.direction = 0
  · rw [hdir] at hcond
    have heval : evalCoefficient (f r) 0 = c r := by
      apply hcond
      change ldtPointToDirect D line.base =
        _ +
          _ • _
      simp [smul_zero]
      have hspec := directLineRepParameter_spec
        (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base)
      rwa [hdir, smul_zero, add_zero] at hspec
    simp [directDiagonalAnswerReadout, hdir, if_true, constantDiagonalAnswer_apply, heval]
  · simp only [directDiagonalAnswerReadout, hdir, if_false]
    rw [DiagonalLinePolynomial.reparamAt_apply_zero,
      directDiagonalAnswerEquiv_apply, (hcond (directDiagonalRebaseParameter D line)
          (directLineRepParameter_spec
            (ldtPointToDirect D line.direction) (ldtPointToDirect D line.base)) r)]

/-- On the diagonal-line branch with the line on the left, an accepted direct
answer pair has the rebased line answer, evaluated at the LDT base point,
equal to the point readout. -/
theorem directDiagonalAnswerReadout_zeroCoord_eq_of_win (line : DiagonalLine D.toLDTParameters)
    (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directDiagonalQuestionOf line)
      (directPointQuestionOf line.base) a b = true) :
    letI := D.toLDTFieldModel
    directDiagonalAnswerReadout D r line a zeroCoord =
      directPointAnswerReadout r b := by
  letI := D.toLDTFieldModel
  cases a with
  | dlinePolys f =>
      cases b with
      | pointVals c =>
          apply diagonal_readout_of_condition
          have hcondition := hwin
          exact @of_decide_eq_true _ (Classical.propDecidable _) hcondition
      | alinePolys _ =>
          simp_all [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer]
      | dlinePolys _ =>
          simp_all [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer]
  | pointVals _ =>
      simp_all [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer]
  | alinePolys _ =>
      simp_all [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer]

/-- On the diagonal-line branch with the point on the left, an accepted
direct answer pair has the point readout equal to the rebased line answer
evaluated at the LDT base point. -/
theorem directPointAnswerReadout_eq_diagonal_zeroCoord_of_win (line : DiagonalLine D.toLDTParameters)
    (a b : DirectLdAnswer D)
    (hwin : directLdWinPredicate D (directPointQuestionOf line.base)
      (directDiagonalQuestionOf line) a b = true) :
    letI := D.toLDTFieldModel
    directPointAnswerReadout r a =
      directDiagonalAnswerReadout D r line b zeroCoord := by
  letI := D.toLDTFieldModel
  cases a with
  | pointVals c =>
      cases b with
      | dlinePolys f =>
          refine (diagonal_readout_of_condition D r line f c ?_).symm
          have hcondition := hwin
          exact @of_decide_eq_true _ (Classical.propDecidable _) hcondition
      | pointVals _ =>
          simp_all [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer]
      | alinePolys _ =>
          simp_all [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer]
  | alinePolys _ =>
      simp_all [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer]
  | dlinePolys _ =>
      simp_all [directLdWinPredicate, directDiagonalQuestionOf, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer]

end

/-! ## Direct samples as products -/

/-- A direct sample as its point-index pair together with its direction.
Formalization-only reindexing of the direct sample space. -/
def directLdSpaceSplitEquiv :
    DirectLdSpace D ≃
      ((DirectPoint D) × Fin D.m) × (DirectPoint D) where
  toFun s := ((s.point, s.index), s.direction)
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv s := by cases s; rfl
  right_inv x := rfl

end

/-! ## The point-agreement and axis-line branches -/

section PointAxisBranches

variable (D : DirectLdParams) (S : Strategy (directLdGame D))
  (hS : S.IsProjective) (r : Fin D.k)

/-- The point-agreement failure of the coordinate strategy is at most the
point-point branch rejection of the direct game. -/
theorem directCoordinate_point_agreement_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat S hS r).pointAgreementFailureProbability ≤
      directLdBranchRejectionProbability S (.point, .point) := by
  letI := D.toLDTFieldModel
  refine le_trans (avgOver_mono _ _ _ fun u => (by
                                                 letI := D.toLDTFieldModel
                                                 exact qBipartiteConsDefect_le_directRejectedMass D S hS
                                                   (directPointQuestionOf u) (directPointQuestionOf u)
                                                   (directPointAnswerReadout r) (directPointAnswerReadout r)
                                                   (fun a b hab =>
                                                     directPointAnswerReadout_eq_of_win D r a b hab)))
    (le_of_eq ?_)
  let f : _ → ℝ := fun p =>
    directRejectedMass D S (directLdPointQuestionOf D p) (directLdPointQuestionOf D p)
  calc
    _ =
        avgOver (uniformDistribution (DirectPoint D)) f :=
      (avgOver_uniform_equiv (directPointEquiv D) f).symm
    _ = avgOver (uniformDistribution ((DirectPoint D) × Fin D.m))
        (fun pi => f pi.1) :=
      (avgOver_uniform_fst f).symm
    _ = _ :=
      (avgOver_uniform_equiv_fst (directLdSpaceSplitEquiv D) (fun pi => f pi.1)).symm
    _ = _ := by
      rfl

/-- Axis-line defect with the line on the left is at most the rejected direct
mass at the canonical direct questions of the reindexed sample. -/
private theorem axis_line_point_defect_le
    (s : AxisParallelTestSample D.toLDTParameters) :
    letI := D.toLDTFieldModel
    qBipartiteConsDefect (directCoordinateProjStrat S hS r).state
        ((directCoordinateProjStrat S hS r).axisParallelLineAnswerFamilyA s)
        ((directCoordinateProjStrat S hS r).axisParallelPointAnswerFamilyB s) ≤
      directRejectedMass D S
        (.aline, ⟨lineRepMap (coordinateDirection (Fin.rev s.2))
          (ldtPointToDirect D s.1), Fin.rev s.2, 0⟩)
        (directLdPointQuestionOf D (ldtPointToDirect D s.1)) := by
  letI := D.toLDTFieldModel
  have h := qBipartiteConsDefect_le_directRejectedMass D S hS
    (directAxisQuestionOf D ⟨s.1, s.2⟩) (directPointQuestionOf s.1)
    (fun a => directAxisAnswerReadout D r ⟨s.1, s.2⟩ a zeroCoord)
    (directPointAnswerReadout r)
    (fun a b hab =>
      (by
        letI := D.toLDTFieldModel
        cases a with
        | alinePolys f =>
            cases b with
            | pointVals c =>
                refine axis_readout_of_condition D r _ f c ?_
                have hcondition := hab
                simp [directAxisQuestionOf] at hcondition
                exact @of_decide_eq_true _ (Classical.propDecidable _) hcondition
            | alinePolys _ =>
                simp [directLdWinPredicate, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer] at hab
            | dlinePolys _ =>
                simp [directLdWinPredicate, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer] at hab
        | pointVals _ =>
            simp [directLdWinPredicate, directAxisQuestionOf, directLdPointQuestionOf, validDirectLdAnswer] at hab
        | dlinePolys _ =>
            simp [directLdWinPredicate, directAxisQuestionOf, directLdPointQuestionOf, validDirectLdAnswer] at hab))
  change qBipartiteConsDefect (strategyQuantumState S)
      (postprocess
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            _
            (hS.1 (directAxisQuestionOf D ⟨s.1, s.2⟩)))
          (directAxisAnswerReadout D r ⟨s.1, s.2⟩)).toSubMeas
        (fun g => g zeroCoord))
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas
          _
          (hS.2 (directPointQuestionOf s.1)))
        (directPointAnswerReadout r)).toSubMeas ≤ _
  simp at h ⊢
  exact h

/-- Axis-line defect with the point on the left is at most the rejected direct
mass at the canonical direct questions of the reindexed sample. -/
private theorem axis_point_line_defect_le
    (s : AxisParallelTestSample D.toLDTParameters) :
    letI := D.toLDTFieldModel
    qBipartiteConsDefect (directCoordinateProjStrat S hS r).state
        ((directCoordinateProjStrat S hS r).axisParallelPointAnswerFamilyA s)
        ((directCoordinateProjStrat S hS r).axisParallelLineAnswerFamilyB s) ≤
      directRejectedMass D S
        (directLdPointQuestionOf D (ldtPointToDirect D s.1))
        (.aline, ⟨lineRepMap (coordinateDirection (Fin.rev s.2))
          (ldtPointToDirect D s.1), Fin.rev s.2, 0⟩) := by
  letI := D.toLDTFieldModel
  have h := qBipartiteConsDefect_le_directRejectedMass D S hS
    (directPointQuestionOf s.1) (directAxisQuestionOf D ⟨s.1, s.2⟩)
    (directPointAnswerReadout r)
    (fun b => directAxisAnswerReadout D r ⟨s.1, s.2⟩ b zeroCoord)
    (fun a b hab =>
      (by
        letI := D.toLDTFieldModel
        cases a with
        | pointVals c =>
            cases b with
            | alinePolys f =>
                refine (axis_readout_of_condition D r _ f c ?_).symm
                have hcondition := hab
                simp [directAxisQuestionOf] at hcondition
                exact @of_decide_eq_true _ (Classical.propDecidable _) hcondition
            | pointVals _ =>
                simp [directLdWinPredicate, directAxisQuestionOf, directLdPointQuestionOf, validDirectLdAnswer] at hab
            | dlinePolys _ =>
                simp [directLdWinPredicate, directAxisQuestionOf, directLdPointQuestionOf, validDirectLdAnswer] at hab
        | alinePolys _ =>
            simp [directLdWinPredicate, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer] at hab
        | dlinePolys _ =>
            simp [directLdWinPredicate, directPointQuestionOf, directLdPointQuestionOf, validDirectLdAnswer] at hab))
  change qBipartiteConsDefect (strategyQuantumState S)
      (ProjMeas.postprocess
        (matrixMeasurementToLDTProjMeas
          _
          (hS.1 (directPointQuestionOf s.1)))
        (directPointAnswerReadout r)).toSubMeas
      (postprocess
        (ProjMeas.postprocess
          (matrixMeasurementToLDTProjMeas
            _
            (hS.2 (directAxisQuestionOf D ⟨s.1, s.2⟩)))
          (directAxisAnswerReadout D r ⟨s.1, s.2⟩)).toSubMeas
        (fun g => g zeroCoord)) ≤ _
  simp at h ⊢
  exact h

/-- Reindex a uniform average over LDT axis samples to the direct sample
space; the averaged function depends only on the decoded point and the
reversed coordinate index. -/
private theorem avgOver_axis_sample_eq
    (f : (DirectPoint D) × Fin D.m → ℝ) :
    avgOver (uniformDistribution (AxisParallelTestSample D.toLDTParameters))
        (fun s => f (ldtPointToDirect D s.1, Fin.rev s.2)) =
      avgOver (uniformDistribution (DirectLdSpace D))
        (fun sample => f (sample.point, sample.index)) := by
  calc
    _ =
        avgOver (uniformDistribution ((DirectPoint D) × Fin D.m)) f := by
      rw [avgOver_uniform_equiv ((directPointEquiv D).prodCongr Fin.revPerm) f]
      rfl
    _ = _ :=
      (avgOver_uniform_equiv_fst (directLdSpaceSplitEquiv D) f).symm
    _ = _ := by
      rfl

/-- The axis-line failure with the line on the left is at most the
axis-line/point branch rejection of the direct game. -/
theorem directCoordinate_axis_line_point_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat S hS r).axisParallelLineLeftPointRightFailureProbability ≤
      directLdBranchRejectionProbability S (.aline, .point) := by
  letI := D.toLDTFieldModel
  refine le_trans
    (avgOver_mono _ _ _ fun s => axis_line_point_defect_le D S hS r s) (le_of_eq ?_)
  exact avgOver_axis_sample_eq D (fun pi =>
    directRejectedMass D S
      (.aline, ⟨lineRepMap (coordinateDirection pi.2) pi.1, pi.2, 0⟩)
      (directLdPointQuestionOf D pi.1))

/-- The axis-line failure with the point on the left is at most the
point/axis-line branch rejection of the direct game. -/
theorem directCoordinate_axis_point_line_le :
    letI := D.toLDTFieldModel
    (directCoordinateProjStrat S hS r).axisParallelPointLeftLineRightFailureProbability ≤
      directLdBranchRejectionProbability S (.point, .aline) := by
  letI := D.toLDTFieldModel
  refine le_trans
    (avgOver_mono _ _ _ fun s => axis_point_line_defect_le D S hS r s) (le_of_eq ?_)
  exact avgOver_axis_sample_eq D (fun pi =>
    directRejectedMass D S
      (directLdPointQuestionOf D pi.1)
      (.aline, ⟨lineRepMap (coordinateDirection pi.2) pi.1, pi.2, 0⟩))

end PointAxisBranches

end

end MIPStarRE.QPBT
