module

public import QPBT.Combining.ExtendedLineGame.LinePointRejection
public import QPBT.Combining.Points.Placement
public import QPBT.Combining.Lines.PairStateConsistencyTransport

/-!
# Point/point rejection for the extended direct game

This module bounds the point-agreement branch of the directly indexed
low-degree strategy by the self-consistency error of the supplied joint point
measurements.  The common extended point is transported by one coordinate
equivalence to the jointly uniform tuple `(x, z, alpha, beta)` before the
scalar coarse-graining is applied.

This is a formalization-only auxiliary for the supplied-witness route in the
proof of `lem:qld-4-7`; it does not construct the point witness or establish
the complete passing-value estimate.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-311`
- Issue Dengnifer/MIPStarRE-QPBT-bak#313.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open ProjectiveSetting

noncomputable section

namespace ExtendedLineGame

variable {P : AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : ProjectiveSetting P epsilon}
variable {points : CombinedPointsWitness setting deltaQ}

@[simp] private theorem piCongrLeft_const_apply
    {I J K : Type*} (e : I ≃ J) (f : I → K) (j : J) :
    (e.piCongrLeft fun _ => K) f j = f (e.symm j) := by
  simp only [Equiv.piCongrLeft_apply, eq_rec_constant]

/-- Split a direct extended point into its two Pauli points and two scalar
coordinates.  This is a single bijection, so uniformity is joint rather than
an inference from four separate marginals. -/
noncomputable def directPointExtendedQuestionEquiv (P : AdmissibleParams) :
    (DirectPoint P.extendedDirectLd) ≃
      ExtendedPointQuestion P :=
  (Equiv.piCongrRight fun _ => (extendedDirectScalarEquiv P).toEquiv).trans <|
    ((finCombineEquiv P.m).piCongrLeft fun _ => PauliScalar P).trans <|
      (Equiv.sumPiEquivProdPi fun _ : (Fin P.m ⊕ Fin P.m) ⊕ Fin 2 =>
        PauliScalar P).trans <|
        (Equiv.sumPiEquivProdPi fun _ : Fin P.m ⊕ Fin P.m =>
          PauliScalar P).prodCongr
            (piFinTwoEquiv fun _ => PauliScalar P)

/-- The joint coordinate equivalence reads exactly as `projX`, `projZ`,
`alphaVar`, and `betaVar`. -/
theorem directPointExtendedQuestionEquiv_apply
    (P : AdmissibleParams)
    (u : DirectPoint P.extendedDirectLd) :
    directPointExtendedQuestionEquiv P u =
      ExtendedPointQuestion.ofDirect P u := by
  unfold directPointExtendedQuestionEquiv ExtendedPointQuestion.ofDirect
  refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun i => ?_)) (Prod.ext ?_ ?_) <;>
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.sumPiEquivProdPi,
      Prod.map, Equiv.coe_fn_mk, piFinTwoEquiv, piCongrLeft_const_apply] <;> rfl

private theorem point_point_win_iff_read_eq
    (sample : DirectLdSpace P.extendedDirectLd)
    (valuesA valuesB : Fin P.extendedDirectLd.k →
      DirectScalarQ P.extendedDirectLd) :
    directLdWinPredicate P.extendedDirectLd
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.pointVals valuesA) (.pointVals valuesB) = true ↔
      pointGameRead (.pointVals valuesA) = pointGameRead (.pointVals valuesB) := by
  simp only [directLdWinPredicate, validDirectLdAnswer,
    Bool.and_self, if_true, decide_eq_true_eq, pointGameRead, Option.some.injEq]
  rw [(extendedDirectScalarEquiv P).injective.eq_iff]
  letI : Subsingleton (Fin P.extendedDirectLd.k) := inferInstanceAs (Subsingleton (Fin 1))
  exact ⟨fun h => congrFun h _, fun h => funext fun i => (Subsingleton.elim i onlyCoordinate) ▸ h⟩

section

variable (lines : ExtendedLinesWitness setting points deltaL)
include lines

private theorem point_rejectedMass_eq_read_mismatch
    (sample : DirectLdSpace P.extendedDirectLd) :
    directRejectedMass P.extendedDirectLd (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.point, directLdMap P.extendedDirectLd .point sample) =
      outcomeEventWeight (strategy lines)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (.point, directLdMap P.extendedDirectLd .point sample)
        (fun answerA answerB => pointGameRead answerA ≠ pointGameRead answerB) := by
  apply rejectedMass_eq_of_valid_reads
  intro a b ha hb
  cases a <;> cases b <;> simp [validDirectLdAnswer] at ha hb
  exact point_point_win_iff_read_eq sample _ _

/-- On the point branch, rejection is disagreement of the two scalar reads. -/
theorem point_read_defect_on_direct_samples_eq_rejection :
    readoutDefect lines .point .point (fun _ => pointGameRead) (fun _ => pointGameRead) =
      branchRejection lines .point .point :=
  readoutDefect_eq_branchRejection lines _ _ _ _ (point_rejectedMass_eq_read_mismatch lines)

/-- The unused index and direction in each sample do not affect the point defect. -/
private theorem point_branch_rejection_eq_consistencyDefect :
    branchRejection lines .point .point =
      bipartiteDefect (uniformDistribution (DirectPoint P.extendedDirectLd))
        (completedPointReadout points .alice) (completedPointReadout points .bob)
        (pairState setting) := by
  have hread (side : PlayerSide) : sampleReadout lines side .point (fun _ => pointGameRead) =
      fun s => completedPointReadout points side s.point := by
    funext s
    apply Quantum.Measurement.ext
    exact point_read_effect lines side s
  rw [← point_read_defect_on_direct_samples_eq_rejection lines, readoutDefect, hread, hread]
  unfold bipartiteDefect consistencyDefect
  rw [← uniformDistribution_map_fst_of_equiv (directLdSpacePointEquiv P.extendedDirectLd)
    DirectLdSpace.point (fun _ => rfl), Distribution.avgOver_map]

set_option maxHeartbeats 800000 in
-- Reindexing the extended points entails several nested finite instances.
/-- The point/point rejection probability of the supplied extended strategy is
bounded by the self-consistency error of its joint point measurements. -/
theorem point_point_rejection_le :
    directLdBranchRejectionProbability P.extendedDirectLd (strategy lines)
        (.point, .point) ≤ deltaQ := by
  change branchRejection lines .point .point ≤ deltaQ
  rw [point_branch_rejection_eq_consistencyDefect lines]
  let X := PointPair P
  let A (q : X) := points.Q .alice q.1 q.2
  let B (q : X) := points.Q .bob q.1 q.2
  let f (q : ExtendedPointQuestion P) := some ∘ q.read
  refine le_of_eq_of_le ?_ ((consistencyDefect_postprocess_question_le
    (uniformDistribution (ExtendedPointQuestion P)) (fun q => A q.1) (fun q => B q.1)
    (pairState setting) f).trans ?_)
  · simp only [bipartiteDefect, ← consistencyDefect_uniform_question_equiv (directPointExtendedQuestionEquiv P)]
    apply consistencyDefect_congr <;> intro u answer <;>
      rw [directPointExtendedQuestionEquiv_apply, completedPointReadout,
        CombinedPointsWitness.extendedQ, Measurement.postprocess_comp] <;> rfl
  have hsmall : bipartiteDefect (uniformDistribution X) A B (pairState setting) ≤ deltaQ := by
    rw [setting.consistencyDefect_pairState_eq_AA'_BA'']
    exact (consistencyDefect_le_opFamilyDistSq_of_projective (uniformDistribution X)
      (setting.placedMeasurement .AA' ∘ A) (setting.placedMeasurement .BA'' ∘ B)
      setting.psiHat
      (fun q => setting.placedMeasurement_isProjective .AA' _ (points.projective .alice q.1 q.2))
      (fun q => setting.placedMeasurement_isProjective .BA'' _ (points.projective .bob q.1 q.2))).trans
      (points.self_consistent .AA' .BA'' trivial)
  rw [← uniformDistribution_map_fst (α := X) (β := PauliScalar P × PauliScalar P)] at hsmall
  simpa only [bipartiteDefect, consistencyDefect, Distribution.avgOver_map] using! hsmall

end

end ExtendedLineGame

end

end MIPStarRE.QPBT
