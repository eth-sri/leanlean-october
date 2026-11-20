module

public import QPBT.Extraction.BlockMeasurement
public import QPBT.Extraction.PullingPointConsistency

/-!
# Evaluated consistency of the difference-polynomial measurements

The exact overlap identities identify the consistency with the opposite
player's point measurement with the consistency supplied by the global witness.

## References

- Blueprint `lem:qld-construct-the-paulis`, Item 2.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1495-1545`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#123 tracks the extraction obligations of this chapter; the
  global
  witness is supplied here, not constructed. This module was originally
  filed under issue Dengnifer/MIPStarRE-QPBT-bak#520, now closed.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder Classical

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus

noncomputable section

variable {P : AdmissibleParams}

section

variable {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon} (w : GlobalPairWitness S deltaG)
  (W : PauliKind)

/-- The Alice evaluation defect is bounded by the supplied global consistency
error, with no decoder correction or non-encoding mass term. -/
theorem pullingMeas_eval_point_consistent_alice :
    consistencyDefect (uniformDistribution (PauliPoint P))
      (fun u a => S.placeSide .alice
        (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤
        deltaG := by
  let mu := uniformDistribution (PauliPoint P)
  let readout u := (pullingMeas w .alice W).postprocess (fun g => evalPoly g u)
  let pulled := fun u => S.blockMeasurement .alice
    (readout u)
  let point := fun u => S.placedMeasurement .BB' (leftPlacedMeasurement (S.pointMeas .bob W u))
  let marginal := fun u => S.placedMeasurement .AA'
    ((w.marginalPoly .alice W).postprocess (fun g => evalPoly g u))
  let expanded := fun u => S.placedMeasurement .BA'' (S.pointMeasExp .bob W u)
  have heq : consistencyDefect mu (fun u => (pulled u).effect)
      (fun u => (point u).effect) S.psiHat =
      consistencyDefect mu (fun u => (marginal u).effect)
        (fun u => (expanded u).effect) S.psiHat := by
    rw [(consistencyDefect_eq_one_sub_overlap pulled point
      (uniformDistribution_isProbability _) S.psiHat_norm), (consistencyDefect_eq_one_sub_overlap marginal expanded
      (uniformDistribution_isProbability _) S.psiHat_norm)]
    apply congrArg
    apply avgOver_congr
    intro u
    change (∑ a, stateQForm S.psiHat (S.placeSide .alice
      ((readout u).effect a) *
      S.placePlayer .bob ((S.pointMeas .bob W u).effect a))) = _
    rw [← stateQForm_finset_sum, sum_pullingMeas_eval_mul_pointMeas, ← stateQForm_finset_sum]
    exact congrArg (stateQForm S.psiHat)
      (sum_marginalPoly_eval_mul w .AA' W u
        (fun a => S.place .BA'' ((S.pointMeasExp .bob W u).effect a))).symm
  have hbound := marginalPoly_pointMeas_consistent_alice w W
  exact heq.le.trans hbound

/-- Bob's evaluation defect has the same bound, using the Bob point-consistency
estimate of the supplied witness and its `BB'`--`AB''` placements. -/
theorem pullingMeas_eval_point_consistent_bob :
    consistencyDefect (uniformDistribution (PauliPoint P))
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placeSide .bob
        (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a)) S.psiHat ≤
        deltaG := by
  let mu := uniformDistribution (PauliPoint P)
  let readout u := (pullingMeas w .bob W).postprocess (fun g => evalPoly g u)
  let pulled := fun u => S.blockMeasurement .bob
    (readout u)
  let point := fun u => S.placedMeasurement .AA' (leftPlacedMeasurement (S.pointMeas .alice W u))
  let marginal := fun u => S.placedMeasurement .BB'
    ((w.marginalPoly .bob W).postprocess (fun g => evalPoly g u))
  let expanded := fun u => S.placedMeasurement .AB'' (S.pointMeasExp .alice W u)
  have heq : consistencyDefect mu (fun u => (point u).effect)
      (fun u => (pulled u).effect) S.psiHat =
      consistencyDefect mu (fun u => (marginal u).effect)
        (fun u => (expanded u).effect) S.psiHat := by
    rw [(consistencyDefect_eq_one_sub_overlap point pulled
      (uniformDistribution_isProbability _) S.psiHat_norm), (consistencyDefect_eq_one_sub_overlap marginal expanded
      (uniformDistribution_isProbability _) S.psiHat_norm)]
    apply congrArg
    apply avgOver_congr
    intro u
    change (∑ a, stateQForm S.psiHat
      (S.placePlayer .alice ((S.pointMeas .alice W u).effect a) * S.placeSide .bob
        ((readout u).effect a))) = _
    rw [← stateQForm_finset_sum, sum_pointMeas_mul_pullingMeas_eval, ← stateQForm_finset_sum]
    exact congrArg (stateQForm S.psiHat)
      (sum_marginalPoly_eval_mul w .BB' W u
        (fun a => S.place .AB'' ((S.pointMeasExp .alice W u).effect a))).symm
  have hbound := marginalPoly_pointMeas_consistent_bob w W
  exact heq.le.trans hbound

end

/-- The evaluated difference-polynomial measurements are self-consistent.
Agreement and two squared-distance triangle inequalities combine the two
opposite-player comparisons with the original point self-consistency.
The error is linear in the supplied witness error, as required before
the collision step `eq:qld-pulling-12`. -/
theorem pullingMeas_eval_consistencyDefect_le
    {epsilon deltaG : ℝ} {S : ProjectiveSetting P epsilon}
    (w : GlobalPairWitness S deltaG) (W : PauliKind) :
    consistencyDefect (uniformDistribution (PauliPoint P))
        (fun u a => S.placeSide .alice
          (((pullingMeas w .alice W).postprocess (fun g => evalPoly g u)).effect a))
        (fun u a => S.placeSide .bob
          (((pullingMeas w .bob W).postprocess (fun g => evalPoly g u)).effect a))
        S.psiHat ≤ 12 * deltaG + 8 * (Fintype.card PauliEdge : ℝ) * epsilon := by
  let mu := uniformDistribution (PauliPoint P)
  let A := fun u => S.blockMeasurement .alice
    ((pullingMeas w .alice W).postprocess (fun g => evalPoly g u))
  let B := fun u => S.blockMeasurement .bob
    ((pullingMeas w .bob W).postprocess (fun g => evalPoly g u))
  let PA := fun u => S.placedMeasurement .AA'
    (leftPlacedMeasurement (S.pointMeas .alice W u))
  let PB := fun u => S.placedMeasurement .BB'
    (leftPlacedMeasurement (S.pointMeas .bob W u))
  have hpoint : consistencyDefect mu (fun u => (PA u).effect)
      (fun u => (PB u).effect) S.psiHat ≤ (Fintype.card PauliEdge) * epsilon := by
    change consistencyDefect mu
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤ _
    rw [S.consistencyDefect_placePlayers
        (uniformDistribution (Fin P.m → PauliScalar _))
        (fun u => S.pointMeas .alice _ u) (fun u => S.pointMeas .bob _ u)]
    apply point_self_consistency_le
  have hP := (opFamilyDistSq_le_two_mul_consistencyDefect mu PA PB S.psiHat).trans
    (mul_le_mul_of_nonneg_left hpoint (by norm_num))
  rw [opFamilyDistSq_symm] at hP
  have hAP := opFamilyDistSq_le_of_le_of_le (μ := mu) _ _ _ S.psiHat _ _ ((opFamilyDistSq_le_two_mul_consistencyDefect mu A PB S.psiHat).trans
    (mul_le_mul_of_nonneg_left (pullingMeas_eval_point_consistent_alice w W)
    (by norm_num : (0 : ℝ) ≤ 2))) hP
  have hAB := opFamilyDistSq_le_of_le_of_le (μ := mu) _ _ _ S.psiHat _ _ hAP ((opFamilyDistSq_le_two_mul_consistencyDefect mu PA B S.psiHat).trans
    (mul_le_mul_of_nonneg_left (pullingMeas_eval_point_consistent_bob w W)
    (by norm_num : (0 : ℝ) ≤ 2)))
  have hproj (side : PlayerSide) (u : PauliPoint P) :
      Measurement.IsProjective (S.blockMeasurement side
        ((pullingMeas w side W).postprocess (fun g => evalPoly g u))) :=
    S.blockMeasurement_isProjective side _
      (SandwichProduct.postprocess_isProjective _ ((by
                                                     apply SandwichProduct.postprocess_isProjective
                                                     intro outcome
                                                     exact MakingMeasurementsProjective.isProj_kronecker
                                                       (w.marginalPoly_isProjective side W outcome.1)
                                                       ⟨by simp [IsIdempotentElem, pauliRegisterMeas, Measurement.ofSumEqOne,
                                                           pauliProj_mul_pauliProj],
                                                         (posSemidef_pauliProj W outcome.2).isHermitian⟩)) _)
  exact (consistencyDefect_le_opFamilyDistSq_of_projective mu A B S.psiHat
    (hproj .alice) (hproj .bob)).trans (hAB.trans (by ring_nf; rfl))

end

end MIPStarRE.QPBT
