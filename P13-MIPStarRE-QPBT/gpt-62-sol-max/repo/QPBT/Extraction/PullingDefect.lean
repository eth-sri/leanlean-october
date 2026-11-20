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
open MIPStarRE.Quantum DistanceCalculus ProjectiveSetting

noncomputable section

/-- Evaluating the difference measurement has the witness's original point defect. -/
theorem pullingMeas_eval_point_consistent {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (w : GlobalPairWitness S δ) {p : Placement}
    (hp : p.Primary) (W : PauliKind) :
    measurementDefect (uniformDistribution (PauliPoint P))
      (fun u => S.blockMeasurement p.side ((pullingMeas w p.side W).postprocess (fun g => evalPoly g u)))
      (fun u => S.playerMeasurement (overlapPartner p).side (S.pointMeas (overlapPartner p).side W u))
      S.psiHat ≤ δ :=
  (pullingReadout_defect_eq w hp W (fun u g => evalPoly g u) _ (pullingMeas_eval_effect w p.side W)).trans_le
    (marginalPoly_pointMeas_consistent w hp W)

/-- Tensoring the strategy state with the two normalized EPR states preserves
the point-measurement consistency defect. This is the six-register form of
the point self-consistency used at `eq:qld-pulling-3`. -/
theorem point_consistencyDefect_psiHat {P : AdmissibleParams} {epsilon : ℝ}
    (S : ProjectiveSetting P epsilon) (W : PauliKind) :
    consistencyDefect (uniformDistribution (PauliPoint P))
        (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
        (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat =
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pointMeas .alice W)
        (S.pointMeas .bob W) S.toStrategy.ψ := by
  exact S.consistencyDefect_placePlayers
    (uniformDistribution (PauliPoint P))
    (fun u => S.pointMeas .alice W u) (fun u => S.pointMeas .bob W u)

set_option maxHeartbeats 800000 in
/-- The evaluated difference-polynomial measurements are self-consistent.
Agreement and two squared-distance triangle inequalities combine the two
opposite-player comparisons with the original point self-consistency.
The error is linear in the supplied witness error, as required before
the collision step `eq:qld-pulling-12`. -/
theorem pullingMeas_eval_consistencyDefect_le {P : AdmissibleParams}
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
  let PA := fun u => S.playerMeasurement .alice (S.pointMeas .alice W u)
  let PB := fun u => S.playerMeasurement .bob (S.pointMeas .bob W u)
  have hA := (opFamilyDistSq_le_two_mul_consistencyDefect mu A PB S.psiHat).trans
    (mul_le_mul_of_nonneg_left (pullingMeas_eval_point_consistent w .alice W)
      (by norm_num : (0 : ℝ) ≤ 2))
  have hB := (opFamilyDistSq_le_two_mul_consistencyDefect mu PA B S.psiHat).trans
    (mul_le_mul_of_nonneg_left ((measurementDefect_symm mu PA B S.psiHat).trans_le (pullingMeas_eval_point_consistent w .bob W))
      (by norm_num : (0 : ℝ) ≤ 2))
  have hpoint : measurementDefect mu PA
      PB S.psiHat ≤ (Fintype.card PauliEdge : ℝ) * epsilon := by
    change consistencyDefect mu
      (fun u a => S.placePlayer .alice ((S.pointMeas .alice W u).effect a))
      (fun u a => S.placePlayer .bob ((S.pointMeas .bob W u).effect a)) S.psiHat ≤ _
    rw [point_consistencyDefect_psiHat]
    exact point_self_consistency_le S W
  have hP := (opFamilyDistSq_le_two_mul_consistencyDefect mu PA PB S.psiHat).trans
    (mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2))
  rw [measurementDistSq, opFamilyDistSq_symm] at hP
  have hAP := opFamilyDistSq_le_of_le_of_le mu _ _ _ S.psiHat _ _ hA hP
  have hAB := opFamilyDistSq_le_of_le_of_le mu _ _ _ S.psiHat _ _ hAP hB
  have hproj (side : PlayerSide) (u : PauliPoint P) :
      Measurement.IsProjective (S.blockMeasurement side
        ((pullingMeas w side W).postprocess (fun g => evalPoly g u))) :=
    S.blockMeasurement_isProjective side _
      (SandwichProduct.postprocess_isProjective _ (pullingMeas_isProjective w side W) _)
  have hdef := consistencyDefect_le_opFamilyDistSq_of_projective mu A B S.psiHat
    (hproj .alice) (hproj .bob)
  exact hdef.trans (hAB.trans (by ring_nf; rfl))

end

end MIPStarRE.QPBT
