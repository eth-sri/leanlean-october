module

public import QPBT.Combining.Points.MarginalContraction

/-!
# Marginal distances for combined point witnesses

This module applies the generic marginal contraction estimate to the combined
point measurements of `lem:qld-4-10`. The X marginal uses the ordered
Z-then-X consistency relation, while the Z marginal uses the ordered
X-then-Z relation; no commutation of point effects on one player is assumed.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:914-930`:
the two marginal displays inside the proof of `lem:qld-xz-lines`, namely
`eq:qld-qxz-close-to-point` at lines 914--917 with its supporting calculation
at lines 918--927, and the symmetric `eq:qld-qxz-close-to-point-2` at lines
928--930.  The line-measurement-to-point consistency bounds at lines 931--935
are a separate later step of that proof and are not formalized here.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

set_option maxHeartbeats 800000 in
theorem CombinedPointsWitness.marginal_X_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz a => ∑ b, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz a => S.place p2 ((S.pointMeasExp p2.side .X xz.1).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_ZX p1 p2 hopp) (by norm_num))
  unfold opFamilyDistSq; rw [← avgOver_const_mul]
  refine avgOver_mono _ _ _ fun xz => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le _
      (fun b => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
      (fun hbc => DistanceCalculus.projective_effect_mul_effect_eq_zero
        (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
        (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
        (fun h => hbc (congrArg Prod.snd h)))
      (S.placedMeasurement p2 (S.pointMeasExp p2.side .Z xz.2))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      (fun b => S.place_comm p1 p2 hopp _ _) _ S.psiHat

set_option maxHeartbeats 800000 in
theorem CombinedPointsWitness.marginal_Z_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p1 p2 : Placement) (hopp : p1.IsOpposite p2) :
    opFamilyDistSq
      (uniformDistribution
        ((Fin P.m → PauliScalar P) × (Fin P.m → PauliScalar P)))
      (fun xz b => ∑ a, S.place p1 ((points.Q p1.side xz.1 xz.2).effect (a, b)))
      (fun xz b => S.place p2 ((S.pointMeasExp p2.side .Z xz.2).effect b))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_XZ p1 p2 hopp) (by norm_num))
  unfold opFamilyDistSq; rw [← avgOver_const_mul]
  refine avgOver_mono _ _ _ fun xz => ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  simpa only [ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le _
      (fun a => S.placedMeasurement_isProjective p1 _ (points.projective _ _ _) (a, b))
      (fun hac => DistanceCalculus.projective_effect_mul_effect_eq_zero
        (S.placedMeasurement p1 (points.Q p1.side xz.1 xz.2))
        (S.placedMeasurement_isProjective p1 _ (points.projective _ _ _))
        (fun h => hac (congrArg Prod.fst h)))
      (S.placedMeasurement p2 (S.pointMeasExp p2.side .X xz.1))
      (S.placedMeasurement_isProjective p2 _ (S.pointMeasExp_isProjective _ _ _))
      (fun a => S.place_comm p1 p2 hopp _ _) _ S.psiHat

end

end MIPStarRE.QPBT
