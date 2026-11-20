module

public import QPBT.Combining.Points.MarginalContraction
public import QPBT.Combining.OrderedPoints

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

/-- Order the outcome pair so that the marginal under consideration is first. -/
private theorem postprocess_component_effect {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι] (M : Measurement (α × α) ι) (W : PauliKind) (a : α) :
    (M.postprocess W.component).effect a = ∑ b, M.effect (W.pairOrder (a,b)) := by
  rw [Measurement.postprocess_effect, Finset.sum_filter,
    ← (W.pairOrder).sum_comp, Fintype.sum_prod_type]
  simp [PauliKind.component_pairOrder, Finset.sum_ite]

set_option maxHeartbeats 800000 in
-- The elaborator compares the placed and unplaced measurement families.
/-- The indicated marginal of the joint point witness is close to the
opposite point measurement (`eq:qld-qxz-close-to-point` and its Z analogue). -/
theorem CombinedPointsWitness.marginal_distance_le
    {P : AdmissibleParams} {ε δQ : ℝ} {S : ProjectiveSetting P ε}
    (points : CombinedPointsWitness S δQ)
    (p q : Placement) (hop : p.IsOpposite q) (W : PauliKind) :
    opFamilyDistSq
      (uniformDistribution (PointPair P))
      (fun xz a => S.place p (((points.Q p.side xz.1 xz.2).postprocess W.component).effect a))
      (fun xz a => S.place q ((S.pointMeasExp q.side W (W.component xz)).effect a))
      S.psiHat ≤ 4 * δQ := by
  classical
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (points.consistent_ordered p q hop W.other)
    (by norm_num : (0 : ℝ) ≤ 4))
  unfold opFamilyDistSq
  rw [← avgOver_const_mul]
  refine avgOver_mono _ _ _ fun xz => ?_
  rw [← (W.pairOrder).sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  simp only [postprocess_component_effect, ProjectiveSetting.place_finset_sum,
    ProjectiveSetting.placedOrderedPointProduct, ProjectiveSetting.orderedPointProduct,
    ProjectiveSetting.pointPairEffect, PauliKind.other_other, PauliKind.component_pairOrder,
    PauliKind.other_component_pairOrder]
  let Q := S.placedMeasurement p (points.Q p.side xz.1 xz.2)
  let B := S.placedMeasurement q (S.pointMeasExp q.side W.other (W.other.component xz))
  have hQ := S.placedMeasurement_isProjective p _ (points.projective p.side xz.1 xz.2)
  have hB := S.placedMeasurement_isProjective q _
    (S.pointMeasExp_isProjective q.side W.other (W.other.component xz))
  simpa only [Q, B, ProjectiveSetting.placedMeasurement_effect, ProjectiveSetting.place_mul] using
    norm_marginal_sub_sq_le
      (fun b => Q.effect (W.pairOrder (a,b)))
      (fun b => hQ (W.pairOrder (a,b)))
      (fun hne => DistanceCalculus.projective_effect_mul_effect_eq_zero Q hQ
        (fun e => hne (congrArg Prod.snd ((W.pairOrder).injective e))))
      B hB (fun b => S.place_comm p q hop _ _)
      (S.place q ((S.pointMeasExp q.side W (W.component xz)).effect a)) S.psiHat

end

end MIPStarRE.QPBT
