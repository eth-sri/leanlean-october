module

public import QPBT.Combining.Points.WitnessMarginals
public import QPBT.Combining.PointsDataProcessing

/-!
# Combining the point measurements

This module constructs the projective joint X/Z point measurements and defines
their scalar linear coarse-graining. The latter is
the genuine postprocessing of a complete measurement on each heterogeneous
player space.

## References

The construction is `lem:qld-4-10` in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:689-709`.
The coarse-graining is `lem:qld-4-12` in the same blueprint, with paper source
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:993-1011`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Construction of the projective joint point measurements of
`lem:qld-4-10`, paper lines 689--709.  The witness retains both ordered
products and all four directed heterogeneous placement comparisons.

The construction works on the original expanded local spaces: the sandwich
POVM `M^Z_b M^X_a M^Z_b`, formed directly with outcomes in `F_q × F_q`, is
close to the ordered product by the field-valued commutation estimate
(`expPoint_comm`), self-consistent between opposite placements
(`sandwich_offDiagonal_le_sandwichDefectBound`), and is made projective for
each point pair by the orthonormalization lemma
(`exists_projective_close_sandwich`); the three consistency conclusions follow
by the triangle inequality (`chain_bounds`).  This replacement for the source's
binary-refinement and quantum-linearity argument is explained in
`docs/paper-gaps/qpbt_combined-points-field-valued.tex`.  It uses no additional
ancillary space and does not require the common-extension construction of
`rem:linearity-import`.  The error is
`K ε^{1/8}` for a universal constant `K`. -/
theorem exists_combined_points_witness_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), ε ≤ 1 →
      Nonempty (CombinedPointsWitness S
        (pauliBaselinePointConstant * Real.rpow ε (1 / 8 : ℝ))) := by
  intro P ε S hε1
  let T := pauliBaselineTwistedConstant
  let C := 344 + 3 * T
  let η := 440 * Real.rpow (C * (ε + Real.sqrt ε)) (1 / 4 : ℝ)
  have hT : 0 ≤ T := by unfold T pauliBaselineTwistedConstant pauliBaselineCommutatorConstant; positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hε := S.eps_nonneg
  let μ := uniformDistribution (PointPair P)
  obtain ⟨Qa, hQa, hQaR⟩ := S.exists_projective_close_sandwich .AA'
  obtain ⟨Qb, hQb, hQbR⟩ := S.exists_projective_close_sandwich .BA''
  let Q (side : PlayerSide) : PointPair P →
      Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side) :=
    match side with | .alice => Qa | .bob => Qb
  have hp (side : PlayerSide) (xz : PointPair P) : Measurement.IsProjective (Q side xz) := by
    cases side
    · exact hQa _
    · exact hQb _
  have hbound (p q : Placement) (hop : p.IsOpposite q) :
      220 * Real.rpow (avgOver μ (S.sandwichDefectBound p q)) (1 / 4 : ℝ) ≤ η := by
    have hn := avgOver_nonneg μ _ (S.sandwichDefectBound_nonneg p q)
    have h := ProjectiveSetting.avg_sandwich_defect_bound_le_explicit P ε S p q hop
    exact mul_le_mul (by norm_num : (220 : ℝ) ≤ 440)
      (Real.rpow_le_rpow hn h (by norm_num)) (Real.rpow_nonneg hn _) (by norm_num)
  have hQR (p : Placement) : opFamilyDistSq μ (S.placedPointPairFamily (fun side x z => Q side (x,z)) p)
      (fun xz ab => S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab)) S.psiHat ≤ η := by
    have hA := hQaR.trans (hbound .AA' .BA'' trivial)
    have hB := hQbR.trans (hbound .BA'' .AA' trivial)
    have hmove (side) := S.opFamilyDistSq_placeOnEpr μ side
      (fun xz ab => (Q side xz).effect ab)
      (fun xz ab => (S.sandwichPoint side xz.1 xz.2).effect ab)
    cases p
    · exact hA
    · exact hB
    · exact (hmove .bob).trans_le hB
    · exact (hmove .alice).trans_le hA
  have hc := S.chain_bounds (fun side x z => Q side (x, z)) η
    (T * Real.sqrt ε) (T * Real.sqrt ε) (688 * ε) hQR
    (ProjectiveSetting.sandwich_point_ordered_dist_le_explicit P ε S)
    (ProjectiveSetting.exp_point_comm_explicit P ε S)
    (ProjectiveSetting.ordered_cross_dist_le_explicit P ε S)
  obtain ⟨he, hs, hη⟩ := error_terms_le_rpow_eighth hε hε1 hC
  have hnη : 0 ≤ η := by dsimp [η]; positivity
  have hnT : 0 ≤ T * Real.sqrt ε := by positivity
  have hsum : 12 * η + 24 * (T * Real.sqrt ε) + 11008 * ε ≤
      pauliBaselinePointConstant * Real.rpow ε (1 / 8 : ℝ) := by
    change _ ≤ (10560 * C + 24 * T + 11008) * Real.rpow ε (1 / 8 : ℝ)
    dsimp only [η]
    nlinarith only [hη, mul_le_mul_of_nonneg_left hs hT, he]
  exact ⟨⟨fun side x z => Q side (x, z), fun side x z => hp side (x, z),
    fun p q h => (hc p q h).2.trans (by linarith),
    fun p q h W => (hc p q h).1 W |>.trans (by linarith)⟩⟩

/-- The fixed polynomial error `pauliBaselinePointConstant * ε^(1/8)` produces a
combined-point witness for every projective Pauli-test setting. -/
theorem exists_combinedPointsWitness :
    ∃ deltaQ : ℝ -> ℝ, IsPolyErr deltaQ ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε), ε ≤ 1 →
        Nonempty (CombinedPointsWitness S (deltaQ ε)) := by
  have hQ : (1 : ℝ) ≤ pauliBaselinePointConstant := by
    simp only [pauliBaselinePointConstant, pauliBaselineTwistedConstant,
      pauliBaselineCommutatorConstant]
    nlinarith [Real.sqrt_nonneg (344 : ℝ)]
  refine ⟨fun ε => pauliBaselinePointConstant * Real.rpow ε (1 / 8 : ℝ),
    ⟨pauliBaselinePointConstant, 1 / 8, hQ, by norm_num, fun ε hε =>
      ⟨mul_nonneg (by linarith) (Real.rpow_nonneg hε _), le_rfl⟩⟩,
    exists_combined_points_witness_explicit⟩

/-- Scalar affine coarse-graining of an operator family on pairs of point values. -/
noncomputable def pointAffinePostprocess {P : AdmissibleParams} {ι : Type*}
    (B : PointPair P → PauliScalar P × PauliScalar P → Op ι)
    (x : ExtendedPointQuestion P) (c : PauliScalar P) : Op ι :=
  ∑ ab ∈ Finset.univ.filter (fun ab => x.read ab = c), B x.1 ab

/-- The affine fibers of the ordered product, with first basis `W`. -/
noncomputable def ProjectiveSetting.extendedPointProduct {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (side : PlayerSide) (W : PauliKind) :
    ExtendedPointQuestion P → PauliScalar P → Op (S.ExpandedLocalSpace side) :=
  pointAffinePostprocess (S.orderedPointProduct side W)

namespace CombinedPointsWitness

variable {P : AdmissibleParams} {ε δ : ℝ} {S : ProjectiveSetting P ε}

section

variable (points : CombinedPointsWitness S δ) (p q : Placement)
include points p q

set_option maxHeartbeats 800000 in
-- The coarse-graining compares finite sums on dependent placement spaces.
private theorem extendedQ_dist_le
    (B : PointPair P → PauliScalar P × PauliScalar P → Op (S.ExpandedLocalSpace q.side))
    (hB : ∀ xz, ∑ ab, B xz ab = 1)
    (hd : opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz ab => S.place p ((points.Q p.side xz.1 xz.2).effect ab))
      (fun xz ab => S.place q (B xz ab)) S.psiHat ≤ δ) :
    opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun x c => S.place p ((points.extendedQ p.side x).effect c))
      (fun x c => S.place q (pointAffinePostprocess B x c)) S.psiHat ≤ δ := by
  have h := opFamilyDistSq_uniform_affine_postprocess_le
    (X := PointPair P) (K := PauliScalar P)
    (fun xz ab => S.place p ((points.Q p.side xz.1 xz.2).effect ab))
    (fun xz ab => S.place q (B xz ab)) S.psiHat
    (fun xz => by rw [← S.place_finset_sum, ← S.place_finset_sum,
      (points.Q p.side xz.1 xz.2).sum_eq_one, hB, S.place_one, S.place_one])
  refine le_trans ?_ hd
  simpa only [CombinedPointsWitness.extendedQ, Measurement.postprocess_effect,
    pointAffinePostprocess, ExtendedPointQuestion.read, ProjectiveSetting.place_finset_sum] using! h

/-- Opposite joint point measurements remain close after affine coarse-graining. -/
theorem extendedQ_self_consistency_le (hop : p.IsOpposite q) :
    opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun x c => S.place p ((points.extendedQ p.side x).effect c))
      (fun x c => S.place q ((points.extendedQ q.side x).effect c))
      S.psiHat ≤ δ :=
  points.extendedQ_dist_le p q (fun xz => (points.Q q.side xz.1 xz.2).effect)
    (fun xz => (points.Q q.side xz.1 xz.2).sum_eq_one) (points.self_consistent p q hop)

set_option maxHeartbeats 800000 in
-- Elaborate the dependent operator family of the chosen placement.
/-- Affine coarse-graining preserves the comparison with either ordered product. -/
theorem extendedQ_ordered_consistency_le (hop : p.IsOpposite q) (W : PauliKind) :
    opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
      (fun x c => S.place p ((points.extendedQ p.side x).effect c))
      (fun x c => S.place q (S.extendedPointProduct q.side W x c)) S.psiHat ≤ δ := by
  refine points.extendedQ_dist_le p q (S.orderedPointProduct q.side W)
    (fun xz => ?_) (points.consistent_ordered p q hop W)
  rw [← (W.pairOrder (α := PauliScalar P)).sum_comp, Fintype.sum_prod_type]
  simp only [Function.comp_apply, ProjectiveSetting.orderedPointProduct,
    ProjectiveSetting.pointPairEffect, PauliKind.component_pairOrder, PauliKind.other_component_pairOrder,
    ← Finset.mul_sum, Measurement.sum_eq_one, mul_one]

end

end CombinedPointsWitness

end

end MIPStarRE.QPBT
