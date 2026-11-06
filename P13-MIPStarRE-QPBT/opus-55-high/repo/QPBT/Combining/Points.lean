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

/-- A pair of source points and the two scalar coefficients used by the
extended point measurement. -/
abbrev ExtendedPointQuestion (P : AdmissibleParams) :=
  ((Fin P.m -> PauliScalar P) × (Fin P.m -> PauliScalar P)) ×
    (PauliScalar P × PauliScalar P)

namespace CombinedPointsWitness

/-- Coarse-grain a joint point measurement by `(a,b) |-> alpha*a + beta*b`
on the selected player side.  This is the concrete measurement of
`lem:qld-4-12`, paper lines 993--1011. -/
noncomputable def extendedQ {P : AdmissibleParams} {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δ)
    (side : PlayerSide) (x z : Fin P.m -> PauliScalar P)
    (alpha beta : PauliScalar P) :
    Measurement (PauliScalar P) (S.ExpandedLocalSpace side) :=
  (points.Q side x z).postprocess fun ab => alpha * ab.1 + beta * ab.2

end CombinedPointsWitness

/-- The fixed polynomial error `pauliBaselinePointConstant * ε^(1/8)` produces a
combined-point witness for every projective Pauli-test setting (`lem:qld-4-12`);
see `docs/paper-gaps/qpbt_combined-points-field-valued.tex`. -/
theorem exists_combinedPointsWitness :
    ∃ deltaQ : ℝ -> ℝ, IsPolyErr deltaQ ∧
      ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε),
        Nonempty (CombinedPointsWitness S (deltaQ ε)) := by
  have hT : (1 : ℝ) ≤ pauliBaselineTwistedConstant := by
    simp only [pauliBaselineTwistedConstant, pauliBaselineCommutatorConstant]
    linarith [Real.sqrt_nonneg (344 : ℝ)]
  have hK : (4 : ℝ) ≤ pauliBaselinePointConstant := by
    simp only [pauliBaselinePointConstant]; linarith
  refine ⟨fun ε => pauliBaselinePointConstant * Real.rpow ε (1 / 8 : ℝ),
    ⟨pauliBaselinePointConstant, 1 / 8, by linarith, by norm_num, fun ε hε =>
      ⟨mul_nonneg (by linarith) (Real.rpow_nonneg hε _), le_rfl⟩⟩, fun P ε S => ?_⟩
  have hε : (0 : ℝ) ≤ ε := by linarith [S.toStrategy.value_le_one, S.win]
  obtain ⟨Qa, hQa, -, hQaR⟩ := S.exists_projective_close_sandwich .AA' .BA'' trivial
    (ProjectiveSetting.aaBaBipartition P _ _) S.reindexOp_aaBaBipartition_left S.reindexOp_aaBaBipartition_right
  obtain ⟨Qb, hQb, -, hQbR⟩ := S.exists_projective_close_sandwich .BA'' .AA' trivial
    (baAaBipartition P _ _) S.reindexOp_baAaBipartition_left S.reindexOp_baAaBipartition_right
  let Q : (side : PlayerSide) → PointPair P →
      Measurement (PauliScalar P × PauliScalar P) (S.ExpandedLocalSpace side)
    | .alice => Qa
    | .bob => Qb
  have hbound : ∀ p₁ p₂ : Placement, p₁.IsOpposite p₂ →
      220 * Real.rpow (avgOver (uniformDistribution (PointPair P))
        (S.sandwichDefectBound p₁ p₂)) (1 / 4 : ℝ) ≤
      440 * Real.rpow ((344 + 3 * pauliBaselineTwistedConstant) * (ε + Real.sqrt ε)) (1 / 4 : ℝ) :=
    fun p₁ p₂ hopp => by
      simp
      linarith [Real.rpow_le_rpow (avgOver_nonneg _ _ (S.sandwichDefectBound_nonneg p₁ p₂))
        (ProjectiveSetting.avg_sandwich_defect_bound_le_explicit P ε S p₁ p₂ hopp)
        (by norm_num : (0 : ℝ) ≤ 1 / 4), Real.rpow_nonneg (mul_nonneg (by linarith)
          (by positivity) : 0 ≤ (344 + 3 * pauliBaselineTwistedConstant) * (ε + Real.sqrt ε))
          (1 / 4 : ℝ)]
  have hQR : ∀ p : Placement, opFamilyDistSq (uniformDistribution (PointPair P))
      (fun xz (ab : PauliScalar P × PauliScalar P) =>
        S.place p ((Q p.side xz).effect ab))
      (fun xz ab => S.place p ((S.sandwichPoint p.side xz.1 xz.2).effect ab))
      S.psiHat ≤ 440 * Real.rpow ((344 + 3 * pauliBaselineTwistedConstant) *
        (ε + Real.sqrt ε)) (1 / 4 : ℝ) := by
    have ha := hQaR.trans (hbound .AA' .BA'' trivial)
    have hb := hQbR.trans (hbound .BA'' .AA' trivial)
    rintro (_ | _ | _ | _)
    exacts [ha, hb, (ProjectiveSetting.opFamilyDistSq_place_BB'_eq_BA'' _ _ _ _).trans_le hb,
      (ProjectiveSetting.opFamilyDistSq_place_AB''_eq_AA' _ _ _ _).trans_le ha]
  rcases le_or_gt ε 1 with hε1 | hε1
  · obtain ⟨hε8, hs8, hq8⟩ := error_terms_le_rpow_eighth hε hε1
      (by linarith : (1 : ℝ) ≤ 344 + 3 * pauliBaselineTwistedConstant)
    have h1 := mul_le_mul_of_nonneg_left hs8 (by linarith : (0 : ℝ) ≤ pauliBaselineTwistedConstant)
    have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ pauliBaselineTwistedConstant)
      (Real.rpow_nonneg hε (1 / 8 : ℝ))
    have h3 := Real.rpow_nonneg hε (1 / 8 : ℝ)
    have h4 := Real.sqrt_nonneg ε
    have h₁ := ProjectiveSetting.sandwich_point_ordered_dist_le_explicit P ε S
    have hc (p₁ p₂ : Placement) (hopp : p₁.IsOpposite p₂) := by
      have hQXZ := opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _ (hQR p₁)
        (opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _ (h₁ p₁)
          (ProjectiveSetting.ordered_cross_dist_le_explicit P ε S p₁ p₂ hopp))
      have hQZX := opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _ hQXZ
        (ProjectiveSetting.exp_point_comm_explicit P ε S p₂)
      exact And.intro hQXZ (And.intro hQZX (opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _
        hQZX ((DistanceCalculus.opFamilyDistSq_symm ..).trans_le
          (opFamilyDistSq_le_of_le_of_le _ _ _ _ S.psiHat _ _ (hQR p₂) (h₁ p₂)))))
    simp only [pauliBaselinePointConstant]
    refine ⟨⟨fun side x z => Q side (x, z), by rintro (_ | _) x z; exacts [hQa _, hQb _],
      fun p₁ p₂ h => (hc p₁ p₂ h).2.2.trans ?_, fun p₁ p₂ h => (hc p₁ p₂ h).1.trans ?_,
      fun p₁ p₂ h => (hc p₁ p₂ h).2.1.trans ?_⟩⟩ <;>
      simp only [Real.rpow_eq_pow] at hq8 h1 hε8 ⊢ <;> linarith
  · have h4 : (4 : ℝ) ≤ pauliBaselinePointConstant * Real.rpow ε (1 / 8 : ℝ) := by
      have := Real.one_le_rpow hε1.le (by norm_num : (0 : ℝ) ≤ 1 / 8)
      rw [Real.rpow_eq_pow]; nlinarith
    have hQ := fun p xz => measurement_sum_adjoint_mul_le_one (S.placedMeasurement p (Q p.side xz))
    have hp := fun p W u =>
      S.placedMeasurement_isProjective p _ (S.pointMeasExp_isProjective p.side W u)
    refine ⟨⟨fun side x z => Q side (x, z), by rintro (_ | _) x z; exacts [hQa _, hQb _],
      fun p₁ p₂ _ => (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (hQ p₁) (hQ p₂)).trans h4,
      fun p₁ p₂ _ => (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (hQ p₁) fun xz => ?_).trans h4,
      fun p₁ p₂ _ => (opFamilyDistSq_uniform_le_four _ _ S.psiHat S.psiHat_norm
        (hQ p₁) fun xz => ?_).trans h4⟩⟩ <;>
      simp only [ProjectiveSetting.place_mul]
    exacts [(sum_mul_conjTranspose_mul_self_eq_one _ _ (hp _ .X xz.1) (hp _ .Z xz.2)).le,
      (sum_mul_conjTranspose_mul_self_eq_one' _ _ (hp _ .X xz.1) (hp _ .Z xz.2)).le]

/-- Register placement distributes over a filtered outcome sum. -/
theorem place_finset_sum {ε : ℝ}
    (S : ProjectiveSetting P ε) (p : Placement) {α : Type*}
    (s : Finset α) (A : α → Op (S.ExpandedLocalSpace p.side)) :
    S.place p (∑ a ∈ s, A a) = ∑ a ∈ s, S.place p (A a) := by
  ext i j
  cases p <;> simp [ProjectiveSetting.place, Matrix.sum_apply,
    Finset.sum_mul, Finset.mul_sum]

/-- Projectivity and the three data-processed consistency guarantees for
`CombinedPointsWitness.extendedQ`, given a joint point measurement. This is
the coarse-graining specification used by `exists_extendedQ` to prove
`lem:qld-4-12`, paper lines 993--1018; the `XZ` and `ZX` source products
remain separate. -/
theorem extendedQ_spec {ε δ : ℝ}
    {S : ProjectiveSetting P ε} (points : CombinedPointsWitness S δ) :
    (∀ side x z alpha beta,
      Measurement.IsProjective (points.extendedQ side x z alpha beta)) ∧
    (∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          ((points.extendedQ p2.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        S.psiHat <= δ) ∧
    (∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
              question.2.1 * ab.1 + question.2.2 * ab.2 = c),
            (S.pointMeasExp p2.side .X question.1.1).effect ab.1 *
              (S.pointMeasExp p2.side .Z question.1.2).effect ab.2))
        S.psiHat <= δ) ∧
    ∀ p1 p2 : Placement, p1.IsOpposite p2 ->
      opFamilyDistSq (uniformDistribution (ExtendedPointQuestion P))
        (fun question c => S.place p1
          ((points.extendedQ p1.side question.1.1 question.1.2
            question.2.1 question.2.2).effect c))
        (fun question c => S.place p2
          (∑ ab ∈ Finset.univ.filter (fun ab : PauliScalar P × PauliScalar P =>
              question.2.1 * ab.1 + question.2.2 * ab.2 = c),
            (S.pointMeasExp p2.side .Z question.1.2).effect ab.2 *
              (S.pointMeasExp p2.side .X question.1.1).effect ab.1))
        S.psiHat <= δ := by
  refine ⟨fun side x z alpha beta =>
      SandwichProduct.postprocess_isProjective _ (points.projective side x z) _,
    fun p1 p2 h => le_trans ?_ (points.self_consistent p1 p2 h),
    fun p1 p2 h => le_trans ?_ (points.consistent_XZ p1 p2 h),
    fun p1 p2 h => le_trans ?_ (points.consistent_ZX p1 p2 h)⟩ <;>
    refine le_of_eq_of_le ?_ (opFamilyDistSq_uniform_affine_postprocess_le _ _ S.psiHat
      fun xz => ?_) <;>
    simp only [CombinedPointsWitness.extendedQ, Measurement.postprocess_effect, place_finset_sum,
      sum_placed_measurement_eq_one, sum_placed_measurement_products_eq_one]
  rw [← (Equiv.prodComm _ _).sum_comp]
  exact (sum_placed_measurement_products_eq_one ..).symm

end

end MIPStarRE.QPBT
