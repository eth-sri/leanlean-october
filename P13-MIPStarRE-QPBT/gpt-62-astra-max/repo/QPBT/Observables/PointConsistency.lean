module

public import QPBT.Observables.ExpandedCommutation

/-!
# Expanded point consistency and commutation

This module records the quantitative conclusions for the expanded point
measurements on each of the four register placements. No symmetry-transfer
principle is assumed: the four placements occur explicitly in the statements.

## References

The declarations formalize blueprint
`lem:qld-comm-cons`, whose paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:452-505`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

local instance pauliEdgeNonemptyPointConsistency : Nonempty PauliEdge :=
  pauliEdge_nonempty

/-! ## Consistency of the unexpanded point measurements -/

section

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind)

/-- Full point-measurement inconsistency is the probability that the two
postprocessed point answers differ. This is the point self-loop specialization
used in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pointConsistency_eq_mismatch :
    bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pointMeas .alice W)
        (S.pointMeas .bob W)
        S.toStrategy.ψ =
      avgOver (uniformDistribution (PauliPoint P)) (fun u =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W u)
          (ProjectiveSetting.pointQuestion P W u)
          (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
            ProjectiveSetting.pointAnswerOrZero B)) := by
  solve_by_elim [ProjectiveSetting.pointQuestion, WinImplications.consistencyDefect_postprocess_eq_mismatch, S.pointMeas, S.toStrategy.A, S.toStrategy.B, consistencyDefect_congr]

/-- The two strategy point measurements are self-consistent on average over
the point, with the rejection bound of the point self-loop. This is the input
used at paper `14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem point_self_consistency_le :
    bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pointMeas .alice W)
        (S.pointMeas .bob W)
        S.toStrategy.ψ ≤ (Fintype.card PauliEdge : ℝ) * ε := by
  rw [pointConsistency_eq_mismatch]
  have hsource :
      avgOver (uniformDistribution (PauliPoint P)) (fun u =>
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pointQuestion P W u)
            (ProjectiveSetting.pointQuestion P W u)
            (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
              ProjectiveSetting.pointAnswerOrZero B)) =
        avgOver (uniformDistribution (PauliSpace P)) (fun z =>
          outcomeEventWeight S.toStrategy
            (ProjectiveSetting.pointQuestion P W (pauliToLd P W z).point)
            (ProjectiveSetting.pointQuestion P W (pauliToLd P W z).point)
            (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
              ProjectiveSetting.pointAnswerOrZero B)) := by
    let g : _ → ℝ := fun u =>
      outcomeEventWeight S.toStrategy
        (ProjectiveSetting.pointQuestion P W u)
        (ProjectiveSetting.pointQuestion P W u)
        (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
          ProjectiveSetting.pointAnswerOrZero B)
    exact ((WinImplications.avgOver_pauliToLd_uniform W (fun z => g z.point)).trans (WinImplications.avgOver_ldPoint_uniform P.toLdParams g)).symm
  rw [hsource]
  calc
    _ ≤ _ := by
      apply avgOver_mono
      intro z
      refine le_trans ?_
        (WinImplications.loopMismatch_le_rejection S (.point W) z)
      apply outcome_event_weight_mono
      grind
    _ ≤ _ :=
      WinImplications.fixedEdgeRejection_le_error S _

end

/-- Postprocessing a measurement after adjoining an identity register agrees
effectwise with adjoining that register after postprocessing. -/
theorem leftPlacedMeasurement_postprocess_effect
    {α β ι κ : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Measurement α ι) (f : α → β) (b : β) :
    ((DistanceCalculus.leftPlacedMeasurement (ιB := κ) M).postprocess f).effect b =
      heteroKron ((M.postprocess f).effect b) (1 : Op κ) := by
  apply leftTensor_finset_sum

-- The statements below are indexed by the fourfold iterated product of
-- `eq:def-psihat`; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default, which the
-- `synthInstance.maxSize` settings below supply declaration by declaration.
namespace ProjectiveSetting

/-! ## Fine-product consistency on the two bipartitions -/

variable {P : AdmissibleParams} {ε : ℝ} (S : ProjectiveSetting P ε) (W : PauliKind)

set_option synthInstance.maxSize 400 in
/-- Tensoring the strategy point measurements with the perfectly correlated
Pauli point measurement does not change their consistency defect on the
`AA' | BA''(B'B'')` bipartition. This is the product step in item 1 of
`lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pointTauConsistency_aaBa_eq :
    consistencyDefect (uniformDistribution (PauliPoint P))
        (fun u p => heteroKron ((S.pointTauMeas .alice W u).effect p)
          (1 : Op ((S.toStrategy.ιB × PauliRegister P) ×
            (PauliRegister P × PauliRegister P))))
        (fun u p => heteroKron (1 : Op (S.toStrategy.ιA × PauliRegister P))
          (heteroKron ((S.pointTauMeas .bob W u).effect p)
            (1 : Op (PauliRegister P × PauliRegister P))))
        (reindexState (aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
          S.psiHat) =
      bipartiteDefect (uniformDistribution (PauliPoint P))
        (S.pointMeas .alice W)
        (S.pointMeas .bob W)
        S.toStrategy.ψ := by
  let X := PauliPoint P
  let R := PauliRegister P
  let μ := uniformDistribution X
  let e := aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let fineA : X → Measurement (PauliScalar P × PauliScalar P)
      (S.toStrategy.ιA × R) := S.pointTauMeas .alice W
  let fineB : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιB × R) × (R × R)) := fun u =>
    DistanceCalculus.leftPlacedMeasurement
      (S.pointTauMeas .bob W u)
  let readout :=
    Measurement (PauliScalar P × PauliScalar P)
    ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R)))
  let A : X → readout :=
    fun u => DistanceCalculus.leftPlacedMeasurement (fineA u)
  let B : X → readout :=
    fun u => DistanceCalculus.rightPlacedMeasurement (fineB u)
  let pointA : X → Measurement _
      (S.toStrategy.ιA × S.toStrategy.ιB) := fun u =>
    DistanceCalculus.leftPlacedMeasurement (S.pointMeas .alice W u)
  let pointB : X → Measurement _
      (S.toStrategy.ιA × S.toStrategy.ιB) := fun u =>
    DistanceCalculus.rightPlacedMeasurement (S.pointMeas .bob W u)
  have hμ := uniformDistribution_isProbability X
  have hgroup : ‖reindexState e S.psiHat‖ = 1 := by
    rw [reindexState_norm_eq, psiHat_norm]
  have hfine :=
    DistanceCalculus.consistencyDefect_eq_one_sub_overlap A B hμ hgroup
  change consistencyDefect μ (fun u => (A u).effect)
      (fun u => (B u).effect) (reindexState e S.psiHat) =
    consistencyDefect μ (fun u => (pointA u).effect)
      (fun u => (pointB u).effect) S.toStrategy.ψ
  rw [hfine, (DistanceCalculus.consistencyDefect_eq_one_sub_overlap pointA pointB hμ
      S.toStrategy.ψ_norm)]
  congr 1
  apply avgOver_congr
  intro u
  have hterm (p : PauliScalar P × PauliScalar P) :
      DistanceCalculus.stateQForm (reindexState e S.psiHat)
          ((A u).effect p * (B u).effect p) =
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.pointMeas .alice W u).effect p.1)
              ((S.pointMeas .bob W u).effect p.1)) *
          DistanceCalculus.stateQForm (eprState (PauliRegister P))
            (heteroKron (tauPointProj W u p.2) (tauPointProj W u p.2)) := by
    let OA :=
      (S.pointTauMeas .alice W u).effect p
    let OB :=
      (S.pointTauMeas .bob W u).effect p
    simp [A, B, fineB, DistanceCalculus.leftPlacedMeasurement, DistanceCalculus.rightPlacedMeasurement, Measurement.ofSumEqOne]
    rw [DistanceCalculus.placed_product_stateQForm_eq,
      WinImplications.stateQForm_reindexState]
    rw [show heteroKron OA (heteroKron OB (1 : Op (R × R))) =
          heteroKron OA 1 *
            heteroKron 1 (heteroKron OB (1 : Op (R × R))) by
        simp [heteroKron_mul], WinImplications.reindexOp_mul,
        reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right]
    convert stateQForm_place_AA'_mul_BA'' S
        _
        _ (tauPointProj W u p.2)
      (measurement_effect_hermitian (S.pointMeas .alice W u) p.1)
      (measurement_effect_hermitian (S.pointMeas .bob W u) p.1)
      (measurement_effect_hermitian (tauPointMeas W u) p.2) using 1
    rfl
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : PauliScalar P, ∑ y : PauliScalar P,
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.pointMeas .alice W u).effect x)
              ((S.pointMeas .bob W u).effect x)) *
          DistanceCalculus.stateQForm (eprState R)
            (heteroKron (tauPointProj W u y) (tauPointProj W u y))) =
      (∑ x : PauliScalar P,
        DistanceCalculus.stateQForm S.toStrategy.ψ
          (heteroKron ((S.pointMeas .alice W u).effect x)
            ((S.pointMeas .bob W u).effect x))) *
        ∑ y : PauliScalar P, DistanceCalculus.stateQForm (eprState R)
          (heteroKron (tauPointProj W u y) (tauPointProj W u y)) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = _ := by
      rw [sum_tauPointProj_pair_stateQForm_eprState, mul_one]
      simp [pointA, pointB, DistanceCalculus.leftPlacedMeasurement, DistanceCalculus.rightPlacedMeasurement, Measurement.ofSumEqOne, DistanceCalculus.placed_product_stateQForm_eq]

/-! ## Data processing and transport back to the six registers -/

set_option synthInstance.maxSize 400 in
/-- Expanded point consistency for the directed `AA'`--`BA''` placement pair.
This is the explicit data-processing estimate for item 1 of
`lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:468-489`,
blueprint `ch14_qpbt_observables.tex:1155-1163`. -/
theorem expPointDist_aaBa_le :
    opFamilyDistSq (uniformDistribution (PauliPoint P))
        (fun u a => S.place .AA' ((S.pointMeasExp .alice W u).effect a))
        (fun u a => S.place .BA'' ((S.pointMeasExp .bob W u).effect a))
        S.psiHat ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) := by
  let X := PauliPoint P
  let R := PauliRegister P
  let μ := uniformDistribution X
  let e := aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB
  let add : PauliScalar P × PauliScalar P → PauliScalar P :=
    fun p => p.1 + p.2
  let fineA : X → Measurement (PauliScalar P × PauliScalar P)
      (S.toStrategy.ιA × R) := S.pointTauMeas .alice W
  let fineB : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιB × R) × (R × R)) := fun u =>
    DistanceCalculus.leftPlacedMeasurement
      (S.pointTauMeas .bob W u)
  have hcoarse :=
    le_trans (consistencyDefect_postprocess_le μ fineA fineB
      _ add) (by
        calc
          _ = consistencyDefect (uniformDistribution X)
              (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
              (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
              S.toStrategy.ψ := by
            convert pointTauConsistency_aaBa_eq S W using 1
            all_goals rfl
          _ ≤ _ := point_self_consistency_le S W)
  have hdist := WinImplications.opFamilyDistSq_placed_le_of_consistencyDefect_le hcoarse
  let effectAt u := (S.pointMeasExp .alice W u).effect
  have hAeff (u : X) (a : PauliScalar P) :
      ((fineA u).postprocess add).effect a =
        effectAt u a := by
    convert
      (S.pointMeasExp_effect_eq_pointTauMeas_postprocess .alice W u a).symm
        using 1 <;> rfl
  have hBeff (u : X) (a : PauliScalar P) :
      ((fineB u).postprocess add).effect a =
        heteroKron ((S.pointMeasExp .bob W u).effect a) 1 := by
    calc
      _ = heteroKron
          (((S.pointTauMeas .bob W u).postprocess add).effect a)
          1 := by
        apply leftPlacedMeasurement_postprocess_effect
      _ = _ := by
        rw [← S.pointMeasExp_effect_eq_pointTauMeas_postprocess]
  have hnorm (u : X) (a : PauliScalar P) :
      ‖applyOperatorToState
          (S.place .AA' (effectAt u a) -
            S.place .BA'' ((S.pointMeasExp .bob W u).effect a)) S.psiHat‖ =
        ‖applyOperatorToState
          (heteroKron (((fineA u).postprocess add).effect a) 1 -
            heteroKron 1 (((fineB u).postprocess add).effect a))
          (reindexState e S.psiHat)‖ := by
    let OA :=
      effectAt u a
    let OB :=
      (S.pointMeasExp .bob W u).effect a
    rw [hAeff, hBeff, WinImplications.norm_applyOperatorToState_reindexState]
    rw [WinImplications.reindexOp_sub,
        reindexOp_aaBaBipartition_left, reindexOp_aaBaBipartition_right]
  refine Eq.trans_le ?_ hdist
  unfold opFamilyDistSq
  apply avgOver_congr
  intro u
  apply Finset.sum_congr rfl
  intro a _
  rw [hnorm]

set_option synthInstance.maxSize 400 in
/-- Expanded point consistency for the directed `AB''`--`BB'` placement pair.
This is the second bipartition of item 1 and does not assume strategy symmetry;
paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:468-489`,
blueprint `ch14_qpbt_observables.tex:1155-1163`. -/
theorem expPointDist_abBb_le :
    opFamilyDistSq (uniformDistribution (PauliPoint P))
        (fun u a => S.place .AB'' ((S.pointMeasExp .alice W u).effect a))
        (fun u a => S.place .BB' ((S.pointMeasExp .bob W u).effect a))
        S.psiHat ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε)  := by
  simpa only [opFamilyDistSq, opposite_place_norm_sub_eq] using expPointDist_aaBa_le S W

end ProjectiveSetting

/-- The four directed cross-party placement pairs asserted by the source's
“symmetric equivalents” clause. The relation lists the two orientations of
each of the `AA'`--`BA''` and `BB'`--`AB''` pairs; paper
`14_analysis_of_the_pauli_basis_test.tex:420-450`, blueprint
`def:symmetric-equivalents`. -/
def Placement.IsOpposite : Placement → Placement → Prop
  | .AA', .BA'' => True
  | .BA'', .AA' => True
  | .BB', .AB'' => True
  | .AB'', .BB' => True
  | _, _ => False

/-- Expanded point measurements are self-consistent with the fixed coefficient
`172 = 2 * |PauliEdge|`. This is item 1 of `lem:qld-comm-cons`, paper
`14_analysis_of_the_pauli_basis_test.tex:455-465`, blueprint
`lem:qld-comm-cons`. -/
theorem exp_point_self_cons_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
      ∀ W : PauliKind,
        opFamilyDistSq (uniformDistribution (PauliPoint P))
          (fun u a => S.place p₁
            ((S.pointMeasExp p₁.side W u).effect a))
          (fun u a => S.place p₂
            ((S.pointMeasExp p₂.side W u).effect a))
          S.psiHat ≤ 172 * ε := by
  intro P ε S p₁ p₂ hopp W
  cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
  · convert ProjectiveSetting.expPointDist_aaBa_le S W using 1 <;>
      simp only [Placement.side, pauli_edge_card, Nat.cast_ofNat] <;> ring
  · rw [DistanceCalculus.opFamilyDistSq_symm]
    convert ProjectiveSetting.expPointDist_aaBa_le S W using 1 <;>
      simp only [Placement.side, pauli_edge_card, Nat.cast_ofNat] <;> ring
  · rw [DistanceCalculus.opFamilyDistSq_symm]
    convert ProjectiveSetting.expPointDist_abBb_le S W using 1 <;>
      simp only [Placement.side, pauli_edge_card, Nat.cast_ofNat] <;> ring
  · convert ProjectiveSetting.expPointDist_abBb_le S W using 1 <;>
      simp only [Placement.side, pauli_edge_card, Nat.cast_ofNat] <;> ring

end

end MIPStarRE.QPBT
