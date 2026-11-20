module

public import QPBT.Games.ErrorFunctions
public import QPBT.Observables.ExpandedCommutation
public import QPBT.Observables.ExpandedReadout

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

/-! ## Consistency of the unexpanded point measurements -/

section

variable {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind)
include P ε S W

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
  exact WinImplications.consistencyDefect_postprocess_eq_mismatch _ S.toStrategy
    (ProjectiveSetting.pointQuestion P W) (ProjectiveSetting.pointQuestion P W)
    (fun _ => ProjectiveSetting.pointAnswerOrZero) (fun _ => ProjectiveSetting.pointAnswerOrZero)

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
    let g : (PauliPoint P) → ℝ := fun u =>
      outcomeEventWeight S.toStrategy
        (ProjectiveSetting.pointQuestion P W u)
        (ProjectiveSetting.pointQuestion P W u)
        (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
          ProjectiveSetting.pointAnswerOrZero B)
    have hld := WinImplications.avgOver_pauliToLd_uniform P W (fun z => g z.point)
    have hpoint := WinImplications.avgOver_ldPoint_uniform P.toLdParams g
    exact (hld.trans hpoint).symm
  rw [hsource]
  calc
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (WinImplications.pauliRejectionAt S.toStrategy
          (WinImplications.pauliLoopEdge (.point W))) := by
      apply avgOver_mono
      intro z
      refine le_trans ?_
        (WinImplications.loopMismatch_le_rejection S (.point W) z)
      apply outcome_event_weight_mono
      intro A B hne hAB
      exact hne (congrArg ProjectiveSetting.pointAnswerOrZero hAB)
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
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
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
  exact id (leftTensor_finset_sum {a | f a = b} M.effect)

-- The statements below are indexed by the fourfold iterated product of
-- `eq:def-psihat`; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default, which the
-- `synthInstance.maxSize` settings below supply declaration by declaration.
set_option maxHeartbeats 800000 in
-- The expanded operators have dependent local spaces on both placements.
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
  intro P ε S p q hp W
  classical
  obtain rfl := Placement.eq_overlapPartner hp
  let q := ProjectiveSetting.overlapPartner p
  let μ := uniformDistribution (PauliPoint P)
  let A := fun u => S.placedMeasurement p (S.pointMeasExp p.side W u)
  let B := fun u => S.placedMeasurement q (S.pointMeasExp q.side W u)
  have h := opFamilyDistSq_le_two_mul_consistencyDefect μ A B S.psiHat
  rw [DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ A B S.psiHat
    (uniformDistribution_isProbability _) S.psiHat_norm] at h
  have hf (u : PauliPoint P) : (∑ a, DistanceCalculus.stateQForm S.psiHat
      ((A u).effect a * (B u).effect a)) =
      ∑ a, S.strategyOverlap p ((S.pointMeas p.side W u).effect a)
        ((S.pointMeas q.side W u).effect a) := by
    simp only [A, B, q, ProjectiveSetting.placedMeasurement_effect,
      S.pointMeasExp_effect_eq_pointTauMeas_postprocess]
    exact S.placed_shift_overlap p W u (S.pointMeas p.side W u) (S.pointMeas q.side W u)
        (· + ·) (fun _ _ _ => add_right_cancel)
  simp_rw [hf] at h
  have hw := point_self_consistency_le S W
  rw [DistanceCalculus.consistencyDefect_placed_eq_one_sub_overlap μ _ _ _
    (uniformDistribution_isProbability _) S.toStrategy.ψ_norm, pauli_edge_card] at hw
  refine h.trans ?_
  have he : (172 : ℝ) * ε = 2 * (↑(86 : ℕ) * ε) := by push_cast; ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  cases p <;> exact hw

end

end MIPStarRE.QPBT
