module

public import QPBT.Games.ErrorFunctions
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

/-! ## Consistency of the unexpanded point measurements -/

/-- Full point-measurement inconsistency is the probability that the two
postprocessed point answers differ. This is the point self-loop specialization
used in item 1 of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem pointConsistency_eq_mismatch {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ =
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
        outcomeEventWeight S.toStrategy
          (ProjectiveSetting.pointQuestion P W u)
          (ProjectiveSetting.pointQuestion P W u)
          (fun A B => ProjectiveSetting.pointAnswerOrZero A ≠
            ProjectiveSetting.pointAnswerOrZero B)) := by
  let X := Fin P.m → PauliScalar P
  let q : X → PauliQuestion P := fun u => ProjectiveSetting.pointQuestion P W u
  let f : X → PauliAnswer P → PauliScalar P := fun _ =>
    ProjectiveSetting.pointAnswerOrZero
  have h := WinImplications.consistencyDefect_postprocess_eq_mismatch
    (X := X) (uniformDistribution X) S.toStrategy q q f f
  have hA : ∀ (u : X) c,
      heteroKron ((S.pointMeas .alice W u).effect c)
          (1 : Op S.toStrategy.ιB) =
        heteroKron (((S.toStrategy.A (q u)).postprocess (f u)).effect c)
          (1 : Op S.toStrategy.ιB) := by
    intro u c
    rfl
  have hB : ∀ (u : X) c,
      heteroKron (1 : Op S.toStrategy.ιA)
          ((S.pointMeas .bob W u).effect c) =
        heteroKron (1 : Op S.toStrategy.ιA)
          (((S.toStrategy.B (q u)).postprocess (f u)).effect c) := by
    intro u c
    rfl
  calc
    _ = consistencyDefect (uniformDistribution X)
        (fun u c => heteroKron
          (((S.toStrategy.A (q u)).postprocess (f u)).effect c) 1)
        (fun u c => heteroKron 1
          (((S.toStrategy.B (q u)).postprocess (f u)).effect c))
        S.toStrategy.ψ :=
          consistencyDefect_congr _ _ _ _ _ _ hA hB
    _ = avgOver (uniformDistribution X) (fun u =>
        outcomeEventWeight S.toStrategy (q u) (q u)
          (fun A B => f u A ≠ f u B)) := h
    _ = _ := by rfl

/-- The two strategy point measurements are self-consistent on average over
the point, with the rejection bound of the point self-loop. This is the input
used at paper `14_analysis_of_the_pauli_basis_test.tex:455-465`. -/
theorem point_self_consistency_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind) :
    consistencyDefect (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => heteroKron ((S.pointMeas .alice W u).effect a) 1)
        (fun u a => heteroKron 1 ((S.pointMeas .bob W u).effect a))
        S.toStrategy.ψ ≤ (Fintype.card PauliEdge : ℝ) * ε := by
  rw [pointConsistency_eq_mismatch]
  have hsource :
      avgOver (uniformDistribution (Fin P.m → PauliScalar P)) (fun u =>
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
    let g : (Fin P.m → PauliScalar P) → ℝ := fun u =>
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

/-- Postprocessing a measurement after adjoining an identity register agrees
effectwise with adjoining that register after postprocessing. -/
theorem leftPlacedMeasurement_postprocess_effect
    {α β ι κ : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Measurement α ι) (f : α → β) (b : β) :
    ((DistanceCalculus.leftPlacedMeasurement (ιB := κ) M).postprocess f).effect b =
      heteroKron ((M.postprocess f).effect b) (1 : Op κ) := by
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
  change (∑ a ∈ Finset.univ.filter (fun a => f a = b),
      leftTensor (ι₂ := κ) (M.effect a)) =
    leftTensor (ι₂ := κ)
      (∑ a ∈ Finset.univ.filter (fun a => f a = b), M.effect a)
  exact leftTensor_finset_sum _ _

-- The statements below are indexed by the fourfold iterated product of
-- `eq:def-psihat`; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default, which the
-- `synthInstance.maxSize` settings below supply declaration by declaration.
namespace ProjectiveSetting

/-! ## Fine-product consistency on the two bipartitions -/

set_option synthInstance.maxSize 400 in
theorem expPointDist_bipartition_le {P : AdmissibleParams} {ε : ℝ}
    (S : ProjectiveSetting P ε) (W : PauliKind)
    (placeA : Op (S.toStrategy.ιA × PauliRegister P) →
      Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB))
    (placeB : Op (S.toStrategy.ιB × PauliRegister P) →
      Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB))
    (e : SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃
      (S.toStrategy.ιA × PauliRegister P) ×
        ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P)))
    (he_left : ∀ OA, reindexOp e (heteroKron OA 1) = placeA OA)
    (he_right : ∀ OB, reindexOp e (heteroKron 1 (heteroKron OB 1)) = placeB OB)
    (hstate : ∀ (A : Op S.toStrategy.ιA) (B : Op S.toStrategy.ιB) (C : Op (PauliRegister P)),
      A.IsHermitian → B.IsHermitian → C.IsHermitian →
      DistanceCalculus.stateQForm S.psiHat (placeA (heteroKron A C) * placeB (heteroKron B C)) =
        DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B) *
          DistanceCalculus.stateQForm (eprState (PauliRegister P)) (heteroKron C C)) :
    opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => placeA ((S.pointMeasExp .alice W u).effect a))
        (fun u a => placeB ((S.pointMeasExp .bob W u).effect a))
        S.psiHat ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) := by
  let X := Fin P.m → PauliScalar P
  let R := PauliRegister P
  let μ := uniformDistribution X
  let add : PauliScalar P × PauliScalar P → PauliScalar P := fun p => p.1 + p.2
  let fineA : X → Measurement (PauliScalar P × PauliScalar P) (S.toStrategy.ιA × R) :=
    fun u => S.pointTauMeas .alice W u
  let fineB : X → Measurement (PauliScalar P × PauliScalar P) ((S.toStrategy.ιB × R) × (R × R)) :=
    fun u => DistanceCalculus.leftPlacedMeasurement (ιB := R × R) (S.pointTauMeas .bob W u)
  let A : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun u => DistanceCalculus.leftPlacedMeasurement (fineA u)
  let B : X → Measurement (PauliScalar P × PauliScalar P)
      ((S.toStrategy.ιA × R) × ((S.toStrategy.ιB × R) × (R × R))) :=
    fun u => DistanceCalculus.rightPlacedMeasurement (fineB u)
  let pointA : X → Measurement (PauliScalar P) (S.toStrategy.ιA × S.toStrategy.ιB) :=
    fun u => DistanceCalculus.leftPlacedMeasurement (S.pointMeas .alice W u)
  let pointB : X → Measurement (PauliScalar P) (S.toStrategy.ιA × S.toStrategy.ιB) :=
    fun u => DistanceCalculus.rightPlacedMeasurement (S.pointMeas .bob W u)
  have hμ : μ.IsProbability := uniformDistribution_isProbability X
  have hgroup : ‖reindexState e S.psiHat‖ = 1 := by rw [reindexState_norm_eq, psiHat_norm]
  have hfine_eq :
      consistencyDefect μ (fun u p => (A u).effect p)
          (fun u p => (B u).effect p) (reindexState e S.psiHat) =
        consistencyDefect μ (fun u a => (pointA u).effect a)
          (fun u a => (pointB u).effect a) S.toStrategy.ψ := by
    rw [DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ A B _ hμ hgroup,
      DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ pointA pointB _ hμ
        S.toStrategy.ψ_norm]
    congr 1
    apply avgOver_congr
    intro u
    have hterm (p : PauliScalar P × PauliScalar P) :
        DistanceCalculus.stateQForm (reindexState e S.psiHat)
            ((A u).effect p * (B u).effect p) =
          DistanceCalculus.stateQForm S.toStrategy.ψ
              (heteroKron ((S.pointMeas .alice W u).effect p.1)
                ((S.pointMeas .bob W u).effect p.1)) *
            DistanceCalculus.stateQForm (eprState R)
              (heteroKron (tauPointProj W u p.2) (tauPointProj W u p.2)) := by
      let OA : Op (S.toStrategy.ιA × R) := (S.pointTauMeas .alice W u).effect p
      let OB : Op (S.toStrategy.ιB × R) := (S.pointTauMeas .bob W u).effect p
      have hop : reindexOp e (heteroKron OA (heteroKron OB (1 : Op (R × R)))) =
          placeA OA * placeB OB := by
        rw [show heteroKron OA (heteroKron OB (1 : Op (R × R))) =
            heteroKron OA 1 * heteroKron 1 (heteroKron OB (1 : Op (R × R))) by
          rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]]
        rw [WinImplications.reindexOp_mul, he_left, he_right]
      simp only [A, B, fineA, fineB, DistanceCalculus.leftPlacedMeasurement,
        DistanceCalculus.rightPlacedMeasurement, Measurement.ofSumEqOne]
      rw [DistanceCalculus.placed_product_stateQForm_eq,
        WinImplications.stateQForm_reindexState]
      change DistanceCalculus.stateQForm S.psiHat
        (reindexOp e (heteroKron OA (heteroKron OB (1 : Op (R × R))))) = _
      rw [hop]
      exact hstate ((S.pointMeas .alice W u).effect p.1)
        ((S.pointMeas .bob W u).effect p.1) (tauPointProj W u p.2)
        (Matrix.nonneg_iff_posSemidef.mp ((S.pointMeas .alice W u).pos p.1)).isHermitian
        (Matrix.nonneg_iff_posSemidef.mp ((S.pointMeas .bob W u).pos p.1)).isHermitian
        (Matrix.nonneg_iff_posSemidef.mp ((tauPointMeas W u).pos p.2)).isHermitian
    simp_rw [hterm]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, sum_tauPointProj_pair_stateQForm_eprState, mul_one]
    simp only [pointA, pointB, DistanceCalculus.leftPlacedMeasurement,
      DistanceCalculus.rightPlacedMeasurement, Measurement.ofSumEqOne]
    simp_rw [DistanceCalculus.placed_product_stateQForm_eq]
  have hcoarse :
      consistencyDefect μ
          (fun u a => heteroKron (((fineA u).postprocess add).effect a)
            (1 : Op ((S.toStrategy.ιB × R) × (R × R))))
          (fun u a => heteroKron (1 : Op (S.toStrategy.ιA × R))
            (((fineB u).postprocess add).effect a))
          (reindexState e S.psiHat) ≤ (Fintype.card PauliEdge : ℝ) * ε :=
    (consistencyDefect_postprocess_le μ fineA fineB (reindexState e S.psiHat) add).trans
      (hfine_eq.le.trans (point_self_consistency_le S W))
  have hdist := WinImplications.opFamilyDistSq_placed_le_of_consistencyDefect_le
    μ (fun u => (fineA u).postprocess add)
      (fun u => (fineB u).postprocess add) (reindexState e S.psiHat) hcoarse
  have hAeff (u : X) (a : PauliScalar P) :
      ((fineA u).postprocess add).effect a = (S.pointMeasExp .alice W u).effect a :=
    (S.pointMeasExp_effect_eq_pointTauMeas_postprocess .alice W u a).symm
  have hBeff (u : X) (a : PauliScalar P) :
      ((fineB u).postprocess add).effect a =
        heteroKron ((S.pointMeasExp .bob W u).effect a) (1 : Op (R × R)) := by
    rw [leftPlacedMeasurement_postprocess_effect,
      ← S.pointMeasExp_effect_eq_pointTauMeas_postprocess .bob W u a]
  refine le_of_eq_of_le (avgOver_congr _ _ _ fun u => Finset.sum_congr rfl fun a _ => ?_) hdist
  dsimp only
  rw [hAeff, hBeff, WinImplications.norm_applyOperatorToState_reindexState,
    WinImplications.reindexOp_sub, he_left, he_right]

end ProjectiveSetting

/-- The four directed cross-party placement pairs asserted by the source's
“symmetric equivalents” clause. -/
def Placement.IsOpposite : Placement → Placement → Prop
  | .AA', .BA'' => True
  | .BA'', .AA' => True
  | .BB', .AB'' => True
  | .AB'', .BB' => True
  | _, _ => False

/-- Expanded point measurements are self-consistent with the fixed coefficient
`172 = 2 * |PauliEdge|`. -/
theorem exp_point_self_cons_explicit :
    ∀ (P : AdmissibleParams) (ε : ℝ) (S : ProjectiveSetting P ε)
      (p₁ p₂ : Placement), p₁.IsOpposite p₂ →
      ∀ W : PauliKind,
        opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
          (fun u a => S.place p₁
            ((S.pointMeasExp p₁.side W u).effect a))
          (fun u a => S.place p₂
            ((S.pointMeasExp p₂.side W u).effect a))
          S.psiHat ≤ 172 * ε := by
  intro P ε S p₁ p₂ hopp W
  have haa := ProjectiveSetting.expPointDist_bipartition_le S W
    (S.place .AA') (S.place .BA'')
    (ProjectiveSetting.aaBaBipartition P S.toStrategy.ιA S.toStrategy.ιB)
    (ProjectiveSetting.reindexOp_aaBaBipartition_left S)
    (ProjectiveSetting.reindexOp_aaBaBipartition_right S)
    (ProjectiveSetting.stateQForm_place_AA'_mul_BA'' S)
  have hab := ProjectiveSetting.expPointDist_bipartition_le S W
    (S.place .AB'') (S.place .BB')
    (ProjectiveSetting.abBbBipartition P S.toStrategy.ιA S.toStrategy.ιB)
    (ProjectiveSetting.reindexOp_abBbBipartition_left S)
    (ProjectiveSetting.reindexOp_abBbBipartition_right S)
    (ProjectiveSetting.stateQForm_place_AB''_mul_BB' S)
  rw [pauli_edge_card, Nat.cast_ofNat] at haa hab
  cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
  · linarith
  · rw [DistanceCalculus.opFamilyDistSq_symm]; linarith
  · rw [DistanceCalculus.opFamilyDistSq_symm]; linarith
  · linarith

end

end MIPStarRE.QPBT
