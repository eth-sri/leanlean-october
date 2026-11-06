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
      grind
    _ ≤ (Fintype.card PauliEdge : ℝ) * ε :=
      WinImplications.fixedEdgeRejection_le_error S _

/-- Postprocessing a measurement after adjoining an identity register agrees
effectwise with adjoining that register after postprocessing. -/
theorem leftPlacedMeasurement_postprocess_effect
    {α β ι κ : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Measurement α ι) (f : α → β) (b : β) :
    ((DistanceCalculus.leftPlacedMeasurement (ιB := κ) M).postprocess f).effect b =
      heteroKron ((M.postprocess f).effect b) (1 : Op κ) :=
  leftTensor_finset_sum _ _

-- The statements below are indexed by the fourfold iterated product of
-- `eq:def-psihat`; instance search for its `Fintype` and `DecidableEq`
-- structure needs a larger budget than the default, which the
-- `synthInstance.maxSize` settings below supply declaration by declaration.
namespace ProjectiveSetting

variable {P : AdmissibleParams} {ε : ℝ}

set_option synthInstance.maxSize 400 in
/-- Expanded point consistency for a directed placement pair which a
bipartition `e` of the six registers turns into ordinary left and right
placements. Tensoring the strategy point measurements with the perfectly
correlated Pauli point measurement does not change their consistency defect,
and data processing passes to the expanded point measurements. This is item 1
of `lem:qld-comm-cons`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:455-489`,
blueprint `ch14_qpbt_observables.tex:1155-1163`. -/
theorem expPointDist_le (S : ProjectiveSetting P ε) (W : PauliKind)
    (e : SixReg P S.toStrategy.ιA S.toStrategy.ιB ≃ (S.toStrategy.ιA × PauliRegister P) ×
      ((S.toStrategy.ιB × PauliRegister P) × (PauliRegister P × PauliRegister P)))
    (pl : Op (S.toStrategy.ιA × PauliRegister P) → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB))
    (pr : Op (S.toStrategy.ιB × PauliRegister P) → Op (SixReg P S.toStrategy.ιA S.toStrategy.ιB))
    (hl : ∀ O, reindexOp e (heteroKron O 1) = pl O)
    (hr : ∀ O, reindexOp e (heteroKron 1 (heteroKron O (1 : Op (PauliRegister P × PauliRegister P)))) = pr O)
    (hfac : ∀ A B T, A.IsHermitian → B.IsHermitian → T.IsHermitian →
      DistanceCalculus.stateQForm S.psiHat (pl (heteroKron A T) * pr (heteroKron B T)) =
        DistanceCalculus.stateQForm S.toStrategy.ψ (heteroKron A B) *
          DistanceCalculus.stateQForm (eprState (PauliRegister P)) (heteroKron T T)) :
    opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
        (fun u a => pl ((S.pointMeasExp .alice W u).effect a))
        (fun u a => pr ((S.pointMeasExp .bob W u).effect a))
        S.psiHat ≤ 2 * ((Fintype.card PauliEdge : ℝ) * ε) := by
  let μ := uniformDistribution (Fin P.m → PauliScalar P)
  have hμ : μ.IsProbability := uniformDistribution_isProbability _
  let fineB := fun u => DistanceCalculus.leftPlacedMeasurement
    (ιB := PauliRegister P × PauliRegister P) (S.pointTauMeas .bob W u)
  refine le_of_eq_of_le ?_ (opFamilyDistSq_placed_le_of_consistencyDefect_le μ
    (fun u => (S.pointTauMeas .alice W u).postprocess fun p => p.1 + p.2)
    (fun u => (fineB u).postprocess fun p => p.1 + p.2) (reindexState e S.psiHat)
    ((consistencyDefect_postprocess_le μ (fun u => S.pointTauMeas .alice W u) fineB _
      fun p => p.1 + p.2).trans (le_of_eq_of_le ?_ (point_self_consistency_le S W))))
  · refine avgOver_congr _ _ _ fun u => Finset.sum_congr rfl fun a _ => ?_
    dsimp only [fineB]
    rw [leftPlacedMeasurement_postprocess_effect, ← S.pointMeasExp_effect_eq_pointTauMeas_postprocess,
      ← S.pointMeasExp_effect_eq_pointTauMeas_postprocess,
      WinImplications.norm_applyOperatorToState_reindexState, WinImplications.reindexOp_sub, hl, hr]
  refine (DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
    (fun u => DistanceCalculus.leftPlacedMeasurement (S.pointTauMeas .alice W u))
    (fun u => DistanceCalculus.rightPlacedMeasurement (fineB u)) _ hμ
    (by rw [reindexState_norm_eq, psiHat_norm])).trans (.trans ?_
      (DistanceCalculus.consistencyDefect_eq_one_sub_overlap μ
        (fun u => DistanceCalculus.leftPlacedMeasurement (S.pointMeas .alice W u))
        (fun u => DistanceCalculus.rightPlacedMeasurement (S.pointMeas .bob W u)) _ hμ
        S.toStrategy.ψ_norm).symm)
  refine congrArg (1 - ·) (avgOver_congr _ _ _ fun u => ?_)
  have hterm (p : PauliScalar P × PauliScalar P) :
      DistanceCalculus.stateQForm (reindexState e S.psiHat)
          (heteroKron ((S.pointTauMeas .alice W u).effect p) 1 *
            heteroKron 1 (heteroKron ((S.pointTauMeas .bob W u).effect p) 1)) =
        DistanceCalculus.stateQForm S.toStrategy.ψ
            (heteroKron ((S.pointMeas .alice W u).effect p.1)
              ((S.pointMeas .bob W u).effect p.1)) *
          DistanceCalculus.stateQForm (eprState (PauliRegister P))
            (heteroKron (tauPointProj W u p.2) (tauPointProj W u p.2)) := by
    rw [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_mul, hl, hr]
    exact hfac _ _ _ (IsSelfAdjoint.of_nonneg ((S.pointMeas .alice W u).pos p.1))
      (IsSelfAdjoint.of_nonneg ((S.pointMeas .bob W u).pos p.1)) (IsSelfAdjoint.of_nonneg ((tauPointMeas W u).pos p.2))
  change ∑ p, DistanceCalculus.stateQForm (reindexState e S.psiHat)
      (heteroKron ((S.pointTauMeas .alice W u).effect p) 1 *
        heteroKron 1 (heteroKron ((S.pointTauMeas .bob W u).effect p) 1)) = _
  simp only [hterm, Fintype.sum_prod_type, ← Finset.mul_sum, sum_tauPointProj_pair_stateQForm_eprState,
    mul_one]
  exact Finset.sum_congr rfl fun a _ => (DistanceCalculus.placed_product_stateQForm_eq _ _ _).symm

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
        opFamilyDistSq (uniformDistribution (Fin P.m → PauliScalar P))
          (fun u a => S.place p₁
            ((S.pointMeasExp p₁.side W u).effect a))
          (fun u a => S.place p₂
            ((S.pointMeasExp p₂.side W u).effect a))
          S.psiHat ≤ 172 * ε := by
  intro P ε S p₁ p₂ hopp W
  have h := pauli_edge_card ▸ (show (2 : ℝ) * ((86 : ℕ) * ε) = 172 * ε by push_cast; ring)
  cases p₁ <;> cases p₂ <;> simp only [Placement.IsOpposite] at hopp
  · exact h ▸ ProjectiveSetting.expPointDist_le S W _ _ _ (S.reindexOp_aaBaBipartition_left)
      (S.reindexOp_aaBaBipartition_right) (S.stateQForm_place_AA'_mul_BA'')
  · rw [DistanceCalculus.opFamilyDistSq_symm]
    exact h ▸ ProjectiveSetting.expPointDist_le S W _ _ _ (S.reindexOp_aaBaBipartition_left)
      (S.reindexOp_aaBaBipartition_right) (S.stateQForm_place_AA'_mul_BA'')
  · rw [DistanceCalculus.opFamilyDistSq_symm]
    exact h ▸ ProjectiveSetting.expPointDist_le S W _ _ _ (S.reindexOp_abBbBipartition_left)
      (S.reindexOp_abBbBipartition_right) (S.stateQForm_place_AB''_mul_BB')
  · exact h ▸ ProjectiveSetting.expPointDist_le S W _ _ _ (S.reindexOp_abBbBipartition_left)
      (S.reindexOp_abBbBipartition_right) (S.stateQForm_place_AB''_mul_BB')

end

end MIPStarRE.QPBT
