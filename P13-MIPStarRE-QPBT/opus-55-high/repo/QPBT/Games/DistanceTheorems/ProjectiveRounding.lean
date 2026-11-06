module

public import QPBT.Games.DistanceTheorems.TensorSupport
public import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
public import MIPStarRE.LDT.Preliminaries.Completion
public import MIPStarRE.LDT.Preliminaries.Triangles.Core
public import MIPStarRE.LDT.Test.StrategyRole.Algebra

/-!
# Projective rounding for consistent POVMs

This module proves the orthonormalization lemma `lem:ortho` with an explicit
error constant: if a POVM `Q` on Alice's space and a POVM `R` on Bob's space are
`δ`-consistent on a unit bipartite state `ψ`, then Alice has a projective
measurement `P` on her original space with `P_a ⊗ 1` within `220 · δ^(1/4)` of
`Q_a ⊗ 1` on `ψ`.

The argument passes to Alice's reduced state and follows the construction of the
LDT orthonormalization theorem. Rounding the almost-projective effects of `Q` and
reducing their ranks gives a family of projectors `Q_a` whose ranges are almost
orthogonal; assembling those ranges into one auxiliary space gives an operator
`X`, whose positive-Gram polar factor `X̂` is a coisometry; and pulling the block
projector of each outcome back along `X̂`, so that `P_a = X̂ᴴ T_a X̂`, gives a
projective family close to `Q`. The family `P` lives on Alice's original space
and is completed to a measurement at one fixed outcome once its missing state
mass has been shown to be small.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:131-153`
- Blueprint `lem:ortho`
- Blueprint `lem:ortho-explicit-constant`, the statement proved in this module
- `references/ldt-paper/orthonormalization.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum DistanceCalculus
open MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (ψ : EuclideanSpace ℂ ι)

/-- The normalized pure state whose vector is the given unit Euclidean vector. -/
noncomputable def roundPureState (hψ : ‖ψ‖ = 1) : PureState ι where
  vector := ψ.ofLp
  unit := by
    calc
      star ψ.ofLp ⬝ᵥ ψ.ofLp = ψ.ofLp ⬝ᵥ star ψ.ofLp := dotProduct_comm _ _
      _ = inner ℂ ψ ψ := (EuclideanSpace.inner_eq_star_dotProduct ψ ψ).symm
      _ = (‖ψ‖ ^ 2 : ℂ) := inner_self_eq_norm_sq_to_K ψ
      _ = 1 := by simp_all

/-- The QPBT vector quadratic form equals evaluation in `roundPureState`. -/
theorem round_stateQForm_eq_ev (hψ : ‖ψ‖ = 1) (T : Op ι) :
    stateQForm ψ T = ev (roundPureState ψ hψ : QuantumState ι) T := by
  rw [PureState.ev_eq_re_inner]
  change (inner ℂ ψ (WithLp.toLp 2 (T *ᵥ ψ.ofLp))).re =
    (star ψ.ofLp ⬝ᵥ T *ᵥ ψ.ofLp).re
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- Evaluation of an operator square in `roundPureState` is the squared vector norm. -/
theorem round_ev_adjoint_mul_self_eq_norm_sq (hψ : ‖ψ‖ = 1) (T : Op ι) :
    ev (roundPureState ψ hψ : QuantumState ι) (Tᴴ * T) =
      ‖applyOperatorToState T ψ‖ ^ 2 := by
  rw [← round_stateQForm_eq_ev]
  symm
  rw [@norm_sq_eq_re_inner ℂ]
  unfold stateQForm applyOperatorToState
  rw [Matrix.toEuclideanLin_conjTranspose_mul_self]
  change (inner ℂ (Matrix.toEuclideanLin T ψ) (Matrix.toEuclideanLin T ψ)).re =
    (inner ℂ ψ ((Matrix.toEuclideanLin T).adjoint (Matrix.toEuclideanLin T ψ))).re
  rw [LinearMap.adjoint_inner_right]

/-- Regard a nonempty finite coordinate set as an LDT finite Hilbert space. -/
@[reducible] def roundFiniteHilbertSpace (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : FiniteHilbertSpace :=
  { carrier := ι
    instFintype := inferInstance
    instDecidableEq := inferInstance
    instNonempty := inferInstance }

/-- A complete measurement on a nonzero finite space has a nonempty outcome type. -/
theorem round_measurement_outcome_nonempty {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : MIPStarRE.Quantum.Measurement α ι) : Nonempty α := by
  by_contra hα
  let i : ι := Classical.choice inferInstance
  have heq := congrArg (fun X : Op ι => X i i) M.sum_eq_one
  simp_all

variable {ιA ιB α : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype α] [DecidableEq α]

/-- QPBT vector consistency is the LDT bipartite consistency relation on the
associated pure state and concrete measurements. -/
lemma round_consRel_of_consistencyDefect [Nonempty ιA] [Nonempty ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (Q : MIPStarRE.Quantum.Measurement α ιA)
    (R : MIPStarRE.Quantum.Measurement α ιB) (δ : Error)
    (hcons : consistencyDefect (uniformDistribution Unit)
      (fun _ a => heteroKron (Q.effect a) 1)
      (fun _ a => heteroKron 1 (R.effect a)) ψ ≤ δ) :
    let ψp : PureState (ιA × ιB) := roundPureState ψ hψ
    let HA : FiniteHilbertSpace := roundFiniteHilbertSpace ιA
    let HB : FiniteHilbertSpace := roundFiniteHilbertSpace ιB
    let A : MIPStarRE.LDT.Measurement α ιA :=
      MatrixMeasurement.toMeasurement (H := HA) Q
    let B : MIPStarRE.LDT.Measurement α ιB :=
      MatrixMeasurement.toMeasurement (H := HB) R
    ConsRel (ψp : QuantumState (ιA × ιB)) (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) δ := by
    let Qm : MatrixMeasurement α (roundFiniteHilbertSpace ιA) := Q
    let Rm : MatrixMeasurement α (roundFiniteHilbertSpace ιB) := R
    constructor
    simp only [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    rw [qBipartiteConsDefect_of_measurements]
    rw [ev_one_of_isNormalized _ (roundPureState ψ hψ).toQuantumState_isNormalized]
    rw [show qBipartiteMatchMass (roundPureState ψ hψ : QuantumState (ιA × ιB))
        (MatrixMeasurement.toMeasurement Qm).toSubMeas
        (MatrixMeasurement.toMeasurement Rm).toSubMeas =
      ∑ a : α, stateQForm ψ (heteroKron (Q.effect a) (R.effect a)) by
      apply Finset.sum_congr rfl
      intro a _
      simpa [Qm, Rm, MatrixMeasurement.toMeasurement_outcome,
        MIPStarRE.QPBT.heteroKron, MIPStarRE.LDT.opTensor] using
        (round_stateQForm_eq_ev ψ hψ (heteroKron (Q.effect a) (R.effect a))).symm]
    have hdefect := consistencyDefect_eq_one_sub_overlap (uniformDistribution Unit)
      (fun _ => DistanceCalculus.leftPlacedMeasurement (ιB := ιB) Q)
      (fun _ => DistanceCalculus.rightPlacedMeasurement (ιA := ιA) R) ψ
      (uniformDistribution_isProbability _) hψ
    simp only [DistanceCalculus.leftPlacedMeasurement, DistanceCalculus.rightPlacedMeasurement,
      MIPStarRE.Quantum.Measurement.ofSumEqOne, heteroKron_mul, mul_one, one_mul] at hdefect
    simp_all [avgOver, uniformDistribution]

/-- Rank reduction of the almost-projective effects, orthonormalization of the
resulting ranges into the family `P_a = X̂ᴴ T_a X̂`, and completion at one fixed
outcome give a projective measurement on Alice's original space within
`220 * δ^(1/4)` of the given one. -/
lemma round_projective_ldt [Nonempty ιA] [Nonempty ιB]
    (Ψ : QuantumState (ιA × ιB)) (hΨ : Ψ.IsNormalized)
    (A : MIPStarRE.LDT.Measurement α ιA)
    (B : MIPStarRE.LDT.Measurement α ιB) (a₀ : α) (δ : Error)
    (hδ : 0 ≤ δ)
    (hCons : ConsRel Ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) δ) :
    ∃ C : ProjMeas α ιA,
      qSDD Ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (leftPlacedSubMeas (ιB := ιB) C.toSubMeas) ≤
          220 * zetaQuarterRoot δ := by
  let φ : QuantumState ιA := leftMarginalState Ψ
  have hφ : φ.IsNormalized := leftMarginalState_isNormalized hΨ
  let t : Error := zetaQuarterRoot δ
  have ht_nonneg : 0 ≤ t := zetaQuarterRoot_nonneg hδ
  by_cases ht_small : t ≤ 1 / (24 : Error)
  · have hδ_small : δ ≤ 1 / (4 : Error) := by
      have ht_four : t ^ (4 : Nat) = δ := by
        simp only [t, zetaQuarterRoot, Real.rpow_eq_pow]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hδ]; norm_num
      nlinarith [pow_le_pow_left₀ ht_nonneg ht_small 4]
    have hsource :
        ∑ a, ev φ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * δ := by
      simpa [φ, leftLiftedMeasurement, leftPlacedSubMeas, leftTensor_sub,
        leftTensor_mul_leftTensor, leftMarginal_ev_eq, consistencyToAlmostProjectiveError] using
        (consistencyToAlmostProjective (ψ := Ψ) (A := A) (B := B) (ζ := δ) hCons).sourceAlmostProjective
    obtain ⟨qLayer, hRank⟩ :=
      projectiveLowRankSum φ A δ hφ hδ hδ_small hsource
    have hq_complete :
        ev φ (QTotal qLayer) ≥ 1 - 11 * t := by
      simpa using qCompleteness φ A δ qLayer hφ hδ hδ_small hRank
    have hsigma : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : α => (qLayer.q.outcome a).rank)) := by
      by_contra hsigma
      have hzero (a : α) : qLayer.q.outcome a = 0 := by
        refine matrix_eq_zero_of_rank_eq_zero _ (by_contra fun hrank => hsigma ?_)
        exact ⟨⟨Fintype.equivFin α a, ⟨0, by simpa [Fintype.equivFin] using Nat.pos_of_ne_zero hrank⟩⟩⟩
      simp [hRank.sum_eq_total.symm.trans (Finset.sum_eq_zero fun a _ => hzero a), ev] at hq_complete
      linarith
    letI := hsigma
    obtain ⟨_xHat, _hxHat_coisometry, _hxHat_mixed, data, hq, _hx, _hxHat, hQP⟩ :=
      pQApprox_ofRankReductionSigmaRangePositiveGram φ A δ hRank hφ hδ hδ_small
    have hRankData : RankReductionWitness φ A δ data.qLayer :=
      hq.symm ▸ hRank.toSigmaRangeQLayer
    have hAQ :
        SDDOpRel φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily α ιA))
          (constOpFamily data.qLayer.q) (roundingToProjectiveError δ) := by
      simpa [hq] using hRank.toSigmaRangeQLayer.closeness
    have hAP :
        SDDOpRel φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily α ιA))
          (constOpFamily (PFamily data)) (84 * t) := by
      refine MIPStarRE.LDT.Preliminaries.sddOpRel_mono _ _ _ _ _ _
        (MIPStarRE.LDT.Preliminaries.sddOpRel_triangle _ _ _ _ _ _ _ hAQ hQP) ?_
      have htrunc := spectralTruncationError_le_zetaQuarterRoot δ hδ hδ_small
      dsimp [roundingToProjectiveError, spectralTruncationError, t] at htrunc ⊢
      linarith
    let P : ProjSubMeas α ιA := qxpProjSubMeas data
    let pMass : Error := ev φ P.toSubMeas.total
    let qMass : Error := ev φ (QTotal data.qLayer)
    let sqrtMass : Error := ev φ (CFC.sqrt (QTotal data.qLayer))
    have hqtotal_nonneg : 0 ≤ QTotal data.qLayer := by
      rw [← hRankData.sum_eq_total]
      exact Finset.sum_nonneg fun a _ => hRankData.outcome_nonneg a
    have hq_nonneg : 0 ≤ qMass := ev_nonneg_of_psd φ _ hqtotal_nonneg
    have hp_nonneg : 0 ≤ pMass := ev_nonneg_of_psd φ _ P.toSubMeas.total_nonneg
    have hsqrt_nonneg : 0 ≤ sqrtMass := ev_nonneg_of_psd φ _ (CFC.sqrt_nonneg _)
    have hsqrt_complete : sqrtMass ≥ 1 - 12 * t := by
      simpa using
        sqrtQCompleteness φ A δ data.qLayer hφ hδ hδ_small hRankData
    have hsupport :
        CFC.sqrt (QTotal data.qLayer) * P.toSubMeas.total =
          CFC.sqrt (QTotal data.qLayer) := by
      rw [qxpProjSubMeas_total_eq_xHat_adjoint_mul_xHat data, ← data.xHat_mixed,
        ← Matrix.mul_assoc, Matrix.mul_assoc data.xᴴ, data.xHat_coisometry, Matrix.mul_one]
    have hq_sqrt_sq :
        CFC.sqrt (QTotal data.qLayer) * (CFC.sqrt (QTotal data.qLayer))ᴴ =
          QTotal data.qLayer := by
      rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian.eq,
        CFC.sqrt_mul_sqrt_self _ hqtotal_nonneg]
    have hp_sq : P.toSubMeas.totalᴴ * P.toSubMeas.total =
        P.toSubMeas.total := by
      rw [(Matrix.nonneg_iff_posSemidef.mp P.toSubMeas.total_nonneg).isHermitian.eq]
      exact MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P
    have hcs : |sqrtMass| ≤ Real.sqrt qMass * Real.sqrt pMass := by
      have hcs0 :=
        ev_abs_mul_le_sqrt φ (CFC.sqrt (QTotal data.qLayer)) P.toSubMeas.total
      rw [hsupport, hq_sqrt_sq, hp_sq] at hcs0
      simpa using hcs0
    have hsquare : sqrtMass ^ 2 ≤ qMass * pMass := by
      have := pow_le_pow_left₀ (abs_nonneg _) hcs 2
      rwa [sq_abs, mul_pow, Real.sq_sqrt hq_nonneg, Real.sq_sqrt hp_nonneg] at this
    have hq_le : qMass ≤ 1 + 2 * t := by
      have hscale := ev_scale φ (1 + 2 * spectralTruncationError δ) (1 : Op ιA)
      push_cast at hscale
      rw [ev_one_of_isNormalized φ hφ, mul_one] at hscale
      have := (ev_mono φ _ _ hRankData.total_le).trans_eq hscale
      linarith [spectralTruncationError_le_zetaQuarterRoot δ hδ hδ_small]
    have hp_lower : 1 - 26 * t ≤ pMass := by
      nlinarith
    let C : ProjMeas α ιA :=
      MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj P a₀
    have hAPq : qSDD φ A.toSubMeas P.toSubMeas ≤ 84 * t := by
      have hraw : qSDDCore φ A.outcome (PFamily data).outcome ≤ 84 * t := by
        simpa [SDDOpRel, sddErrorOp, avgOver, uniformDistribution,
          constOpFamily, qSDDOp, SubMeas.toOpFamily] using hAP.squaredDistanceBound
      unfold qSDD qSDDCore
      unfold qSDDCore at hraw
      simpa [P, PFamily, pFamilyFromXHat, Pa, qxpProjSubMeas_outcome] using hraw
    have hPCq : qSDD φ P.toSubMeas C.toSubMeas ≤ 26 * t := by
      rw [show C.toSubMeas =
          (MIPStarRE.LDT.Preliminaries.completeAtOutcome P.toSubMeas a₀).toSubMeas from rfl,
        MIPStarRE.LDT.Preliminaries.completion_self_distance,
        IsIdempotentElem.eq (IsIdempotentElem.one_sub
          (MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P)), ev_sub,
        ev_one_of_isNormalized φ hφ]
      dsimp [pMass] at hp_lower
      linarith
    have hACq := MIPStarRE.LDT.Preliminaries.questionSDD_triangle
      φ A.toSubMeas P.toSubMeas C.toSubMeas
    refine ⟨C, ?_⟩
    have hlift :
        qSDD Ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas) =
        qSDD φ A.toSubMeas C.toSubMeas := by
      simp [qSDD, qSDDCore, φ, leftPlacedSubMeas, leftTensor_sub, leftTensor_conjTranspose,
        leftTensor_mul_leftTensor, leftMarginal_ev_eq]
    linarith
  · let C : ProjMeas α ιA := MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj zeroProjSubMeas a₀
    refine ⟨C, (MIPStarRE.LDT.Preliminaries.questionSDD_triangle Ψ _
      (leftPlacedSubMeas (ιB := ιB) (zeroProjSubMeas : ProjSubMeas α ιA).toSubMeas) _).trans ?_⟩
    rw [MIPStarRE.LDT.Preliminaries.qSDD_symm Ψ _ (leftPlacedSubMeas (ιB := ιB) C.toSubMeas)]
    linarith [qSDD_leftPlaced_zeroProjSubMeas_le_one Ψ hΨ A.toSubMeas,
      qSDD_leftPlaced_zeroProjSubMeas_le_one Ψ hΨ C.toSubMeas]

/-- A consistent pair of POVMs admits an Alice-side projective rounding with
the explicit dimension-independent error `220 * δ^(1/4)`. -/
theorem projective_rounding_with_explicit_constant (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (Q : MIPStarRE.Quantum.Measurement α ιA)
    (R : MIPStarRE.Quantum.Measurement α ιB) (δ : Error) (hδ : 0 ≤ δ)
    (hcons : consistencyDefect (uniformDistribution Unit)
      (fun _ a => heteroKron (Q.effect a) 1)
      (fun _ a => heteroKron 1 (R.effect a)) ψ ≤ δ) :
    ∃ Pm : MIPStarRE.Quantum.Measurement α ιA,
      MIPStarRE.QPBT.Measurement.IsProjective Pm ∧
      opFamilyDistSq (uniformDistribution Unit)
        (fun _ a => heteroKron (Pm.effect a) 1)
        (fun _ a => heteroKron (Q.effect a) 1) ψ ≤
          220 * Real.rpow δ (1 / 4 : Error) := by
  have hι : Nonempty (ιA × ιB) := by
    by_contra hempty
    have := not_nonempty_iff.mp hempty
    simp [Subsingleton.elim ψ 0] at hψ
  haveI : Nonempty ιA := ⟨(Classical.choice hι).1⟩
  haveI : Nonempty ιB := ⟨(Classical.choice hι).2⟩
  have hα : Nonempty α := round_measurement_outcome_nonempty Q
  let a₀ : α := Classical.choice hα
  let Ψ : PureState (ιA × ιB) := roundPureState ψ hψ
  let HA : FiniteHilbertSpace := roundFiniteHilbertSpace ιA
  let HB : FiniteHilbertSpace := roundFiniteHilbertSpace ιB
  let A : MIPStarRE.LDT.Measurement α ιA :=
    MatrixMeasurement.toMeasurement (H := HA) Q
  let B : MIPStarRE.LDT.Measurement α ιB :=
    MatrixMeasurement.toMeasurement (H := HB) R
  have hCons : ConsRel (Ψ : QuantumState (ιA × ιB)) (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) δ := by
    simpa [Ψ, HA, HB, A, B] using
      round_consRel_of_consistencyDefect ψ hψ Q R δ hcons
  obtain ⟨C, hC⟩ := round_projective_ldt (Ψ : QuantumState (ιA × ιB))
    Ψ.toQuantumState_isNormalized A B a₀ δ hδ hCons
  let Pm : MIPStarRE.Quantum.Measurement α ιA :=
    MIPStarRE.Quantum.Measurement.ofSumEqOne C.outcome C.outcome_pos <| by
      rw [C.sum_eq_total, C.total_eq_one]
  have hPm_projective : MIPStarRE.QPBT.Measurement.IsProjective Pm := by
    intro a
    exact
      { isIdempotentElem := C.proj a
        isSelfAdjoint :=
          (Matrix.nonneg_iff_posSemidef.mp (C.outcome_pos a)).isHermitian.eq }
  refine ⟨Pm, hPm_projective, ?_⟩
  have hdist :
      opFamilyDistSq (uniformDistribution Unit)
          (fun _ a => heteroKron (Pm.effect a) 1)
          (fun _ a => heteroKron (Q.effect a) 1) ψ =
        qSDD (Ψ : QuantumState (ιA × ιB))
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas) := by
    simp only [opFamilyDistSq, qSDD, qSDDCore, Ψ, round_ev_adjoint_mul_self_eq_norm_sq ψ hψ]
    simp [avgOver, uniformDistribution]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
    rfl
  simp_all [MIPStarRE.LDT.Preliminaries.qSDD_symm, zetaQuarterRoot]

end

end MIPStarRE.QPBT
