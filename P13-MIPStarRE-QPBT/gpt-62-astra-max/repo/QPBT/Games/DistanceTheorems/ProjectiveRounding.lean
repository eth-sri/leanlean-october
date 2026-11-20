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

variable {ιA ιB α ι : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
  [Fintype α] [Fintype ι] [DecidableEq ι] [Nonempty ι] (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
  (T : Op ι)

include hψ in
/-- The normalized pure state whose vector is the given unit Euclidean vector. -/
private noncomputable def roundPureState : PureState ι where
  vector := ψ.ofLp
  unit := by
    refine Eq.trans (dotProduct_comm _ _) ?_
    refine Eq.trans ((EuclideanSpace.inner_eq_star_dotProduct ψ ψ).symm) ?_
    refine Eq.trans (inner_self_eq_norm_sq_to_K ψ) ?_
    rw [hψ]; norm_num

/-- The QPBT vector quadratic form equals evaluation in `roundPureState`. -/
private theorem round_stateQForm_eq_ev :
    stateQForm ψ T = ev (roundPureState ψ hψ : QuantumState ι) T :=
  pureState_stateQForm_eq_ev (roundPureState ψ hψ) T

/-- Evaluation of an operator square in `roundPureState` is the squared vector norm. -/
private theorem round_ev_adjoint_mul_self_eq_norm_sq :
    ev (roundPureState ψ hψ : QuantumState ι) (Tᴴ * T) =
      ‖applyOperatorToState T ψ‖ ^ 2 := by
  rw [← round_stateQForm_eq_ev]
  exact (norm_applyOperatorToState_sq_eq _ _).symm

/-- Regard a nonempty finite coordinate set as an LDT finite Hilbert space. -/
@[reducible] private def roundFiniteHilbertSpace (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : FiniteHilbertSpace :=
  { carrier := ι
    instFintype := inferInstance
    instDecidableEq := inferInstance
    instNonempty := inferInstance }

/-- A complete measurement on a nonzero finite space has a nonempty outcome type. -/
private theorem round_measurement_outcome_nonempty
    (M : MIPStarRE.Quantum.Measurement α ι) : Nonempty α := by
  classical
  by_contra hα
  haveI := not_nonempty_iff.mp hα
  let i : ι := Classical.choice inferInstance
  have heq := congrArg (fun X : Op ι => X i i) M.sum_eq_one
  simp at heq

/-- QPBT vector consistency is the LDT bipartite consistency relation on the
associated pure state and concrete measurements. -/
private lemma round_consRel_of_consistencyDefect [DecidableEq α] [Nonempty ιA] [Nonempty ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (Q : MIPStarRE.Quantum.Measurement α ιA)
    (R : MIPStarRE.Quantum.Measurement α ιB) (δ : Error)
    (hcons : bipartiteDefect (uniformDistribution Unit)
      (fun _ => Q)
      (fun _ => R) ψ ≤ δ) :
    let ψp := roundPureState ψ hψ
    let HA := roundFiniteHilbertSpace ιA
    let HB := roundFiniteHilbertSpace ιB
    let A :=
      MatrixMeasurement.toMeasurement (H := HA) Q
    let B :=
      MatrixMeasurement.toMeasurement (H := HB) R
    ConsRel (ψp : QuantumState (ιA × ιB)) (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) δ := by
    dsimp
    let Qm : MatrixMeasurement α (roundFiniteHilbertSpace ιA) := Q
    let Rm : MatrixMeasurement α (roundFiniteHilbertSpace ιB) := R
    constructor
    change bipartiteConsError
        (roundPureState ψ hψ : QuantumState (ιA × ιB))
        (uniformDistribution Unit)
        (constSubMeasFamily (MatrixMeasurement.toMeasurement Qm).toSubMeas)
        (constSubMeasFamily (MatrixMeasurement.toMeasurement Rm).toSubMeas) ≤ δ
    rw [show bipartiteConsError
        (roundPureState ψ hψ : QuantumState (ιA × ιB))
        (uniformDistribution Unit)
        (constSubMeasFamily
          (MatrixMeasurement.toMeasurement Qm).toSubMeas)
        (constSubMeasFamily
          (MatrixMeasurement.toMeasurement Rm).toSubMeas) =
        qBipartiteConsDefect
          (roundPureState ψ hψ : QuantumState (ιA × ιB))
          (MatrixMeasurement.toMeasurement Qm).toSubMeas
          (MatrixMeasurement.toMeasurement Rm).toSubMeas by
      simp [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]]
    rw [qBipartiteConsDefect_of_measurements]
    rw [ev_one_of_isNormalized _ (roundPureState ψ hψ).toQuantumState_isNormalized]
    rw [show qBipartiteMatchMass (roundPureState ψ hψ : QuantumState (ιA × ιB))
        (MatrixMeasurement.toMeasurement Qm).toSubMeas
        (MatrixMeasurement.toMeasurement Rm).toSubMeas =
      ∑ a : α, stateQForm ψ (heteroKron (Q.effect a) (R.effect a)) by
      unfold qBipartiteMatchMass
      apply Finset.sum_congr rfl
      intro a _
      simpa [Qm, Rm, MatrixMeasurement.toMeasurement_outcome,
        MIPStarRE.QPBT.heteroKron, MIPStarRE.LDT.opTensor] using
        (round_stateQForm_eq_ev ψ hψ (heteroKron (Q.effect a) (R.effect a))).symm]
    have hdefect : bipartiteDefect (uniformDistribution Unit)
        (fun _ => Q)
        (fun _ => R) ψ =
        1 - ∑ a : α, stateQForm ψ (heteroKron (Q.effect a) (R.effect a)) := by
      simp only [bipartiteDefect, consistencyDefect]
      simp_rw [consistency_term_eq_stateQForm]
      rw [show avgOver (uniformDistribution Unit)
          (fun _ => ∑ a : α, ∑ b : α, if a = b then 0 else
            stateQForm ψ
              (heteroKron (Q.effect a) 1 * heteroKron 1 (R.effect b))) =
          ∑ a : α, ∑ b : α, if a = b then 0 else
            stateQForm ψ
              (heteroKron (Q.effect a) 1 * heteroKron 1 (R.effect b)) by
        simp [avgOver, uniformDistribution]]
      rw [show (∑ a : α, ∑ b : α, if a = b then 0 else
            stateQForm ψ
              (heteroKron (Q.effect a) 1 * heteroKron 1 (R.effect b))) =
          ‖ψ‖ ^ 2 - ∑ a : α,
            stateQForm ψ (heteroKron (Q.effect a) (R.effect a)) by
        have hdiag :
            (∑ a : α,
                stateQForm ψ (heteroKron (Q.effect a) (R.effect a))) =
              ∑ a : α, stateQForm ψ
                ((DistanceCalculus.leftPlacedMeasurement (ιB := ιB) Q).effect a *
                  (DistanceCalculus.rightPlacedMeasurement (ιA := ιA) R).effect a) := by
          apply Finset.sum_congr rfl
          intro a _
          symm
          simpa [DistanceCalculus.leftPlacedMeasurement,
            DistanceCalculus.rightPlacedMeasurement,
            MIPStarRE.Quantum.Measurement.ofSumEqOne] using
              DistanceCalculus.placed_product_stateQForm_eq ψ (Q.effect a) (R.effect a)
        rw [hdiag]
        simpa [DistanceCalculus.leftPlacedMeasurement,
          DistanceCalculus.rightPlacedMeasurement,
          MIPStarRE.Quantum.Measurement.ofSumEqOne] using (point_defect_eq
            (DistanceCalculus.leftPlacedMeasurement (ιB := ιB) Q)
            (DistanceCalculus.rightPlacedMeasurement (ιA := ιA) R) ψ)]
      rw [hψ]
      norm_num
    rw [← hdefect]
    exact hcons

/-- Rank reduction of the almost-projective effects, orthonormalization of the
resulting ranges into the family `P_a = X̂ᴴ T_a X̂`, and completion at one fixed
outcome give a projective measurement on Alice's original space within
`220 * δ^(1/4)` of the given one. -/
private lemma round_projective_ldt [DecidableEq α] [Nonempty ιA] [Nonempty ιB]
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
  classical
  let φ := leftMarginalState Ψ
  have hφ := leftMarginalState_isNormalized hΨ
  let t := zetaQuarterRoot δ
  have ht_nonneg := zetaQuarterRoot_nonneg hδ
  by_cases ht_small : t ≤ 1 / (24 : Error)
  · have hδ_small : δ ≤ 1 / (4 : Error) := by
      have ht_four : t ^ (4 : Nat) = δ := by
        dsimp [t, zetaQuarterRoot]
        calc
          _ =
              Real.rpow δ ((1 / (4 : Error)) * 4) := by
                rw [← Real.rpow_natCast]
                simpa using
                  (Real.rpow_mul hδ (1 / (4 : Error)) (4 : Error)).symm
          _ = δ := by norm_num [Real.rpow_natCast]
      have hpow := pow_le_pow_left₀ ht_nonneg ht_small 4
      rw [ht_four] at hpow
      refine le_trans hpow ?_
      norm_num
    have hsourceLifted := (consistencyToAlmostProjective
      (ψ := Ψ) (A := A) (B := B) (ζ := δ) hCons).sourceAlmostProjective
    have hterm : ∀ a : α,
        ev Ψ
          ((leftLiftedMeasurement (ιB := ιB) A).outcome a -
            (leftLiftedMeasurement (ιB := ιB) A).outcome a *
              (leftLiftedMeasurement (ιB := ιB) A).outcome a) =
        ev φ (A.outcome a - A.outcome a * A.outcome a) := by
      intro a
      simpa [φ, leftLiftedMeasurement, leftPlacedSubMeas, leftTensor_sub,
        leftTensor_mul_leftTensor] using
        (leftMarginal_ev_eq Ψ (A.outcome a - A.outcome a * A.outcome a))
    obtain ⟨qLayer, hRank⟩ :=
      projectiveLowRankSum φ A δ hφ hδ hδ_small (by simpa [hterm, consistencyToAlmostProjectiveError] using hsourceLifted)
    have hq_complete :
        ev φ (QTotal qLayer) ≥ 1 - 11 * t := by
      simpa [t] using qCompleteness φ A δ qLayer hφ hδ hδ_small hRank
    have hsigma : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : α => (qLayer.q.outcome a).rank)) := by
      by_contra hsigma
      have hzero_rank : ∀ a : α, (qLayer.q.outcome a).rank = 0 := by
        intro a
        by_contra hrank
        have hpos := Nat.pos_of_ne_zero hrank
        have : Nonempty (FiniteHilbertSpace.sigmaFinCarrier
            (fun a : α => (qLayer.q.outcome a).rank)) := by
          refine ⟨⟨Fintype.equivFin α a, ⟨0, ?_⟩⟩⟩
          simpa [Fintype.equivFin] using hpos
        exact hsigma this
      have hzero : ∀ a : α, qLayer.q.outcome a = 0 := by
        intro a
        exact matrix_eq_zero_of_rank_eq_zero (hzero_rank a)
      have htotal_zero : QTotal qLayer = 0 := by
        rw [← Finset.sum_eq_zero fun a _ => hzero a]
        exact hRank.sum_eq_total.symm
      have : ev φ (QTotal qLayer) = 0 := by simp [htotal_zero, ev]
      rw [this] at hq_complete
      nlinarith
    letI := hsigma
    obtain ⟨_xHat, _hxHat_coisometry, _hxHat_mixed, data, hq, _hx, _hxHat, hQP⟩ :=
      pQApprox_ofRankReductionSigmaRangePositiveGram φ A δ hRank hφ hδ hδ_small
    have hRankData := hq.symm ▸ hRank.toSigmaRangeQLayer
    have hAP :
        SDDOpRel φ (uniformDistribution Unit)
          (constOpFamily (A.toSubMeas : OpFamily α ιA))
          (constOpFamily (PFamily data)) (84 * t) := by
      have htri := MIPStarRE.LDT.Preliminaries.sddOpRel_triangle φ
        (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily α ιA))
        (constOpFamily data.qLayer.q) (constOpFamily (PFamily data))
        (roundingToProjectiveError δ) (30 * zetaQuarterRoot δ) (by simpa [hq] using hRank.toSigmaRangeQLayer.closeness) hQP
      refine MIPStarRE.LDT.Preliminaries.sddOpRel_mono φ
        (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily α ιA))
        (constOpFamily (PFamily data))
        (2 * (roundingToProjectiveError δ + 30 * zetaQuarterRoot δ))
        (84 * t) htri ?_
      have htrunc :=
        spectralTruncationError_le_zetaQuarterRoot δ hδ hδ_small
      dsimp [roundingToProjectiveError, spectralTruncationError, t]
      dsimp [spectralTruncationError] at htrunc
      nlinarith
    let P := qxpProjSubMeas data
    let pMass := ev φ P.toSubMeas.total
    let qMass := ev φ (QTotal data.qLayer)
    let sqrtMass := ev φ (CFC.sqrt (QTotal data.qLayer))
    have hqtotal_nonneg : 0 ≤ QTotal data.qLayer := by
      rw [← hRankData.sum_eq_total]
      exact Finset.sum_nonneg fun a _ => hRankData.outcome_nonneg a
    have hq_nonneg : 0 ≤ qMass := by
      dsimp [qMass]
      exact ev_nonneg_of_psd φ _ hqtotal_nonneg
    have hp_nonneg : 0 ≤ pMass := ev_nonneg_of_psd φ P.toSubMeas.total P.toSubMeas.total_nonneg
    have hsqrt_nonneg := ev_nonneg_of_psd φ _ (CFC.sqrt_nonneg (QTotal data.qLayer))
    have hsqrt_complete : sqrtMass ≥ 1 - 12 * t := by
      simpa [sqrtMass, t] using
        sqrtQCompleteness φ A δ data.qLayer hφ hδ hδ_small hRankData
    have hsupport :
        CFC.sqrt (QTotal data.qLayer) * P.toSubMeas.total =
          CFC.sqrt (QTotal data.qLayer) := by
      rw [show P.toSubMeas.total = data.xHatᴴ * data.xHat by
        exact qxpProjSubMeas_total_eq_xHat_adjoint_mul_xHat data]
      rw [← data.xHat_mixed]
      calc
        _ =
            data.xᴴ * (data.xHat * data.xHatᴴ) * data.xHat := by
              simp only [Matrix.mul_assoc]
        _ = _ := by simp [data.xHat_coisometry]
    have hq_sqrt_sq :
        CFC.sqrt (QTotal data.qLayer) * (CFC.sqrt (QTotal data.qLayer))ᴴ =
          QTotal data.qLayer := by
      have hsqrt_herm :=
        (Matrix.nonneg_iff_posSemidef.mp
          (CFC.sqrt_nonneg (QTotal data.qLayer))).isHermitian.eq
      rw [hsqrt_herm]
      exact CFC.sqrt_mul_sqrt_self _ hqtotal_nonneg
    have hp_sq : P.toSubMeas.totalᴴ * P.toSubMeas.total =
        P.toSubMeas.total := by
      rw [(Matrix.nonneg_iff_posSemidef.mp P.toSubMeas.total_nonneg).isHermitian.eq]
      exact MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P
    have hcs : |sqrtMass| ≤ Real.sqrt qMass * Real.sqrt pMass := by
      have hcs0 :=
        ev_abs_mul_le_sqrt φ (CFC.sqrt (QTotal data.qLayer)) P.toSubMeas.total
      rw [hsupport, hq_sqrt_sq, hp_sq] at hcs0
      simpa [sqrtMass, qMass, pMass] using hcs0
    have hsquare : sqrtMass ^ 2 ≤ qMass * pMass := by
      have hsquare' :=
        (sq_le_sq₀ (abs_nonneg sqrtMass)
          (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hcs
      simpa [sq_abs, mul_pow, Real.sq_sqrt hq_nonneg,
        Real.sq_sqrt hp_nonneg] using hsquare'
    have hq_le : qMass ≤ 1 + 2 * t := by
      have hbound := ev_mono φ _ _ hRankData.total_le
      have hbound' : qMass ≤ 1 + 2 * spectralTruncationError δ := by
        have hscale :=
          ev_scale φ (1 + 2 * spectralTruncationError δ) (1 : Op ιA)
        rw [ev_one_of_isNormalized φ hφ, mul_one] at hscale
        have hscalar :
            (((1 : Error) + 2 * spectralTruncationError δ : Error) : ℂ) =
              (1 : ℂ) + 2 * (spectralTruncationError δ : ℂ) := by
          norm_num
        rw [hscalar] at hscale
        dsimp [qMass]
        exact hbound.trans_eq hscale
      have htrunc := spectralTruncationError_le_zetaQuarterRoot δ hδ hδ_small
      dsimp [t]
      linarith
    have hbase_nonneg : 0 ≤ 1 - 12 * t := by linarith
    have hp_lower : 1 - 26 * t ≤ pMass := by
      nlinarith [sq_nonneg t]
    have hresidual :
        ev φ ((1 - P.toSubMeas.total) * (1 - P.toSubMeas.total)) ≤ 26 * t := by
      have hresidual_eq :
          (1 - P.toSubMeas.total) * (1 - P.toSubMeas.total) =
            1 - P.toSubMeas.total := by
        calc
          _ =
              1 - P.toSubMeas.total - P.toSubMeas.total +
                P.toSubMeas.total * P.toSubMeas.total := by noncomm_ring
          _ = _ := by
            rw [MIPStarRE.LDT.Preliminaries.projSubMeas_total_proj P]
            abel
      rw [hresidual_eq, ev_sub, ev_one_of_isNormalized φ hφ]
      dsimp [pMass] at hp_lower
      linarith
    let C :=
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
          (MIPStarRE.LDT.Preliminaries.completeAtOutcome P.toSubMeas a₀).toSubMeas by
        rfl]
      rw [MIPStarRE.LDT.Preliminaries.completion_self_distance]
      exact hresidual
    refine ⟨C, ?_⟩
    have hlift :
        qSDD Ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas) =
        qSDD φ A.toSubMeas C.toSubMeas := by
      unfold qSDD qSDDCore
      apply Finset.sum_congr rfl
      intro a _
      simpa [φ, leftPlacedSubMeas, leftTensor_sub, leftTensor_conjTranspose,
        leftTensor_mul_leftTensor] using
        leftMarginal_ev_eq Ψ
          ((A.outcome a - C.outcome a)ᴴ * (A.outcome a - C.outcome a))
    rw [hlift]
    calc
      _ ≤
          2 * (qSDD φ A.toSubMeas P.toSubMeas +
            qSDD φ P.toSubMeas C.toSubMeas) :=
        MIPStarRE.LDT.Preliminaries.questionSDD_triangle
          φ A.toSubMeas P.toSubMeas C.toSubMeas
      _ ≤ 2 * (84 * t + 26 * t) := by gcongr
      _ = 220 * t := by ring
  · -- Outside the small-error range, the universal distance bound is below `220 * t`.
    let Z : ProjSubMeas α ιA := zeroProjSubMeas
    let C :=
      MIPStarRE.LDT.Preliminaries.completeAtOutcomeProj Z a₀
    have hAZ :=
      qSDD_leftPlaced_zeroProjSubMeas_le_one Ψ hΨ A.toSubMeas
    have hCZ :=
      qSDD_leftPlaced_zeroProjSubMeas_le_one Ψ hΨ C.toSubMeas
    have hZC :
        qSDD Ψ (leftPlacedSubMeas (ιB := ιB) Z.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas) ≤ 1 := by
      simpa [MIPStarRE.LDT.Preliminaries.qSDD_symm] using hCZ
    refine ⟨C, ?_⟩
    calc
      _ ≤
          2 * (qSDD Ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
              (leftPlacedSubMeas (ιB := ιB) Z.toSubMeas) +
            qSDD Ψ (leftPlacedSubMeas (ιB := ιB) Z.toSubMeas)
              (leftPlacedSubMeas (ιB := ιB) C.toSubMeas)) :=
        MIPStarRE.LDT.Preliminaries.questionSDD_triangle Ψ
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) Z.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) C.toSubMeas)
      _ ≤ 4 := by linarith
      _ ≤ 220 * t := by nlinarith

/-- A consistent pair of POVMs admits an Alice-side projective rounding with
the explicit dimension-independent error `220 * δ^(1/4)`. -/
theorem projective_rounding_with_explicit_constant [DecidableEq α]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (Q : MIPStarRE.Quantum.Measurement α ιA)
    (R : MIPStarRE.Quantum.Measurement α ιB) (δ : Error) (hδ : 0 ≤ δ)
    (hcons : bipartiteDefect (uniformDistribution Unit)
      (fun _ => Q)
      (fun _ => R) ψ ≤ δ) :
    ∃ Pm : MIPStarRE.Quantum.Measurement α ιA,
      MIPStarRE.QPBT.Measurement.IsProjective Pm ∧
      opFamilyDistSq (uniformDistribution Unit)
        (fun _ a => heteroKron (Pm.effect a) 1)
        (fun _ a => heteroKron (Q.effect a) 1) ψ ≤
          220 * Real.rpow δ (1 / 4 : Error) := by
  have hι : Nonempty (ιA × ιB) := by
    by_contra hempty
    letI := not_nonempty_iff.mp hempty
    have hzero : ψ = 0 := Subsingleton.elim _ _
    simp_all
  haveI : Nonempty ιA := ⟨(Classical.choice hι).1⟩
  haveI : Nonempty ιB := ⟨(Classical.choice hι).2⟩
  have hα := round_measurement_outcome_nonempty Q
  letI := hα
  let Ψ := roundPureState ψ hψ
  let HA := roundFiniteHilbertSpace ιA
  let HB := roundFiniteHilbertSpace ιB
  let A :=
    MatrixMeasurement.toMeasurement (H := HA) Q
  let B :=
    MatrixMeasurement.toMeasurement (H := HB) R
  obtain ⟨C, hC⟩ := round_projective_ldt Ψ
    Ψ.toQuantumState_isNormalized A B (Classical.choice hα) δ hδ (by
      solve_by_elim [round_consRel_of_consistencyDefect])
  let Pm :=
    MIPStarRE.Quantum.Measurement.ofSumEqOne C.outcome C.outcome_pos <| by
      rw [C.sum_eq_total, C.total_eq_one]
  refine ⟨Pm, (by
    intro a
    exact
      { isIdempotentElem := C.proj a
        isSelfAdjoint :=
          (Matrix.nonneg_iff_posSemidef.mp (C.outcome_pos a)).isHermitian.eq }), ?_⟩
  have hdist :
      opFamilyDistSq (uniformDistribution Unit)
          (fun _ a => heteroKron (Pm.effect a) 1)
          (fun _ a => heteroKron (Q.effect a) 1) ψ =
        qSDD Ψ
          (leftPlacedSubMeas C.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas) := by
    unfold opFamilyDistSq
    rw [show avgOver (uniformDistribution Unit)
        (fun _ => ∑ a : α,
          ‖applyOperatorToState
            (heteroKron (Pm.effect a) 1 - heteroKron (Q.effect a) 1) ψ‖ ^ 2) =
        ∑ a : α,
          ‖applyOperatorToState
            (heteroKron (Pm.effect a) 1 - heteroKron (Q.effect a) 1) ψ‖ ^ 2 by
      simp [avgOver, uniformDistribution]]
    congr 1 with a
    rw [round_ev_adjoint_mul_self_eq_norm_sq]
    rfl
  rw [hdist, MIPStarRE.LDT.Preliminaries.qSDD_symm]
  exact hC

end

end MIPStarRE.QPBT
