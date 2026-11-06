module

public import QPBT.Observables.WinImplications.LowDegree
public import QPBT.Observables.WinImplications.FactorTransport
public import QPBT.Observables.Defs
public import QPBT.Combining.ActualErrorBounds
public import QPBT.Test.Soundness.NaimarkAssembly
public import QPBT.Test.Soundness.EpsReduction

/-!
# Transfer from completed to raw Pauli effects
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

/-- Completing the Pauli-answer measurement changes only outcome zero, where
it adds the total effect of malformed answers. -/
theorem completedPauliEffect_eq_raw_add_wrongForm {P : AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Measurement (PauliAnswer P) ι)
    (W : PauliKind) (u : PauliRegister P) :
    (M.postprocess pauliAnswerOrZero).effect u =
      M.effect (.pauliOutcome u) +
        if u = 0 then ProjectiveSetting.wrongFormEffect (.pauli W) M else 0 := by
  classical
  rw [Measurement.postprocess_effect, ProjectiveSetting.wrongFormEffect,
    Finset.sum_filter]
  by_cases hu : u = 0
  · subst u
    simp only [ite_true]
    calc
      (∑ answer, if pauliAnswerOrZero answer = 0 then M.effect answer else 0) =
          ∑ answer, ((if answer = .pauliOutcome 0 then M.effect answer else 0) +
            (if validPauliAnswer (.pauli W) answer = false then M.effect answer else 0)) := by
        refine Finset.sum_congr rfl fun answer _ => ?_
        cases answer <;> simp [pauliAnswerOrZero, validPauliAnswer]
        rfl
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp
        · rw [← Finset.sum_filter]
  · simp only [hu, ite_false, add_zero]
    rw [Finset.sum_eq_single (.pauliOutcome u)]
    · simp [pauliAnswerOrZero]
    · intro answer _ hanswer
      have hzero : (0 : PauliRegister P) ≠ u := by simpa [eq_comm] using hu
      cases answer <;> simp_all [pauliAnswerOrZero]
    · simp

namespace WinImplications

/-- A strategy winning with probability at least `1 - ε` has average Pauli-edge
rejection probability at most `ε`. -/
theorem pauliRejectionAverage_le_error_of_win {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) :
    avgOver (uniformDistribution (PauliEdge × PauliSpace P))
        (fun ez => pauliRejectionAt S ez.1 ez.2) ≤ ε := by
  have havg : avgOver (uniformDistribution (PauliEdge × PauliSpace P))
      (fun ez => pauliRejectionAt S ez.1 ez.2) = 1 - S.value := by
    rw [← rejectionEventAverage_eq_one_sub_value S]
    unfold pauliBasisTest pauliQuestionDistribution
    rw [Distribution.avgOver_map]
    rfl
  linarith

/-- Rejection on one fixed oriented edge is at most the number of edge types
times the total rejection probability. -/
theorem fixedEdgeRejection_le_error_of_win {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (e : PauliEdge) :
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S e) ≤
      (Fintype.card PauliEdge : ℝ) * ε :=
  (avgOver_uniform_fixed_le_card_mul_prod _
    (fun edge z => pauliRejectionAt_nonneg S edge z) e).trans
    (mul_le_mul_of_nonneg_left (pauliRejectionAverage_le_error_of_win S hwin)
      (Nat.cast_nonneg _))

end WinImplications

open DistanceCalculus

/-- Bob's malformed Pauli-answer mass is bounded by rejection on the
point-to-Pauli edge. -/
theorem wrongFormPauliMass_bob_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  have hpoint (z : PauliSpace P) :
      stateQForm S.ψ
          (heteroKron 1
            (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤
        WinImplications.pauliRejectionAt S (WinImplications.pointPauliEdge W) z := by
    have hmass :
        stateQForm S.ψ
            (heteroKron 1
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.B (pauliQuestion P W)))) =
          bobEventWeight S (pauliQuestion P W)
            (fun b => validPauliAnswer (.pauli W) b = false) := by
      unfold ProjectiveSetting.wrongFormEffect bobEventWeight
      rw [heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : validPauliAnswer (.pauli W) b = false <;>
        simp [hb, stateQForm, bobOutcomeWeight]
    rw [hmass, ← outcome_event_weight_right_eq S
      ((.point W), pauliCL P (.point W) z) (pauliQuestion P W)]
    unfold WinImplications.pauliRejectionAt WinImplications.pauliSourceQuestions
    simp only [WinImplications.pointPauliEdge, pauliCL, pauliQuestion]
    exact outcome_event_weight_mono S _ _ _ _ fun a b hb => by simp [pauliWinPredicate, hb]
  calc
    stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) =
        avgOver (uniformDistribution (PauliSpace P)) (fun _ =>
          stateQForm S.ψ
            (heteroKron 1
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.B (pauliQuestion P W))))) := (avgOver_uniform_const _).symm
    _ ≤ avgOver (uniformDistribution (PauliSpace P))
        (WinImplications.pauliRejectionAt S (WinImplications.pointPauliEdge W)) :=
      avgOver_mono _ _ _ hpoint
    _ ≤ _ := WinImplications.fixedEdgeRejection_le_error_of_win S hwin _

/-- Alice's malformed Pauli-answer mass is bounded by rejection on the
Pauli-to-point edge. -/
theorem wrongFormPauliMass_alice_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  have hwin' : 1 - ε ≤ (WinImplications.pauliStrategySwap S).value := by
    rwa [WinImplications.pauliStrategySwap_value]
  have h := wrongFormPauliMass_bob_le_error (WinImplications.pauliStrategySwap S) hwin' W
  change stateQForm (reindexState (Equiv.prodComm S.ιA S.ιB) S.ψ)
    (heteroKron (1 : Op S.ιB)
      (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W)))) ≤ _ at h
  rwa [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_prodComm_heteroKron] at h

private theorem raw_transfer_liftedAEffect_eq_tensor {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (M : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φA M =
      heteroKron (conjIsometry φA M) (1 : Op (ιB' × PauliRegister P)) := by
  ext i j
  simp [liftedAEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem raw_transfer_liftedBEffect_eq_tensor {P : AdmissibleParams} {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P)) (M : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φB M =
      heteroKron (1 : Op (ιA' × PauliRegister P)) (conjIsometry φB M) := by
  ext i j
  simp [liftedBEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem raw_pauli_operator_distance_le_completed_aux {P : AdmissibleParams}
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {ε δ : ℝ} (M : Measurement (PauliAnswer P) ι) (W : PauliKind)
    (lift : Op ι → Op κ) (hlift_add : ∀ A B, lift (A + B) = lift A + lift B)
    (ideal : PauliRegister P → Op κ) (theta Delta : EuclideanSpace ℂ κ)
    (hstate : ‖theta - Delta‖ ≤ δ)
    (hQcontr : (lift (ProjectiveSetting.wrongFormEffect (.pauli W) M))ᴴ *
      lift (ProjectiveSetting.wrongFormEffect (.pauli W) M) ≤ 1)
    (htheta : ‖applyOperatorToState
      (lift (ProjectiveSetting.wrongFormEffect (.pauli W) M)) theta‖ ^ 2 ≤
      (Fintype.card PauliEdge : ℝ) * ε) :
    (∑ u : PauliRegister P,
        ‖applyOperatorToState (lift (M.effect (.pauliOutcome u)) - ideal u) Delta‖ ^ 2) ≤
      2 * (∑ u : PauliRegister P,
        ‖applyOperatorToState
          (lift ((M.postprocess pauliAnswerOrZero).effect u) - ideal u) Delta‖ ^ 2) +
        4 * δ ^ 2 + 4 * (Fintype.card PauliEdge : ℝ) * ε := by
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let Q := lift E
  let bad := ‖applyOperatorToState Q Delta‖ ^ 2
  have hbad : bad ≤ 2 * δ ^ 2 + 2 * (Fintype.card PauliEdge : ℝ) * ε := by
    have hdecomp : applyOperatorToState Q Delta =
        applyOperatorToState Q (Delta - theta) + applyOperatorToState Q theta := by
      simp [applyOperatorToState]
    have hfirst : ‖applyOperatorToState Q (Delta - theta)‖ ≤ δ :=
      (MagicSquareRigidity.norm_applyOperatorToState_le hQcontr _).trans
        (by rw [norm_sub_rev]; exact hstate)
    have htri := pow_le_pow_left₀ (norm_nonneg _)
      (norm_add_le (applyOperatorToState Q (Delta - theta)) (applyOperatorToState Q theta)) 2
    have hfirstsq := pow_le_pow_left₀ (norm_nonneg _) hfirst 2
    dsimp only [bad]
    rw [hdecomp]
    nlinarith [sq_nonneg (‖applyOperatorToState Q (Delta - theta)‖ -
      ‖applyOperatorToState Q theta‖)]
  have hpoint (u : PauliRegister P) :
      ‖applyOperatorToState (lift (M.effect (.pauliOutcome u)) - ideal u) Delta‖ ^ 2 ≤
        2 * ‖applyOperatorToState
          (lift ((M.postprocess pauliAnswerOrZero).effect u) - ideal u) Delta‖ ^ 2 +
          if u = 0 then 2 * bad else 0 := by
    by_cases hu : u = 0
    · subst u
      simp only [ite_true, completedPauliEffect_eq_raw_add_wrongForm M W 0]
      have hvec :
          applyOperatorToState (lift (M.effect (.pauliOutcome 0)) - ideal 0) Delta =
            applyOperatorToState (lift (M.effect (.pauliOutcome 0) + E) - ideal 0) Delta -
              applyOperatorToState Q Delta := by
        rw [hlift_add]
        simp only [Q, applyOperatorToState, map_sub, LinearMap.sub_apply, map_add,
          LinearMap.add_apply]
        abel
      rw [hvec]
      have htri := pow_le_pow_left₀ (norm_nonneg _)
        (norm_sub_le
          (applyOperatorToState (lift (M.effect (.pauliOutcome 0) + E) - ideal 0) Delta)
          (applyOperatorToState Q Delta)) 2
      dsimp only [bad]
      nlinarith [sq_nonneg
        (‖applyOperatorToState (lift (M.effect (.pauliOutcome 0) + E) - ideal 0) Delta‖ -
          ‖applyOperatorToState Q Delta‖)]
    · simp only [hu, ite_false, completedPauliEffect_eq_raw_add_wrongForm M W u, add_zero]
      nlinarith [sq_nonneg ‖applyOperatorToState (lift (M.effect (.pauliOutcome u)) - ideal u) Delta‖]
  calc
    (∑ u : PauliRegister P,
        ‖applyOperatorToState (lift (M.effect (.pauliOutcome u)) - ideal u) Delta‖ ^ 2) ≤
        ∑ u : PauliRegister P,
          (2 * ‖applyOperatorToState
            (lift ((M.postprocess pauliAnswerOrZero).effect u) - ideal u) Delta‖ ^ 2 +
            if u = 0 then 2 * bad else 0) :=
      Finset.sum_le_sum fun u _ => hpoint u
    _ = 2 * (∑ u : PauliRegister P,
          ‖applyOperatorToState
            (lift ((M.postprocess pauliAnswerOrZero).effect u) - ideal u) Delta‖ ^ 2) +
          2 * bad := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ _ := by linarith

/-- Alice's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceA_le_completed {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind) :
    rawPauliOperatorDistanceA P S w W ≤
      2 * pauliOperatorDistanceA P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  let M := S.A (pauliQuestion P W)
  let N := M.postprocess (validPauliAnswer (.pauli W))
  have hE : ProjectiveSetting.wrongFormEffect (.pauli W) M = N.effect false := rfl
  refine raw_pauli_operator_distance_le_completed_aux M W
    (liftedAEffect S (ιB' := w.ιB') w.φA)
    (fun A B => by
      rw [raw_transfer_liftedAEffect_eq_tensor, raw_transfer_liftedAEffect_eq_tensor,
        raw_transfer_liftedAEffect_eq_tensor, ← heteroKron_add_left]
      congr 1; simp [conjIsometry, Matrix.mul_add, Matrix.add_mul])
    (pauliProjOnA'' P W) (isometryTensor w.φA w.φB S.ψ) (idealState P w.aux) hstate ?_ ?_
  · rw [raw_transfer_liftedAEffect_eq_tensor, hE]
    exact MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry w.φA
        (MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false))
  · rw [raw_transfer_liftedAEffect_eq_tensor,
      MagicSquareRigidity.applyOperatorToState_leftTensor_conjIsometry,
      MagicSquareRigidity.norm_isometryTensor, MagicSquareRigidity.norm_applyOperatorToState_sq]
    have hKpos : 0 ≤ heteroKron (ProjectiveSetting.wrongFormEffect (.pauli W) M) (1 : Op S.ιB) := by
      rw [hE]; exact kronecker_nonneg (N.pos false) (by simp)
    have hKle : heteroKron (ProjectiveSetting.wrongFormEffect (.pauli W) M) (1 : Op S.ιB) ≤ 1 := by
      rw [hE, ← Matrix.one_kronecker_one]
      exact kronecker_mono_left (measurement_effect_le_one N false) (by simp)
    rw [(Matrix.nonneg_iff_posSemidef.mp hKpos).isHermitian.eq]
    exact (quadratic_form_mono (MIPStarRE.Quantum.sq_le_self hKpos hKle) S.ψ).trans
      (wrongFormPauliMass_alice_le_error S hwin W)

/-- Bob's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceB_le_completed {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind) :
    rawPauliOperatorDistanceB P S w W ≤
      2 * pauliOperatorDistanceB P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  let M := S.B (pauliQuestion P W)
  let N := M.postprocess (validPauliAnswer (.pauli W))
  have hE : ProjectiveSetting.wrongFormEffect (.pauli W) M = N.effect false := rfl
  refine raw_pauli_operator_distance_le_completed_aux M W
    (liftedBEffect S (ιA' := w.ιA') w.φB)
    (fun A B => by
      rw [raw_transfer_liftedBEffect_eq_tensor, raw_transfer_liftedBEffect_eq_tensor,
        raw_transfer_liftedBEffect_eq_tensor, ← heteroKron_add_right]
      congr 1; simp [conjIsometry, Matrix.mul_add, Matrix.add_mul])
    (pauliProjOnB'' P W) (isometryTensor w.φA w.φB S.ψ) (idealState P w.aux) hstate ?_ ?_
  · rw [raw_transfer_liftedBEffect_eq_tensor, hE]
    exact MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry w.φB
        (MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false))
  · rw [raw_transfer_liftedBEffect_eq_tensor,
      MagicSquareRigidity.applyOperatorToState_rightTensor_conjIsometry,
      MagicSquareRigidity.norm_isometryTensor, MagicSquareRigidity.norm_applyOperatorToState_sq]
    have hKpos : 0 ≤ heteroKron (1 : Op S.ιA) (ProjectiveSetting.wrongFormEffect (.pauli W) M) := by
      rw [hE]; exact kronecker_nonneg (by simp) (N.pos false)
    have hKle : heteroKron (1 : Op S.ιA) (ProjectiveSetting.wrongFormEffect (.pauli W) M) ≤ 1 := by
      rw [hE, ← Matrix.one_kronecker_one]
      exact kronecker_le_kronecker_right_one (by simp) (measurement_effect_le_one N false)
    rw [(Matrix.nonneg_iff_posSemidef.mp hKpos).isHermitian.eq]
    exact (quadratic_form_mono (MIPStarRE.Quantum.sq_le_self hKpos hKle) S.ψ).trans
      (wrongFormPauliMass_bob_le_error S hwin W)

end

end MIPStarRE.QPBT
