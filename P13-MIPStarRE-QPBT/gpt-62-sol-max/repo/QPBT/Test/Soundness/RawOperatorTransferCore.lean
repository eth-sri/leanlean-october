module

public import QPBT.Observables.WinImplications.LowDegree
public import QPBT.Observables.WinImplications.Interchange
public import QPBT.Observables.Defs
public import QPBT.Combining.ActualErrorBounds
public import QPBT.Test.Soundness.NaimarkAssembly
public import QPBT.Test.Soundness.EpsReduction
public import QPBT.Test.Soundness.PlayerExchange

/-!
# Transfer from completed to raw Pauli effects

The extraction proof uses the complete Pauli-register measurement obtained by
folding malformed answers into outcome zero. The source theorem instead
compares the raw effects attached to answers of the form `.pauliOutcome u`.
This module bounds the malformed-answer mass by rejection on the two oriented
point/Pauli edges and transfers the completed-family estimates to the raw
families without adding a hypothesis to the source theorem.

## References

Paper `thm:pauli`,
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1431-1445`,
and its proof at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1862-1876`.
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
        apply Finset.sum_congr rfl
        intro answer _
        cases answer <;> simp [pauliAnswerOrZero, validPauliAnswer] <;> rfl
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simp
        · rw [← Finset.sum_filter]
  · simp only [hu, ite_false, add_zero]
    rw [Finset.sum_eq_single (.pauliOutcome u)]
    · simp [pauliAnswerOrZero]
    · intro answer _ hanswer
      have hzero : (0 : PauliRegister P) ≠ u := by
        simpa [eq_comm] using hu
      cases answer <;> simp_all [pauliAnswerOrZero]
    · simp

open DistanceCalculus

section

variable {P : AdmissibleParams}

/-- Alice's malformed Pauli-answer mass is bounded by rejection on the
Pauli-to-point edge. -/
theorem wrongFormPauliMass_alice_le_error {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  have hmass : stateQForm S.ψ
      (heteroKron (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) =
      aliceEventWeight S (pauliQuestion P W) (fun a => validPauliAnswer (.pauli W) a = false) := by
    rw [ProjectiveSetting.wrongFormEffect, heteroKron_finset_sum_left,
      stateQForm_finset_sum, Finset.sum_filter]
    rfl
  rw [hmass, ← avgOver_uniform_const (α := PauliSpace P)
      (aliceEventWeight S (pauliQuestion P W) (fun a => validPauliAnswer (.pauli W) a = false))]
  refine (avgOver_mono _ _ _ fun z => ?_).trans (WinImplications.fixedEdgeRejection_le_error_of_win
    S hwin (WinImplications.pauliPointEdge W))
  rw [← outcome_event_weight_left_eq S (pauliQuestion P W) ((.point W), pauliCL P (.point W) z)]
  apply outcome_event_weight_mono
  intro a b ha
  change pauliWinPredicate P (pauliQuestion P W) (.point W, pauliCL P (.point W) z) a b = false
  simp [pauliWinPredicate, pauliQuestion, ha]

private theorem raw_transfer_liftedAEffect_add {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (A B : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φA (A + B) =
      liftedAEffect S φA A + liftedAEffect S φA B := by
  simp only [liftedAEffect, ← heteroKron_add_left]
  congr 1
  simp [conjIsometry, Matrix.mul_add, Matrix.add_mul]

private theorem wrongFormEffect_eq_validity_effect {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Measurement (PauliAnswer P) ι)
    (W : PauliKind) :
    ProjectiveSetting.wrongFormEffect (.pauli W) M =
      (M.postprocess (validPauliAnswer (.pauli W))).effect false := by
  rw [ProjectiveSetting.wrongFormEffect, Measurement.postprocess_effect]

private theorem norm_add_sq_le_two {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2, sq_nonneg (‖x‖ - ‖y‖)]

open MagicSquareRigidity DistanceCalculus in
/-- Testing an effect on a nearby target state costs twice the state error
squared plus twice the original Born weight. -/
private theorem lifted_effect_norm_le {α ιA ιB κA κB : Type} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
    (φA : EuclideanSpace ℂ ιA →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
    (φB : EuclideanSpace ℂ ιB →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (ξ : EuclideanSpace ℂ (κA × κB))
    (M : Measurement α ιA) (a : α) {δ r : ℝ}
    (hξ : ‖isometryTensor φA φB ψ - ξ‖ ≤ δ)
    (hM : stateQForm ψ (heteroKron (M.effect a) 1) ≤ r) :
    ‖applyOperatorToState (heteroKron (conjIsometry φA (M.effect a)) 1) ξ‖ ^ 2 ≤
      2 * δ ^ 2 + 2 * r := by
  let Q := heteroKron (conjIsometry φA (M.effect a)) (1 : Op κB)
  let θ := isometryTensor φA φB ψ
  have hc : Qᴴ * Q ≤ 1 := conjTranspose_mul_le_one_leftTensor
    (conjTranspose_mul_le_one_conjIsometry φA (conjTranspose_mul_le_one_of_effect M a))
  have hθ : ‖applyOperatorToState Q θ‖ ^ 2 ≤ r := by
    dsimp only [Q, θ]
    rw [applyOperatorToState_leftTensor_conjIsometry, norm_isometryTensor]
    let N := leftPlacedMeasurement (ιB := ιB) M
    change ‖applyOperatorToState (N.effect a) ψ‖ ^ 2 ≤ r
    rw [DistanceCalculus.norm_applyOperatorToState_sq, measurement_effect_hermitian]
    exact (quadratic_form_mono (sq_le_self (N.pos a) (measurement_effect_le_one N a)) ψ).trans hM
  have hd := (norm_applyOperatorToState_le hc (ξ - θ)).trans (by rwa [norm_sub_rev])
  have he : applyOperatorToState Q ξ =
      applyOperatorToState Q (ξ - θ) + applyOperatorToState Q θ := by
    rw [← applyOperatorToState_add, sub_add_cancel]
  change ‖applyOperatorToState Q ξ‖ ^ 2 ≤ _
  rw [he]
  refine (norm_add_sq_le_two _ _).trans ?_
  have hd' := pow_le_pow_left₀ (norm_nonneg _) hd 2
  have hξ' := pow_le_pow_left₀ (norm_nonneg _) hξ 2
  linarith

private theorem raw_error_le_of_completion {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Measurement (PauliAnswer P) ι) (W : PauliKind) (lift : Op ι → Op κ)
    (hadd : ∀ A B, lift (A + B) = lift A + lift B)
    (ideal : PauliRegister P → Op κ) (ψ : EuclideanSpace ℂ κ) :
    let error := fun u (A : Op ι) => ‖applyOperatorToState (lift A - ideal u) ψ‖ ^ 2
    (∑ u, error u (M.effect (.pauliOutcome u))) ≤
      2 * (∑ u, error u ((M.postprocess pauliAnswerOrZero).effect u)) +
        2 * ‖applyOperatorToState (lift (ProjectiveSetting.wrongFormEffect (.pauli W) M)) ψ‖ ^ 2 := by
  intro error
  classical
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let bad := ‖applyOperatorToState (lift E) ψ‖ ^ 2
  let total := M.postprocess pauliAnswerOrZero
  have hp (u : PauliRegister P) : error u (M.effect (.pauliOutcome u)) ≤
      2 * error u (total.effect u) + (if u = 0 then 2 * bad else 0) := by
    have h := completedPauliEffect_eq_raw_add_wrongForm M W u
    by_cases hu : u = 0
    · subst u
      simp only [ite_true] at h ⊢
      have he : lift (M.effect (.pauliOutcome 0)) - ideal 0 =
          lift (total.effect 0) - ideal 0 + -lift E := by
        change total.effect 0 = _ at h
        rw [h, hadd]
        abel
      dsimp only [error]
      rw [he, MagicSquareRigidity.applyOperatorToState_add_op,
        MagicSquareRigidity.applyOperatorToState_neg_op]
      simpa only [bad, norm_neg] using norm_add_sq_le_two
        (applyOperatorToState (lift (total.effect 0) - ideal 0) ψ) (-(applyOperatorToState (lift E) ψ))
    · simp only [hu, ite_false, add_zero] at h ⊢
      change total.effect u = _ at h
      rw [h]
      exact le_mul_of_one_le_left (sq_nonneg _) (by norm_num)
  refine (Finset.sum_le_sum fun u _ => hp u).trans_eq ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [bad, E, total]

end

section

variable {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind)
include P ε δ S hwin w hstate W

/-- Alice's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceA_le_completed :
    rawPauliOperatorDistanceA P S w W ≤
      2 * pauliOperatorDistanceA P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  let M := S.A (pauliQuestion P W)
  let L := liftedAEffect S (ιB' := w.ιB') w.φA
  let ξ := idealState P w.aux
  have h := raw_error_le_of_completion M W L (raw_transfer_liftedAEffect_add S w.φA)
    (pauliProjOnA'' P W) ξ
  have hmass := wrongFormPauliMass_alice_le_error S hwin W
  have hbad : ‖applyOperatorToState (L (ProjectiveSetting.wrongFormEffect (.pauli W) M)) ξ‖ ^ 2 ≤
      2 * δ ^ 2 + 2 * ((Fintype.card PauliEdge : ℝ) * ε) := by
    let N := M.postprocess (validPauliAnswer (.pauli W))
    change stateQForm S.ψ (heteroKron (ProjectiveSetting.wrongFormEffect (.pauli W) M) 1) ≤ _ at hmass
    rw [wrongFormEffect_eq_validity_effect] at hmass
    dsimp only [L]
    rw [liftedAEffect, wrongFormEffect_eq_validity_effect]
    exact lifted_effect_norm_le w.φA w.φB S.ψ ξ N false hstate hmass
  change rawPauliOperatorDistanceA P S w W ≤
    2 * pauliOperatorDistanceA P S w W + _ at h
  linarith

/-- Bob's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceB_le_completed :
    rawPauliOperatorDistanceB P S w W ≤
      2 * pauliOperatorDistanceB P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  have h := raw_pauli_operator_distanceA_le_completed ((pauliBasisTestSymm P).swapStrategy S)
    (((pauliBasisTestSymm P).swapStrategy_value S).symm ▸ hwin) w.swap
    (w.swap_state_error.le.trans hstate) W
  rwa [w.swap_raw_distance, w.swap_completed_distance] at h

end

end

end MIPStarRE.QPBT
