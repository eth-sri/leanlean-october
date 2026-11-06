module

public import QPBT.Observables.WinImplications.LowDegree
public import QPBT.Observables.WinImplications.Interchange
public import QPBT.Observables.Defs
public import QPBT.Combining.ActualErrorBounds
public import QPBT.Test.Soundness.NaimarkAssembly
public import QPBT.Test.Soundness.EpsReduction

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

variable {P : AdmissibleParams}

/-- Completing the Pauli-answer measurement changes only outcome zero, where
it adds the total effect of malformed answers. -/
theorem completedPauliEffect_eq_raw_add_wrongForm {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Measurement (PauliAnswer P) ι)
    (W : PauliKind) (u : PauliRegister P) :
    (M.postprocess pauliAnswerOrZero).effect u =
      M.effect (.pauliOutcome u) +
        if u = 0 then ProjectiveSetting.wrongFormEffect (.pauli W) M else 0 := by
  rw [Measurement.postprocess_effect, ProjectiveSetting.wrongFormEffect,
    Finset.sum_filter]
  by_cases hu : u = 0
  · subst u
    simp
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

/-- Alice's malformed Pauli-answer mass is bounded by rejection on an
oriented point/Pauli edge. -/
theorem wrongFormPauliMass_alice_le_error {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  refine ((avgOver_uniform_const _).symm.trans_le (avgOver_mono _ _ _ fun z => le_of_eq_of_le
    (b := aliceEventWeight S (pauliQuestion P W) fun a => validPauliAnswer (.pauli W) a = false) ?_ ?_)).trans
    (WinImplications.fixedEdgeRejection_le_error_of_win S hwin (WinImplications.pauliPointEdge W))
  · unfold ProjectiveSetting.wrongFormEffect aliceEventWeight
    rw [heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : validPauliAnswer (.pauli W) a = false <;> simp [h, stateQForm, aliceOutcomeWeight]
  · rw [← outcome_event_weight_left_eq S (pauliQuestion P W)
      ((.point W), pauliCL P (.point W) z)]
    unfold WinImplications.pauliRejectionAt WinImplications.pauliSourceQuestions
    simp only [WinImplications.pauliPointEdge, pauliCL, pauliQuestion]
    apply outcome_event_weight_mono
    intro a b h
    simp [pauliWinPredicate, h]

/-- Bob's malformed Pauli-answer mass is bounded by rejection on an
oriented point/Pauli edge. -/
theorem wrongFormPauliMass_bob_le_error {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  refine ((avgOver_uniform_const _).symm.trans_le (avgOver_mono _ _ _ fun z => le_of_eq_of_le
    (b := bobEventWeight S (pauliQuestion P W) fun b => validPauliAnswer (.pauli W) b = false) ?_ ?_)).trans
    (WinImplications.fixedEdgeRejection_le_error_of_win S hwin (WinImplications.pointPauliEdge W))
  · unfold ProjectiveSetting.wrongFormEffect bobEventWeight
    rw [heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases h : validPauliAnswer (.pauli W) b = false <;> simp [h, stateQForm, bobOutcomeWeight]
  · rw [← outcome_event_weight_right_eq S ((.point W), pauliCL P (.point W) z)
      (pauliQuestion P W)]
    unfold WinImplications.pauliRejectionAt WinImplications.pauliSourceQuestions
    simp only [WinImplications.pointPauliEdge, pauliCL, pauliQuestion]
    apply outcome_event_weight_mono
    intro a b h
    simp [pauliWinPredicate, h]

theorem raw_transfer_liftedAEffect_eq_tensor {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (M : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φA M =
      heteroKron (conjIsometry φA M) (1 : Op (ιB' × PauliRegister P)) := by
  ext i j
  simp [liftedAEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

theorem raw_transfer_liftedBEffect_eq_tensor {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P)) (M : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φB M =
      heteroKron (1 : Op (ιA' × PauliRegister P)) (conjIsometry φB M) := by
  ext i j
  simp [liftedBEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

theorem raw_transfer_liftedAEffect_add {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (A B : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φA (A + B) =
      liftedAEffect S φA A + liftedAEffect S φA B := by
  rw [raw_transfer_liftedAEffect_eq_tensor, raw_transfer_liftedAEffect_eq_tensor,
    raw_transfer_liftedAEffect_eq_tensor, ← heteroKron_add_left]
  congr 1
  simp [conjIsometry, Matrix.mul_add, Matrix.add_mul]

theorem raw_transfer_liftedBEffect_add {G : Game}
    (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P)) (A B : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φB (A + B) =
      liftedBEffect S φB A + liftedBEffect S φB B := by
  rw [raw_transfer_liftedBEffect_eq_tensor, raw_transfer_liftedBEffect_eq_tensor,
    raw_transfer_liftedBEffect_eq_tensor, ← heteroKron_add_right]
  congr 1
  simp [conjIsometry, Matrix.mul_add, Matrix.add_mul]

theorem wrongFormEffect_eq_validity_effect {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Measurement (PauliAnswer P) ι)
    (W : PauliKind) :
    ProjectiveSetting.wrongFormEffect (.pauli W) M =
      (M.postprocess (validPauliAnswer (.pauli W))).effect false := by
  rw [ProjectiveSetting.wrongFormEffect, Measurement.postprocess_effect]

theorem norm_apply_sq_le_of_near {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Op ι}
    (hQ : Qᴴ * Q ≤ 1) {θ Δ : EuclideanSpace ℂ ι} {δ r : ℝ} (hθΔ : ‖θ - Δ‖ ≤ δ)
    (hθ : ‖applyOperatorToState Q θ‖ ^ 2 ≤ r) :
    ‖applyOperatorToState Q Δ‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  have h1 := (MagicSquareRigidity.norm_applyOperatorToState_le hQ (Δ - θ)).trans
    ((norm_sub_rev _ _).trans_le hθΔ)
  have hd : applyOperatorToState Q Δ =
      applyOperatorToState Q (Δ - θ) + applyOperatorToState Q θ := by
    simp [applyOperatorToState]
  rw [hd]
  have htri := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (applyOperatorToState Q (Δ - θ))
    (applyOperatorToState Q θ)) 2
  have h1sq := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖applyOperatorToState Q (Δ - θ)‖ - ‖applyOperatorToState Q θ‖)]

theorem norm_apply_sq_le_stateQForm {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Op ι}
    (h0 : 0 ≤ K) (h1 : K ≤ 1) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState K v‖ ^ 2 ≤ stateQForm v K := by
  rw [MagicSquareRigidity.norm_applyOperatorToState_sq,
    (Matrix.nonneg_iff_posSemidef.mp h0).isHermitian.eq]
  exact quadratic_form_mono (MIPStarRE.Quantum.sq_le_self h0 h1) v

theorem wrongFormEffect_ideal_norm_alice_le (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S)
    (W : PauliKind) (δ r : ℝ)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (hmass : stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤ r) :
    ‖applyOperatorToState
        (liftedAEffect S w.φA
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))))
        (idealState P w.aux)‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  set N := (S.A (pauliQuestion P W)).postprocess (validPauliAnswer (.pauli W))
  rw [wrongFormEffect_eq_validity_effect] at hmass ⊢
  rw [raw_transfer_liftedAEffect_eq_tensor]
  refine norm_apply_sq_le_of_near (MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
    (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry w.φA
      (MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false))) hstate ?_
  rw [MagicSquareRigidity.applyOperatorToState_leftTensor_conjIsometry,
    MagicSquareRigidity.norm_isometryTensor]
  refine (norm_apply_sq_le_stateQForm (kronecker_nonneg (N.pos false) (by simp)) ?_ S.ψ).trans hmass
  rw [← Matrix.one_kronecker_one]
  exact kronecker_mono_left (measurement_effect_le_one N false) (by simp)

theorem wrongFormEffect_ideal_norm_bob_le (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S)
    (W : PauliKind) (δ r : ℝ)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (hmass : stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤ r) :
    ‖applyOperatorToState
        (liftedBEffect S w.φB
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W))))
        (idealState P w.aux)‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  set N := (S.B (pauliQuestion P W)).postprocess (validPauliAnswer (.pauli W))
  rw [wrongFormEffect_eq_validity_effect] at hmass ⊢
  rw [raw_transfer_liftedBEffect_eq_tensor]
  refine norm_apply_sq_le_of_near (MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
    (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry w.φB
      (MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false))) hstate ?_
  rw [MagicSquareRigidity.applyOperatorToState_rightTensor_conjIsometry,
    MagicSquareRigidity.norm_isometryTensor]
  refine (norm_apply_sq_le_stateQForm (kronecker_nonneg (by simp) (N.pos false)) ?_ S.ψ).trans hmass
  rw [← Matrix.one_kronecker_one]
  exact kronecker_le_kronecker_right_one (by simp) (measurement_effect_le_one N false)

/-- If `y u = x u + [u = u₀] b` and `‖b‖ ^ 2 ≤ c`, then the squared norms of `x`
sum to at most twice those of `y` plus `2 c`. -/
theorem sum_norm_sq_le_of_eq_add {U V : Type*} [Fintype U] [DecidableEq U]
    [SeminormedAddCommGroup V] (x y : U → V) (b : V) (u₀ : U)
    (h : ∀ u, y u = x u + if u = u₀ then b else 0) {c : ℝ} (hb : ‖b‖ ^ 2 ≤ c) :
    ∑ u, ‖x u‖ ^ 2 ≤ 2 * ∑ u, ‖y u‖ ^ 2 + 2 * c := by
  have key (u : U) : ‖x u‖ ^ 2 ≤ 2 * ‖y u‖ ^ 2 + 2 * ‖if u = u₀ then b else 0‖ ^ 2 := by
    have h1 := norm_sub_le (y u) (if u = u₀ then b else 0)
    rw [show y u - _ = x u by rw [h u, add_sub_cancel_right]] at h1
    nlinarith [norm_nonneg (x u), sq_nonneg (‖y u‖ - ‖if u = u₀ then b else 0‖)]
  refine (Finset.sum_le_sum fun u _ => key u).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp [apply_ite, hb]

/-- Alice's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceA_le_completed {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind) :
    rawPauliOperatorDistanceA P S w W ≤
      2 * pauliOperatorDistanceA P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  have h := sum_norm_sq_le_of_eq_add
    (fun u => applyOperatorToState (liftedAEffect S w.φA ((S.A (pauliQuestion P W)).effect (.pauliOutcome u)) -
      pauliProjOnA'' P W u) (idealState P w.aux))
    (fun u => applyOperatorToState (liftedAEffect S w.φA
      (((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect u) - pauliProjOnA'' P W u)
        (idealState P w.aux)) _ 0 (fun u => ?_)
    (wrongFormEffect_ideal_norm_alice_le S w W δ _ hstate (wrongFormPauliMass_alice_le_error S hwin W))
  · unfold rawPauliOperatorDistanceA pauliOperatorDistanceA
    linarith
  rw [completedPauliEffect_eq_raw_add_wrongForm]
  split_ifs
  · rw [raw_transfer_liftedAEffect_add]
    simp only [applyOperatorToState, map_sub, LinearMap.sub_apply, map_add, LinearMap.add_apply]
    abel
  · simp

/-- Bob's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceB_le_completed {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind) :
    rawPauliOperatorDistanceB P S w W ≤
      2 * pauliOperatorDistanceB P S w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  have h := sum_norm_sq_le_of_eq_add
    (fun u => applyOperatorToState (liftedBEffect S w.φB ((S.B (pauliQuestion P W)).effect (.pauliOutcome u)) -
      pauliProjOnB'' P W u) (idealState P w.aux))
    (fun u => applyOperatorToState (liftedBEffect S w.φB
      (((S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect u) - pauliProjOnB'' P W u)
        (idealState P w.aux)) _ 0 (fun u => ?_)
    (wrongFormEffect_ideal_norm_bob_le S w W δ _ hstate (wrongFormPauliMass_bob_le_error S hwin W))
  · unfold rawPauliOperatorDistanceB pauliOperatorDistanceB
    linarith
  rw [completedPauliEffect_eq_raw_add_wrongForm]
  split_ifs
  · rw [raw_transfer_liftedBEffect_add]
    simp only [applyOperatorToState, map_sub, LinearMap.sub_apply, map_add, LinearMap.add_apply]
    abel
  · simp

end

end MIPStarRE.QPBT
