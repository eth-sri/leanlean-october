module

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
    calc
      _ =
          ∑ answer, ((if answer = .pauliOutcome 0 then M.effect answer else 0) +
            (if validPauliAnswer (.pauli W) answer = false then M.effect answer else 0)) := by
        congr 1 with answer
        cases answer <;> simp [pauliAnswerOrZero, validPauliAnswer] <;> rfl
      _ = _ := by
        simp [Finset.sum_add_distrib, ← Finset.sum_filter]
  · simp_all
    rw [Finset.sum_eq_single (.pauliOutcome u)]
    · simp [pauliAnswerOrZero]
    · intro answer _ hanswer
      have hzero : 0 ≠ u := by
        simpa [eq_comm] using hu
      cases answer <;> simp_all [pauliAnswerOrZero]
    · simp

namespace WinImplications

/-- Rejection on one fixed oriented edge is at most the number of edge types
times the total rejection probability. -/
theorem fixedEdgeRejection_le_error_of_win {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (e : PauliEdge) :
    avgOver (uniformDistribution (PauliSpace P)) (pauliRejectionAt S e) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  calc
    _ ≤
        _ := avgOver_uniform_fixed_le_card_mul_prod
        (pauliRejectionAt_nonneg S) e
    _ ≤ _ := mul_le_mul_of_nonneg_left ((by
                                          have havg : avgOver (uniformDistribution (PauliEdge × PauliSpace _))
                                              (fun ez => pauliRejectionAt S ez.1 ez.2) = 1 - S.value := by
                                            rw [← rejectionEventAverage_eq_one_sub_value S]
                                            unfold pauliBasisTest pauliQuestionDistribution
                                            rw [Distribution.avgOver_map]
                                            rfl
                                          rw [havg]
                                          linarith))
        (Nat.cast_nonneg _)

end WinImplications

open DistanceCalculus

/-- Alice's malformed Pauli-answer mass is bounded by rejection on the
Pauli-to-point edge. -/
theorem wrongFormPauliMass_alice_le_error {P : AdmissibleParams} {ε : ℝ}
    {S : Strategy (pauliBasisTest P)} (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  have hpoint (z : PauliSpace P) :
      stateQForm S.ψ
          (heteroKron
            (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤
        WinImplications.pauliRejectionAt S (WinImplications.pauliPointEdge W) z := by
    have hmass :
        stateQForm S.ψ
            (heteroKron
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.A (pauliQuestion P W))) 1) =
          aliceEventWeight S (pauliQuestion P W)
            (fun a => validPauliAnswer (.pauli W) a = false) := by
      unfold ProjectiveSetting.wrongFormEffect aliceEventWeight
      rw [heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
      rfl
    rw [hmass]
    rw [← outcome_event_weight_left_eq]
    unfold WinImplications.pauliRejectionAt WinImplications.pauliSourceQuestions
    simp [WinImplications.pauliPointEdge]
    apply outcome_event_weight_mono
    intro a b ha
    simp [pauliWinPredicate, ha]
  calc
    _ =
        avgOver (uniformDistribution (PauliSpace P)) (fun _ =>
          stateQForm S.ψ
            (heteroKron
              (ProjectiveSetting.wrongFormEffect (.pauli W)
                (S.A (pauliQuestion P W))) 1)) := by
      symm
      exact avgOver_uniform_const _
    _ ≤ _ := avgOver_mono _ _ _ hpoint
    _ ≤ _ := WinImplications.fixedEdgeRejection_le_error_of_win S hwin _

/-- Bob's malformed Pauli-answer mass is bounded by rejection on the
point-to-Pauli edge. -/
theorem wrongFormPauliMass_bob_le_error {P : AdmissibleParams} {ε : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value) (W : PauliKind) :
    stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤
      (Fintype.card PauliEdge : ℝ) * ε := by
  let G := pauliBasisTestSymm P
  have h := wrongFormPauliMass_alice_le_error (P := P) (ε := ε) ((G.value_swapStrategy S).symm ▸ hwin) W
  change DistanceCalculus.stateQForm (reindexState (Equiv.prodComm _ _) S.ψ)
    (heteroKron (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W))) 1) ≤ _ at h
  rwa [WinImplications.stateQForm_reindexState, WinImplications.reindexOp_prodComm_heteroKron] at h

section

variable {P : AdmissibleParams} {G : Game} (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA']
  [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']

private theorem raw_transfer_liftedAEffect_add
    (φA : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (A B : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φA (A + B) =
      liftedAEffect S φA A + liftedAEffect S φA B := by
  rw [liftedAEffect_eq_tensor, liftedAEffect_eq_tensor,
    liftedAEffect_eq_tensor, ← heteroKron_add_left]
  simp [conjIsometry, Matrix.mul_add, Matrix.add_mul]

private theorem raw_transfer_liftedBEffect_add
    (φB : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P)) (A B : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φB (A + B) =
      liftedBEffect S φB A + liftedBEffect S φB B := by
  rw [liftedBEffect_eq_tensor, liftedBEffect_eq_tensor,
    liftedBEffect_eq_tensor, ← heteroKron_add_right]
  simp [conjIsometry, Matrix.mul_add, Matrix.add_mul]

end

private theorem wrongFormEffect_eq_validity_effect {P : AdmissibleParams} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (M : Measurement (PauliAnswer P) ι)
    (W : PauliKind) :
    ProjectiveSetting.wrongFormEffect (.pauli W) M =
      (M.postprocess (validPauliAnswer (.pauli W))).effect false := by
  rfl

/-- Transfer an effect's Born mass to the squared action norm of a contraction
on a nearby state. Only the action norm on the transported state is needed. -/
private theorem effect_norm_transfer {ι κ α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype α] (M : Measurement α ι) (a : α)
    {ψ : EuclideanSpace ℂ ι} {θ Δ : EuclideanSpace ℂ κ} {Q : Op κ} {δ r : ℝ}
    (hQ : Qᴴ * Q ≤ 1) (hmass : stateQForm ψ (M.effect a) ≤ r) (hstate : ‖θ - Δ‖ ≤ δ)
    (hiso : ‖applyOperatorToState Q θ‖ = ‖applyOperatorToState (M.effect a) ψ‖) :
    ‖applyOperatorToState Q Δ‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  have hθ : ‖applyOperatorToState Q θ‖ ^ 2 ≤ r := by
    rw [hiso, DistanceCalculus.norm_applyOperatorToState_sq_eq, measurement_effect_hermitian]
    exact (quadratic_form_mono (MIPStarRE.Quantum.sq_le_self (M.pos a) (measurement_effect_le_one M a)) ψ).trans hmass
  let v := applyOperatorToState Q (Δ - θ)
  let w := applyOperatorToState Q θ
  have hv : ‖v‖ ≤ δ := (MagicSquareRigidity.norm_applyOperatorToState_le hQ _).trans ((norm_sub_rev θ Δ) ▸ hstate)
  have he : applyOperatorToState Q Δ = v + w := by simp [v, w, applyOperatorToState]
  change ‖w‖ ^ 2 ≤ _ at hθ
  rw [he]
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) (norm_add_le v w) 2,
    pow_le_pow_left₀ (norm_nonneg _) hv 2, sq_nonneg (‖v‖ - ‖w‖)]

private theorem wrongFormEffect_ideal_norm_alice_le {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S)
    (W : PauliKind) (δ r : ℝ)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (hmass : stateQForm S.ψ
        (heteroKron
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))) 1) ≤ r) :
    ‖applyOperatorToState
        (liftedAEffect S w.φA
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.A (pauliQuestion P W))))
        (idealState P w.aux)‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  let N := (S.A (pauliQuestion P W)).postprocess (validPauliAnswer (.pauli W))
  rw [wrongFormEffect_eq_validity_effect] at hmass ⊢
  rw [liftedAEffect_eq_tensor]
  refine effect_norm_transfer (leftPlacedMeasurement N) false ?_ hmass hstate ?_
  · exact MagicSquareRigidity.conjTranspose_mul_le_one_leftTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry _
        (MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false))
  · rw [MagicSquareRigidity.applyOperatorToState_leftTensor_conjIsometry, MagicSquareRigidity.norm_isometryTensor]
    rfl

private theorem wrongFormEffect_ideal_norm_bob_le {P : AdmissibleParams}
    (S : Strategy (pauliBasisTest P)) (w : PauliSoundnessWitness P S)
    (W : PauliKind) (δ r : ℝ)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (hmass : stateQForm S.ψ
        (heteroKron 1
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W)))) ≤ r) :
    ‖applyOperatorToState
        (liftedBEffect S w.φB
          (ProjectiveSetting.wrongFormEffect (.pauli W) (S.B (pauliQuestion P W))))
        (idealState P w.aux)‖ ^ 2 ≤ 2 * δ ^ 2 + 2 * r := by
  let N := (S.B (pauliQuestion P W)).postprocess (validPauliAnswer (.pauli W))
  rw [wrongFormEffect_eq_validity_effect] at hmass ⊢
  rw [liftedBEffect_eq_tensor]
  refine effect_norm_transfer (rightPlacedMeasurement N) false ?_ hmass hstate ?_
  · exact MagicSquareRigidity.conjTranspose_mul_le_one_rightTensor
      (MagicSquareRigidity.conjTranspose_mul_le_one_conjIsometry _
        (MagicSquareRigidity.conjTranspose_mul_le_one_of_effect N false))
  · rw [MagicSquareRigidity.applyOperatorToState_rightTensor_conjIsometry, MagicSquareRigidity.norm_isometryTensor]
    rfl

/-- Raw and completed answers differ only at zero. This transfers squared
operator error for either player's additive lifting map. -/
private theorem raw_completed_sum_le {P : AdmissibleParams} {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Measurement (PauliAnswer P) ι) (W : PauliKind) (L : Op ι → Op κ)
    (hadd : ∀ A B, L (A + B) = L A + L B) (T : PauliRegister P → Op κ)
    (ψ : EuclideanSpace ℂ κ) (δ r : ℝ)
    (hb : ‖applyOperatorToState (L (ProjectiveSetting.wrongFormEffect (.pauli W) M)) ψ‖ ^ 2 ≤
      2 * δ ^ 2 + 2 * r) :
    ∑ u, ‖applyOperatorToState (L (M.effect (.pauliOutcome u)) - T u) ψ‖ ^ 2 ≤
      2 * ∑ u, ‖applyOperatorToState (L ((M.postprocess pauliAnswerOrZero).effect u) - T u) ψ‖ ^ 2 +
      4 * δ ^ 2 + 4 * r := by
  let E := ProjectiveSetting.wrongFormEffect (.pauli W) M
  let C u := applyOperatorToState (L ((M.postprocess pauliAnswerOrZero).effect u) - T u) ψ
  let e := applyOperatorToState (L E) ψ
  have hpoint u : ‖applyOperatorToState (L (M.effect (.pauliOutcome u)) - T u) ψ‖ ^ 2 ≤
      2 * ‖C u‖ ^ 2 + if u = 0 then 2 * ‖e‖ ^ 2 else 0 := by
    by_cases hu : u = 0
    · subst u
      rw [if_pos rfl]
      have heq : applyOperatorToState (L (M.effect (.pauliOutcome 0)) - T 0) ψ = C 0 - e := by
        dsimp only [C, e, E]
        rw [completedPauliEffect_eq_raw_add_wrongForm M W, if_pos rfl, hadd]
        simp [applyOperatorToState]
        abel
      rw [heq]
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (C 0) e) 2, sq_nonneg (‖C 0‖ - ‖e‖)]
    · dsimp only [C]
      rw [completedPauliEffect_eq_raw_add_wrongForm M W u, if_neg hu, if_neg hu, add_zero, add_zero]
      nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hpoint u)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp [Finset.sum_ite_eq'] at hsum
  linarith

/-- Alice's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceA_le_completed {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind) :
    rawPauliOperatorDistanceA P S w W ≤
      2 * pauliOperatorDistanceA w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  simpa only [rawPauliOperatorDistanceA, pauliOperatorDistanceA, mul_assoc] using raw_completed_sum_le (S.A (pauliQuestion P W)) W
    (liftedAEffect S w.φA) (raw_transfer_liftedAEffect_add S w.φA)
    (pauliProjOnA'' P W) (idealState P w.aux) δ _
    (wrongFormEffect_ideal_norm_alice_le S w W δ _ hstate (wrongFormPauliMass_alice_le_error hwin W))

/-- Bob's raw prescribed-answer distance is controlled by the completed
distance, state error, and malformed-answer rejection mass. -/
theorem raw_pauli_operator_distanceB_le_completed {P : AdmissibleParams} {ε δ : ℝ}
    (S : Strategy (pauliBasisTest P)) (hwin : 1 - ε ≤ S.value)
    (w : PauliSoundnessWitness P S)
    (hstate : ‖isometryTensor w.φA w.φB S.ψ - idealState P w.aux‖ ≤ δ)
    (W : PauliKind) :
    rawPauliOperatorDistanceB P S w W ≤
      2 * pauliOperatorDistanceB w W + 4 * δ ^ 2 +
        4 * (Fintype.card PauliEdge : ℝ) * ε := by
  simpa only [rawPauliOperatorDistanceB, pauliOperatorDistanceB, mul_assoc] using raw_completed_sum_le (S.B (pauliQuestion P W)) W
    (liftedBEffect S w.φB) (raw_transfer_liftedBEffect_add S w.φB)
    (pauliProjOnB'' P W) (idealState P w.aux) δ _
    (wrongFormEffect_ideal_norm_bob_le S w W δ _ hstate (wrongFormPauliMass_bob_le_error S hwin W))

end

end MIPStarRE.QPBT
