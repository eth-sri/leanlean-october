module

public import QPBT.Test.Soundness.NaimarkReduction
public import QPBT.Test.Soundness.RangeProjection

/-!
# Pauli operator transfer through Naimark compression
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus

noncomputable section

private theorem liftedAEffect_eq_tensor {P : AdmissibleParams} {G : Game} (S : Strategy G)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (M : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φ M = heteroKron (conjIsometry φ M) 1 := by
  ext i j
  simp [liftedAEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem liftedBEffect_eq_tensor {P : AdmissibleParams} {G : Game} (S : Strategy G)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P)) (M : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φ M = heteroKron 1 (conjIsometry φ M) := by
  ext i j
  simp [liftedBEffect, heteroKron, Matrix.kronecker, Matrix.one_apply]

private theorem naimark_isProj_conjIsometry {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    {Q : Op ι} (hQ : IsProj Q) : IsProj (conjIsometry φ Q) :=
  ⟨by change conjIsometry φ Q * conjIsometry φ Q = _
      rw [conjIsometry_mul, hQ.isIdempotentElem.eq],
   by change star (conjIsometry φ Q) = _
      simp [conjIsometry_eq, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        hQ.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]⟩

private theorem naimark_left_isProj {ι κ : Type} [Fintype ι]
    [Fintype κ] [DecidableEq κ] {Q : Op ι} (hQ : IsProj Q) :
    IsProj (heteroKron Q (1 : Op κ)) := by
  classical
  exact ⟨by change heteroKron Q 1 * heteroKron Q 1 = _
            rw [heteroKron_mul, hQ.isIdempotentElem.eq, Matrix.one_mul],
         by change star (heteroKron Q (1 : Op κ)) = _
            simp [heteroKron, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
              hQ.isSelfAdjoint.isHermitian.eq]⟩

private theorem naimark_right_isProj {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {Q : Op κ} (hQ : IsProj Q) :
    IsProj (heteroKron (1 : Op ι) Q) := by
  classical
  exact ⟨by change heteroKron 1 Q * heteroKron 1 Q = _
            rw [heteroKron_mul, hQ.isIdempotentElem.eq, Matrix.one_mul],
         by change star (heteroKron (1 : Op ι) Q) = _
            simp [heteroKron, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
              hQ.isSelfAdjoint.isHermitian.eq]⟩

private theorem naimark_left_sum_adjoint_mul_le_one {α ι κ : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : α → Op ι) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (heteroKron (N a) (1 : Op κ))ᴴ * heteroKron (N a) 1 ≤ 1 := by
  change ∑ a, (MIPStarRE.LDT.leftTensor (ι₂ := κ) (N a))ᴴ *
    MIPStarRE.LDT.leftTensor (N a) ≤ 1
  simpa only [← MIPStarRE.LDT.leftTensor_finset_sum,
    MIPStarRE.LDT.leftTensor_one, MIPStarRE.LDT.leftTensor_conjTranspose,
    MIPStarRE.LDT.leftTensor_mul_leftTensor] using MIPStarRE.LDT.leftTensor_mono (ι₂ := κ) hN

private theorem naimark_right_sum_adjoint_mul_le_one {α ι κ : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : α → Op κ) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (heteroKron (1 : Op ι) (N a))ᴴ * heteroKron 1 (N a) ≤ 1 := by
  change ∑ a, (MIPStarRE.LDT.rightTensor (ι₁ := ι) (N a))ᴴ *
    MIPStarRE.LDT.rightTensor (N a) ≤ 1
  simpa only [← MIPStarRE.LDT.rightTensor_finset_sum,
    MIPStarRE.LDT.rightTensor_one, MIPStarRE.LDT.rightTensor_conjTranspose,
    MIPStarRE.LDT.rightTensor_mul_rightTensor] using MIPStarRE.LDT.rightTensor_mono (ι₁ := ι) hN

private theorem naimark_sum_conjIsometry_adjoint_mul_le_one {α ι κ : Type}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (N : α → Op ι) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (conjIsometry φ (N a))ᴴ * conjIsometry φ (N a) ≤ 1 := by
  have heq (a : α) : (conjIsometry φ (N a))ᴴ * conjIsometry φ (N a) =
      isometryMatrix φ * ((N a)ᴴ * N a) * (isometryMatrix φ)ᴴ := by
    simp only [conjIsometry_eq, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (isometryMatrix φ)ᴴ (isometryMatrix φ),
      isometryMatrix_conjTranspose_mul, Matrix.one_mul]
  simp_rw [heq]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum]
  calc
    _ ≤ isometryMatrix φ * (1 : Op ι) * (isometryMatrix φ)ᴴ := by
      rw [Matrix.le_iff]
      convert (Matrix.le_iff.mp hN).mul_mul_conjTranspose_same (isometryMatrix φ)
        using 1; simp [Matrix.mul_sub, Matrix.sub_mul]
    _ ≤ 1 := by rw [Matrix.mul_one]; exact isometryMatrix_mul_conjTranspose_le_one φ

private theorem liftedA_sum_adjoint_mul_le_one {P : AdmissibleParams} {G : Game}
    {α : Type} [Fintype α] (S : Strategy G)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P))
    (M : Measurement α S.ιA) :
    ∑ a, (liftedAEffect S (ιB' := ιB') φ (M.effect a))ᴴ *
      liftedAEffect S φ (M.effect a) ≤ 1 := by
  classical
  simp only [liftedAEffect_eq_tensor]
  exact naimark_left_sum_adjoint_mul_le_one _
    (naimark_sum_conjIsometry_adjoint_mul_le_one φ M.effect
      (measurement_sum_adjoint_mul_le_one M))

private theorem liftedB_sum_adjoint_mul_le_one {P : AdmissibleParams} {G : Game}
    {α : Type} [Fintype α] (S : Strategy G)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (φ : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P))
    (M : Measurement α S.ιB) :
    ∑ a, (liftedBEffect S (ιA' := ιA') φ (M.effect a))ᴴ *
      liftedBEffect S φ (M.effect a) ≤ 1 := by
  classical
  simp only [liftedBEffect_eq_tensor]
  exact naimark_right_sum_adjoint_mul_le_one _
    (naimark_sum_conjIsometry_adjoint_mul_le_one φ M.effect
      (measurement_sum_adjoint_mul_le_one M))

private theorem naimark_norm_add_three_sq_le {ι : Type*} [Fintype ι]
    (x y z : EuclideanSpace ℂ ι) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (show ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ from norm_add₃_le) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
    sq_nonneg (‖y‖ - ‖z‖)]

private theorem naimark_apply_sub_operator {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A B : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (A - B) v =
      applyOperatorToState A v - applyOperatorToState B v := by
  simp [applyOperatorToState]

private theorem sum_norm_compression_sub_sq_le {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (N T R : α → Op ι) (Q : Op ι) (hQ : IsProj Q)
    (hN : ∑ a, (N a)ᴴ * N a ≤ 1) (hR : ∑ a, (R a)ᴴ * R a ≤ 1)
    (theta delta : EuclideanSpace ℂ ι)
    (hfix : applyOperatorToState Q theta = theta)
    (hmirror : ∀ a, applyOperatorToState (T a) delta =
      applyOperatorToState (R a) delta)
    (hcomm : ∀ a, Q * R a = R a * Q) :
    ∑ a, ‖applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
      3 * (∑ a, ‖applyOperatorToState (N a - T a) delta‖ ^ 2) +
        6 * ‖delta - theta‖ ^ 2 := by
  have hcontract (v : EuclideanSpace ℂ ι) :
      ‖applyOperatorToState Q v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_applyOperatorToState_le (conjTranspose_mul_le_one_of_isProj hQ) v) 2
  have hvanish : applyOperatorToState (1 - Q) theta = 0 := by
    simp [applyOperatorToState, show Matrix.toEuclideanLin Q theta = theta from hfix]
  have hrange : ‖applyOperatorToState (1 - Q) delta‖ ^ 2 ≤
      ‖delta - theta‖ ^ 2 := by
    have h := norm_applyOperatorToState_le
      (conjTranspose_mul_le_one_of_isProj hQ.one_sub) (delta - theta)
    rw [applyOperatorToState_sub, hvanish, sub_zero] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hn := (sum_norm_mul_apply_le N (1 - Q) delta hN).trans hrange
  have hr := (sum_norm_mul_apply_le R (1 - Q) delta hR).trans hrange
  have hpoint (a : α) :
      ‖applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
        3 * (‖applyOperatorToState (N a - T a) delta‖ ^ 2 +
          ‖applyOperatorToState (N a * (1 - Q)) delta‖ ^ 2 +
          ‖applyOperatorToState (R a * (1 - Q)) delta‖ ^ 2) := by
    have hs : Q * N a * Q - T a =
        Q * (N a - T a) - Q * (N a * (1 - Q)) - (1 - Q) * T a := by noncomm_ring
    have hm : applyOperatorToState ((1 - Q) * T a) delta =
        applyOperatorToState (R a * (1 - Q)) delta := by
      rw [applyOperatorToState_mul, hmirror, ← applyOperatorToState_mul]
      congr 1
      rw [sub_mul, mul_sub, one_mul, mul_one, hcomm]
    rw [hs, naimark_apply_sub_operator, naimark_apply_sub_operator,
      hm, applyOperatorToState_mul, applyOperatorToState_mul,
      sub_eq_add_neg, sub_eq_add_neg]
    have h := naimark_norm_add_three_sq_le
      (applyOperatorToState Q (applyOperatorToState (N a - T a) delta))
      (-applyOperatorToState Q (applyOperatorToState (N a * (1 - Q)) delta))
      (-applyOperatorToState (R a * (1 - Q)) delta)
    simp only [norm_neg] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (hcontract _) (hcontract _)) le_rfl) (by norm_num))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  nlinarith

private def idealPauliMeasurement (P : AdmissibleParams) (W : PauliKind) :
    Measurement (PauliRegister P) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliProj W) (fun h => (posSemidef_pauliProj W h).nonneg)
    (sum_pauliProj_eq_one W)

private theorem pauliProjOnA_eq_tensor (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind) (h : PauliRegister P) :
    pauliProjOnA'' P (ιA' := ιA') (ιB' := ιB') W h =
      heteroKron (heteroKron 1 (pauliProj W h)) 1 := by
  ext i j
  simp [pauliProjOnA'', heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

private theorem pauliProjOnB_eq_tensor (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind) (h : PauliRegister P) :
    pauliProjOnB'' P (ιA' := ιA') (ιB' := ιB') W h =
      heteroKron 1 (heteroKron 1 (pauliProj W h)) := by
  ext i j
  simp [pauliProjOnB'', heteroKron, Matrix.kronecker, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

private theorem idealState_pauli_mirror (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB']
    (aux : EuclideanSpace ℂ (ιA' × ιB')) (W : PauliKind)
    (h : PauliRegister P) :
    applyOperatorToState (pauliProjOnA'' P W h) (idealState P aux) =
      applyOperatorToState (pauliProjOnB'' P W h) (idealState P aux) := by
  rw [pauliProjOnA_eq_tensor, pauliProjOnB_eq_tensor]
  nth_rw 2 [← pauliProj_transpose W h]
  ext p
  simp [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, heteroKron, Matrix.kronecker, Matrix.one_apply,
    idealState, eprState, Fintype.sum_prod_type, mul_comm]

private theorem pauliProjOnA_sum_adjoint_mul_le_one (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind) :
    ∑ h, (pauliProjOnA'' P (ιA' := ιA') (ιB' := ιB') W h)ᴴ *
      pauliProjOnA'' P W h ≤ 1 := by
  simp only [pauliProjOnA_eq_tensor]
  exact measurement_sum_adjoint_mul_le_one
    (leftPlacedMeasurement (rightPlacedMeasurement (idealPauliMeasurement P W)))

private theorem pauliProjOnB_sum_adjoint_mul_le_one (P : AdmissibleParams)
    {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA']
    [Fintype ιB'] [DecidableEq ιB'] (W : PauliKind) :
    ∑ h, (pauliProjOnB'' P (ιA' := ιA') (ιB' := ιB') W h)ᴴ *
      pauliProjOnB'' P W h ≤ 1 := by
  simp only [pauliProjOnB_eq_tensor]
  exact measurement_sum_adjoint_mul_le_one
    (rightPlacedMeasurement (rightPlacedMeasurement (idealPauliMeasurement P W)))

private theorem naimark_conjIsometry_compressed {ι α κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ (ι × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (N : Op (ι × Option α)) :
    conjIsometry (φ.comp (naimarkEmbedding ι α)) (naimarkCompression N) =
      conjIsometry φ (groundProjection ι α) * conjIsometry φ N *
        conjIsometry φ (groundProjection ι α) := by
  rw [conjIsometry_comp_naimarkEmbedding, naimarkInflation_naimarkCompression,
    conjIsometry_mul, conjIsometry_mul]

private theorem naimark_lifted_compression_alice
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) (W : PauliKind)
    (h : PauliRegister P) :
    liftedAEffect S (ιB' := w.ιB') (pauliNaimarkWitness P S w).φA
        (((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h) =
      liftedAEffect (pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
          (groundProjection S.ιA (PauliAnswer P)) *
        liftedAEffect (pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
          ((((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess
            pauliAnswerOrZero).effect h) *
        liftedAEffect (pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
          (groundProjection S.ιA (PauliAnswer P)) := by
  have heff : naimarkCompression
      ((((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess
        pauliAnswerOrZero).effect h) =
      ((S.A (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h :=
    congrArg (fun M => M.effect h) (pauliNaimarkStrategy_pauli_compressA P S W)
  simp only [pauliNaimarkWitness, pauliNaimarkEmbeddingA,
    liftedAEffect_eq_tensor, heteroKron_mul, Matrix.one_mul, ← heff]
  exact congrArg (heteroKron · 1) (naimark_conjIsometry_compressed w.φA _)

private theorem naimark_lifted_compression_bob
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) (W : PauliKind)
    (h : PauliRegister P) :
    liftedBEffect S (ιA' := w.ιA') (pauliNaimarkWitness P S w).φB
        (((S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h) =
      liftedBEffect (pauliNaimarkStrategy P S) (ιA' := w.ιA') w.φB
          (groundProjection S.ιB (PauliAnswer P)) *
        liftedBEffect (pauliNaimarkStrategy P S) (ιA' := w.ιA') w.φB
          ((((pauliNaimarkStrategy P S).B (pauliQuestion P W)).postprocess
            pauliAnswerOrZero).effect h) *
        liftedBEffect (pauliNaimarkStrategy P S) (ιA' := w.ιA') w.φB
          (groundProjection S.ιB (PauliAnswer P)) := by
  have heff : naimarkCompression
      ((((pauliNaimarkStrategy P S).B (pauliQuestion P W)).postprocess
        pauliAnswerOrZero).effect h) =
      ((S.B (pauliQuestion P W)).postprocess pauliAnswerOrZero).effect h :=
    congrArg (fun M => M.effect h) (pauliNaimarkStrategy_pauli_compressB P S W)
  simp only [pauliNaimarkWitness, pauliNaimarkEmbeddingB,
    liftedBEffect_eq_tensor, heteroKron_mul, Matrix.one_mul, ← heff]
  exact congrArg (heteroKron 1 ·) (naimark_conjIsometry_compressed w.φB _)

set_option maxHeartbeats 800000 in
-- Finite-register matrix algebra and nested finite sums make this proof
-- expensive to elaborate.
/-- Alice's complete Pauli operator-family distance after Naimark pullback is
at most three times the dilated distance plus six times the squared state error. -/
theorem pauli_naimark_operator_distanceA_le
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) (W : PauliKind) :
    pauliOperatorDistanceA P S (pauliNaimarkWitness P S w) W ≤
      3 * pauliOperatorDistanceA P (pauliNaimarkStrategy P S) w W +
        6 * ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ -
          idealState P w.aux‖ ^ 2 := by
  let Q := liftedAEffect (pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
    (groundProjection S.ιA (PauliAnswer P))
  have hQ : IsProj Q := by
    dsimp only [Q]; rw [liftedAEffect_eq_tensor]
    exact naimark_left_isProj (naimark_isProj_conjIsometry w.φA
      (isProj_groundProjection S.ιA (PauliAnswer P)))
  have hfix : applyOperatorToState Q
      (isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ) =
        isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ := by
    dsimp only [Q]
    rw [liftedAEffect_eq_tensor, applyOperatorToState_leftTensor_conjIsometry,
      show padState (none : Option (PauliAnswer P)) (none : Option (PauliAnswer P)) S.ψ =
        naimarkDilatedState (PauliAnswer P) S.ψ from pauliNaimarkStrategy_state P S]
    erw [applyOperatorToState_leftTensor_groundProjection (PauliAnswer P) S.ψ]
  have hcomm (h : PauliRegister P) : Q * pauliProjOnB'' P W h =
      pauliProjOnB'' P W h * Q := by
    dsimp only [Q]; rw [liftedAEffect_eq_tensor, pauliProjOnB_eq_tensor]
    simp only [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  have hb := sum_norm_compression_sub_sq_le
    (fun h => liftedAEffect (pauliNaimarkStrategy P S) (ιB' := w.ιB') w.φA
      ((((pauliNaimarkStrategy P S).A (pauliQuestion P W)).postprocess
        pauliAnswerOrZero).effect h))
    (pauliProjOnA'' P W) (pauliProjOnB'' P W) Q hQ
    (liftedA_sum_adjoint_mul_le_one _ w.φA _)
    (pauliProjOnB_sum_adjoint_mul_le_one P W)
    (isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ)
    (idealState P w.aux) hfix (idealState_pauli_mirror P w.aux W) hcomm
  unfold pauliOperatorDistanceA
  refine le_of_eq_of_le (Finset.sum_congr rfl fun h _ => ?_)
    (by simpa only [pauliOperatorDistanceA, norm_sub_rev] using hb)
  have hcomp := naimark_lifted_compression_alice P S w W h
  dsimp only [pauliNaimarkWitness] at hcomp ⊢
  convert congrArg
    (fun M : Op ((w.ιA' × PauliRegister P) × (w.ιB' × PauliRegister P)) =>
      ‖applyOperatorToState (M - pauliProjOnA'' P W h) (idealState P w.aux)‖ ^ 2) hcomp using 1

set_option maxHeartbeats 800000 in
-- The symmetric finite-register matrix calculation likewise requires extra
-- elaboration heartbeats.
/-- Bob's complete Pauli operator-family distance after Naimark pullback has
the same dimension-independent bound as Alice's. -/
theorem pauli_naimark_operator_distanceB_le
    (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
    (w : PauliSoundnessWitness P (pauliNaimarkStrategy P S)) (W : PauliKind) :
    pauliOperatorDistanceB P S (pauliNaimarkWitness P S w) W ≤
      3 * pauliOperatorDistanceB P (pauliNaimarkStrategy P S) w W +
        6 * ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ -
          idealState P w.aux‖ ^ 2 := by
  let Q := liftedBEffect (pauliNaimarkStrategy P S) (ιA' := w.ιA') w.φB
    (groundProjection S.ιB (PauliAnswer P))
  have hQ : IsProj Q := by
    dsimp only [Q]; rw [liftedBEffect_eq_tensor]
    exact naimark_right_isProj (naimark_isProj_conjIsometry w.φB
      (isProj_groundProjection S.ιB (PauliAnswer P)))
  have hfix : applyOperatorToState Q
      (isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ) =
        isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ := by
    dsimp only [Q]
    rw [liftedBEffect_eq_tensor, applyOperatorToState_rightTensor_conjIsometry,
      show padState (none : Option (PauliAnswer P)) (none : Option (PauliAnswer P)) S.ψ =
        naimarkDilatedState (PauliAnswer P) S.ψ from pauliNaimarkStrategy_state P S]
    erw [applyOperatorToState_rightTensor_groundProjection (PauliAnswer P) S.ψ]
  have hcomm (h : PauliRegister P) : Q * pauliProjOnA'' P W h =
      pauliProjOnA'' P W h * Q := by
    dsimp only [Q]; rw [liftedBEffect_eq_tensor, pauliProjOnA_eq_tensor]
    simp only [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  have hb := sum_norm_compression_sub_sq_le
    (fun h => liftedBEffect (pauliNaimarkStrategy P S) (ιA' := w.ιA') w.φB
      ((((pauliNaimarkStrategy P S).B (pauliQuestion P W)).postprocess
        pauliAnswerOrZero).effect h))
    (pauliProjOnB'' P W) (pauliProjOnA'' P W) Q hQ
    (liftedB_sum_adjoint_mul_le_one _ w.φB _)
    (pauliProjOnA_sum_adjoint_mul_le_one P W)
    (isometryTensor w.φA w.φB (pauliNaimarkStrategy P S).ψ)
    (idealState P w.aux) hfix
    (fun h => (idealState_pauli_mirror P w.aux W h).symm) hcomm
  unfold pauliOperatorDistanceB
  refine le_of_eq_of_le (Finset.sum_congr rfl fun h _ => ?_)
    (by simpa only [pauliOperatorDistanceB, norm_sub_rev] using hb)
  have hcomp := naimark_lifted_compression_bob P S w W h
  dsimp only [pauliNaimarkWitness] at hcomp ⊢
  convert congrArg
    (fun M : Op ((w.ιA' × PauliRegister P) × (w.ιB' × PauliRegister P)) =>
      ‖applyOperatorToState (M - pauliProjOnB'' P W h) (idealState P w.aux)‖ ^ 2) hcomp using 1

end

end MIPStarRE.QPBT
