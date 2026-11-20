module

public import QPBT.Test.Soundness.NaimarkReduction
public import QPBT.Test.Soundness.RangeProjection

/-!
# Pauli operator transfer through Naimark compression

The questionwise Naimark dilation preserves the complete Pauli readout only
after ground-slice compression.  This module proves the corresponding
state-dependent transfer for both players.  The range projection is retained
on both sides of every dilated effect, and the opposite ideal Pauli family is
used on the EPR state to control the second range defect.

## References

This is a formalization-only support result for `thm:pauli`, whose source
statement is at
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:1426-1447`.
The projective reduction and the final isometry passage are at
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:160-190,1862-1876`.
The omitted range-projection calculation is documented in
`docs/paper-gaps/qpbt_extraction-transfer.tex` and issue Dengnifer/MIPStarRE-QPBT-bak#604.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum MagicSquareRigidity DistanceCalculus

noncomputable section

section

variable {P : AdmissibleParams} {G : Game} (S : Strategy G) {ιA' ιB' : Type*} [Fintype ιA']
  [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']

theorem liftedAEffect_eq_tensor
    (φ : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P)) (M : Op S.ιA) :
    liftedAEffect S (ιB' := ιB') φ M = heteroKron (conjIsometry φ M) 1 := by
  ext i j
  simp [liftedAEffect, heteroKron, Matrix.one_apply]

theorem liftedBEffect_eq_tensor
    (φ : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P)) (M : Op S.ιB) :
    liftedBEffect S (ιA' := ιA') φ M = heteroKron 1 (conjIsometry φ M) := by
  ext i j
  simp [liftedBEffect, heteroKron, Matrix.one_apply]

end

section

variable {ι κ : Type} [Fintype ι]

private theorem naimark_isProj_conjIsometry [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    {Q : Op ι} (hQ : IsProj Q) : IsProj (conjIsometry φ Q) := by
  constructor
  · change _ = conjIsometry φ Q
    rw [conjIsometry_mul, hQ.isIdempotentElem.eq]
  · change _ = conjIsometry φ Q
    simp [conjIsometry_eq, Matrix.star_eq_conjTranspose, hQ.isSelfAdjoint.isHermitian.eq, Matrix.mul_assoc]

end

section

variable {α ι κ : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem naimark_left_sum_adjoint_mul_le_one
    (N : α → Op ι) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (heteroKron (N a) (1 : Op κ))ᴴ * heteroKron (N a) 1 ≤ 1 := by
  change ∑ a, (MIPStarRE.LDT.leftTensor (N a))ᴴ *
    MIPStarRE.LDT.leftTensor (N a) ≤ 1
  simpa only [← MIPStarRE.LDT.leftTensor_finset_sum,
    MIPStarRE.LDT.leftTensor_one, MIPStarRE.LDT.leftTensor_conjTranspose,
    MIPStarRE.LDT.leftTensor_mul_leftTensor] using (MIPStarRE.LDT.leftTensor_mono (ι₂ := κ) hN)

private theorem naimark_right_sum_adjoint_mul_le_one
    (N : α → Op κ) (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (heteroKron (1 : Op ι) (N a))ᴴ * heteroKron 1 (N a) ≤ 1 := by
  change ∑ a, (MIPStarRE.LDT.rightTensor (N a))ᴴ *
    MIPStarRE.LDT.rightTensor (N a) ≤ 1
  simpa only [← MIPStarRE.LDT.rightTensor_finset_sum,
    MIPStarRE.LDT.rightTensor_one, MIPStarRE.LDT.rightTensor_conjTranspose,
    MIPStarRE.LDT.rightTensor_mul_rightTensor] using (MIPStarRE.LDT.rightTensor_mono (ι₁ := ι) hN)

end

private theorem naimark_sum_conjIsometry_adjoint_mul_le_one {α ι κ : Type}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    {N : α → Op ι} (hN : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (conjIsometry φ (N a))ᴴ * conjIsometry φ (N a) ≤ 1 := by
  have heq (a : α) : (conjIsometry φ (N a))ᴴ * conjIsometry φ (N a) =
      isometryMatrix φ * ((N a)ᴴ * N a) * (isometryMatrix φ)ᴴ := by
    simp [conjIsometry_eq, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    simp [← Matrix.mul_assoc, isometryMatrix_conjTranspose_mul, Matrix.one_mul]
  simp_rw [heq]
  have hsum : (∑ a, isometryMatrix φ * ((N a)ᴴ * N a) *
      (isometryMatrix φ)ᴴ) =
      isometryMatrix φ * (∑ a, (N a)ᴴ * N a) * (isometryMatrix φ)ᴴ := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [hsum]
  calc
    _ ≤ isometryMatrix φ * (1 : Op ι) * (isometryMatrix φ)ᴴ := by
      rw [Matrix.le_iff]
      convert (Matrix.le_iff.mp hN).mul_mul_conjTranspose_same (isometryMatrix φ)
        using 1; simp [Matrix.mul_sub, Matrix.sub_mul]
    _ ≤ 1 := by
      simp
      exact isometryMatrix_mul_conjTranspose_le_one φ

section

variable {P : AdmissibleParams} {G : Game} {α : Type} [Fintype α] (S : Strategy G)
  {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']

private theorem liftedA_sum_adjoint_mul_le_one
    (φ : EuclideanSpace ℂ S.ιA →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιA' × PauliRegister P))
    (M : Measurement α S.ιA) :
    ∑ a, (liftedAEffect S (ιB' := ιB') φ (M.effect a))ᴴ *
      liftedAEffect S φ (M.effect a) ≤ 1 := by
  classical
  simp only [liftedAEffect_eq_tensor]
  exact naimark_left_sum_adjoint_mul_le_one _
    (naimark_sum_conjIsometry_adjoint_mul_le_one φ
      (measurement_sum_adjoint_mul_le_one M))

private theorem liftedB_sum_adjoint_mul_le_one
    (φ : EuclideanSpace ℂ S.ιB →ₗᵢ[ℂ]
      EuclideanSpace ℂ (ιB' × PauliRegister P))
    (M : Measurement α S.ιB) :
    ∑ a, (liftedBEffect S (ιA' := ιA') φ (M.effect a))ᴴ *
      liftedBEffect S φ (M.effect a) ≤ 1 := by
  classical
  simp only [liftedBEffect_eq_tensor]
  exact naimark_right_sum_adjoint_mul_le_one _
    (naimark_sum_conjIsometry_adjoint_mul_le_one φ
      (measurement_sum_adjoint_mul_le_one M))

end

section

variable {ι : Type*} [Fintype ι]

private theorem naimark_norm_add_three_sq_le
    (x y z : EuclideanSpace ℂ ι) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (show ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ from norm_add₃_le) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
    sq_nonneg (‖y‖ - ‖z‖)]

private theorem naimark_apply_sub_operator
    [DecidableEq ι] (A B : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (A - B) v =
      applyOperatorToState A v - applyOperatorToState B v := by
  simp [applyOperatorToState]

end

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
  have hcontract (v : EuclideanSpace ℂ ι)  :=
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_applyOperatorToState_le (conjTranspose_mul_le_one_of_isProj hQ) v) 2
  have hvanish : applyOperatorToState (1 - Q) theta = 0 := by
    simp [applyOperatorToState, show Matrix.toEuclideanLin Q theta = theta from hfix]
  have hrange : ‖applyOperatorToState (1 - Q) delta‖ ^ 2 ≤
      ‖delta - theta‖ ^ 2 := by
    have h := norm_applyOperatorToState_le
      (conjTranspose_mul_le_one_of_isProj hQ.one_sub) (delta - theta)
    simp [applyOperatorToState_sub, hvanish] at h
    gcongr
  have hn := (sum_norm_mul_apply_le N (1 - Q) delta hN).trans hrange
  have hr := (sum_norm_mul_apply_le R (1 - Q) delta hR).trans hrange
  have hpoint (a : α) :
      ‖applyOperatorToState (Q * N a * Q - T a) delta‖ ^ 2 ≤
        3 * (‖applyOperatorToState (N a - T a) delta‖ ^ 2 +
          ‖applyOperatorToState (N a * (1 - Q)) delta‖ ^ 2 +
          ‖applyOperatorToState (R a * (1 - Q)) delta‖ ^ 2) := by
    have hs : Q * N a * Q - T a =
        Q * (N a - T a) - Q * (N a * (1 - Q)) - (1 - Q) * T a := by
      noncomm_ring
    have hm : applyOperatorToState ((1 - Q) * T a) delta =
        applyOperatorToState (R a * (1 - Q)) delta := by
      rw [applyOperatorToState_mul, hmirror, ← applyOperatorToState_mul]
      simp [sub_mul, mul_sub, hcomm]
    rw [hs, naimark_apply_sub_operator, naimark_apply_sub_operator, hm, applyOperatorToState_mul, applyOperatorToState_mul,
      sub_eq_add_neg, sub_eq_add_neg]
    have h := naimark_norm_add_three_sq_le
      (applyOperatorToState Q (applyOperatorToState (N a - T a) delta))
      (-applyOperatorToState Q (applyOperatorToState (N a * (1 - Q)) delta))
      (-applyOperatorToState (R a * (1 - Q)) delta)
    simp at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (hcontract _) (hcontract _)) le_rfl) (by norm_num))
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hpoint a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  nlinarith

section

variable (P : AdmissibleParams)

private def idealPauliMeasurement (W : PauliKind) :
    Measurement (PauliRegister P) (PauliRegister P) :=
  Measurement.ofSumEqOne (pauliProj W) (fun h => (posSemidef_pauliProj W h).nonneg)
    (sum_pauliProj_eq_one W)

section

variable {ιA' ιB' : Type} [Fintype ιA'] [DecidableEq ιA'] [Fintype ιB'] [DecidableEq ιB']

private theorem pauliProjOnA_eq_tensor (W : PauliKind) (h : PauliRegister P) :
    pauliProjOnA'' P (ιA' := ιA') (ιB' := ιB') W h =
      heteroKron (heteroKron 1 (pauliProj W h)) 1 := by
  ext i j
  simp [pauliProjOnA'', heteroKron, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

private theorem pauliProjOnB_eq_tensor (W : PauliKind) (h : PauliRegister P) :
    pauliProjOnB'' P (ιA' := ιA') (ιB' := ιB') W h =
      heteroKron 1 (heteroKron 1 (pauliProj W h)) := by
  ext i j
  simp [pauliProjOnB'', heteroKron, Matrix.one_apply, ite_and]
  split_ifs <;> simp_all

private theorem idealState_transpose
    (aux : EuclideanSpace ℂ (ιA' × ιB')) (M : Op (PauliRegister P)) :
    applyOperatorToState (heteroKron (heteroKron 1 M) 1) (idealState P aux) =
      applyOperatorToState (heteroKron 1 (heteroKron 1 Mᵀ)) (idealState P aux) := by
  ext p
  simp [applyOperatorToState, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, heteroKron, Matrix.kronecker, Matrix.one_apply,
    idealState, eprState, Fintype.sum_prod_type, mul_comm]

private theorem idealState_pauli_mirror
    (aux : EuclideanSpace ℂ (ιA' × ιB')) (W : PauliKind)
    (h : PauliRegister P) :
    applyOperatorToState (pauliProjOnA'' P W h) (idealState P aux) =
      applyOperatorToState (pauliProjOnB'' P W h) (idealState P aux) := by
  simpa [pauliProjOnA_eq_tensor, pauliProjOnB_eq_tensor, pauliProj_transpose] using idealState_transpose P aux (pauliProj W h)

end

end

/-- Pullback of a dilated, postprocessed effect is its ground-projection sandwich. -/
private theorem naimark_postprocess_sandwich {α β ι κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (φ : EuclideanSpace ℂ (ι × Option α) →ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (a₀ : α) (M : Measurement α ι) (f : α → β) (b : β) :
    conjIsometry (φ.comp (naimarkEmbedding ι α)) ((M.postprocess f).effect b) =
      conjIsometry φ (groundProjection ι α) *
        conjIsometry φ (((dilatedMeasurement a₀ M).postprocess f).effect b) *
        conjIsometry φ (groundProjection ι α) := by
  let N := (dilatedMeasurement a₀ M).postprocess f
  have he : naimarkCompression (N.effect b) = (M.postprocess f).effect b := by
    change (N.compressAt none).effect b = _
    simp only [N, MIPStarRE.Quantum.Measurement.compressAt_postprocess, Measurement.compressAt_dilatedMeasurement]
  rw [← he, conjIsometry_comp_naimarkEmbedding, naimarkInflation_naimarkCompression,
    conjIsometry_mul, conjIsometry_mul]

variable (P : AdmissibleParams) (S : Strategy (pauliBasisTest P))
  (w : PauliSoundnessWitness P (pauliNaimarkStrategy S)) (W : PauliKind)

set_option maxHeartbeats 800000 in
-- Finite-register matrix algebra and nested finite sums make this proof
-- expensive to elaborate.
/-- Alice's complete Pauli operator-family distance after Naimark pullback is
at most three times the dilated distance plus six times the squared state error.
This is a Lean-only support theorem for the source proof; its witness is an
explicit actual witness on the constructed dilation. -/
theorem pauli_naimark_operator_distanceA_le :
    pauliOperatorDistanceA (pauliNaimarkWitness P S w) W ≤
      3 * pauliOperatorDistanceA w W +
        6 * ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ -
          idealState P w.aux‖ ^ 2 := by
  let Q := liftedAEffect _ (ιB' := w.ιB') w.φA
    (groundProjection S.ιA (PauliAnswer P))
  have hfix : applyOperatorToState Q
      (isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ) =
        isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ := by
    dsimp only [Q]
    rw [liftedAEffect_eq_tensor, applyOperatorToState_leftTensor_conjIsometry]
    have hp : padState none
        none S.ψ =
          naimarkDilatedState (PauliAnswer P) S.ψ :=
      pauliNaimarkStrategy_state P S
    simp [hp, applyOperatorToState_leftTensor_groundProjection]
  have hcomm (h : PauliRegister P) : Q * pauliProjOnB'' P W h =
      pauliProjOnB'' P W h * Q := by
    simp [Q, liftedAEffect_eq_tensor, pauliProjOnB_eq_tensor, heteroKron_mul]
  have hb := sum_norm_compression_sub_sq_le
    (fun h => liftedAEffect (pauliNaimarkStrategy S) (ιB' := w.ιB') w.φA
      ((((pauliNaimarkStrategy S).A (pauliQuestion P W)).postprocess
        pauliAnswerOrZero).effect h))
    _ _ Q (by
      dsimp only [Q]
      rw [liftedAEffect_eq_tensor]
      classical
      constructor
      · change _ = heteroKron _ 1
        simp [heteroKron_mul, (naimark_isProj_conjIsometry w.φA (isProj_groundProjection S.ιA (PauliAnswer P))).isIdempotentElem.eq]
      · change _ = heteroKron _ 1
        simp [heteroKron, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
          (naimark_isProj_conjIsometry w.φA (isProj_groundProjection S.ιA (PauliAnswer P))).isSelfAdjoint.isHermitian.eq])
    (liftedA_sum_adjoint_mul_le_one _ w.φA _)
    ((by
       simp only [pauliProjOnB_eq_tensor]
       exact measurement_sum_adjoint_mul_le_one
         (rightPlacedMeasurement (rightPlacedMeasurement (idealPauliMeasurement P W)))))
    _
    _ hfix (idealState_pauli_mirror P w.aux W) hcomm
  apply le_of_eq_of_le ?_ (by simpa only [pauliOperatorDistanceA, norm_sub_rev] using hb)
  apply Finset.sum_congr rfl
  intro h _
  simp only [Q, pauliNaimarkWitness, pauliNaimarkEmbeddingA, liftedAEffect_eq_tensor,
    heteroKron_mul, Matrix.one_mul, naimark_postprocess_sandwich w.φA (default : PauliAnswer P)]

set_option maxHeartbeats 800000 in
-- The symmetric finite-register matrix calculation likewise requires extra
-- elaboration heartbeats.
/-- Bob's complete Pauli operator-family distance after Naimark pullback has
the same dimension-independent bound as Alice's. -/
theorem pauli_naimark_operator_distanceB_le :
    pauliOperatorDistanceB (pauliNaimarkWitness P S w) W ≤
      3 * pauliOperatorDistanceB w W +
        6 * ‖isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ -
          idealState P w.aux‖ ^ 2 := by
  let Q := liftedBEffect _ (ιA' := w.ιA') w.φB
    (groundProjection S.ιB (PauliAnswer P))
  have hfix : applyOperatorToState Q
      (isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ) =
        isometryTensor w.φA w.φB (pauliNaimarkStrategy S).ψ := by
    dsimp only [Q]
    rw [liftedBEffect_eq_tensor, applyOperatorToState_rightTensor_conjIsometry]
    have hp : padState none
        none S.ψ =
          naimarkDilatedState (PauliAnswer P) S.ψ :=
      pauliNaimarkStrategy_state P S
    simp [hp, applyOperatorToState_rightTensor_groundProjection]
  have hcomm (h : PauliRegister P) : Q * pauliProjOnA'' P W h =
      pauliProjOnA'' P W h * Q := by
    simp [Q, liftedBEffect_eq_tensor, pauliProjOnA_eq_tensor, heteroKron_mul]
  have hb := sum_norm_compression_sub_sq_le
    (fun h => liftedBEffect (pauliNaimarkStrategy S) (ιA' := w.ιA') w.φB
      ((((pauliNaimarkStrategy S).B (pauliQuestion P W)).postprocess
        pauliAnswerOrZero).effect h))
    _ _ Q (by
      dsimp only [Q]
      rw [liftedBEffect_eq_tensor]
      classical
      constructor
      · change _ = heteroKron 1 _
        simp [heteroKron_mul, (naimark_isProj_conjIsometry w.φB (isProj_groundProjection S.ιB (PauliAnswer P))).isIdempotentElem.eq]
      · change _ = heteroKron 1 _
        simp [heteroKron, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
          (naimark_isProj_conjIsometry w.φB (isProj_groundProjection S.ιB (PauliAnswer P))).isSelfAdjoint.isHermitian.eq])
    (liftedB_sum_adjoint_mul_le_one _ w.φB _)
    ((by
       simp only [pauliProjOnA_eq_tensor]
       exact measurement_sum_adjoint_mul_le_one
         (leftPlacedMeasurement (rightPlacedMeasurement (idealPauliMeasurement P W)))))
    _
    _ hfix
    (fun h => (idealState_pauli_mirror P w.aux W h).symm) hcomm
  apply le_of_eq_of_le ?_ (by simpa only [pauliOperatorDistanceB, norm_sub_rev] using hb)
  apply Finset.sum_congr rfl
  intro h _
  simp only [Q, pauliNaimarkWitness, pauliNaimarkEmbeddingB, liftedBEffect_eq_tensor,
    heteroKron_mul, Matrix.one_mul, naimark_postprocess_sandwich w.φB (default : PauliAnswer P)]

end

end MIPStarRE.QPBT
