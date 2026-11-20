module

public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer

/-!
# Transfer of Bob's anticommutator estimate along the projective dilation

The right-placed counterpart of the Alice-side anticommutator transfer in
`Rigidity/Transfer.lean`: Bob's dilated observables leak out of the ground
slice by at most the forward cell-consistency defects, and the product of the
compressed observables is compared with the product of the dilated ones on the
dilated state through Alice's partner observable.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

section

variable (S : Strategy msGame) (i : Fin 6) (x : MsType) (f : MsAnswer → ZMod 2) (k : Fin 3)

/-- Alice's dilated observable of a totalized bit, typed on the enlarged local
space.  Formalization-only abbreviation. -/
abbrev dilatedObsAf :
    Op (S.ιA × Option MsAnswer) :=
  obsOf (((msDilatedStrategy S).A x).postprocess f)

/-- The inflation of Bob's original observable is the ground compression of
his dilated observable. -/
theorem naimarkInflation_obs_B (y : MsType) :
    naimarkInflation (α := MsAnswer) (obsOf ((S.B y).postprocess msBitOrZero)) =
      groundProjection S.ιB MsAnswer * dilatedObsB S y msBitOrZero *
        groundProjection S.ιB MsAnswer := by
  change naimarkInflation (((S.B y).postprocess msBitOrZero).effect 0 -
    ((S.B y).postprocess msBitOrZero).effect 1) =
    groundProjection S.ιB MsAnswer *
      (dilatedEffectB S y msBitOrZero 0 - dilatedEffectB S y msBitOrZero 1) *
      groundProjection S.ιB MsAnswer
  rw [naimarkInflation_sub, naimarkInflation_postprocess_B, naimarkInflation_postprocess_B,
    Matrix.mul_sub, Matrix.sub_mul]

/-- Alice's dilated totalized observables are contractions. -/
theorem conjTranspose_mul_le_one_dilatedObsAf :
    (dilatedObsAf S x f)ᴴ * dilatedObsAf S x f ≤ 1 :=
  conjTranspose_mul_le_one_of_obsOf _

/-- The leakage of Bob's dilated observable out of the ground slice is bounded
by the two forward intertwining defects of its effects. -/
theorem norm_leak_obs_le_B :
    ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection S.ιB MsAnswer) *
        dilatedObsB S (.var (msConstraintVars i k)) msBitOrZero))
        (naimarkDilatedState MsAnswer S.ψ)‖ ≤
      ‖applyOperatorToState
        (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) 0) 1 -
          heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero 0))
        (naimarkDilatedState MsAnswer S.ψ)‖ +
      ‖applyOperatorToState
        (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) 1) 1 -
          heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero 1))
        (naimarkDilatedState MsAnswer S.ψ)‖ := by
  change ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection S.ιB MsAnswer) *
    (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero 0 -
      dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero 1)))
    _‖ ≤ _
  rw [Matrix.mul_sub, heteroKron_sub_right, DistanceCalculus.applyOperatorToState_sub_op]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_) <;> apply norm_rightTensor_one_sub_groundProjection_mul_le

/-- The intertwining defect of Alice's dilated constraint observable against
Bob's dilated variable observable is bounded by the two forward defects. -/
theorem norm_intertwine_obs_le_B :
    ‖applyOperatorToState (heteroKron (dilatedObsAf S (.constraint i) (constraintBitOrZero k)) 1 -
        heteroKron 1 (dilatedObsB S (.var (msConstraintVars i k)) msBitOrZero))
        (naimarkDilatedState MsAnswer S.ψ)‖ ≤
      ‖applyOperatorToState
        (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) 0) 1 -
          heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero 0))
        (naimarkDilatedState MsAnswer S.ψ)‖ +
      ‖applyOperatorToState
        (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) 1) 1 -
          heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero 1))
        (naimarkDilatedState MsAnswer S.ψ)‖ := by
  have hsplit : heteroKron (dilatedObsAf S (.constraint i) (constraintBitOrZero k)) 1 -
      heteroKron 1 (dilatedObsB S (.var (msConstraintVars i k)) msBitOrZero) =
      (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) 0) 1 -
        heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero 0)) -
      (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) 1) 1 -
        heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero 1)) := by
    change heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) 0 -
      dilatedEffectA S (.constraint i) (constraintBitOrZero k) 1) 1 -
      heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero 0 -
        dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero 1) = _
    rw [heteroKron_sub_left, heteroKron_sub_right]
    abel
  rw [hsplit, DistanceCalculus.applyOperatorToState_sub_op]
  apply norm_sub_le

end

/-- Right-placed counterpart of `norm_leftTensor_compressed_product_sub_le`. -/
theorem norm_rightTensor_compressed_product_sub_le (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB))
    (A B : Op (ιB × Option α)) (Y : Op (ιA × Option α))
    (hA : Aᴴ * A ≤ 1) (hY : Yᴴ * Y ≤ 1) :
    ‖applyOperatorToState (heteroKron 1 (groundProjection ιB α * A * groundProjection ιB α *
        (groundProjection ιB α * B * groundProjection ιB α) - A * B))
        (naimarkDilatedState α ψ)‖ ≤
      ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection ιB α) * B))
        (naimarkDilatedState α ψ)‖ +
      ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection ιB α) * A))
        (naimarkDilatedState α ψ)‖ +
      ‖applyOperatorToState (heteroKron Y 1 - heteroKron 1 B) (naimarkDilatedState α ψ)‖ := by
  have hGG :=
    (isProj_groundProjection ιB α).isIdempotentElem.eq
  have hGc :=
    conjTranspose_mul_le_one_of_isProj (isProj_groundProjection ιB α)
  have h1Gc :=
    conjTranspose_mul_le_one_of_isProj (isProj_groundProjection ιB α).one_sub
  have hstep1 : applyOperatorToState (heteroKron 1 (groundProjection ιB α * A *
      groundProjection ιB α * (groundProjection ιB α * B * groundProjection ιB α)))
      (naimarkDilatedState α ψ) =
      applyOperatorToState (heteroKron 1 (groundProjection ιB α * A * groundProjection ιB α * B))
        (naimarkDilatedState α ψ) := by
    have hassoc : groundProjection ιB α * A * groundProjection ιB α *
        (groundProjection ιB α * B * groundProjection ιB α) =
        groundProjection ιB α * A * groundProjection ιB α * B * groundProjection ιB α := by
      simp only [Matrix.mul_assoc]
      simp [← Matrix.mul_assoc, hGG]
    rw [hassoc, show heteroKron 1 (groundProjection ιB α * A *
        groundProjection ιB α * B * groundProjection ιB α) =
        heteroKron 1 (groundProjection ιB α * A * groundProjection ιB α * B) *
          heteroKron 1 (groundProjection ιB α) by simp [heteroKron_mul],
      applyOperatorToState_mul, applyOperatorToState_rightTensor_groundProjection]
  have hdec : groundProjection ιB α * A * groundProjection ιB α * B - A * B =
      -(groundProjection ιB α * A * ((1 - groundProjection ιB α) * B)) -
        ((1 - groundProjection ιB α) * A) * B := by
    noncomm_ring
  have hfirst : ‖applyOperatorToState (heteroKron 1 (groundProjection ιB α * A *
      ((1 - groundProjection ιB α) * B))) (naimarkDilatedState α ψ)‖ ≤
      ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection ιB α) * B))
        (naimarkDilatedState α ψ)‖ := by
    rw [show heteroKron 1 (groundProjection ιB α * A *
        ((1 - groundProjection ιB α) * B)) =
        heteroKron 1 (groundProjection ιB α * A) * heteroKron 1 ((1 - groundProjection ιB α) * B)
        by simp [heteroKron_mul], applyOperatorToState_mul]
    exact norm_applyOperatorToState_le
      (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_mul hGc hA)) _
  have hsecond : ‖applyOperatorToState (heteroKron 1 (((1 - groundProjection ιB α) * A) * B))
      (naimarkDilatedState α ψ)‖ ≤
      ‖applyOperatorToState (heteroKron Y 1 - heteroKron 1 B) (naimarkDilatedState α ψ)‖ +
      ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection ιB α) * A))
        (naimarkDilatedState α ψ)‖ := by
    have hcomm : heteroKron 1 ((1 - groundProjection ιB α) * A) *
        heteroKron Y 1 = heteroKron Y 1 * heteroKron 1 ((1 - groundProjection ιB α) * A) := by
      simp [heteroKron_mul]
    rw [show heteroKron 1 (((1 - groundProjection ιB α) * A) * B) =
        heteroKron 1 ((1 - groundProjection ιB α) * A) * heteroKron 1 B
        by simp [heteroKron_mul], applyOperatorToState_mul]
    have hdecB : applyOperatorToState (heteroKron 1 B) (naimarkDilatedState α ψ) =
        applyOperatorToState (heteroKron 1 B - heteroKron Y 1) (naimarkDilatedState α ψ) +
          applyOperatorToState (heteroKron Y 1) (naimarkDilatedState α ψ) := by
      simp [DistanceCalculus.applyOperatorToState_sub_op]
    rw [hdecB, applyOperatorToState_add, ← applyOperatorToState_mul _ (heteroKron Y 1), hcomm,
      applyOperatorToState_mul, DistanceCalculus.applyOperatorToState_sub_op, DistanceCalculus.applyOperatorToState_sub_op, norm_sub_rev]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · exact norm_applyOperatorToState_le (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_mul h1Gc hA)) _
    · exact norm_applyOperatorToState_le (conjTranspose_mul_le_one_leftTensor hY) _
  calc _ =
        ‖applyOperatorToState (heteroKron 1 (groundProjection ιB α * A * groundProjection ιB α *
          B - A * B)) (naimarkDilatedState α ψ)‖ := by
        simp [heteroKron_sub_right, DistanceCalculus.applyOperatorToState_sub_op, hstep1]
    _ = ‖-applyOperatorToState (heteroKron 1 (groundProjection ιB α * A *
          ((1 - groundProjection ιB α) * B))) (naimarkDilatedState α ψ) -
          applyOperatorToState (heteroKron 1 (((1 - groundProjection ιB α) * A) * B))
            (naimarkDilatedState α ψ)‖ := by
        rw [hdec, heteroKron_sub_right, heteroKron_neg_right, DistanceCalculus.applyOperatorToState_sub_op,
          applyOperatorToState_neg_op]
    _ ≤ ‖applyOperatorToState (heteroKron 1 (groundProjection ιB α * A *
          ((1 - groundProjection ιB α) * B))) (naimarkDilatedState α ψ)‖ +
          ‖applyOperatorToState (heteroKron 1 (((1 - groundProjection ιB α) * A) * B))
            (naimarkDilatedState α ψ)‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        simp
    _ ≤ _ := by linarith [hfirst, hsecond]

variable {κA κB : Type} [Fintype κA] [DecidableEq κA] [Fintype κB] [DecidableEq κB]
  (S : Strategy msGame)
  (φA : EuclideanSpace ℂ (S.ιA × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
  (φB : EuclideanSpace ℂ (S.ιB × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
  (ξ : EuclideanSpace ℂ (κA × κB))

/-- Right-placed counterpart of `norm_product_transfer_le_A`. -/
theorem norm_product_transfer_le_B {A B : Op (S.ιB × Option MsAnswer)}
    (hA : Aᴴ * A ≤ 1) (hB : Bᴴ * B ≤ 1) :
    ‖applyOperatorToState
        (heteroKron 1 (conjIsometry φB (groundProjection S.ιB MsAnswer * A *
            groundProjection S.ιB MsAnswer)) *
          heteroKron 1 (conjIsometry φB (groundProjection S.ιB MsAnswer * B *
            groundProjection S.ιB MsAnswer)) -
          heteroKron 1 (conjIsometry φB A) * heteroKron 1 (conjIsometry φB B)) ξ‖ ≤
      ‖applyOperatorToState (heteroKron 1 (groundProjection S.ιB MsAnswer * A *
          groundProjection S.ιB MsAnswer * (groundProjection S.ιB MsAnswer * B *
            groundProjection S.ιB MsAnswer) - A * B)) (naimarkDilatedState MsAnswer S.ψ)‖ +
      2 * ‖isometryTensor φA φB (naimarkDilatedState MsAnswer S.ψ) - ξ‖ := by
  have hGc :=
    conjTranspose_mul_le_one_of_isProj (isProj_groundProjection S.ιB MsAnswer)
  have hGA := conjTranspose_mul_le_one_mul (conjTranspose_mul_le_one_mul hGc hA) hGc
  have hGB := conjTranspose_mul_le_one_mul (conjTranspose_mul_le_one_mul hGc hB) hGc
  have hprod : heteroKron (1 : Op κA) (conjIsometry φB (groundProjection S.ιB MsAnswer * A *
      groundProjection S.ιB MsAnswer)) *
      heteroKron 1 (conjIsometry φB (groundProjection S.ιB MsAnswer * B *
        groundProjection S.ιB MsAnswer)) -
      heteroKron 1 (conjIsometry φB A) * heteroKron 1 (conjIsometry φB B) =
      heteroKron 1 (conjIsometry φB (groundProjection S.ιB MsAnswer * A *
        groundProjection S.ιB MsAnswer * (groundProjection S.ιB MsAnswer * B *
          groundProjection S.ιB MsAnswer) - A * B)) := by
    simp [heteroKron_mul, conjIsometry_mul, conjIsometry_sub, heteroKron_sub_right]
  rw [hprod]
  have hswap : applyOperatorToState (heteroKron 1 (conjIsometry φB
      (groundProjection S.ιB MsAnswer * A * groundProjection S.ιB MsAnswer *
        (groundProjection S.ιB MsAnswer * B * groundProjection S.ιB MsAnswer) - A * B))) ξ =
      applyOperatorToState (heteroKron 1 (conjIsometry φB
        (groundProjection S.ιB MsAnswer * A * groundProjection S.ιB MsAnswer *
          (groundProjection S.ιB MsAnswer * B * groundProjection S.ιB MsAnswer) - A * B)))
        (isometryTensor φA φB (naimarkDilatedState MsAnswer S.ψ)) -
      applyOperatorToState (heteroKron 1 (conjIsometry φB
        (groundProjection S.ιB MsAnswer * A * groundProjection S.ιB MsAnswer *
          (groundProjection S.ιB MsAnswer * B * groundProjection S.ιB MsAnswer) - A * B)))
        (isometryTensor φA φB (naimarkDilatedState MsAnswer S.ψ) - ξ) := by
    simp [applyOperatorToState_sub]
  rw [hswap]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
  · rw [applyOperatorToState_rightTensor_conjIsometry, norm_isometryTensor]
  · rw [conjIsometry_sub, heteroKron_sub_right]
    exact norm_applyOperatorToState_sub_le (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_conjIsometry φB
        (conjTranspose_mul_le_one_mul hGA hGB))) (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_conjIsometry φB
        (conjTranspose_mul_le_one_mul hA hB))) _

/-- Transfer of Bob's anticommutator estimate of `thm:ms-rigidity` from the
dilated strategy to the original one; see `ms_anticommutator_transfer_A`.
The left-hand side is `msAnticommutatorDistanceB S w` for the witness whose
isometry is the composite of the dilation embedding and `φ_B`. -/
theorem ms_anticommutator_transfer_B (ε η : ℝ)
    (hwin : 1 - ε ≤ S.value)
    (hξ : ‖isometryTensor φA φB (msDilatedStrategy S).ψ - ξ‖ ≤ η) :
    opDistSq (uniformDistribution Unit)
        (fun _ => heteroKron 1 (conjIsometry (φB.comp (naimarkEmbedding S.ιB MsAnswer))
            (obsOf ((S.B (.var 0)).postprocess msBitOrZero))) *
          heteroKron 1 (conjIsometry (φB.comp (naimarkEmbedding S.ιB MsAnswer))
            (obsOf ((S.B (.var 4)).postprocess msBitOrZero))))
        (fun _ => -(heteroKron 1 (conjIsometry (φB.comp (naimarkEmbedding S.ιB MsAnswer))
            (obsOf ((S.B (.var 4)).postprocess msBitOrZero))) *
          heteroKron 1 (conjIsometry (φB.comp (naimarkEmbedding S.ιB MsAnswer))
            (obsOf ((S.B (.var 0)).postprocess msBitOrZero))))) ξ ≤
      3 * opDistSq (uniformDistribution Unit)
        (fun _ => heteroKron 1 (conjIsometry φB
            (obsOf (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero))) *
          heteroKron 1 (conjIsometry φB
            (obsOf (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero))))
        (fun _ => -(heteroKron 1 (conjIsometry φB
            (obsOf (((msDilatedStrategy S).B (.var 4)).postprocess msBitOrZero))) *
          heteroKron 1 (conjIsometry φB
            (obsOf (((msDilatedStrategy S).B (.var 0)).postprocess msBitOrZero))))) ξ +
      15552 * ε + 48 * η ^ 2 := by
  obtain ⟨i0, k0, h0⟩ := every_variable_is_incident 0
  obtain ⟨i4, k4, h4⟩ := every_variable_is_incident 4
  have hξ' : ‖isometryTensor φA φB (naimarkDilatedState MsAnswer S.ψ) - ξ‖ ≤ η := hξ
  rw [opDistSq_uniform_unit, opDistSq_uniform_unit, conjIsometry_comp_naimarkEmbedding,
    conjIsometry_comp_naimarkEmbedding, naimarkInflation_obs_B, naimarkInflation_obs_B]
  have hXc := conjTranspose_mul_le_one_dilatedObsB S (.var 0) msBitOrZero
  have hZc := conjTranspose_mul_le_one_dilatedObsB S (.var 4) msBitOrZero
  have hleakX := norm_leak_obs_le_B S i0 k0
  have hintX := norm_intertwine_obs_le_B S i0 k0
  have hleakZ := norm_leak_obs_le_B S i4 k4
  have hintZ := norm_intertwine_obs_le_B S i4 k4
  have hsqX := sq_add_le_of_sum_sq_le _ _ ε (sum_norm_sq_intertwining_le_forward S i0 k0)
    (forward_cell_mismatch_mass_le S ε hwin i0 k0)
  have hsqZ := sq_add_le_of_sum_sq_le _ _ ε (sum_norm_sq_intertwining_le_forward S i4 k4)
    (forward_cell_mismatch_mass_le S ε hwin i4 k4)
  rw [h0] at hleakX hintX hsqX
  rw [h4] at hleakZ hintZ hsqZ
  have hdXZ := norm_rightTensor_compressed_product_sub_le MsAnswer S.ψ
    _ (dilatedObsB S (.var 4) msBitOrZero)
    _ hXc (conjTranspose_mul_le_one_dilatedObsAf S (.constraint i4) (constraintBitOrZero k4))
  have hdZX := norm_rightTensor_compressed_product_sub_le MsAnswer S.ψ
    _ (dilatedObsB S (.var 0) msBitOrZero)
    _ hZc (conjTranspose_mul_le_one_dilatedObsAf S (.constraint i0) (constraintBitOrZero k0))
  have hsplit : ∀ (Xo Zo Xd Zd : Op (κA × κB)),
      applyOperatorToState (Xo * Zo - -(Zo * Xo)) ξ =
        applyOperatorToState (Xd * Zd - -(Zd * Xd)) ξ +
          applyOperatorToState (Xo * Zo - Xd * Zd) ξ +
          applyOperatorToState (Zo * Xo - Zd * Xd) ξ := by
    intro Xo Zo Xd Zd
    rw [← applyOperatorToState_add_op, ← applyOperatorToState_add_op]
    abel
  rw [hsplit]
  refine anticommutator_arith (norm_nonneg _) ?_ hsqX hsqZ
  refine le_trans (norm_add_le _ _) (le_trans (add_le_add_left (norm_add_le _ _) _) ?_)
  linarith [(norm_product_transfer_le_B S φA φB ξ hXc hZc), (norm_product_transfer_le_B S φA φB ξ hZc hXc), hdXZ, hdZX, hleakX, hintX, hleakZ, hintZ, hξ']

end

end MIPStarRE.QPBT.MagicSquareRigidity
