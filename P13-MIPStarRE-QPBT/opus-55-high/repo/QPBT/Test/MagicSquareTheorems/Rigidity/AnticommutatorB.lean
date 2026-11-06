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

/-- The norm of a difference acting on a state is symmetric. -/
theorem norm_applyOperatorToState_sub_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Op ι) (v : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState (M - N) v‖ = ‖applyOperatorToState (N - M) v‖ := by
  simp [applyOperatorToState_sub_op, norm_sub_rev]

/-- The inflation of Bob's original observable is the ground compression of
his dilated observable. -/
theorem naimarkInflation_obs_B (S : Strategy msGame) (y : MsType) :
    naimarkInflation (α := MsAnswer) (obsOf ((S.B y).postprocess msBitOrZero)) =
      groundProjection S.ιB MsAnswer * dilatedObsB S y msBitOrZero *
        groundProjection S.ιB MsAnswer := by
  change naimarkInflation (α := MsAnswer) (((S.B y).postprocess msBitOrZero).effect 0 -
    ((S.B y).postprocess msBitOrZero).effect 1) =
    groundProjection S.ιB MsAnswer *
      (dilatedEffectB S y msBitOrZero 0 - dilatedEffectB S y msBitOrZero 1) *
      groundProjection S.ιB MsAnswer
  rw [naimarkInflation_sub, naimarkInflation_postprocess_B, naimarkInflation_postprocess_B,
    Matrix.mul_sub, Matrix.sub_mul]

/-- Alice's dilated totalized observables are contractions. -/
theorem conjTranspose_mul_le_one_dilatedObsAf (S : Strategy msGame) (x : MsType)
    (f : MsAnswer → ZMod 2) :
    (dilatedObsAf S x f)ᴴ * dilatedObsAf S x f ≤ 1 :=
  conjTranspose_mul_le_one_of_obsOf _

/-- The leakage of Bob's dilated observable out of the ground slice is bounded
by the two intertwining defects of its effects. -/
theorem norm_leak_obs_le_B (S : Strategy msGame) (x y : MsType) (f g : MsAnswer → ZMod 2) :
    ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection S.ιB MsAnswer) * dilatedObsB S y g))
        (naimarkDilatedState MsAnswer S.ψ)‖ ≤
      ‖applyOperatorToState (heteroKron (dilatedEffectA S x f 0) 1 - heteroKron 1 (dilatedEffectB S y g 0))
        (naimarkDilatedState MsAnswer S.ψ)‖ +
      ‖applyOperatorToState (heteroKron (dilatedEffectA S x f 1) 1 - heteroKron 1 (dilatedEffectB S y g 1))
        (naimarkDilatedState MsAnswer S.ψ)‖ := by
  change ‖applyOperatorToState (heteroKron 1 ((1 - groundProjection S.ιB MsAnswer) *
    (dilatedEffectB S y g 0 - dilatedEffectB S y g 1))) (naimarkDilatedState MsAnswer S.ψ)‖ ≤ _
  rw [Matrix.mul_sub, heteroKron_sub_right, applyOperatorToState_sub_op]
  exact (norm_sub_le _ _).trans (add_le_add (norm_rightTensor_one_sub_groundProjection_mul_le _ _ _ _)
    (norm_rightTensor_one_sub_groundProjection_mul_le _ _ _ _))

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
  have hG := isProj_groundProjection ιB α
  have h1 : 1 - heteroKron (1 : Op (ιA × Option α)) (groundProjection ιB α) =
      heteroKron 1 (1 - groundProjection ιB α) := by rw [heteroKron_sub_right, heteroKron_one_one]
  have := norm_compressed_product_sub_le _ _ (heteroKron 1 A) (heteroKron 1 B) _
    (by rw [heteroKron_mul, hG.isIdempotentElem.eq, mul_one])
    (conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_of_isProj hG))
    (h1 ▸ conjTranspose_mul_le_one_rightTensor (conjTranspose_mul_le_one_of_isProj hG.one_sub))
    (conjTranspose_mul_le_one_rightTensor hA) (conjTranspose_mul_le_one_leftTensor hY)
    (applyOperatorToState_rightTensor_groundProjection (α := α) ψ)
    (by simp only [h1, heteroKron_mul, mul_one, one_mul])
  simpa only [h1, heteroKron_mul, mul_one, ← heteroKron_sub_right,
    norm_applyOperatorToState_sub_comm (heteroKron 1 B)] using this

/-- Transfer of Bob's anticommutator estimate of `thm:ms-rigidity` from the
dilated strategy to the original one on the dilated state; see
`ms_anticommutator_transfer_A`. -/
theorem ms_anticommutator_transfer_B (S : Strategy msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState
        (heteroKron 1 (naimarkInflation (obsOf ((S.B (.var 0)).postprocess msBitOrZero))) *
            heteroKron 1 (naimarkInflation (obsOf ((S.B (.var 4)).postprocess msBitOrZero))) -
          -(heteroKron 1 (naimarkInflation (obsOf ((S.B (.var 4)).postprocess msBitOrZero))) *
            heteroKron 1 (naimarkInflation (obsOf ((S.B (.var 0)).postprocess msBitOrZero)))))
        (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤
      3 * ‖applyOperatorToState
        (heteroKron 1 (dilatedObsB S (.var 0) msBitOrZero) * heteroKron 1 (dilatedObsB S (.var 4) msBitOrZero) -
          -(heteroKron 1 (dilatedObsB S (.var 4) msBitOrZero) * heteroKron 1 (dilatedObsB S (.var 0) msBitOrZero)))
        (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 + 15552 * ε := by
  obtain ⟨i0, k0, h0⟩ := every_variable_is_incident 0
  obtain ⟨i4, k4, h4⟩ := every_variable_is_incident 4
  rw [naimarkInflation_obs_B, naimarkInflation_obs_B]
  have hXc := conjTranspose_mul_le_one_dilatedObsB S (.var 0) msBitOrZero
  have hZc := conjTranspose_mul_le_one_dilatedObsB S (.var 4) msBitOrZero
  have hYXc := conjTranspose_mul_le_one_dilatedObsAf S (.constraint i0) (constraintBitOrZero k0)
  have hYZc := conjTranspose_mul_le_one_dilatedObsAf S (.constraint i4) (constraintBitOrZero k4)
  have hleakX := norm_leak_obs_le_B S (.constraint i0) (.var (msConstraintVars i0 k0)) (constraintBitOrZero k0) msBitOrZero
  have hintX := norm_intertwine_obs_le S (.constraint i0) (.var (msConstraintVars i0 k0)) (constraintBitOrZero k0) msBitOrZero
  have hleakZ := norm_leak_obs_le_B S (.constraint i4) (.var (msConstraintVars i4 k4)) (constraintBitOrZero k4) msBitOrZero
  have hintZ := norm_intertwine_obs_le S (.constraint i4) (.var (msConstraintVars i4 k4)) (constraintBitOrZero k4) msBitOrZero
  have hsqX := sq_add_le_of_sum_sq_le _ _ ε (sum_norm_sq_intertwining_le S (.constraint i0)
    (.var (msConstraintVars i0 k0)) (constraintBitOrZero k0) msBitOrZero)
    (forward_cell_mismatch_mass_le S ε hwin i0 k0)
  have hsqZ := sq_add_le_of_sum_sq_le _ _ ε (sum_norm_sq_intertwining_le S (.constraint i4)
    (.var (msConstraintVars i4 k4)) (constraintBitOrZero k4) msBitOrZero)
    (forward_cell_mismatch_mass_le S ε hwin i4 k4)
  rw [h0] at hleakX hintX hsqX
  rw [h4] at hleakZ hintZ hsqZ
  have hdXZ := norm_rightTensor_compressed_product_sub_le MsAnswer S.ψ _ (dilatedObsB S (.var 4) msBitOrZero) _
    hXc hYZc
  have hdZX := norm_rightTensor_compressed_product_sub_le MsAnswer S.ψ _ (dilatedObsB S (.var 0) msBitOrZero) _
    hZc hYXc
  exact anticommutator_arith _ (by simp only [heteroKron_mul, one_mul, ← heteroKron_sub_right]; linarith) hsqX hsqZ

end

end MIPStarRE.QPBT.MagicSquareRigidity
