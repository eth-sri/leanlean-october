module

public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-! # Ground-slice bounds for Magic Square

Approximate agreement with the opposite player's cell effects bounds the
leakage of each dilated variable observable. Projecting the dilated
anticommutator back into the ground slice then costs just the two leakages.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

noncomputable section

/-! ## Cell consistency of the postprocessed effects -/

/-- The Born overlap of Alice's totalized variable bit with Bob's totalized
constraint bit, summed over the bit, is the complement of the reverse
cell-mismatch mass. -/
theorem sum_stateQForm_reverse_eq (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    ∑ b : ZMod 2, stateQForm S.ψ (heteroKron
        (((S.A (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b)
        (((S.B (.constraint i)).postprocess (constraintBitOrZero k)).effect b)) =
      1 - reverseCellMismatchMass S i k := by
  classical
  rw [diagonal_postprocess_stateQForm_eq_pair_sum, reverseCellMismatchMass,
    outcomeEventWeight, eq_sub_iff_add_eq, ← outcomeWeight_sum_eq_one S
      (.var (msConstraintVars i k)) (.constraint i)]
  simp_rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : msBitOrZero a = constraintBitOrZero k b <;> simp_all [outcomeWeight, stateQForm]

/-! ## The dilated effects on the enlarged ground spaces -/

section

variable (S : Strategy msGame) (x : MsType) (f : MsAnswer → ZMod 2)
    (b : ZMod 2)

/-- Alice's dilated postprocessed effect, typed on the enlarged local space
`ℂ^{ιA × Option MsAnswer}`.  Formalization-only abbreviation. -/
abbrev dilatedEffectA : Op (S.ιA × Option MsAnswer) :=
  (((msDilatedStrategy S).A x).postprocess f).effect b

/-- Bob's dilated postprocessed effect, typed on the enlarged local space
`ℂ^{ιB × Option MsAnswer}`.  Formalization-only abbreviation. -/
abbrev dilatedEffectB (S : Strategy msGame) (y : MsType) (f : MsAnswer → ZMod 2)
    (b : ZMod 2) : Op (S.ιB × Option MsAnswer) :=
  (((msDilatedStrategy S).B y).postprocess f).effect b

/-- Alice's dilated variable bit approximately intertwines with Bob's dilated
constraint bit: the summed squared defect is at most twice the reverse
cell-mismatch mass of the original strategy.  This is the first item of
blueprint `fact:agreement`, applied to the
dilated strategy, whose Born masses are those of the original one. -/
theorem sum_norm_sq_intertwining_le_reverse (S : Strategy msGame) (i : Fin 6) (k : Fin 3) :
    ∑ b : ZMod 2, ‖applyOperatorToState
        (heteroKron (dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero b) 1 -
          heteroKron 1 (dilatedEffectB S (.constraint i) (constraintBitOrZero k) b))
        (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤ 2 * reverseCellMismatchMass S i k := by
  let T := msDilatedStrategy S
  have h := point_distance_le_two_defect
    (leftPlacedMeasurement (ιB := T.ιB) ((T.A (.var (msConstraintVars i k))).postprocess msBitOrZero))
    (rightPlacedMeasurement (ιA := T.ιA) ((T.B (.constraint i)).postprocess (constraintBitOrZero k))) T.ψ
  rw [point_defect_eq, T.ψ_norm] at h
  simp only [leftPlacedMeasurement_effect, rightPlacedMeasurement_effect,
    placed_product_stateQForm_eq, sum_stateQForm_reverse_eq] at h
  rw [show reverseCellMismatchMass T i k = _ from
    ms_dilated_strategy_reverse_cell_mismatch_mass S i k] at h
  change ∑ b, ‖applyOperatorToState (heteroKron (dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero b)
    (1 : Op (S.ιB × Option MsAnswer)) - heteroKron (1 : Op (S.ιA × Option MsAnswer))
      (dilatedEffectB S (.constraint i) (constraintBitOrZero k) b))
    (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤ _ at h
  linarith

/-- Compressing one of Alice's dilated postprocessed effects returns her original
postprocessed effect. -/
theorem naimarkCompression_dilatedEffectA :
    naimarkCompression (dilatedEffectA S x f b) = ((S.A x).postprocess f).effect b := by
  have h := (naimarkCompression_finset_sum (Finset.univ.filter fun a : MsAnswer => f a = b)
    fun a => ((msDilatedStrategy S).A x).effect a).trans
    (Finset.sum_congr rfl fun a _ => naimarkCompression_msDilatedStrategy_A_effect S x a)
  assumption

/-- The inflation of Alice's original postprocessed effect is the ground
compression `Π P Π` of her dilated one. -/
theorem naimarkInflation_postprocess_A :
    naimarkInflation (α := MsAnswer) (((S.A x).postprocess f).effect b) =
      groundProjection S.ιA MsAnswer * dilatedEffectA S x f b *
        groundProjection S.ιA MsAnswer := by
  rw [← naimarkCompression_dilatedEffectA, naimarkInflation_naimarkCompression]

end

/-- Inflation respects differences. -/
theorem naimarkInflation_sub {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op ι) :
    naimarkInflation (α := α) (M - N) =
      naimarkInflation (α := α) M - naimarkInflation (α := α) N := by
  ext p q
  by_cases h : p.2 = none ∧ q.2 = none <;> simp [h]

/-- The action on states respects negation of operators. -/
theorem applyOperatorToState_neg_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (-M) v = -applyOperatorToState M v := by
  simp [applyOperatorToState]

section

variable (S : Strategy msGame)
include S

/-- Alice's dilated observable of a variable question, typed on the enlarged
local space.  Formalization-only abbreviation. -/
abbrev dilatedObsA (x : MsType) : Op (S.ιA × Option MsAnswer) :=
  obsOf (((msDilatedStrategy S).A x).postprocess msBitOrZero)

/-- The inflation of Alice's original observable is the ground compression of
her dilated observable. -/
theorem naimarkInflation_obs_A (x : MsType) :
    naimarkInflation (α := MsAnswer) (obsOf ((S.A x).postprocess msBitOrZero)) =
      groundProjection S.ιA MsAnswer * dilatedObsA S x * groundProjection S.ιA MsAnswer := by
  change naimarkInflation (α := MsAnswer) (((S.A x).postprocess msBitOrZero).effect 0 -
    ((S.A x).postprocess msBitOrZero).effect 1) =
    groundProjection S.ιA MsAnswer *
      (dilatedEffectA S x msBitOrZero 0 - dilatedEffectA S x msBitOrZero 1) *
      groundProjection S.ιA MsAnswer
  rw [naimarkInflation_sub, naimarkInflation_postprocess_A, naimarkInflation_postprocess_A,
    Matrix.mul_sub, Matrix.sub_mul]

/-- Alice's dilated observables are contractions. -/
theorem conjTranspose_mul_le_one_dilatedObsA (x : MsType) :
    (dilatedObsA S x)ᴴ * dilatedObsA S x ≤ 1 :=
  conjTranspose_mul_le_one_of_obsOf _

/-- The leakage of Alice's dilated observable out of the ground slice is bounded
by the two intertwining defects of its effects. -/
theorem norm_leak_obs_le_A (i : Fin 6) (k : Fin 3) :
    ‖applyOperatorToState (heteroKron ((1 - groundProjection S.ιA MsAnswer) *
        dilatedObsA S (.var (msConstraintVars i k))) 1) (naimarkDilatedState MsAnswer S.ψ)‖ ≤
      ‖applyOperatorToState
        (heteroKron (dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero 0) 1 -
          heteroKron 1 (dilatedEffectB S (.constraint i) (constraintBitOrZero k) 0))
        (naimarkDilatedState MsAnswer S.ψ)‖ +
      ‖applyOperatorToState
        (heteroKron (dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero 1) 1 -
          heteroKron 1 (dilatedEffectB S (.constraint i) (constraintBitOrZero k) 1))
        (naimarkDilatedState MsAnswer S.ψ)‖ := by
  change ‖applyOperatorToState (heteroKron ((1 - groundProjection S.ιA MsAnswer) *
    (dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero 0 -
      dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero 1)) 1)
    (naimarkDilatedState MsAnswer S.ψ)‖ ≤ _
  rw [Matrix.mul_sub, heteroKron_sub_left, applyOperatorToState_sub_op]
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
  · exact norm_leftTensor_one_sub_groundProjection_mul_le MsAnswer S.ψ _ _
  · exact norm_leftTensor_one_sub_groundProjection_mul_le MsAnswer S.ψ _ _

/-- Approximate agreement bounds the leakage of a variable observable. -/
theorem norm_leak_obs_le_sqrt (ε : ℝ) (hwin : 1 - ε ≤ S.value)
    (i : Fin 6) (k : Fin 3) :
    ‖applyOperatorToState (heteroKron ((1 - groundProjection S.ιA MsAnswer) *
          dilatedObsA S (.var (msConstraintVars i k))) 1) (naimarkDilatedState MsAnswer S.ψ)‖ ≤
      12 * Real.sqrt ε := by
  let e (b : ZMod 2) := ‖applyOperatorToState
    (heteroKron (dilatedEffectA S (.var (msConstraintVars i k)) msBitOrZero b) 1 -
      heteroKron 1 (dilatedEffectB S (.constraint i) (constraintBitOrZero k) b))
    (naimarkDilatedState MsAnswer S.ψ)‖
  have h : ∑ b, e b ^ 2 ≤ _ := sum_norm_sq_intertwining_le_reverse S i k
  have he : ∑ b : Fin 2, e b ^ 2 ≤ 2 * reverseCellMismatchMass S i k := h
  rw [Fin.sum_univ_two] at he
  change e 0 ^ 2 + e 1 ^ 2 ≤ _ at he
  have hs := reverse_cell_mismatch_mass_le S ε hwin i k
  refine (norm_leak_obs_le_A S i k).trans ?_
  change e 0 + e 1 ≤ _
  rw [← show Real.sqrt 144 = 12 by norm_num, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 144)]
  exact Real.le_sqrt_of_sq_le (by nlinarith only [he, hs, sq_nonneg (e 0 - e 1)])

end

/-- On a state fixed by a projection, the norm of the compressed
anticommutator is bounded by the dilated norm and one leakage per factor. -/
theorem norm_compressed_anticommutator_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (P A B : Op ι) (hP : P * P = P)
    (hfix : applyOperatorToState P ψ = ψ) (hPc : Pᴴ * P ≤ 1)
    (hA : Aᴴ * A ≤ 1) (hB : Bᴴ * B ≤ 1) :
    ‖applyOperatorToState ((P * A * P) * (P * B * P) + (P * B * P) * (P * A * P)) ψ‖ ≤
      ‖applyOperatorToState (A * B + B * A) ψ‖ +
        ‖applyOperatorToState ((1 - P) * B) ψ‖ + ‖applyOperatorToState ((1 - P) * A) ψ‖ := by
  have hmul (M N : Op ι) : (P * M * P) * (P * N * P) = P * M * P * N * P := by
    simp only [mul_assoc]
    rw [← mul_assoc P P, hP]
  rw [hmul A B, hmul B A, show P * A * P * B * P + P * B * P * A * P =
    P * (A * B + B * A - A * ((1 - P) * B) - B * ((1 - P) * A)) * P by noncomm_ring,
    applyOperatorToState_mul _ P, hfix, applyOperatorToState_mul P]
  refine (norm_applyOperatorToState_le hPc _).trans ?_
  simp only [applyOperatorToState_sub_op]
  refine (norm_sub_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add_right ?_ _)) ?_)
  · rw [applyOperatorToState_mul A]
    exact norm_applyOperatorToState_le hA _
  · rw [applyOperatorToState_mul B]
    exact norm_applyOperatorToState_le hB _

end

end MIPStarRE.QPBT.MagicSquareRigidity
