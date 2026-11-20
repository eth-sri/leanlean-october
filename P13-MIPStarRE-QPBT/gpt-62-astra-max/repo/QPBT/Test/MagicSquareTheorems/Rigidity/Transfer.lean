module

public import QPBT.Test.MagicSquareTheorems.Rigidity.GroundSlice

/-!
# Transfer of rigidity bounds along the projective dilation

The self-testing argument behind `thm:ms-rigidity` is carried out for the
projective dilation `msDilatedStrategy S` of an arbitrary Magic Square strategy
`S`.  Its conclusions are state-dependent bounds for the *dilated* projectors,
conjugated by local isometries `φ_A`, `φ_B` out of the enlarged local spaces.
The witness for the original strategy is obtained by composing these isometries
with the ground embeddings, and the operators appearing in its bounds are the
conjugates of the *original* effects, that is, of the compressions `Π P Π` of
the dilated projectors `P` to the ground slice (`Π` the ground projection).

Naimark dilation preserves Born probabilities but not state-dependent `≈_δ`
estimates in general (`references/ldt-paper/orthonormalization.tex:82-101`,
blueprint `ex:easy-but-long`), so `Π P Π` and `P` need not act
alike on the dilated state.  Their difference on the dilated state `ψ'` is the
*leakage* `(1 - Π) P ψ'` of `P` out of the ground slice, and the point of this
file is that in the Magic Square game this leakage is controlled by the
cell-consistency defect of the value-to-parity layer: the dilated effect
`P ⊗ 1` almost agrees with the partner effect `1 ⊗ Q` on the other side, and
`(1 - Π) ⊗ 1` annihilates `1 ⊗ Q ψ'`.  Combined with the closeness of
`(φ_A ⊗ φ_B) ψ'` to the ideal state and the fact that all operators involved
are contractions, this pulls every bound of `thm:ms-rigidity` back from the
dilated strategy to the original one with explicit constants.

## Main statements

* `ms_effect_transfer_A`, `ms_effect_transfer_B`: the bit-measurement distances
  of the original strategy are bounded by three times those of the dilated
  strategy plus `216 ε + 24 η²`, where `η` bounds the state closeness.
* `ms_anticommutator_transfer_A`, `ms_anticommutator_transfer_B`: the
  anticommutator defects transfer with the bound `3 · (dilated) + 15552 ε +
  48 η²`.
* `ms_state_transfer`: the state closeness is unchanged.

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

/-! ## Cell consistency of the postprocessed effects -/

section

variable (S : Strategy msGame) (i : Fin 6) (x y : MsType) (f : MsAnswer → ZMod 2) (k : Fin 3)
  (b : ZMod 2)

/-- The Born overlap of Alice's totalized constraint bit with Bob's totalized
variable bit, summed over the bit, is the complement of the forward
cell-mismatch mass. -/
theorem sum_stateQForm_forward_eq :
    ∑ b : ZMod 2, stateQForm S.ψ (heteroKron
        (((S.A (.constraint i)).postprocess (constraintBitOrZero k)).effect b)
        (((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b)) =
      1 - forwardCellMismatchMass S i k := by
  classical
  have hterm : ∀ b : ZMod 2, stateQForm S.ψ (heteroKron
        (((S.A (.constraint i)).postprocess (constraintBitOrZero k)).effect b)
        (((S.B (.var (msConstraintVars i k))).postprocess msBitOrZero).effect b)) =
      ∑ a : msGame.AnswerA, ∑ c : msGame.AnswerB,
        if constraintBitOrZero k a = b then
          (if msBitOrZero c = b then
            outcomeWeight S (.constraint i) (.var (msConstraintVars i k)) a c else 0)
        else 0 := by
    intro b
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
      MIPStarRE.Quantum.Measurement.postprocess_effect,
      DistanceCalculus.heteroKron_finset_sum_left, DistanceCalculus.stateQForm_finset_sum, Finset.sum_filter]
    congr 1 with a
    split_ifs
    · rw [DistanceCalculus.heteroKron_finset_sum_right, DistanceCalculus.stateQForm_finset_sum, Finset.sum_filter]
      rfl
    · simp
  unfold forwardCellMismatchMass outcomeEventWeight
  simp_rw [hterm]
  rw [Finset.sum_comm, eq_sub_iff_add_eq, ← (outcomeWeight_sum_eq_one S (.constraint i) (.var (msConstraintVars i k))), ← Finset.sum_add_distrib]
  congr 1 with a
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  congr 1 with c
  by_cases h : constraintBitOrZero k a = msBitOrZero c
  · simp [h]
  · simp [h, Ne.symm]

/-! ## The dilated effects on the enlarged ground spaces -/

/-- Alice's dilated postprocessed effect, typed on the enlarged local space
`ℂ^{ιA × Option MsAnswer}`.  Formalization-only abbreviation. -/
abbrev dilatedEffectA : Op (S.ιA × Option MsAnswer) :=
  (((msDilatedStrategy S).A x).postprocess f).effect b

/-- Bob's dilated postprocessed effect, typed on the enlarged local space
`ℂ^{ιB × Option MsAnswer}`.  Formalization-only abbreviation. -/
abbrev dilatedEffectB : Op (S.ιB × Option MsAnswer) :=
  (((msDilatedStrategy S).B y).postprocess f).effect b

/-- Alice's dilated constraint bit approximately intertwines with Bob's dilated
variable bit: the summed squared defect is at most twice the forward
cell-mismatch mass of the original strategy. -/
theorem sum_norm_sq_intertwining_le_forward :
    ∑ b : ZMod 2, ‖applyOperatorToState
        (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) b) 1 -
          heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero b))
        (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤ 2 * forwardCellMismatchMass S i k := by
  set S' := msDilatedStrategy S
  set PA := (S'.A (.constraint i)).postprocess (constraintBitOrZero k)
  set QB := (S'.B (.var (msConstraintVars i k))).postprocess msBitOrZero
  have h1 := point_distance_le_two_defect (leftPlacedMeasurement (ιB := S'.ιB) PA)
    (rightPlacedMeasurement (ιA := S'.ιA) QB) S'.ψ
  rw [point_defect_eq] at h1
  have hover : ∑ a : ZMod 2, stateQForm S'.ψ
      ((leftPlacedMeasurement PA).effect a *
        (rightPlacedMeasurement QB).effect a) =
      1 - forwardCellMismatchMass S i k := by
    rw [← ms_dilated_strategy_forward_cell_mismatch_mass,
      ← sum_stateQForm_forward_eq]
    congr 1 with a
    change stateQForm S'.ψ (heteroKron (PA.effect a) 1 * heteroKron 1 (QB.effect a)) =
      _
    rw [heteroKron_mul, Matrix.mul_one, Matrix.one_mul]
  simp [S'.ψ_norm] at h1
  have h2 : ∑ b : ZMod 2, ‖applyOperatorToState
      (heteroKron (dilatedEffectA S (.constraint i) (constraintBitOrZero k) b) 1 -
        heteroKron 1 (dilatedEffectB S (.var (msConstraintVars i k)) msBitOrZero b))
      (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤
      2 * _ := h1
  linarith

/-! ## Compressions of the dilated postprocessed effects -/

/-- Compressing one of Bob's dilated postprocessed effects returns his original
postprocessed effect. -/
theorem naimarkCompression_dilatedEffectB :
    naimarkCompression (dilatedEffectB S y f b) = ((S.B y).postprocess f).effect b := by
  have h := (naimarkCompression_finset_sum (Finset.univ.filter fun a : MsAnswer => f a = b)
    ((msDilatedStrategy S).B y).effect).trans
    (Finset.sum_congr rfl fun a _ => naimarkCompression_msDilatedStrategy_B_effect S y a)
  exact h

/-- The inflation of Bob's original postprocessed effect is the ground
compression `Π Q Π` of his dilated one. -/
theorem naimarkInflation_postprocess_B :
    naimarkInflation (α := MsAnswer) (((S.B y).postprocess f).effect b) =
      groundProjection S.ιB MsAnswer * dilatedEffectB S y f b *
        groundProjection S.ιB MsAnswer := by
  rw [← naimarkCompression_dilatedEffectB, naimarkInflation_naimarkCompression]

end

/-! ## Transfer of the effect estimates -/

/-! ## Transfer of the anticommutator estimates -/

/-- Inflation respects differences. -/
theorem naimarkInflation_sub {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op ι) :
    naimarkInflation (α := α) (M - N) =
      naimarkInflation (α := α) M - naimarkInflation (α := α) N := by
  ext p q
  by_cases h : p.2 = none ∧ q.2 = none <;> simp [h]

section

variable (S : Strategy msGame) {ι : Type*} [Fintype ι] (i : Fin 6) (x y : MsType)
  [DecidableEq ι] (f : MsAnswer → ZMod 2) (k : Fin 3) (M N : Op ι) (v : EuclideanSpace ℂ ι)

/-- The action on states respects negation of operators. -/
theorem applyOperatorToState_neg_op :
    applyOperatorToState (-M) v = -applyOperatorToState M v := by
  simp [applyOperatorToState]

/-- The one-outcome distance under the one-point uniform distribution. -/
theorem opDistSq_uniform_unit
    (M N : Unit → Op ι) (ψ : EuclideanSpace ℂ ι) :
    opDistSq (uniformDistribution Unit) M N ψ =
      ‖applyOperatorToState (M () - N ()) ψ‖ ^ 2 := by
  simp [opDistSq_eq_opFamilyDistSq, opFamilyDistSq_uniform_unit]

/-- Bob's dilated observable of a totalized bit, typed on the enlarged local
space.  Formalization-only abbreviation. -/
abbrev dilatedObsB :
    Op (S.ιB × Option MsAnswer) :=
  obsOf (((msDilatedStrategy S).B y).postprocess f)

/-- Bob's dilated observables are contractions. -/
theorem conjTranspose_mul_le_one_dilatedObsB :
    (dilatedObsB S y f)ᴴ * dilatedObsB S y f ≤ 1 :=
  conjTranspose_mul_le_one_of_obsOf _

end

variable {κA : Type} (ℓ : ZMod 2 → ℝ) (m : ℝ) {κB : Type} [Fintype κA] [DecidableEq κA]
  [Fintype κB] [DecidableEq κB] (S : Strategy msGame)
  (φA : EuclideanSpace ℂ (S.ιA × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κA)
  (φB : EuclideanSpace ℂ (S.ιB × Option MsAnswer) →ₗᵢ[ℂ] EuclideanSpace ℂ κB)
  (ξ : EuclideanSpace ℂ (κA × κB)) (ε : ℝ)

/-- The square of a two-term leakage sum is controlled by the cell-mismatch
mass. -/
theorem sq_add_le_of_sum_sq_le
    (hL : ∑ b, ℓ b ^ 2 ≤ 2 * m) (hm : m ≤ 36 * ε) :
    (ℓ 0 + ℓ 1) ^ 2 ≤ 144 * ε := by
  have h2 : ∑ b : Fin 2, ℓ b ^ 2 ≤ 2 * m := hL
  simp at h2
  have h3 : ℓ 0 ^ 2 + ℓ 1 ^ 2 ≤ 2 * m := h2
  nlinarith [sq_nonneg (ℓ 0 - ℓ 1)]

/-- The final arithmetic of the anticommutator transfer. -/
theorem anticommutator_arith {o a x z η ε : ℝ} (ho : 0 ≤ o)
    (h : o ≤ a + (x + 2 * z + 2 * η) + (z + 2 * x + 2 * η))
    (hx : x ^ 2 ≤ 144 * ε) (hz : z ^ 2 ≤ 144 * ε) :
    o ^ 2 ≤ 3 * a ^ 2 + 15552 * ε + 48 * η ^ 2 := by
  have h1 : o ^ 2 ≤ (a + 3 * (x + z) + 4 * η) ^ 2 :=
    pow_le_pow_left₀ ho (by linarith) 2
  have h2 : (a + 3 * (x + z) + 4 * η) ^ 2 ≤
      3 * a ^ 2 + 3 * (3 * (x + z)) ^ 2 + 3 * (4 * η) ^ 2 := by
    nlinarith [sq_nonneg (a - 3 * (x + z)), sq_nonneg (3 * (x + z) - 4 * η),
      sq_nonneg (a - 4 * η)]
  have h3 : (x + z) ^ 2 ≤ 2 * x ^ 2 + 2 * z ^ 2 := by nlinarith [sq_nonneg (x - z)]
  linarith

end

end MIPStarRE.QPBT.MagicSquareRigidity
