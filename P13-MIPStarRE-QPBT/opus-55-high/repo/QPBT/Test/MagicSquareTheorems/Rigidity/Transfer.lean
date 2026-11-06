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

variable (S : Strategy msGame)

/-- The Born overlap of two totalized bits, summed over the bit, is the
complement of the mass on which they disagree. -/
theorem sum_stateQForm_postprocess_eq (x y : MsType) (f g : MsAnswer → ZMod 2) :
    ∑ b : ZMod 2, stateQForm S.ψ (heteroKron (((S.A x).postprocess f).effect b)
        (((S.B y).postprocess g).effect b)) =
      1 - outcomeEventWeight S x y (fun a c => f a ≠ g c) := by
  have hterm : ∀ b : ZMod 2, stateQForm S.ψ (heteroKron (((S.A x).postprocess f).effect b)
        (((S.B y).postprocess g).effect b)) =
      ∑ a : msGame.AnswerA, ∑ c : msGame.AnswerB,
        if f a = b then (if g c = b then outcomeWeight S x y a c else 0) else 0 := by
    intro b
    rw [MIPStarRE.Quantum.Measurement.postprocess_effect,
      MIPStarRE.Quantum.Measurement.postprocess_effect,
      heteroKron_finset_sum_left, stateQForm_finset_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · rw [heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.sum_filter]
      rfl
    · simp
  unfold outcomeEventWeight
  simp_rw [hterm]
  rw [Finset.sum_comm, eq_sub_iff_add_eq, ← outcomeWeight_sum_eq_one S x y, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq]
  grind

/-! ## The dilated effects on the enlarged ground spaces -/

/-- Alice's dilated postprocessed effect, typed on the enlarged local space
`ℂ^{ιA × Option MsAnswer}`.  Formalization-only abbreviation. -/
abbrev dilatedEffectA (S : Strategy msGame) (x : MsType) (f : MsAnswer → ZMod 2)
    (b : ZMod 2) : Op (S.ιA × Option MsAnswer) :=
  (((msDilatedStrategy S).A x).postprocess f).effect b

/-- Bob's dilated postprocessed effect, typed on the enlarged local space
`ℂ^{ιB × Option MsAnswer}`.  Formalization-only abbreviation. -/
abbrev dilatedEffectB (S : Strategy msGame) (y : MsType) (f : MsAnswer → ZMod 2)
    (b : ZMod 2) : Op (S.ιB × Option MsAnswer) :=
  (((msDilatedStrategy S).B y).postprocess f).effect b

/-- Alice's and Bob's dilated totalized bits approximately intertwine: the summed
squared defect is at most twice the mismatch mass of the original strategy.
This is the first item of blueprint `fact:agreement`, applied to the dilated
strategy, whose Born masses are those of the original one. -/
theorem sum_norm_sq_intertwining_le (x y : MsType) (f g : MsAnswer → ZMod 2) :
    ∑ b : ZMod 2, ‖applyOperatorToState
        (heteroKron (dilatedEffectA S x f b) 1 - heteroKron 1 (dilatedEffectB S y g b))
        (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤
      2 * outcomeEventWeight S x y (fun a c => f a ≠ g c) := by
  have h1 := point_distance_le_two_defect
    (leftPlacedMeasurement (ιB := (msDilatedStrategy S).ιB) (((msDilatedStrategy S).A x).postprocess f))
    (rightPlacedMeasurement (ιA := (msDilatedStrategy S).ιA) (((msDilatedStrategy S).B y).postprocess g))
    (msDilatedStrategy S).ψ
  rw [point_defect_eq] at h1
  simp only [(msDilatedStrategy S).ψ_norm, leftPlacedMeasurement,
    rightPlacedMeasurement, MIPStarRE.Quantum.Measurement.ofSumEqOne, heteroKron_mul, mul_one,
    one_mul, sum_stateQForm_postprocess_eq, ms_dilated_strategy_outcome_event_weight] at h1
  exact h1.trans_eq (by ring)

/-! ## Compressions of the dilated postprocessed effects -/

/-- Compressing one of Alice's dilated postprocessed effects returns her original
postprocessed effect. -/
theorem naimarkCompression_dilatedEffectA (S : Strategy msGame) (x : MsType)
    (f : MsAnswer → ZMod 2) (b : ZMod 2) :
    naimarkCompression (dilatedEffectA S x f b) = ((S.A x).postprocess f).effect b := by
  have h := (naimarkCompression_finset_sum (Finset.univ.filter fun a : MsAnswer => f a = b)
    fun a => ((msDilatedStrategy S).A x).effect a).trans
    (Finset.sum_congr rfl fun a _ => naimarkCompression_msDilatedStrategy_A_effect S x a)
  exact h

/-- Compressing one of Bob's dilated postprocessed effects returns his original
postprocessed effect. -/
theorem naimarkCompression_dilatedEffectB (S : Strategy msGame) (y : MsType)
    (f : MsAnswer → ZMod 2) (b : ZMod 2) :
    naimarkCompression (dilatedEffectB S y f b) = ((S.B y).postprocess f).effect b := by
  have h := (naimarkCompression_finset_sum (Finset.univ.filter fun a : MsAnswer => f a = b)
    fun a => ((msDilatedStrategy S).B y).effect a).trans
    (Finset.sum_congr rfl fun a _ => naimarkCompression_msDilatedStrategy_B_effect S y a)
  exact h

/-- The inflation of Alice's original postprocessed effect is the ground
compression `Π P Π` of her dilated one. -/
theorem naimarkInflation_postprocess_A (S : Strategy msGame) (x : MsType)
    (f : MsAnswer → ZMod 2) (b : ZMod 2) :
    naimarkInflation (α := MsAnswer) (((S.A x).postprocess f).effect b) =
      groundProjection S.ιA MsAnswer * dilatedEffectA S x f b *
        groundProjection S.ιA MsAnswer := by
  grind [naimarkCompression_dilatedEffectA, naimarkInflation_naimarkCompression]

/-- The inflation of Bob's original postprocessed effect is the ground
compression `Π Q Π` of his dilated one. -/
theorem naimarkInflation_postprocess_B (S : Strategy msGame) (y : MsType)
    (f : MsAnswer → ZMod 2) (b : ZMod 2) :
    naimarkInflation (α := MsAnswer) (((S.B y).postprocess f).effect b) =
      groundProjection S.ιB MsAnswer * dilatedEffectB S y f b *
        groundProjection S.ιB MsAnswer := by
  grind [naimarkCompression_dilatedEffectB, naimarkInflation_naimarkCompression]

/-! ## Transfer of the effect estimates -/

/-! ## Transfer of the anticommutator estimates -/

/-- Inflation respects differences. -/
theorem naimarkInflation_sub {ι α : Type} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] (M N : Op ι) :
    naimarkInflation (α := α) (M - N) =
      naimarkInflation (α := α) M - naimarkInflation (α := α) N := by
  ext p q
  by_cases h : p.2 = none ∧ q.2 = none <;> simp [h]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The action on states respects differences of operators. -/
theorem applyOperatorToState_sub_op (M N : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (M - N) v =
      applyOperatorToState M v - applyOperatorToState N v := by
  simp [applyOperatorToState]

/-- The action on states respects negation of operators. -/
theorem applyOperatorToState_neg_op (M : Op ι) (v : EuclideanSpace ℂ ι) :
    applyOperatorToState (-M) v = -applyOperatorToState M v := by
  simp [applyOperatorToState]

/-- Alice's dilated observable of a variable question, typed on the enlarged
local space.  Formalization-only abbreviation. -/
abbrev dilatedObsA (S : Strategy msGame) (x : MsType) : Op (S.ιA × Option MsAnswer) :=
  obsOf (((msDilatedStrategy S).A x).postprocess msBitOrZero)

/-- Alice's dilated observable of a totalized bit, typed on the enlarged local
space.  Formalization-only abbreviation. -/
abbrev dilatedObsAf (S : Strategy msGame) (x : MsType) (f : MsAnswer → ZMod 2) :
    Op (S.ιA × Option MsAnswer) :=
  obsOf (((msDilatedStrategy S).A x).postprocess f)

/-- Bob's dilated observable of a totalized bit, typed on the enlarged local
space.  Formalization-only abbreviation. -/
abbrev dilatedObsB (S : Strategy msGame) (y : MsType) (f : MsAnswer → ZMod 2) :
    Op (S.ιB × Option MsAnswer) :=
  obsOf (((msDilatedStrategy S).B y).postprocess f)

/-- The inflation of Alice's original observable is the ground compression of
her dilated observable. -/
theorem naimarkInflation_obs_A (S : Strategy msGame) (x : MsType) :
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
theorem conjTranspose_mul_le_one_dilatedObsA (S : Strategy msGame) (x : MsType) :
    (dilatedObsA S x)ᴴ * dilatedObsA S x ≤ 1 :=
  conjTranspose_mul_le_one_of_obsOf _

/-- Bob's dilated observables are contractions. -/
theorem conjTranspose_mul_le_one_dilatedObsB (S : Strategy msGame) (y : MsType)
    (f : MsAnswer → ZMod 2) :
    (dilatedObsB S y f)ᴴ * dilatedObsB S y f ≤ 1 :=
  conjTranspose_mul_le_one_of_obsOf _

/-- The leakage of Alice's dilated observable out of the ground slice is bounded
by the two intertwining defects of its effects. -/
theorem norm_leak_obs_le_A (x y : MsType) (f g : MsAnswer → ZMod 2) :
    ‖applyOperatorToState (heteroKron ((1 - groundProjection S.ιA MsAnswer) *
        dilatedObsAf S x f) 1) (naimarkDilatedState MsAnswer S.ψ)‖ ≤
      ‖applyOperatorToState (heteroKron (dilatedEffectA S x f 0) 1 - heteroKron 1 (dilatedEffectB S y g 0))
        (naimarkDilatedState MsAnswer S.ψ)‖ +
      ‖applyOperatorToState (heteroKron (dilatedEffectA S x f 1) 1 - heteroKron 1 (dilatedEffectB S y g 1))
        (naimarkDilatedState MsAnswer S.ψ)‖ := by
  change ‖applyOperatorToState (heteroKron ((1 - groundProjection S.ιA MsAnswer) *
    (dilatedEffectA S x f 0 - dilatedEffectA S x f 1)) 1) (naimarkDilatedState MsAnswer S.ψ)‖ ≤ _
  rw [Matrix.mul_sub, heteroKron_sub_left, applyOperatorToState_sub_op]
  exact (norm_sub_le _ _).trans (add_le_add (norm_leftTensor_one_sub_groundProjection_mul_le _ _ _ _)
    (norm_leftTensor_one_sub_groundProjection_mul_le _ _ _ _))

/-- The intertwining defect of Alice's dilated observable against Bob's is
bounded by the two intertwining defects of the effects. -/
theorem norm_intertwine_obs_le (x y : MsType) (f g : MsAnswer → ZMod 2) :
    ‖applyOperatorToState (heteroKron (dilatedObsAf S x f) 1 - heteroKron 1 (dilatedObsB S y g))
        (naimarkDilatedState MsAnswer S.ψ)‖ ≤
      ‖applyOperatorToState (heteroKron (dilatedEffectA S x f 0) 1 - heteroKron 1 (dilatedEffectB S y g 0))
        (naimarkDilatedState MsAnswer S.ψ)‖ +
      ‖applyOperatorToState (heteroKron (dilatedEffectA S x f 1) 1 - heteroKron 1 (dilatedEffectB S y g 1))
        (naimarkDilatedState MsAnswer S.ψ)‖ := by
  change ‖applyOperatorToState (heteroKron (dilatedEffectA S x f 0 - dilatedEffectA S x f 1) 1 -
    heteroKron 1 (dilatedEffectB S y g 0 - dilatedEffectB S y g 1)) _‖ ≤ _
  rw [heteroKron_sub_left, heteroKron_sub_right, sub_sub_sub_comm, applyOperatorToState_sub_op]
  exact norm_sub_le _ _

/-- Abstract compressed-product bound. -/
theorem norm_compressed_product_sub_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) (P A B Y : Op ι) (hPP : P * P = P) (hPc : Pᴴ * P ≤ 1)
    (h1Pc : (1 - P)ᴴ * (1 - P) ≤ 1) (hA : Aᴴ * A ≤ 1) (hY : Yᴴ * Y ≤ 1)
    (hv : applyOperatorToState P v = v) (hc : (1 - P) * A * Y = Y * ((1 - P) * A)) :
    ‖applyOperatorToState (P * A * P * (P * B * P) - A * B) v‖ ≤
      ‖applyOperatorToState ((1 - P) * B) v‖ + ‖applyOperatorToState ((1 - P) * A) v‖ +
        ‖applyOperatorToState (B - Y) v‖ := by
  have e : P * A * P * (P * B * P) - A * B = -(P * A * ((1 - P) * B)) - (1 - P) * A * (B - Y) -
      Y * ((1 - P) * A) - P * A * P * B * (1 - P) := by
    rw [← hc, show P * A * P * (P * B * P) = P * A * (P * P) * B * P by noncomm_ring, hPP]
    noncomm_ring
  have h4 : applyOperatorToState (P * A * P * B * (1 - P)) v = 0 := by
    rw [applyOperatorToState_mul, applyOperatorToState_sub_op, applyOperatorToState_one, hv,
      sub_self, applyOperatorToState_zero]
  rw [e, applyOperatorToState_sub_op, applyOperatorToState_sub_op, applyOperatorToState_sub_op,
    applyOperatorToState_neg_op, h4, sub_zero, applyOperatorToState_mul (P * A), applyOperatorToState_mul ((1 - P) * A),
    applyOperatorToState_mul Y]
  have := norm_applyOperatorToState_le (conjTranspose_mul_le_one_mul hPc hA)
    (applyOperatorToState ((1 - P) * B) v)
  have := norm_applyOperatorToState_le (conjTranspose_mul_le_one_mul h1Pc hA)
    (applyOperatorToState (B - Y) v)
  have := norm_applyOperatorToState_le hY (applyOperatorToState ((1 - P) * A) v)
  have := norm_sub_le (-applyOperatorToState (P * A) (applyOperatorToState ((1 - P) * B) v) -
    applyOperatorToState ((1 - P) * A) (applyOperatorToState (B - Y) v))
    (applyOperatorToState Y (applyOperatorToState ((1 - P) * A) v))
  have := norm_sub_le (-applyOperatorToState (P * A) (applyOperatorToState ((1 - P) * B) v))
    (applyOperatorToState ((1 - P) * A) (applyOperatorToState (B - Y) v))
  rw [norm_neg] at this
  linarith

/-- The defect of the compressed product `Π A Π · Π B Π` against `A B` on the
dilated state is controlled by the leakage of `A` and `B` and the intertwining
defect of `B` against any right-placed contraction `Y`.  Since `Π ψ' = ψ'`,
`(Π A Π Π B Π - A B) ψ' = -(Π A (1 - Π) B) ψ' - ((1 - Π) A B) ψ'`; the first
term is bounded by the leakage of `B`, and in the second `B ψ'` is replaced by
`Y ψ'`, which commutes past `(1 - Π) A`. -/
theorem norm_leftTensor_compressed_product_sub_le (α : Type) [Fintype α]
    [DecidableEq α] {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB]
    [DecidableEq ιB] (ψ : EuclideanSpace ℂ (ιA × ιB))
    (A B : Op (ιA × Option α)) (Y : Op (ιB × Option α))
    (hA : Aᴴ * A ≤ 1) (hY : Yᴴ * Y ≤ 1) :
    ‖applyOperatorToState (heteroKron (groundProjection ιA α * A * groundProjection ιA α *
        (groundProjection ιA α * B * groundProjection ιA α) - A * B) 1)
        (naimarkDilatedState α ψ)‖ ≤
      ‖applyOperatorToState (heteroKron ((1 - groundProjection ιA α) * B) 1)
        (naimarkDilatedState α ψ)‖ +
      ‖applyOperatorToState (heteroKron ((1 - groundProjection ιA α) * A) 1)
        (naimarkDilatedState α ψ)‖ +
      ‖applyOperatorToState (heteroKron B 1 - heteroKron 1 Y) (naimarkDilatedState α ψ)‖ := by
  have hG := isProj_groundProjection ιA α
  have h1 : 1 - heteroKron (groundProjection ιA α) (1 : Op (ιB × Option α)) =
      heteroKron (1 - groundProjection ιA α) 1 := by rw [heteroKron_sub_left, heteroKron_one_one]
  have := norm_compressed_product_sub_le _ _ (heteroKron A 1) (heteroKron B 1) _
    (by rw [heteroKron_mul, hG.isIdempotentElem.eq, mul_one])
    (conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_of_isProj hG))
    (h1 ▸ conjTranspose_mul_le_one_leftTensor (conjTranspose_mul_le_one_of_isProj hG.one_sub))
    (conjTranspose_mul_le_one_leftTensor hA) (conjTranspose_mul_le_one_rightTensor hY)
    (applyOperatorToState_leftTensor_groundProjection (α := α) ψ)
    (by simp only [h1, heteroKron_mul, mul_one, one_mul])
  simpa only [h1, heteroKron_mul, mul_one, ← heteroKron_sub_left] using this

theorem sq_add_le_of_sum_sq_le (ℓ : ZMod 2 → ℝ) (m ε : ℝ)
    (hL : ∑ b, ℓ b ^ 2 ≤ 2 * m) (hm : m ≤ 36 * ε) :
    (ℓ 0 + ℓ 1) ^ 2 ≤ 144 * ε := by
  have h2 : ∑ b : Fin 2, ℓ b ^ 2 ≤ 2 * m := hL
  rw [Fin.sum_univ_two] at h2
  have h3 : ℓ 0 ^ 2 + ℓ 1 ^ 2 ≤ 2 * m := h2
  nlinarith [sq_nonneg (ℓ 0 - ℓ 1)]

/-- The final arithmetic of the anticommutator transfer. -/
theorem anticommutator_arith {ι : Type} [Fintype ι] [DecidableEq ι] (ξ : EuclideanSpace ℂ ι)
    {Xo Zo Xd Zd : Op ι} {x z ε : ℝ}
    (h : ‖applyOperatorToState (Xo * Zo - Xd * Zd) ξ‖ + ‖applyOperatorToState (Zo * Xo - Zd * Xd) ξ‖ ≤
      x + 2 * z + (z + 2 * x))
    (hx : x ^ 2 ≤ 144 * ε) (hz : z ^ 2 ≤ 144 * ε) :
    ‖applyOperatorToState (Xo * Zo - -(Zo * Xo)) ξ‖ ^ 2 ≤
      3 * ‖applyOperatorToState (Xd * Zd - -(Zd * Xd)) ξ‖ ^ 2 + 15552 * ε := by
  have h0 : ‖applyOperatorToState (Xo * Zo - -(Zo * Xo)) ξ‖ ≤
      ‖applyOperatorToState (Xd * Zd - -(Zd * Xd)) ξ‖ + 3 * (x + z) :=
    (norm_add₃_le (a := applyOperatorToState (Xd * Zd - -(Zd * Xd)) ξ)
      (b := applyOperatorToState (Xo * Zo - Xd * Zd) ξ) (c := applyOperatorToState (Zo * Xo - Zd * Xd) ξ)).trans_eq'
      (by rw [← applyOperatorToState_add_op, ← applyOperatorToState_add_op]; congr 2; abel) |>.trans
      (by linarith)
  have h1 := mul_self_le_mul_self (norm_nonneg _) h0
  generalize ‖applyOperatorToState (Xd * Zd - -(Zd * Xd)) ξ‖ = a at h1 ⊢
  generalize ‖applyOperatorToState (Xo * Zo - -(Zo * Xo)) ξ‖ = o at h1 ⊢
  nlinarith [sq_nonneg (x - z), sq_nonneg (2 * a - 3 * (x + z))]

/-- Transfer of Alice's anticommutator estimate of `thm:ms-rigidity` from the
dilated strategy to the original one on the dilated state.  The transfer costs
the leakage of both dilated observables out of the ground slice, controlled by
the cell-consistency masses.  Blueprint `thm:ms-rigidity`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`. -/
theorem ms_anticommutator_transfer_A (S : Strategy msGame) (ε : ℝ) (hwin : 1 - ε ≤ S.value) :
    ‖applyOperatorToState
        (heteroKron (naimarkInflation (obsOf ((S.A (.var 0)).postprocess msBitOrZero))) 1 *
            heteroKron (naimarkInflation (obsOf ((S.A (.var 4)).postprocess msBitOrZero))) 1 -
          -(heteroKron (naimarkInflation (obsOf ((S.A (.var 4)).postprocess msBitOrZero))) 1 *
            heteroKron (naimarkInflation (obsOf ((S.A (.var 0)).postprocess msBitOrZero))) 1))
        (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 ≤
      3 * ‖applyOperatorToState
        (heteroKron (dilatedObsA S (.var 0)) 1 * heteroKron (dilatedObsA S (.var 4)) 1 -
          -(heteroKron (dilatedObsA S (.var 4)) 1 * heteroKron (dilatedObsA S (.var 0)) 1))
        (naimarkDilatedState MsAnswer S.ψ)‖ ^ 2 + 15552 * ε := by
  obtain ⟨i0, k0, h0⟩ := every_variable_is_incident 0
  obtain ⟨i4, k4, h4⟩ := every_variable_is_incident 4
  rw [naimarkInflation_obs_A, naimarkInflation_obs_A]
  have hXc := conjTranspose_mul_le_one_dilatedObsA S (.var 0)
  have hZc := conjTranspose_mul_le_one_dilatedObsA S (.var 4)
  have hYXc := conjTranspose_mul_le_one_dilatedObsB S (.constraint i0) (constraintBitOrZero k0)
  have hYZc := conjTranspose_mul_le_one_dilatedObsB S (.constraint i4) (constraintBitOrZero k4)
  -- leakage and intertwining of the two observables
  have hleakX := norm_leak_obs_le_A S (.var (msConstraintVars i0 k0)) (.constraint i0) msBitOrZero (constraintBitOrZero k0)
  have hintX := norm_intertwine_obs_le S (.var (msConstraintVars i0 k0)) (.constraint i0) msBitOrZero (constraintBitOrZero k0)
  have hleakZ := norm_leak_obs_le_A S (.var (msConstraintVars i4 k4)) (.constraint i4) msBitOrZero (constraintBitOrZero k4)
  have hintZ := norm_intertwine_obs_le S (.var (msConstraintVars i4 k4)) (.constraint i4) msBitOrZero (constraintBitOrZero k4)
  have hsqX := sq_add_le_of_sum_sq_le _ _ ε (sum_norm_sq_intertwining_le S (.var (msConstraintVars i0 k0)) (.constraint i0) msBitOrZero
    (constraintBitOrZero k0)) (reverse_cell_mismatch_mass_le S ε hwin i0 k0)
  have hsqZ := sq_add_le_of_sum_sq_le _ _ ε (sum_norm_sq_intertwining_le S (.var (msConstraintVars i4 k4)) (.constraint i4) msBitOrZero
    (constraintBitOrZero k4)) (reverse_cell_mismatch_mass_le S ε hwin i4 k4)
  rw [h0] at hleakX hintX hsqX
  rw [h4] at hleakZ hintZ hsqZ
  have hdXZ := norm_leftTensor_compressed_product_sub_le MsAnswer S.ψ _ (dilatedObsA S (.var 4)) _
    hXc hYZc
  have hdZX := norm_leftTensor_compressed_product_sub_le MsAnswer S.ψ _ (dilatedObsA S (.var 0)) _
    hZc hYXc
  exact anticommutator_arith _ (by simp only [heteroKron_mul, mul_one, ← heteroKron_sub_left]; linarith) hsqX hsqZ

end

end MIPStarRE.QPBT.MagicSquareRigidity
