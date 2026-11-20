module

public import QPBT.Games.DistanceTheorems.Support
public import MIPStarRE.LDT.Preliminaries.ComparisonCore

/-!
# Tensor-placement and marginal identities

This module collects tensor-placement, marginal, and finite-fiber identities
used in data processing and the commutator estimate.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:397-461`
- Blueprint `fact:triangle-for-simeq`, `fact:data-processing`, and
  `lem:commutation-analysis`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective

section

variable {X α β γ δ ιA ιB : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
  [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-- Formalization-only definition used in the proof of Fact 4.26: place a
complete measurement on the left tensor factor. -/
noncomputable def leftPlacedMeasurement
    (M : MIPStarRE.Quantum.Measurement α ιA) :
    MIPStarRE.Quantum.Measurement α (ιA × ιB) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => heteroKron (M.effect a) 1)
    (fun a => MIPStarRE.Quantum.kronecker_nonneg (M.pos a)
      (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : Op ιB)))
    (by
      change ∑ a : α, leftTensor (ι₂ := ιB) (M.effect a) = 1
      rw [leftTensor_finset_sum, M.sum_eq_one, leftTensor_one])

/-- Formalization-only definition used in the proof of Fact 4.26: place a
complete measurement on the right tensor factor. -/
noncomputable def rightPlacedMeasurement
    (M : MIPStarRE.Quantum.Measurement α ιB) :
    MIPStarRE.Quantum.Measurement α (ιA × ιB) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => heteroKron 1 (M.effect a))
    (fun a => MIPStarRE.Quantum.kronecker_nonneg
      (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : Op ιA)) (M.pos a))
    (by
      change ∑ a : α, rightTensor (ι₁ := ιA) (M.effect a) = 1
      rw [rightTensor_finset_sum, M.sum_eq_one, rightTensor_one])

/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : Op ιA) (B : Op ιB) :
    stateQForm ψ (heteroKron A 1 * heteroKron 1 B) =
      stateQForm ψ (heteroKron A B) := by
  congr 1
  apply leftTensor_mul_rightTensor_eq_opTensor

variable (ψ : EuclideanSpace ℂ (ιA × ιB))

/-- A scalar payoff may be pulled back along the two outcome maps. -/
theorem born_payoff_postprocess [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (A : Measurement α ιA) (B : Measurement β ιB) (f : α → γ) (g : β → δ) (v : γ → δ → ℝ) :
    (∑ i, ∑ j, v i j * stateQForm ψ (heteroKron ((A.postprocess f).effect i)
      ((B.postprocess g).effect j))) =
      ∑ a, ∑ b, v (f a) (g b) * stateQForm ψ (heteroKron (A.effect a) (B.effect b)) := by
  classical
  simp only [Measurement.postprocess_effect, heteroKron_finset_sum_left,
    stateQForm_finset_sum, Finset.mul_sum]
  simp only [heteroKron_finset_sum_right, stateQForm_finset_sum, Finset.mul_sum]
  conv_lhs => arg 2; intro i; rw [Finset.sum_comm]
  rw [Finset.sum_readout f]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_readout g _

noncomputable def diagonalOverlap (A : Measurement α ιA) (B : Measurement α ιB) :=
  ∑ a, stateQForm ψ (heteroKron (A.effect a) (B.effect a))

theorem bipartiteDefect_eq_one_sub [Fintype X] [DecidableEq X] [DecidableEq α]
    {μ : Distribution X} (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    bipartiteDefect μ A B ψ = 1 - avgOver μ (fun x => diagonalOverlap ψ (A x) (B x)) := by
  simpa only [leftPlacedMeasurement, rightPlacedMeasurement, Measurement.ofSumEqOne,
    diagonalOverlap, placed_product_stateQForm_eq] using consistencyDefect_eq_one_sub_overlap
      (fun x => leftPlacedMeasurement (A x)) (fun x => rightPlacedMeasurement (B x)) hμ hψ

variable [DecidableEq α] [DecidableEq β] (A : Measurement α ιA) (B : Measurement α ιB) (f : α → β)

theorem diagonal_postprocess_stateQForm_eq_pair_sum :
    (∑ b, stateQForm ψ (heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b))) =
      ∑ a, ∑ b, if f a = f b then stateQForm ψ (heteroKron (A.effect a) (B.effect b)) else 0 := by
  simpa [ite_mul] using born_payoff_postprocess ψ A B f f (fun i j => if i = j then 1 else 0)

/-- Postprocessing can only increase diagonal tensor overlap. -/
theorem diagonal_postprocess_stateQForm_ge :
    (∑ b, stateQForm ψ (heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b))) ≥
      ∑ a, stateQForm ψ (heteroKron (A.effect a) (B.effect a)) := by
  rw [diagonal_postprocess_stateQForm_eq_pair_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  simpa using Finset.single_le_sum (f := fun b => if f a = f b then
    stateQForm ψ (heteroKron (A.effect a) (B.effect b)) else 0)
    (fun b _ => ite_nonneg (stateQForm_nonneg ψ (kronecker_nonneg (A.pos a) (B.pos b)))
      le_rfl)
    (Finset.mem_univ a)

end

section

variable {α β ι ιA ιB : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι] [Fintype ιA]
  [DecidableEq ιA] (M : MIPStarRE.Quantum.Measurement (α × β) ι) [Fintype ιB] [DecidableEq ιB]
  (a : α)

/-- The squared effects in one fiber of a pair-valued measurement sum to at
most the identity. This is the formalization-only estimate
`lem:sandwich-pair-fiber-sum` used for a joint-measurement marginal in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem measurement_fiber_sum_adjoint_mul_le_one :
    ∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b) ≤ 1 := by
  classical
  have hsquare_le (z : α × β) :
      (M.effect z)ᴴ * M.effect z ≤ M.effect z := by
    rw [measurement_effect_hermitian]
    exact MIPStarRE.Quantum.sq_le_self (M.pos z) (measurement_effect_le_one M z)
  rw [← M.sum_eq_one]
  rw [← (Fintype.sum_prod_type _).symm]
  refine le_trans (Finset.sum_le_sum fun b _ => hsquare_le (a, b)) ?_
  exact Finset.single_le_sum
    (fun a' _ => Finset.sum_nonneg fun b _ => M.pos (a', b))
    (Finset.mem_univ a)

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: a left-placed measurement fiber is square-summable. -/
theorem left_fiber_contraction
    (M : MIPStarRE.Quantum.Measurement (α × β) ιA) (a : α) :
    (1 - ∑ b : β, (leftTensor (ι₂ := ιB) (M.effect (a, b)))ᴴ *
      leftTensor (ι₂ := ιB) (M.effect (a, b))).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg]
  calc
    _ =
        _ := by
      congr 1 with b
      simp [leftTensor_mul_leftTensor]
    _ = _ :=
      leftTensor_finset_sum Finset.univ _
    _ ≤ _ :=
      leftTensor_mono (measurement_fiber_sum_adjoint_mul_le_one M a)
    _ = 1 := leftTensor_one

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: a right-placed measurement fiber is square-summable. -/
theorem right_fiber_contraction
    (M : MIPStarRE.Quantum.Measurement (α × β) ιB) (a : α) :
    (1 - ∑ b : β, (rightTensor (ι₁ := ιA) (M.effect (a, b)))ᴴ *
      rightTensor (ι₁ := ιA) (M.effect (a, b))).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg]
  calc
    _ =
        _ := by
      congr 1 with b
      simp [rightTensor_mul_rightTensor]
    _ = _ :=
      rightTensor_finset_sum Finset.univ _
    _ ≤ _ :=
      rightTensor_mono (measurement_fiber_sum_adjoint_mul_le_one M a)
    _ = 1 := rightTensor_one

end

/-- A projective effect is selected exactly by its matching postprocessing
fiber. This is the formalization-only identity
`lem:sandwich-postprocess-effect-left` used in the joint-family comparison for
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem postprocess_effect_mul_effect {ζ α ι : Type*}
    [Fintype ζ] [DecidableEq ζ] [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement ζ ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : ζ → α) (b : α) (z : ζ) :
    (M.postprocess f).effect b * M.effect z =
      if f z = b then M.effect z else 0 := by
  classical
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_mul]
  calc
    _ =
        ∑ y ∈ Finset.univ.filter (fun y => f y = b),
          if y = z then M.effect z else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hyz : y = z
      · subst y
        rw [if_pos rfl]
        exact (hM z).isIdempotentElem.eq
      · rw [if_neg hyz]
        solve_by_elim [projective_effect_mul_effect_eq_zero]
    _ = _ := by simp

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: compatible projective marginals multiply to the joint effect. -/
theorem joint_marginal_product {α β γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    {M : MIPStarRE.Quantum.Measurement ((α × β) × γ) ι}
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (a : α) (b : β) (c : γ) :
    ((M.postprocess (fun abc => abc.1)).effect (a, b)) *
        ((M.postprocess (fun abc => (abc.1.1, abc.2))).effect (a, c)) =
      M.effect ((a, b), c) := by
  classical
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect]
  rw [Finset.mul_sum]
  calc
    _ =
      _ := by
      apply Finset.sum_congr rfl
      intro z _
      solve_by_elim [postprocess_effect_mul_effect]
    _ = _ := by
      rw [Finset.sum_eq_single ((a, b), c)]
      · simp
      · intro z hz hne
        rw [if_neg]
        grind
      · simp

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: compatible projective marginals multiply to the joint effect in
reverse order. -/
theorem joint_marginal_product_rev {α β γ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement ((α × β) × γ) ι)
    (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (a : α) (b : β) (c : γ) :
    ((M.postprocess (fun abc => (abc.1.1, abc.2))).effect (a, c)) *
        ((M.postprocess (fun abc => abc.1)).effect (a, b)) =
      M.effect ((a, b), c) := by
  have h := congrArg Matrix.conjTranspose (joint_marginal_product hM a b c)
  rw [Matrix.conjTranspose_mul, (measurement_effect_hermitian
    (M.postprocess (fun abc => (abc.1.1, abc.2))) (a, c)), (measurement_effect_hermitian
    (M.postprocess (fun abc => abc.1)) (a, b)), (measurement_effect_hermitian M ((a, b), c))] at h
  exact h

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: operators placed on opposite tensor factors commute. -/
theorem left_right_commute {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Op ιA) (B : Op ιB) :
    leftTensor (ι₂ := ιB) A * rightTensor (ι₁ := ιA) B =
      rightTensor (ι₁ := ιA) B * leftTensor (ι₂ := ιB) A := by
  rw [leftTensor_mul_rightTensor_eq_opTensor,
    rightTensor_mul_leftTensor_eq_opTensor]

section

variable {X α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
  (μ : Distribution X) (e : α ≃ β) (A B A' B' : X → α → Op ι) (ψ : EuclideanSpace ℂ ι)

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: reindexing an operator family along an equivalence preserves its
distance. -/
theorem opFamilyDistSq_reindex :
    opFamilyDistSq μ A B ψ =
      opFamilyDistSq μ (fun x b => A x (e.symm b))
        (fun x b => B x (e.symm b)) ψ := by
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact Fintype.sum_equiv e
    _
    (fun b => ‖applyOperatorToState (A x (e.symm b) - B x (e.symm b)) ψ‖ ^ 2)
    (by intro a; simp)

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: pointwise equal operator families have equal state-dependent
distance. -/
theorem opFamilyDistSq_congr
    (hA : ∀ x a, A x a = A' x a) (hB : ∀ x a, B x a = B' x a) :
    opFamilyDistSq μ A B ψ = opFamilyDistSq μ A' B' ψ := by
  unfold opFamilyDistSq avgOver
  simp_all

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: pointwise equal operator differences have equal state-dependent
distance. -/
theorem opFamilyDistSq_congr_sub
    (h : ∀ x a, A x a - B x a = A' x a - B' x a) :
    opFamilyDistSq μ A B ψ = opFamilyDistSq μ A' B' ψ := by
  unfold opFamilyDistSq avgOver
  simp_all

end

/-- Formalization-only definition used in approximate commutation at paper
lines 410--461: exchange the final two coordinates of a nested product. -/
def swapLast (α β γ : Type*) : ((α × γ) × β) ≃ ((α × β) × γ) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv := by rintro ⟨⟨a, c⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨a, b⟩, c⟩; rfl

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: the inverse of `swapLast` has the same coordinate formula. -/
@[simp] theorem swapLast_symm_apply {α β γ : Type*}
    (p : (α × β) × γ) :
    (swapLast α β γ).symm p = ((p.1.1, p.2), p.1.2) :=
  rfl

end MIPStarRE.QPBT.DistanceCalculus
