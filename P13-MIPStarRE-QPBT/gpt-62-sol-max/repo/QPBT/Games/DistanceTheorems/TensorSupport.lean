module

public import QPBT.Games.MeasurementMap
public import QPBT.Games.DistanceTheorems.Support
public import MIPStarRE.LDT.Basic.TensorPlacement
public import MIPStarRE.LDT.MakingMeasurementsProjective.Defs
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

/-- Additive tensor embeddings, with identity on the unused side. -/
abbrev leftTensorAdd {I J : Type*} [DecidableEq J] : Op I →+ Op (I × J) :=
  ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)).flip (1 : Op J)).toAddMonoidHom

abbrev rightTensorAdd {I J : Type*} [DecidableEq I] : Op J →+ Op (I × J) :=
  ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)) (1 : Op I)).toAddMonoidHom

section

variable {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
include α ιA ιB

/-- Formalization-only definition used in the proof of Fact 4.26: place a
complete measurement on the left tensor factor. -/
noncomputable def leftPlacedMeasurement
    (M : MIPStarRE.Quantum.Measurement α ιA) :
    MIPStarRE.Quantum.Measurement α (ιA × ιB) :=
  M.mapEffects leftTensorAdd heteroKron_one_one
    (fun {_} h => kronecker_nonneg h Matrix.PosSemidef.one.nonneg)

/-- Formalization-only definition used in the proof of Fact 4.26: place a
complete measurement on the right tensor factor. -/
noncomputable def rightPlacedMeasurement
    (M : MIPStarRE.Quantum.Measurement α ιB) :
    MIPStarRE.Quantum.Measurement α (ιA × ιB) :=
  M.mapEffects rightTensorAdd heteroKron_one_one
    (fun {_} h => kronecker_nonneg Matrix.PosSemidef.one.nonneg h)

end

@[simp] theorem leftPlacedMeasurement_effect {α I J : Type*}
    [Fintype α] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Measurement α I) (a : α) :
    (leftPlacedMeasurement (ιB := J) M).effect a = heteroKron (M.effect a) 1 := rfl

@[simp] theorem rightPlacedMeasurement_effect {α I J : Type*}
    [Fintype α] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Measurement α J) (a : α) :
    (rightPlacedMeasurement (ιA := I) M).effect a = heteroKron 1 (M.effect a) := rfl

/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : Op ιA) (B : Op ιB) :
    stateQForm ψ (heteroKron A 1 * heteroKron 1 B) =
      stateQForm ψ (heteroKron A B) := by
  congr 1
  exact leftTensor_mul_rightTensor_eq_opTensor A B

/-- On a unit state, consistency is one minus the diagonal tensor overlap. -/
theorem consistencyDefect_placed_eq_one_sub_overlap {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hμ : μ.IsProbability) (hψ : ‖ψ‖ = 1) :
    bipartiteDefect μ A
        B ψ =
      1 - avgOver μ (fun x => ∑ a, stateQForm ψ
        (heteroKron ((A x).effect a) ((B x).effect a))) := by
  simpa only [measurementDefect, bipartiteDefect, leftPlacedMeasurement_effect,
    rightPlacedMeasurement_effect, placed_product_stateQForm_eq] using
    consistencyDefect_eq_one_sub_overlap μ
      (fun x => leftPlacedMeasurement (A x)) (fun x => rightPlacedMeasurement (B x))
      ψ hμ hψ

/-- Diagonal fiber sums keep exactly the pairs of matching labels. -/
theorem sum_matching_fibers {A B X R : Type*} [Fintype A] [Fintype B]
    [Fintype X] [DecidableEq X] [AddCommMonoid R]
    (f : A → X) (g : B → X) (w : A → B → R) :
    (∑ x, ∑ a ∈ Finset.univ.filter (fun a => f a = x),
      ∑ b ∈ Finset.univ.filter (fun b => g b = x), w a b) =
      ∑ a, ∑ b, if f a = g b then w a b else 0 := by
  rw [Finset.sum_fiberwise_apply Finset.univ f
    (fun a x => ∑ b ∈ Finset.univ.filter (fun b => g b = x), w a b)]
  simp only [Finset.sum_filter, eq_comm]

section

variable {α β γ ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
include α β γ ιA ιB

/-- The diagonal overlap of two relabelled measurements sums the original
pairs of outcomes with the same new label. -/
theorem diagonal_fiber_stateQForm_eq_pair_sum
    (A : α → Op ιA) (B : β → Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (f : α → γ) (g : β → γ) :
    (∑ r : γ, stateQForm ψ
      (heteroKron (∑ a ∈ Finset.univ.filter (fun a => f a = r), A a)
        (∑ b ∈ Finset.univ.filter (fun b => g b = r), B b))) =
      ∑ a : α, ∑ b : β, if f a = g b then
        stateQForm ψ (heteroKron (A a) (B b)) else 0 := by
  simp_rw [heteroKron_finset_sum_left, stateQForm_finset_sum,
    heteroKron_finset_sum_right, stateQForm_finset_sum]
  exact sum_matching_fibers f g fun a b => stateQForm ψ (heteroKron (A a) (B b))

/-- The fiber identity specialized to the effects of two measurements. -/
theorem diagonal_postprocess_stateQForm_eq_pair_sum
    (A : MIPStarRE.Quantum.Measurement α ιA) (B : MIPStarRE.Quantum.Measurement β ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (f : α → γ) (g : β → γ) :
    (∑ r : γ, stateQForm ψ
      (heteroKron ((A.postprocess f).effect r) ((B.postprocess g).effect r))) =
      ∑ a : α, ∑ b : β, if f a = g b then
        stateQForm ψ (heteroKron (A.effect a) (B.effect b)) else 0 := by
  simp only [MIPStarRE.Quantum.Measurement.postprocess_effect]
  exact diagonal_fiber_stateQForm_eq_pair_sum A.effect B.effect ψ f g

end

/-- The off-diagonal tensor overlap is the complementary mass of agreement. -/
theorem point_placed_defect_eq {α I J : Type*} [Fintype α] [DecidableEq α]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement α I) (B : Measurement α J) (ψ : EuclideanSpace ℂ (I × J)) :
    (∑ a, ∑ b, if a = b then 0 else stateQForm ψ (heteroKron (A.effect a) (B.effect b))) =
      ‖ψ‖ ^ 2 - ∑ a, stateQForm ψ (heteroKron (A.effect a) (B.effect a)) := by
  simpa only [leftPlacedMeasurement_effect, rightPlacedMeasurement_effect,
    placed_product_stateQForm_eq] using point_defect_eq
      (leftPlacedMeasurement A) (rightPlacedMeasurement B) ψ

/-- The total Born mass of two complete measurements is the squared state norm. -/
theorem sum_tensor_effect_stateQForm {α β I J : Type*} [Fintype α] [Fintype β]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement α I) (B : Measurement β J) (ψ : EuclideanSpace ℂ (I × J)) :
    (∑ a, ∑ b, stateQForm ψ (heteroKron (A.effect a) (B.effect b))) = ‖ψ‖ ^ 2 := by
  simp_rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_right, B.sum_eq_one,
    ← heteroKron_finset_sum_left, A.sum_eq_one, heteroKron_one_one, stateQForm_one]

/-- The mismatch mass after relabelling can be evaluated on the original outcomes. -/
theorem point_placed_defect_postprocess {α β γ I J : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Measurement α I) (B : Measurement β J) (ψ : EuclideanSpace ℂ (I × J))
    (f : α → γ) (g : β → γ) :
    (∑ c, ∑ d, if c = d then 0 else
      stateQForm ψ (heteroKron ((A.postprocess f).effect c) ((B.postprocess g).effect d))) =
    ∑ a, ∑ b, if f a = g b then 0 else stateQForm ψ (heteroKron (A.effect a) (B.effect b)) := by
  rw [point_placed_defect_eq, diagonal_postprocess_stateQForm_eq_pair_sum,
    ← sum_tensor_effect_stateQForm A B ψ]
  simp only [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by split_ifs <;> simp

/-- Postprocessing can only increase diagonal tensor overlap (Fact 4.26). -/
theorem diagonal_postprocess_stateQForm_ge {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (A : MIPStarRE.Quantum.Measurement α ιA)
    (B : MIPStarRE.Quantum.Measurement α ιB) (f : α → β) :
    (∑ b : β, stateQForm ψ
        (heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b))) ≥
      ∑ a : α, stateQForm ψ (heteroKron (A.effect a) (B.effect a)) := by
  rw [diagonal_postprocess_stateQForm_eq_pair_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  let w := fun b => if f a = f b then stateQForm ψ (heteroKron (A.effect a) (B.effect b)) else 0
  have hw (b : α) : 0 ≤ w b := by
    dsimp [w]
    split_ifs
    · exact stateQForm_nonneg ψ (MIPStarRE.Quantum.kronecker_nonneg (A.pos a) (B.pos b))
    · rfl
  simpa [w] using Finset.single_le_sum (f := w) (fun b _ => hw b) (Finset.mem_univ a)

/-- Tensor placement preserves square-summability of an operator family. -/
theorem leftTensor_sum_adjoint_mul_le_one {α ι κ : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {N : α → Op ι} (h : ∑ a, (N a)ᴴ * N a ≤ 1) :
    ∑ a, (leftTensor (ι₂ := κ) (N a))ᴴ * leftTensor (N a) ≤ 1 := by
  simpa only [leftTensor_conjTranspose, leftTensor_mul_leftTensor, ← leftTensor_finset_sum,
    leftTensor_one] using leftTensor_mono (ι₂ := κ) h

/-- Left placement preserves orthogonal projections. -/
theorem isProj_leftTensor {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {Q : Op ι} (hQ : IsProj Q) : IsProj (leftTensor (ι₂ := κ) Q) := by
  refine ⟨?_, ?_⟩
  · simp only [IsIdempotentElem, leftTensor_mul_leftTensor, hQ.isIdempotentElem.eq]
  · simp only [IsSelfAdjoint, Matrix.star_eq_conjTranspose, leftTensor_conjTranspose,
      hQ.isSelfAdjoint.isHermitian.eq]

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
    ∑ y ∈ Finset.univ.filter (fun y => f y = b), M.effect y * M.effect z =
        ∑ y ∈ Finset.univ.filter (fun y => f y = b),
          if y = z then M.effect z else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hyz : y = z
      · subst y
        simp
        exact (hM z).isIdempotentElem.eq
      · rw [if_neg hyz]
        exact projective_effect_mul_effect_eq_zero M hM hyz
    _ = if f z = b then M.effect z else 0 := by simp

section

variable {α β ι : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι] (M : Measurement (α × β) ι)
    (hM : QPBT.Measurement.IsProjective M) (r : α) (s : β)
include α β ι M hM r s

/-- The commuting marginals of a joint projective measurement multiply to its joint effect. -/
theorem joint_marginal_product :
    (M.postprocess Prod.fst).effect r * (M.postprocess Prod.snd).effect s = M.effect (r, s) := by
  classical
  rw [Measurement.postprocess_effect M Prod.snd, Finset.mul_sum]
  simp_rw [postprocess_effect_mul_effect M hM]
  simp_all [Finset.sum_eq_single (r, s)]

theorem joint_marginal_product_rev :
    (M.postprocess Prod.snd).effect s * (M.postprocess Prod.fst).effect r = M.effect (r, s) := by
  simpa only [Matrix.conjTranspose_mul, measurement_effect_hermitian] using
    congrArg Matrix.conjTranspose (joint_marginal_product M hM r s)

end

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: operators placed on opposite tensor factors commute. -/
theorem left_right_commute {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : Op ιA) (B : Op ιB) :
    leftTensor (ι₂ := ιB) A * rightTensor (ι₁ := ιA) B =
      rightTensor (ι₁ := ιA) B * leftTensor (ι₂ := ιB) A := by
  rw [leftTensor_mul_rightTensor_eq_opTensor,
    rightTensor_mul_leftTensor_eq_opTensor]

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: reindexing an operator family along an equivalence preserves its
distance. -/
theorem opFamilyDistSq_reindex {X α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (e : α ≃ β) (A B : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ A B ψ =
      opFamilyDistSq μ (fun x b => A x (e.symm b))
        (fun x b => B x (e.symm b)) ψ := by
  unfold opFamilyDistSq avgOver
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact Fintype.sum_equiv e
    (fun a => ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2)
    (fun b => ‖applyOperatorToState (A x (e.symm b) - B x (e.symm b)) ψ‖ ^ 2)
    (by simp)

/-- Simultaneous exchange of the two local spaces preserves consistency. -/
theorem consistencyDefect_prodComm {X α ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → α → Op ιA) (B : X → α → Op ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    consistencyDefect μ (fun x a => heteroKron (B x a) 1)
        (fun x a => heteroKron 1 (A x a)) (reindexState (Equiv.prodComm ιA ιB) ψ) =
      consistencyDefect μ (fun x a => heteroKron (A x a) 1)
        (fun x a => heteroKron 1 (B x a)) ψ := by
  unfold consistencyDefect
  simp_rw [placed_product_stateQForm_eq,
    stateQForm_reindexState, reindexOp_prodComm_heteroKron]
  apply avgOver_congr
  intro x
  rw [Finset.sum_comm]
  simp [eq_comm]

end MIPStarRE.QPBT.DistanceCalculus
