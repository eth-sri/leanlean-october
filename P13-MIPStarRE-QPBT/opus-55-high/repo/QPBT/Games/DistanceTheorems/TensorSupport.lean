module

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

open MIPStarRE.LDT MIPStarRE.Quantum
open MIPStarRE.LDT.MakingMeasurementsProjective

/-- Formalization-only definition used in the proof of Fact 4.26: place a
complete measurement on the left tensor factor. -/
noncomputable def leftPlacedMeasurement {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
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
noncomputable def rightPlacedMeasurement {α ιA ιB : Type*}
    [Fintype α] [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Measurement α ιB) :
    MIPStarRE.Quantum.Measurement α (ιA × ιB) :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne
    (fun a => heteroKron 1 (M.effect a))
    (fun a => MIPStarRE.Quantum.kronecker_nonneg
      (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : Op ιA)) (M.pos a))
    (by
      change ∑ a : α, rightTensor (ι₁ := ιA) (M.effect a) = 1
      rw [rightTensor_finset_sum, M.sum_eq_one, rightTensor_one])

variable {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-- Formalization-only auxiliary lemma for Fact 4.26: products of left and right
placements evaluate as a Kronecker product. -/
theorem placed_product_stateQForm_eq (ψ : EuclideanSpace ℂ (ιA × ιB)) (A : Op ιA) (B : Op ιB) :
    stateQForm ψ (heteroKron A 1 * heteroKron 1 B) =
      stateQForm ψ (heteroKron A B) := by
  congr 1
  exact leftTensor_mul_rightTensor_eq_opTensor A B

/-- The (possibly unnormalized) rank-one state associated to a Euclidean vector. -/
noncomputable def vectorQuantumState {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : QuantumState ι where
  density := pureDensity ψ.ofLp
  density_psd := by
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    exact (Matrix.posSemidef_vecMulVec_self_star ψ.ofLp).smul
      (by positivity : 0 ≤ (Fintype.card ι : ℂ))

/-- Evaluation in the rank-one vector state is the corresponding quadratic form. -/
theorem vectorQuantumState_ev_eq_stateQForm {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (T : Op ι) :
    ev (vectorQuantumState ψ) T = stateQForm ψ T := by
  change (MIPStarRE.Quantum.normalizedTrace (pureDensity ψ.ofLp * T)).re =
    stateQForm ψ T
  rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
  unfold pureDensity MIPStarRE.Quantum.normalizedTrace
  rw [Matrix.mul_smul, Matrix.mul_vecMulVec, Matrix.trace_smul, Matrix.trace_vecMulVec]
  simp [mul_div_cancel_left₀, stateQForm, applyOperatorToState, EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- Formalization-only auxiliary lemma for Fact 4.26: postprocessing can only
increase diagonal tensor overlap. -/
theorem diagonal_postprocess_stateQForm_ge {α β ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : EuclideanSpace ℂ (ιA × ιB))
    (A : MIPStarRE.Quantum.Measurement α ιA)
    (B : MIPStarRE.Quantum.Measurement α ιB) (f : α → β) :
    (∑ b : β, stateQForm ψ
        (heteroKron ((A.postprocess f).effect b) ((B.postprocess f).effect b))) ≥
      ∑ a : α, stateQForm ψ (heteroKron (A.effect a) (B.effect a)) := by
  cases isEmpty_or_nonempty (ιA × ιB) with
  | inl hι =>
      have hψ : ψ = 0 := Subsingleton.elim _ _
      simp_all [stateQForm, applyOperatorToState]
  | inr hι =>
      letI : Nonempty ιA := ⟨(Classical.choice hι).1⟩
      letI : Nonempty ιB := ⟨(Classical.choice hι).2⟩
      let HA : FiniteHilbertSpace :=
        { carrier := ιA
          instFintype := inferInstance
          instDecidableEq := inferInstance
          instNonempty := inferInstance }
      let HB : FiniteHilbertSpace :=
        { carrier := ιB
          instFintype := inferInstance
          instDecidableEq := inferInstance
          instNonempty := inferInstance }
      let As :=
        (MatrixMeasurement.toMeasurement (H := HA) A).toSubMeas
      let Bs :=
        (MatrixMeasurement.toMeasurement (H := HB) B).toSubMeas
      have hAoutcome (a : α) : As.outcome a = A.effect a := by
        simp [As, HA]
      have hBoutcome (a : α) : Bs.outcome a = B.effect a := by
        simp [Bs, HB]
      have hApost (b : β) :
          (MIPStarRE.LDT.postprocess As f).outcome b =
            (A.postprocess f).effect b := by
        rw [SubMeas.postprocess_outcome,
          MIPStarRE.Quantum.Measurement.postprocess_effect]
        apply Finset.sum_congr rfl
        intro a _
        exact hAoutcome a
      have hBpost (b : β) :
          (MIPStarRE.LDT.postprocess Bs f).outcome b =
            (B.postprocess f).effect b := by
        rw [SubMeas.postprocess_outcome,
          MIPStarRE.Quantum.Measurement.postprocess_effect]
        apply Finset.sum_congr rfl
        intro a _
        exact hBoutcome a
      have h := MIPStarRE.LDT.Preliminaries.qMatchMass_leftRight_postprocess_ge
        (vectorQuantumState ψ) As Bs f
      grind [qMatchMass, leftPlacedSubMeas_outcome, rightPlacedSubMeas_outcome, leftTensor_mul_rightTensor_eq_opTensor, vectorQuantumState_ev_eq_stateQForm, MIPStarRE.QPBT.heteroKron]

/-- The squared effects in one fiber of a pair-valued measurement sum to at
most the identity. This is the formalization-only estimate
`lem:sandwich-pair-fiber-sum` used for a joint-measurement marginal in
`lem:ld-sandwich`; detailed source argument
`references/neexp-paper/05_quantum_preliminaries.tex:930-946`. -/
theorem measurement_fiber_sum_adjoint_mul_le_one {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (M : MIPStarRE.Quantum.Measurement (α × β) ι) (a : α) :
    ∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b) ≤ 1 := by
  have hsquare_le (z : α × β) :
      (M.effect z)ᴴ * M.effect z ≤ M.effect z := by
    rw [measurement_effect_hermitian M z]
    exact MIPStarRE.Quantum.sq_le_self (M.pos z) (measurement_effect_le_one M z)
  calc
    ∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b) ≤
        ∑ b : β, M.effect (a, b) :=
      Finset.sum_le_sum fun b _ => hsquare_le (a, b)
    _ ≤ ∑ a' : α, ∑ b : β, M.effect (a', b) :=
      Finset.single_le_sum
        (fun a' _ => Finset.sum_nonneg fun b _ => M.pos (a', b))
        (Finset.mem_univ a)
    _ = ∑ z : α × β, M.effect z := (Fintype.sum_prod_type _).symm
    _ = 1 := M.sum_eq_one

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: a left-placed measurement fiber is square-summable. -/
theorem left_fiber_contraction {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Measurement (α × β) ιA) (a : α) :
    (1 - ∑ b : β, (leftTensor (ι₂ := ιB) (M.effect (a, b)))ᴴ *
      leftTensor (ι₂ := ιB) (M.effect (a, b))).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg]
  calc
    ∑ b : β, (leftTensor (ι₂ := ιB) (M.effect (a, b)))ᴴ *
          leftTensor (ι₂ := ιB) (M.effect (a, b)) =
        ∑ b : β, leftTensor (ι₂ := ιB)
          ((M.effect (a, b))ᴴ * M.effect (a, b)) := by
      simp [leftTensor_conjTranspose, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ιB)
        (∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b)) :=
      leftTensor_finset_sum Finset.univ _
    _ ≤ leftTensor (ι₂ := ιB) (1 : Op ιA) :=
      leftTensor_mono (measurement_fiber_sum_adjoint_mul_le_one M a)
    _ = 1 := leftTensor_one

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: a right-placed measurement fiber is square-summable. -/
theorem right_fiber_contraction {α β ιA ιB : Type*}
    [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (M : MIPStarRE.Quantum.Measurement (α × β) ιB) (a : α) :
    (1 - ∑ b : β, (rightTensor (ι₁ := ιA) (M.effect (a, b)))ᴴ *
      rightTensor (ι₁ := ιA) (M.effect (a, b))).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [sub_nonneg]
  calc
    ∑ b : β, (rightTensor (ι₁ := ιA) (M.effect (a, b)))ᴴ *
          rightTensor (ι₁ := ιA) (M.effect (a, b)) =
        ∑ b : β, rightTensor (ι₁ := ιA)
          ((M.effect (a, b))ᴴ * M.effect (a, b)) := by
      simp [rightTensor_conjTranspose, rightTensor_mul_rightTensor]
    _ = rightTensor (ι₁ := ιA)
        (∑ b : β, (M.effect (a, b))ᴴ * M.effect (a, b)) :=
      rightTensor_finset_sum Finset.univ _
    _ ≤ rightTensor (ι₁ := ιA) (1 : Op ιB) :=
      rightTensor_mono (measurement_fiber_sum_adjoint_mul_le_one M a)
    _ = 1 := rightTensor_one

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
  rw [MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.sum_mul]
  calc
    ∑ y ∈ Finset.univ.filter (fun y => f y = b), M.effect y * M.effect z =
        ∑ y ∈ Finset.univ.filter (fun y => f y = b),
          if y = z then M.effect z else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hyz : y = z
      · subst y
        rw [if_pos rfl]
        exact (hM z).isIdempotentElem.eq
      simp_all [projective_effect_mul_effect_eq_zero]
    _ = if f z = b then M.effect z else 0 := by simp

variable {α β γ ι : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]

/-- Two coarse-grainings of one projective measurement commute. -/
theorem postprocess_effect_commute {ζ α β V : Type*}
    [Fintype ζ] [DecidableEq ζ] [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype V] [DecidableEq V]
    (M : MIPStarRE.Quantum.Measurement ζ V) (hM : MIPStarRE.QPBT.Measurement.IsProjective M)
    (f : ζ → α) (g : ζ → β) (a : α) (b : β) :
    Commute ((M.postprocess f).effect a) ((M.postprocess g).effect b) := by
  rw [Measurement.postprocess_effect, Measurement.postprocess_effect]
  refine Commute.sum_left _ _ _ fun x _ => Commute.sum_right _ _ _ fun y _ => ?_
  by_cases hxy : x = y
  · subst y
    exact Commute.refl _
  · rw [commute_iff_eq, projective_effect_mul_effect_eq_zero M hM hxy,
      projective_effect_mul_effect_eq_zero M hM (Ne.symm hxy)]

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: operators placed on opposite tensor factors commute. -/
theorem left_right_commute (A : Op ιA) (B : Op ιB) :
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
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact Fintype.sum_equiv e
    (fun a => ‖applyOperatorToState (A x a - B x a) ψ‖ ^ 2)
    (fun b => ‖applyOperatorToState (A x (e.symm b) - B x (e.symm b)) ψ‖ ^ 2)
    (by simp)


/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: pointwise equal operator differences have equal state-dependent
distance. -/
theorem opFamilyDistSq_congr_sub {X α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (μ : Distribution X) (A B A' B' : X → α → Op ι)
    (ψ : EuclideanSpace ℂ ι)
    (h : ∀ x a, A x a - B x a = A' x a - B' x a) :
    opFamilyDistSq μ A B ψ = opFamilyDistSq μ A' B' ψ := by
  unfold opFamilyDistSq avgOver
  simp_all

/-- Formalization-only definition used in approximate commutation at paper
lines 410--461: exchange the final two coordinates of a nested product. -/
def swapLast (α β γ : Type*) : ((α × γ) × β) ≃ ((α × β) × γ) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv := by grind
  right_inv := by grind

/-- Formalization-only auxiliary lemma for approximate commutation at paper
lines 410--461: the inverse of `swapLast` has the same coordinate formula. -/
@[simp] theorem swapLast_symm_apply {α β γ : Type*}
    (p : (α × β) × γ) :
    (swapLast α β γ).symm p = ((p.1.1, p.2), p.1.2) :=
  rfl

end MIPStarRE.QPBT.DistanceCalculus
