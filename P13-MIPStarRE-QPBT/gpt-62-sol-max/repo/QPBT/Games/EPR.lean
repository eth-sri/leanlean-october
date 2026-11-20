module

public import QPBT.Algebra.Pauli
public import QPBT.Games.DistanceTheorems.TensorState

/-! Exact actions and overlaps on a maximally entangled pair. -/

@[expose] public section

open scoped Matrix

namespace MIPStarRE.QPBT

open MIPStarRE.Quantum DistanceCalculus

/-- The EPR state is unchanged by exchanging its two halves. -/
theorem reindexState_prodComm_eprState
    (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V] :
    reindexState (Equiv.prodComm V V) (eprState V) = eprState V := by
  apply (EuclideanSpace.equiv (V × V) ℂ).injective
  funext p
  rcases p with ⟨i, j⟩
  simp only [reindexState, eprState, ContinuousLinearEquiv.apply_symm_apply,
    Equiv.prodComm, Equiv.coe_fn_symm_mk]
  grind

/-- A symmetric operator acts identically on the two halves of an EPR state. -/
theorem epr_action_eq_of_transpose
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (E : Op V) (hE : Eᵀ = E) :
    (heteroKron E 1).mulVec (eprState V) =
      (heteroKron 1 E).mulVec (eprState V) := by
  ext p
  rcases p with ⟨i, j⟩
  simpa [heteroKron, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    eprState, Matrix.one_apply] using congrFun (congrFun hE j) i

section

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

section

variable (A B : Op V) (hB : Bᵀ = B)
include A B hB

/-- Move a symmetric right factor to the left before evaluating on the EPR state. -/
theorem epr_mulVec_heteroKron :
    (heteroKron A B).mulVec (eprState V) =
      (heteroKron (A * B) 1).mulVec (eprState V) := by
  have h : heteroKron A B = heteroKron A 1 * heteroKron 1 B := by
    simp only [heteroKron_mul, mul_one, one_mul]
  rw [h, ← Matrix.mulVec_mulVec, ← epr_action_eq_of_transpose B hB,
    Matrix.mulVec_mulVec, heteroKron_mul, mul_one]

/-- A zero product on one half implies zero action on the maximally entangled pair. -/
theorem heteroKron_mulVec_epr_eq_zero_of_mul_eq_zero (hAB : A * B = 0) :
    (heteroKron A B).mulVec (eprState V) = 0 := by
  rw [epr_mulVec_heteroKron A B hB, hAB]
  simp [heteroKron]

/-- The overlap of a tensor on an EPR pair can be computed on one half. -/
theorem stateQForm_eprState_heteroKron :
    stateQForm (eprState V) (heteroKron A B) =
      stateQForm (eprState V) (heteroKron (A * B) 1) := by
  unfold stateQForm applyOperatorToState
  congr 2
  ext p
  exact congrFun (epr_mulVec_heteroKron A B hB) p

end

/-- Exchanging the two factors does not change an EPR overlap. -/
theorem stateQForm_eprState_swap (A B : Op V) :
    stateQForm (eprState V) (heteroKron A B) =
      stateQForm (eprState V) (heteroKron B A) := by
  have h := stateQForm_reindexState (Equiv.prodComm V V) (heteroKron A B) (eprState V)
  simpa only [reindexState_prodComm_eprState, reindexOp_prodComm_heteroKron] using h

/-- One-sided overlaps of a complete operator family sum to one. -/
theorem sum_stateQForm_eprState_left {α : Type*} [Fintype α] (A : α → Op V)
    (hA : ∑ a, A a = 1) :
    ∑ a, stateQForm (eprState V) (heteroKron (A a) 1) = 1 := by
  rw [← stateQForm_finset_sum, ← heteroKron_finset_sum_left, hA,
    heteroKron_one_one, stateQForm_one, eprState_norm, one_pow]

end

/-- A symmetric operator acts identically on the two halves of the extracted
EPR pair, including arbitrary auxiliary registers in local player order. -/
theorem extracted_epr_actions_eq {I J V : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (aux : EuclideanSpace ℂ (I × J)) (T : Op V) (hT : Tᵀ = T) :
    applyOperatorToState (heteroKron (heteroKron (1 : Op I) T) (1 : Op (J × V)))
        (reindexState prodShuffle (vecTensor aux (eprState V))) =
      applyOperatorToState (heteroKron (1 : Op (I × V)) (heteroKron (1 : Op J) T))
        (reindexState prodShuffle (vecTensor aux (eprState V))) := by
  have h : applyOperatorToState (heteroKron T 1) (eprState V) =
      applyOperatorToState (heteroKron 1 T) (eprState V) := by
    ext p
    exact congrFun (epr_action_eq_of_transpose T hT) p
  have hA := reindexOp_prodShuffle_heteroKron (1 : Op I) (1 : Op J) T (1 : Op V)
  have hB := reindexOp_prodShuffle_heteroKron (1 : Op I) (1 : Op J) (1 : Op V) T
  simp only [heteroKron_one_one] at hA hB
  simp only [applyOperatorToState_reindexState, hA, hB, applyOperatorToState_heteroKron_vecTensor, h]

end MIPStarRE.QPBT
