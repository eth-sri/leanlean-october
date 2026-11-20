module

public import QPBT.Games.DistanceTheorems.TensorSupport
public import QPBT.Games.StrategyClasses

/-! # Transporting state-dependent distances between index sets -/
@[expose] public section
open scoped BigOperators Matrix MatrixOrder ComplexOrder
namespace MIPStarRE.QPBT.WinImplications
open MIPStarRE.LDT MIPStarRE.Quantum

/-- Reindexing an operator is computed entrywise, hence commutes with
subtraction. Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_sub {ι ι' : Type*} (e : ι ≃ ι') (M N : Op ι') :
    reindexOp e (M - N) = reindexOp e M - reindexOp e N := rfl

/-- Interchanging the two tensor factors turns a Kronecker product into the
product of the exchanged factors. Formalization-only support for the
interchanged conclusions of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_prodComm_heteroKron {ιA ιB : Type*}
    (A : Op ιA) (B : Op ιB) :
    reindexOp (Equiv.prodComm ιA ιB) (heteroKron B A) = heteroKron A B := by
  ext i j
  simp [reindexOp, heteroKron, Matrix.kroneckerMap, Matrix.reindex_apply, mul_comm]

/-- Coordinates of an operator applied to a reindexed state. Formalization-only
support for the interchanged conclusions of `lem:qld-win-implications`,
blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem applyOperatorToState_reindexState_ofLp {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (T : Op κ) (ψ : EuclideanSpace ℂ ι) (k : κ) :
    (applyOperatorToState T (reindexState e ψ)).ofLp k =
      (applyOperatorToState (reindexOp e T) ψ).ofLp (e.symm k) := by
  change (T *ᵥ (reindexState e ψ).ofLp) k = (reindexOp e T *ᵥ ψ.ofLp) (e.symm k)
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
    ← e.sum_comp]
  congr 1 with j
  simp [reindexState, reindexOp]

section

variable {ι κ : Type*} [Fintype ι]

/-- Reindexing an operator along an equivalence is multiplicative.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem reindexOp_mul [Fintype κ]
    (e : ι ≃ κ) (M N : Op κ) :
    reindexOp e (M * N) = reindexOp e M * reindexOp e N := by
  ext i j
  change (M * N) (e i) (e j) = ∑ k : ι, M (e i) (e k) * N (e k) (e j)
  rw [Matrix.mul_apply, ← e.sum_comp]

/-- The real quadratic form is invariant under simultaneous reindexing of the
state and operator. Formalization-only support for the interchanged conclusions
of blueprint `lem:qld-win-implications`; see
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:227`. -/
theorem stateQForm_reindexState [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (T : Op κ)
    (ψ : EuclideanSpace ℂ ι) :
    DistanceCalculus.stateQForm (reindexState e ψ) T =
      DistanceCalculus.stateQForm ψ (reindexOp e T) := by
  unfold DistanceCalculus.stateQForm
  apply congrArg Complex.re
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  rw [← e.symm.sum_comp]
  congr 1 with k
  rw [applyOperatorToState_reindexState_ofLp]
  rfl

end

/-- Reindexing a state and its operator preserves the length of the image.
Formalization-only support for the interchanged conclusions of
`lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:701-703`. -/
theorem norm_applyOperatorToState_reindexState {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (T : Op κ) (ψ : EuclideanSpace ℂ ι) :
    ‖applyOperatorToState T (reindexState e ψ)‖ =
      ‖applyOperatorToState (reindexOp e T) ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    ← e.symm.sum_comp]
  congr 1 with k
  rw [applyOperatorToState_reindexState_ofLp]

/-- Pulling both families back along the coordinate equivalence preserves
squared distance in the transported state. -/
theorem opFamilyDistSq_reindexState {X α ι κ : Type*} [Fintype α]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (e : ι ≃ κ)
    (μ : Distribution X) (A B : X → α → Op κ) (ψ : EuclideanSpace ℂ ι) :
    opFamilyDistSq μ A B (reindexState e ψ) = opFamilyDistSq μ
      (fun x a => reindexOp e (A x a)) (fun x a => reindexOp e (B x a)) ψ := by
  unfold opFamilyDistSq
  simp_rw [norm_applyOperatorToState_reindexState, reindexOp_sub]

end MIPStarRE.QPBT.WinImplications
