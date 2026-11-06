module

public import QPBT.Observables.WinImplications.Consistency

/-!
# Interchange of the tensor factors in the winning implications

This module collects the statements shared by the operator-distance companions
of the winning implications and by their factor-interchanged forms: transport of
the state-dependent distance along the interchange of the two tensor factors,
the constant-factor passage from consistency to distance, the reversed
verifier edges, and the clause-by-clause symmetry of the Pauli win predicate
on the ordered type pairs that the implications use.

## References

The declarations support the trailing clause of `lem:qld-win-implications` in
`blueprint/src/chapter/ch14_qpbt_observables.tex:616-706`. Their paper source
is `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:192-267`,
whose closing sentences at lines 227 and 263-264 state both companions.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder

namespace MIPStarRE.QPBT

open MIPStarRE.LDT hiding Measurement
open MIPStarRE.Quantum

noncomputable section

namespace WinImplications

/-! ## Transport of the distance functional along the factor interchange -/

/-- The identity operator acts trivially on a state. Formalization-only support
for blueprint `def:strategy-observables`. -/
theorem applyOperatorToState_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) : applyOperatorToState (1 : Op ι) ψ = ψ := by
  ext i
  simp [applyOperatorToState]

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
  simp [reindexOp, heteroKron, Matrix.kronecker, Matrix.kroneckerMap,
    Matrix.reindex_apply, mul_comm]

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
    ← e.sum_comp (fun l : κ => T k l * (reindexState e ψ).ofLp l)]
  apply Finset.sum_congr rfl
  intro j _
  simp [reindexState, reindexOp]

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
    ← e.symm.sum_comp (fun i : ι =>
      ‖(applyOperatorToState (reindexOp e T) ψ).ofLp i‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro k _
  rw [applyOperatorToState_reindexState_ofLp]

/-- Consistency bounds the state-dependent distance of two oppositely placed
measurement families. This is the first item of `fact:agreement`, blueprint
`ch12_qpbt_games.tex:260-276`, in the placed form used by the trailing clause
of `lem:qld-win-implications`, blueprint `ch14_qpbt_observables.tex:699-701`,
paper `14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_two_mul_consistencyDefect
    {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤
      2 * consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
        (fun x a => heteroKron 1 ((B x).effect a)) ψ :=
  opFamilyDistSq_le_two_mul_consistencyDefect μ
    (fun x => DistanceCalculus.leftPlacedMeasurement (A x))
    (fun x => DistanceCalculus.rightPlacedMeasurement (B x)) ψ

/-- Consistency at level `c` gives operator distance at level `2 * c` for two
oppositely placed measurement families. This is the quantitative form of
`fact:agreement`, blueprint `ch12_qpbt_games.tex:260-276`, used by the trailing
clause of `lem:qld-win-implications`, blueprint
`ch14_qpbt_observables.tex:699-701`, paper
`14_analysis_of_the_pauli_basis_test.tex:263-264`. -/
theorem opFamilyDistSq_placed_le_of_consistencyDefect_le
    {X α ιA ιB : Type*} [Fintype X] [DecidableEq X] [Fintype α] [DecidableEq α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (μ : Distribution X) (A : X → Measurement α ιA) (B : X → Measurement α ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) {c : ℝ}
    (h : consistencyDefect μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ c) :
    opFamilyDistSq μ (fun x a => heteroKron ((A x).effect a) 1)
      (fun x a => heteroKron 1 ((B x).effect a)) ψ ≤ 2 * c := by
  have hstep := opFamilyDistSq_placed_le_two_mul_consistencyDefect μ A B ψ
  linarith

end WinImplications

end

end MIPStarRE.QPBT
