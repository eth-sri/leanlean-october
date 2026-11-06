module

public import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables
public import QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation

/-!
# Swap-isometry extraction for Magic Square rigidity

This module constructs the local swap isometries used in the finite-dimensional
proof of Magic Square rigidity.  A binary observable `Z` splits a local vector
into its two eigenspaces, while a second binary observable `X` identifies the
negative eigenspace with the residual copy of the original Hilbert space.
Crucially, the resulting map is an exact isometry even when `X` and `Z`
anticommute only on the strategy state.

The final section specializes this construction to the distinguished local
binary observables of both players in the projectively dilated Magic Square
strategy.  A joint two-EPR specialization is not stated here: the current
symmetric game does not relate the two players' variable representations.  The
resulting two-copy obstruction is recorded in
`audits/2026-09-04_magic-square-rigidity-orientation-obstruction.md`.

## References

The target statement is blueprint `thm:ms-rigidity`, from
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The concrete binary Pauli projectors and EPR vector are those of
`references/qpbt-paper/04_preliminaries.tex:1097-1262`.  The cited robust
self-test is Coladangelo--Stark, arXiv:1709.09267v2, Theorem 6.9.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]


/-! ## The one-qubit swap isometry -/

/-- Formalization-only linear controlled-swap map supporting
`thm:ms-rigidity`.  For a binary output `b`, its residual component is
`X^b P_b(Z) psi`, where `P_b(Z)` is the spectral effect of the binary observable
`Z`. -/
def binarySwapMap 
    (X Z : Op ι) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ (ZMod 2 × ι) where
  toFun ψ := (EuclideanSpace.equiv (ZMod 2 × ι) ℂ).symm
    (fun bi => applyOperatorToState (X ^ bi.1.val * reflectionEffect Z bi.1) ψ bi.2)
  map_add' ψ ξ := by
    apply (EuclideanSpace.equiv (ZMod 2 × ι) ℂ).injective
    funext bi
    simp [ContinuousLinearEquiv.apply_symm_apply]
    unfold applyOperatorToState
    rw [map_add]
    rfl
  map_smul' c ψ := by
    apply (EuclideanSpace.equiv (ZMod 2 × ι) ℂ).injective
    funext bi
    simp [ContinuousLinearEquiv.apply_symm_apply, RingHom.id_apply]
    unfold applyOperatorToState
    rw [map_smul]
    rfl

/-- Formalization-only support for `thm:ms-rigidity`: the controlled-swap map
preserves norms whenever both controlling operators are binary observables.  No
anticommutation assumption is needed. -/
theorem binarySwapMap_norm {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z)
    (ψ : EuclideanSpace ℂ ι) :
    ‖binarySwapMap X Z ψ‖ = ‖ψ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  change
    (∑ bi : ZMod 2 × ι,
      ‖applyOperatorToState (X ^ bi.1.val * reflectionEffect Z bi.1) ψ bi.2‖ ^ 2) =
      ∑ i : ι, ‖ψ i‖ ^ 2
  rw [Fintype.sum_prod_type, sum_zmod_two]
  simp [ZMod.val_zero, pow_zero, one_mul, ZMod.val_one, pow_one]
  rw [show
      ∑ i : ι, ‖applyOperatorToState (reflectionEffect Z 0) ψ i‖ ^ 2 =
        ‖applyOperatorToState (reflectionEffect Z 0) ψ‖ ^ 2 by
          exact (EuclideanSpace.norm_sq_eq _).symm,
    show
      ∑ i : ι, ‖applyOperatorToState (X * reflectionEffect Z 1) ψ i‖ ^ 2 =
        ‖applyOperatorToState (X * reflectionEffect Z 1) ψ‖ ^ 2 by
          exact (EuclideanSpace.norm_sq_eq _).symm,
    show ∑ i : ι, ‖ψ i‖ ^ 2 = ‖ψ‖ ^ 2 by
      exact (EuclideanSpace.norm_sq_eq _).symm,
    norm_applyOperatorToState_isometry_mul hX.isometry]
  have hplus : applyOperatorToState (reflectionEffect Z 0) ψ =
      (2 : ℂ)⁻¹ • (ψ + applyOperatorToState Z ψ) := by
    simp [reflectionEffect, applyOperatorToState_smul,
      applyOperatorToState_add_op, applyOperatorToState_one]
  have hminus : applyOperatorToState (reflectionEffect Z 1) ψ =
      (2 : ℂ)⁻¹ • (ψ - applyOperatorToState Z ψ) := by
    simp [reflectionEffect, applyOperatorToState]
  rw [hplus, hminus, norm_smul, norm_smul, show ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ by norm_num]
  have hZnorm := norm_applyOperatorToState_of_isometry hZ.isometry ψ
  have hpara := parallelogram_law_with_norm_mul ℂ ψ (applyOperatorToState Z ψ)
  rw [hZnorm] at hpara
  nlinarith [hpara]

/-- Formalization-only local controlled-swap map for `thm:ms-rigidity`, bundled
as a linear isometric embedding. -/
noncomputable def binarySwapIsometry 
    (X Z : Op ι) (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (ZMod 2 × ι) where
  toLinearMap := binarySwapMap X Z
  norm_map' := binarySwapMap_norm X Z hX hZ

/-- Formalization-only coordinate formula for the binary swap isometry used in
`thm:ms-rigidity`. -/
@[simp]
theorem binarySwapIsometry_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (X Z : Op ι) (hX : IsBinaryObservable X) (hZ : IsBinaryObservable Z)
    (ψ : EuclideanSpace ℂ ι) (b : ZMod 2) (i : ι) :
    binarySwapIsometry X Z hX hZ ψ (b, i) =
      applyOperatorToState (X ^ b.val * reflectionEffect Z b) ψ i := rfl

/-! ## Binary Pauli actions on the extracted register -/

/-! ## Local Magic Square specializations -/

end

end MIPStarRE.QPBT.MagicSquareRigidity
