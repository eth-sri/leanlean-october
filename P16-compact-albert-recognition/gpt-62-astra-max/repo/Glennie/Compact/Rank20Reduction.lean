module

public import Glennie.Compact.FlowFamily
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace Glennie.Compact.Rank20

open Glennie.Compact.Flows Glennie.Compact.FlowFamily

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## The derivative matrix and invertibility -/

/-- The matrix of `rowLedgerDeriv T` in the standard basis is `jacobianEntry T`. -/
theorem toMatrix'_rowLedgerDeriv (T : Fin 3 → Fin 3 → Albert) :
    LinearMap.toMatrix' ((rowLedgerDeriv T : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) :
      (Fin 20 → ℝ) →ₗ[ℝ] (Fin 20 → ℝ)) = Matrix.of (jacobianEntry T) := by
  ext <;> simp [LinearMap.toMatrix'_apply, Matrix.of_apply, ContinuousLinearMap.coe_coe, rowLedgerDeriv_single]

/-- A nonzero determinant of the jacobianEntry matrix makes the strict derivative of the
twenty selected ledger rows a continuous linear equivalence of R^20. -/
theorem exists_equiv_of_det_ne_zero (T : Fin 3 → Fin 3 → Albert)
    (h : (Matrix.of (jacobianEntry T)).det ≠ 0) :
    ∃ e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ),
      (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T := by
  have hdet : (rowLedgerDeriv T).det ≠ 0 := by
    simp_all [← toMatrix'_rowLedgerDeriv, LinearMap.det_toMatrix']
  exact ⟨(rowLedgerDeriv T).toContinuousLinearEquivOfDetNeZero hdet,
    (rowLedgerDeriv T).coe_toContinuousLinearEquivOfDetNeZero hdet⟩

/-- The twenty rows then have an invertible strict derivative at 0. -/
theorem hasStrictFDerivAt_rowLedger_of_equiv (T : Fin 3 → Fin 3 → Albert)
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T) :
    HasStrictFDerivAt (rowLedger T) (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) 0 := by
  grind [rowLedger, hasStrictFDerivAt_rowLedger]

end
end Glennie.Compact.Rank20
