module

public import Glennie.Compact.FlowFamily
public import Glennie.Compact.Rank20Certificate
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace Glennie.Compact.Rank20

open Glennie.Compact.NativeDictionary Glennie.Compact.Flows Glennie.Compact.FlowFamily
  Glennie.Compact.Rank20Certificate

section

theorem rank20_of_bridge (T : Fin 3 → Fin 3 → Albert)
    (hT : ∀ r n : Fin 20, jacobianEntry T r n = JQ r n) :
    ∃ e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ),
      (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T := by
  have hm : LinearMap.toMatrix' (rowLedgerDeriv T).toLinearMap = JQ := by
    ext r n
    simpa only [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe,
      rowLedgerDeriv_single] using hT r n
  have hd : (rowLedgerDeriv T).det ≠ 0 := by
    change (rowLedgerDeriv T).toLinearMap.det ≠ 0
    rw [← LinearMap.det_toMatrix', hm]
    exact det_JQ_ne_zero
  exact ⟨(rowLedgerDeriv T).toContinuousLinearEquivOfDetNeZero hd, rfl⟩

/-! ## Entry formulas for the bridge -/

/-- First-frame columns: one trace pairing. -/
theorem jacobianEntry_ctx0 (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20)
    (h : contextIndex n = 0) :
    jacobianEntry T r n = inner (direction n (T 0 (rowIndex r).1))
      (jordan (T 1 (rowIndex r).2.1) (T 2 (rowIndex r).2.2)) := by
  simpa [jacobianEntry, atomTangent, h, inner] using
    inner_jordan_associative (direction n (T 0 (rowIndex r).1))
      (T 1 (rowIndex r).2.1) (T 2 (rowIndex r).2.2)

/-- Second-frame columns: one trace pairing. -/
theorem jacobianEntry_ctx1 (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20)
    (h : contextIndex n = 1) :
    jacobianEntry T r n = inner (direction n (T 1 (rowIndex r).2.1))
      (jordan (T 0 (rowIndex r).1) (T 2 (rowIndex r).2.2)) := by
  simpa [jacobianEntry, atomTangent, h, inner, jordan_comm] using
    inner_jordan_associative (direction n (T 1 (rowIndex r).2.1))
      (T 0 (rowIndex r).1) (T 2 (rowIndex r).2.2)

end
end Glennie.Compact.Rank20
