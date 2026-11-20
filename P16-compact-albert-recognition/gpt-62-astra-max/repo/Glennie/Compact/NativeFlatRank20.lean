module
public import Glennie.Compact.FlatCoordinates
@[expose] public section
namespace Glennie.Compact.NativeFlatRank20
open Glennie.Exact FlowFamily
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
private theorem eval_jac : Matrix.of entry = jac := by funext i; fin_cases i <;> decide +kernel
private theorem check_inverse : invJac * jac = 1 := by funext i; fin_cases i <;> decide +kernel

theorem flat_rank : ∃ e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ),
    (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T := by
  apply Rank20.exists_equiv_of_det_ne_zero
  rw [jacobian_exact, eval_jac]
  exact (Matrix.isUnit_det_of_left_inverse (mapped_left_inverse φ check_inverse)).ne_zero

end Glennie.Compact.NativeFlatRank20
