module
public import Glennie.Compact.NativeNormKernelR01
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Tactic.GRewrite
/- Sharp quadratic polarization. -/
@[expose] public section
namespace Glennie.Compact.NativeNormKernel
open Glennie
noncomputable section
set_option autoImplicit false

 theorem crossU_smul_first (t : ℝ) (x y w : Albert) :
    crossU (t • x) y w = t • crossU x y w := by
  simp only [crossU, jordan_smul_left, jordan_smul_right]
  module

 theorem crossU_polarization (x y w : Albert) :
    crossU x y w = (1/2 : ℝ) • (U (x+y) w - U (x-y) w) := by
  simp only [crossU, U, jordan_add_left, jordan_add_right,
    jordan_sub_left, jordan_sub_right, jordan_comm y x]
  module

 theorem crossU_norm_sum_sq (x y w : Albert) :
    ‖crossU x y w‖ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) * ‖w‖ := by
  grw [crossU_polarization, norm_smul, show ‖(1/2:ℝ)‖ = 1/2 by norm_num, norm_sub_le, U_norm, U_norm]
  rw [← add_mul, parallelogram_law_with_norm ℝ x y]
  ring_nf
  rfl

open NormedSpace in
theorem crossU_norm (x y w : Albert) : ‖crossU x y w‖ ≤ 2 * ‖x‖ * ‖y‖ * ‖w‖ := by
  have h (v : Albert) : ‖normalize v‖ ≤ 1 := by
    by_cases hv : v = 0 <;> simp [hv, norm_normalize]
  nth_rw 1 [← norm_smul_normalize x, ← norm_smul_normalize y]
  simp only [crossU_smul_first, crossU_smul_second, norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
  grw [crossU_norm_sum_sq, h x, h y]
  ring_nf
  rfl

 theorem U_sub_base_polarized (a b w : Albert) :
    U a w - U b w = (1/2:ℝ) • crossU (a+b) (a-b) w := by
  simp only [U, crossU, jordan_add_left, jordan_add_right,
    jordan_sub_left, jordan_sub_right, jordan_comm b a]
  module

theorem U_sub_base_radius (a b w : Albert) (R : ℝ) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖U a w-U b w‖ ≤ 2*R*‖a-b‖*‖w‖ := by
  grw [U_sub_base_polarized, norm_smul, show ‖(1/2:ℝ)‖ = 1/2 by norm_num, crossU_norm,
    norm_add_le, ha, hb]
  ring_nf
  rfl

end
end Glennie.Compact.NativeNormKernel
