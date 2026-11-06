module
public import Glennie.LinearSimp
public import Mathlib.Tactic.GRewrite
public import Glennie.Compact.NativeNormKernelR01

/- Sharp quadratic polarization. -/
@[expose] public section
namespace Glennie.Compact.NativeNormKernel
open Glennie
section
 theorem crossU_smul_first (t : ℝ) (x y w : Albert) :
    crossU (t • x) y w = t • crossU x y w := by
  simp only [crossU, jordan_smul_left, jordan_smul_right]
  module

 theorem crossU_polarization (x y w : Albert) :
    crossU x y w = (1/2 : ℝ) • (U (x+y) w - U (x-y) w) := by
  simp only [albert_linear, crossU, U, jordan_comm y x]
  module

 theorem crossU_norm_sum_sq (x y w : Albert) :
    ‖crossU x y w‖ ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) * ‖w‖ := by
  rw [crossU_polarization, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  grw [norm_sub_le, U_norm, U_norm]
  rw [← add_mul, parallelogram_law_with_norm ℝ x y]
  ring_nf
  rfl

 theorem crossU_norm (x y w : Albert) :
    ‖crossU x y w‖ ≤ 2 * ‖x‖ * ‖y‖ * ‖w‖ := by
  by_cases hx : x = 0
  · subst x
    simp [crossU, jordan_zero_left, jordan_zero_right]
  by_cases hy : y = 0
  · subst y
    simp [crossU, jordan_zero_left, jordan_zero_right]
  have hnx := norm_ne_zero_iff.mpr hx
  have hny := norm_ne_zero_iff.mpr hy
  have H := crossU_norm_sum_sq ((‖x‖⁻¹ : ℝ) • x) ((‖y‖⁻¹ : ℝ) • y) w
  erw [norm_smul_inv_norm (𝕜 := ℝ) hx, norm_smul_inv_norm (𝕜 := ℝ) hy] at H
  norm_num at H
  have H' := mul_le_mul_of_nonneg_left H (mul_nonneg (norm_nonneg x) (norm_nonneg y))
  simpa [crossU_smul_first, crossU_smul_second, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, hnx, hny, mul_comm, mul_left_comm, mul_assoc] using H'

 theorem U_sub_base_polarized (a b w : Albert) :
    U a w - U b w = (1/2:ℝ) • crossU (a+b) (a-b) w := by
  simp only [albert_linear, U, crossU, jordan_comm b a]
  module

 theorem U_sub_base_norm (a b w : Albert) :
    ‖U a w - U b w‖ ≤ (‖a‖+‖b‖) * ‖a-b‖ * ‖w‖ := by
  rw [U_sub_base_polarized, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  grw [crossU_norm, norm_add_le]
  ring_nf
  rfl

                                                   
                                   
                                       
      
                                                    
                                            

end
end Glennie.Compact.NativeNormKernel
