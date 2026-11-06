/- Concrete dimension27 diagonal target plus generic representation bounds. -/
module
public import Mathlib.Tactic.GRewrite
public import Glennie.Compact.CyclicTraceNullR01
public import Glennie.Hilbert
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Positivity

@[expose] public section
namespace Glennie.Compact.NormCompatibleNullTargetR01
section
open Glennie.Compact.CyclicTraceNullR01

section RepresentedBounds
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing M] [NormedAlgebra ℝ M]

theorem symmProd_norm (a b : M) :
    ‖symmProd a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [symmProd, norm_smul]
  norm_num
  nlinarith [norm_add_le (a*b) (b*a), norm_mul_le a b, norm_mul_le b a]

variable (j : E → E → E) (ρ : E →ₗᵢ[ℝ] M)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b)) (a b : E)

include j ρ hj a b in
theorem represented_product_norm  :
    ‖j a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [← ρ.norm_map (j a b), hj]
  simpa only [ρ.norm_map] using symmProd_norm (ρ a) (ρ b)

include j ρ hj a b in
theorem represented_quadratic_norm  :
    ‖quadraticWith j a b‖ ≤ ‖a‖^2 * ‖b‖ := by
  rw [← ρ.norm_map (quadraticWith j a b)]
  change ‖ρ.toLinearMap (quadraticWith j a b)‖ ≤ _
  rw [map_quadraticWith j ρ.toLinearMap hj, quadratic_eq_sandwich]
  grw [norm_mul_le, norm_mul_le]
  simp only [LinearIsometry.coe_toLinearMap, ρ.norm_map]
  nlinarith

end RepresentedBounds

end
end Glennie.Compact.NormCompatibleNullTargetR01
