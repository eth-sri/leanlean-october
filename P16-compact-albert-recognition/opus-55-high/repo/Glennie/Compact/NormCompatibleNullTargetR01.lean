/- Concrete dimension27 diagonal target plus generic representation bounds. -/
module
public import Glennie.Compact.CyclicTraceNullR01
public import Glennie.Hilbert
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Positivity

@[expose] public section
namespace Glennie.Compact.NormCompatibleNullTargetR01
open scoped BigOperators
open Glennie.Compact.CyclicTraceNullR01

section RepresentedBounds
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing M] [NormedAlgebra ℝ M]

theorem symmProd_norm (a b : M) :
    ‖symmProd a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [symmProd, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num)]
  calc
    (1/2:ℝ) * ‖a*b+b*a‖ ≤ (1/2:ℝ) * (‖a*b‖+‖b*a‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1/2:ℝ) * (‖a‖*‖b‖+‖b‖*‖a‖) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)) (by norm_num)
    _ = ‖a‖*‖b‖ := by ring

theorem represented_product_norm (j : E → E → E) (ρ : E →ₗᵢ[ℝ] M)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b)) (a b : E) :
    ‖j a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [← ρ.norm_map (j a b), hj]
  simpa [ρ.norm_map] using symmProd_norm (ρ a) (ρ b)

theorem represented_quadratic_norm (j : E → E → E) (ρ : E →ₗᵢ[ℝ] M)
    (hj : ∀ a b, ρ (j a b) = symmProd (ρ a) (ρ b)) (a b : E) :
    ‖quadraticWith j a b‖ ≤ ‖a‖^2 * ‖b‖ := by
  rw [← ρ.norm_map (quadraticWith j a b)]
  change ‖ρ.toLinearMap (quadraticWith j a b)‖ ≤ _
  rw [map_quadraticWith j ρ.toLinearMap hj, quadratic_eq_sandwich]
  calc
    ‖ρ a * ρ b * ρ a‖ ≤ ‖ρ a * ρ b‖ * ‖ρ a‖ := norm_mul_le _ _
    _ ≤ (‖ρ a‖ * ‖ρ b‖) * ‖ρ a‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖a‖^2 * ‖b‖ := by simp [ρ.norm_map]; ring
end RepresentedBounds

end Glennie.Compact.NormCompatibleNullTargetR01
