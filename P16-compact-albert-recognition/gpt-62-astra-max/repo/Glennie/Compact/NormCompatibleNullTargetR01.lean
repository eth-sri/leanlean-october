/- Concrete dimension27 diagonal target plus generic representation bounds. -/
module
public import Glennie.Compact.CyclicTraceNullR01
public import Glennie.Hilbert
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Positivity

@[expose] public section
namespace Glennie.Compact.NormCompatibleNullTargetR01
noncomputable section
open scoped BigOperators
open Glennie.Compact.CyclicTraceNullR01

section RepresentedBounds
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing M] [NormedAlgebra ℝ M]

theorem symmProd_norm (a b : M) :
    ‖symmProd a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [symmProd, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
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
  simpa only [ρ.norm_map] using symmProd_norm (ρ a) (ρ b)

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
    _ = ‖a‖^2 * ‖b‖ := by simp only [ρ.norm_map]; ring
end RepresentedBounds

/- This concrete target has dimension27, actual positive Hilbert metric,
   a unit, bilinear commutative product, and compatible cyclic trace. -/
abbrev Diagonal27 := EuclideanSpace ℝ (Fin 27)

def diagonalProduct (a b : Diagonal27) : Diagonal27 :=
  WithLp.toLp 2 (fun i => a i * b i)

theorem diagonal_product_comm (a b : Diagonal27) :
    diagonalProduct a b = diagonalProduct b a := by
  ext i
  exact mul_comm (a i) (b i)

theorem diagonal_product_add_left (a b c : Diagonal27) :
    diagonalProduct (a+b) c = diagonalProduct a c + diagonalProduct b c := by
  ext i
  exact add_mul (a i) (b i) (c i)

theorem diagonal_product_smul_left (r : ℝ) (a b : Diagonal27) :
    diagonalProduct (r • a) b = r • diagonalProduct a b := by
  ext i
  exact mul_assoc r (a i) (b i)

end
end Glennie.Compact.NormCompatibleNullTargetR01
