/- Dimension-parametric coordinatewise Euclidean Jordan target. -/
module
public import Glennie.Compact.CyclicTraceNullR01
public import Mathlib.Analysis.InnerProductSpace.PiL2
@[expose] public section
namespace Glennie.Compact.VariableDiagonalNullTargetR01
noncomputable section
open scoped BigOperators
open Glennie.Compact.CyclicTraceNullR01

abbrev DiagonalN (n : ℕ) := EuclideanSpace ℝ (Fin n)

def diagonalNProduct {n : ℕ} (a b : DiagonalN n) : DiagonalN n :=
  WithLp.toLp 2 (fun i => a i * b i)

theorem diagonalN_product_norm {n : ℕ} (a b : DiagonalN n) :
    ‖diagonalNProduct a b‖ ≤ ‖a‖ * ‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq (diagonalNProduct a b),
    EuclideanSpace.real_norm_sq_eq b, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have ha : (a i)^2 ≤ ‖a‖^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg (a i)) (norm_nonneg a)).mpr
      (PiLp.norm_apply_le a i)
    simpa only [Real.norm_eq_abs, sq_abs] using hh
  change (a i*b i)^2 ≤ ‖a‖^2 * (b i)^2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)

theorem diagonalN_quadratic_sandwich {n : ℕ} (a b : DiagonalN n) :
    quadraticWith diagonalNProduct a b = diagonalNProduct a (diagonalNProduct a b) := by
  ext i
  change 2*(a i*(a i*b i)) - (a i*a i)*b i = a i*(a i*b i)
  ring

theorem diagonalN_quadratic_norm {n : ℕ} (a b : DiagonalN n) :
    ‖quadraticWith diagonalNProduct a b‖ ≤ ‖a‖^2 * ‖b‖ := by
  rw [diagonalN_quadratic_sandwich]
  calc
    ‖diagonalNProduct a (diagonalNProduct a b)‖ ≤ ‖a‖ * ‖diagonalNProduct a b‖ :=
      diagonalN_product_norm _ _
    _ ≤ ‖a‖ * (‖a‖ * ‖b‖) :=
      mul_le_mul_of_nonneg_left (diagonalN_product_norm _ _) (norm_nonneg _)
    _ = ‖a‖^2 * ‖b‖ := by ring

theorem diagonalN_phi_zero {n : ℕ} (x y z : DiagonalN n) :
    phiWith diagonalNProduct (Inner.inner ℝ) x y z = 0 := by
  have h : quadraticWith diagonalNProduct x (quadraticWith diagonalNProduct y z) =
      quadraticWith diagonalNProduct y (quadraticWith diagonalNProduct x z) := by
    simp only [diagonalN_quadratic_sandwich]
    ext i
    simp [diagonalNProduct, mul_left_comm]
  simp [phiWith, h]

end
end Glennie.Compact.VariableDiagonalNullTargetR01
