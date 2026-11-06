module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackCorridors
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationDimensionless
import Mathlib.Tactic

/-! # Dimensionless propagation data for the source cap-to-stack corridors -/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

/-- The source normalized corridor parameters recover their exact physical values. -/
theorem stack_propagation_scaling (m : ℕ) {r : ℝ} (hr : 0 < r) :
    (1 / (32 * ((m : ℝ) + 1))) * (((m : ℝ) + 1) * r ^ 2) = r ^ 2 / 32 ∧
      (stackAcceleration m * Real.sqrt ((m : ℝ) + 1)) /
        Real.sqrt (((m : ℝ) + 1) * r ^ 2) = stackAcceleration m / r ∧
      (1 / (1024 * (((m : ℝ) + 1) ^ (3 / 2 : ℝ)))) *
        (((m : ℝ) + 1) * r ^ 2) ^ (3 / 2 : ℝ) = r ^ 3 / (2 * 8 ^ 3) ∧
      (1 / (16 * Real.sqrt ((m : ℝ) + 1))) *
        Real.sqrt (((m : ℝ) + 1) * r ^ 2) = r / 16 := by
  have hM : 0 < (m : ℝ) + 1 := by positivity
  have hsqrt : Real.sqrt ((m + 1) * r ^ 2) =
      Real.sqrt (m + 1) * r := by
    rw [Real.sqrt_mul hM.le, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hpow : ((m + 1) * r ^ 2) ^ (3 / 2 : ℝ) =
      (m + 1) ^ (3 / 2 : ℝ) * r ^ 3 := by
    rw [Real.mul_rpow hM.le (sq_nonneg r), ← Real.rpow_natCast,
      ← Real.rpow_mul hr.le]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · grind
  · rw [hpow]
    norm_num
    field_simp
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
