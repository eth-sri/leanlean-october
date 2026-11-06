module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.StackPositivityScaling
import Mathlib.Tactic

/-! # Scale-independent macroscopic propagation ratios -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth

/-- The exact source acceleration bound for reference travel paths. -/
def macroscopicAcceleration (m : ℕ) : ℝ := 6 * ((m : ℝ) + 5) + 8

/-- The minimum duration and widths recover their physical values at every scale. -/
theorem macroscopic_propagation_scaling (m : ℕ) (r0 : ℝ) {scale : ℝ}
    (hscale : 0 < scale) :
    (r0 ^ 2 / (32 * ((m : ℝ) + 3))) * (((m : ℝ) + 3) * scale ^ 2) =
        (r0 ^ 2 / 32) * scale ^ 2 ∧
      (macroscopicAcceleration m * Real.sqrt ((m : ℝ) + 3)) /
        Real.sqrt (((m : ℝ) + 3) * scale ^ 2) = macroscopicAcceleration m / scale ∧
      (r0 ^ 3 / (1024 * (((m : ℝ) + 3) ^ (3 / 2 : ℝ)))) *
        (((m : ℝ) + 3) * scale ^ 2) ^ (3 / 2 : ℝ) = (r0 ^ 3 / 1024) * scale ^ 3 ∧
      (r0 / (16 * Real.sqrt ((m : ℝ) + 3))) *
        Real.sqrt (((m : ℝ) + 3) * scale ^ 2) = (r0 / 16) * scale := by
  let sharedTerm_9ed958d012 := ((((m : ℝ) + 3) * scale ^ 2))
  have hM : 0 < (m : ℝ) + 3 := by positivity
  have hs  := (Real.sqrt_pos.mpr hM).ne'
  have hp : ((m : ℝ) + 3) ^ (3 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hM _).ne'
  have hsqrt : Real.sqrt sharedTerm_9ed958d012 =
      Real.sqrt ((m : ℝ) + 3) * scale := by
    rw [Real.sqrt_mul hM.le, Real.sqrt_sq_eq_abs, abs_of_pos hscale]
  have hpow : (sharedTerm_9ed958d012) ^ (3 / 2 : ℝ) =
      ((m : ℝ) + 3) ^ (3 / 2 : ℝ) * scale ^ 3 := by
    rw [Real.mul_rpow hM.le (sq_nonneg scale), ← Real.rpow_natCast scale 2,
      ← Real.rpow_mul hscale.le]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · rw [hsqrt]
    field_simp
  · rw [hpow]
    field_simp
  · rw [hsqrt]
    field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth
