/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.TimeIntegrability
/-! # Quadratic exterior Taylor errors -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs

/-- A bounded exterior spatial expectation times a quadratic factor is little-o of
any power below two. No value at the origin is required. -/
theorem fusion_quadratic_time_error (E f : ℂ → ℂ) (C κ A : ℝ) (hκ : κ < 2)
    (hf : ∀ z, ‖f z‖ ≤ A * ‖z‖ ^ 2)
    (hE : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 → ‖E z‖ ≤ C) :
    IsComplexLittleOAtZero κ (fun z : ℂ => f z *
      (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) * E ((t : ℂ) * z))) := by
  apply power_bound_littleO _ κ (2 - κ) (A * C) (1 / 4) (by linarith) (by norm_num)
  intro z hz hz4
  have hb := time_integral_bound E C 0 (1 / 4) (by norm_num)
    (fun w hw hw4 => by simpa only [Real.rpow_zero, mul_one] using hE w hw hw4) z hz hz4
  simp only [Real.rpow_zero, mul_one, zero_add, div_one] at hb
  rw [norm_mul, show κ + (2 - κ) = 2 by ring, Real.rpow_two]
  calc
    _ ≤ (A * ‖z‖ ^ 2) * C := mul_le_mul (hf z) hb (norm_nonneg _) ((norm_nonneg _).trans (hf z))
    _ = _ := by ring
end DOZZ.Proofs
