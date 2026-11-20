/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.RetainedMassLimit

public import DOZZ.Statements.FourPoint.GammaHalfKernel
import Mathlib.Tactic

/-! # Deterministic outer-kernel domination and the reflected limiting density -/

public section

namespace DOZZ.Proofs

section
variable (γ α₁ α₂ α₃ : ℝ)

/-- The literal half-charge kernel is the BPZ weight at zero softening. -/
theorem gammaHalf_kernel_eq_bpzWeight (z x : ℂ) :
    gammaHalfKernel γ α₁ α₂ α₃ z x = bpzSoftWeight γ (γ / 2) α₁ α₂ α₃ 0 z x := by
  rw [bpzSoftWeight_zero, bpzBaseWeight, gammaHalfKernel,
    show γ * (γ / 2) = γ ^ 2 / 2 by ring,
    Real.rpow_neg (norm_nonneg _), Real.rpow_neg (norm_nonneg _), div_eq_mul_inv, mul_inv]
  ring

/-- At zero the half-charge kernel has exactly the effective first charge `α₁-γ/2`. -/
theorem reflected_zero_kernel_weight (x : ℂ)
    (hx : x ≠ 0) (_hx1 : x ≠ 1) :
    gammaHalfKernel γ α₁ α₂ α₃ 0 x =
      normPlus x ^ (γ * ((α₁ - γ / 2) + α₂ + α₃)) /
        (‖x‖ ^ (γ * (α₁ - γ / 2)) * ‖x - 1‖ ^ (γ * α₂)) := by
  rw [gammaHalf_kernel_eq_bpzWeight]
  exact fusion_zero_kernel_weight γ (γ / 2) α₁ α₂ α₃ x hx

/-- The literal real half-charge density is measurable, including all prescribed root values. -/
theorem reflected_gammaHalfKernel_measurable (z : ℂ) :
    Measurable (fun x => gammaHalfKernel γ α₁ α₂ α₃ z x) := by
  unfold gammaHalfKernel normPlus
  fun_prop

end

end DOZZ.Proofs
