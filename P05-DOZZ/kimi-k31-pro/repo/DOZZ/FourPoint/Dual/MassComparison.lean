/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DOZZ.FourPoint.Dual.Kernel
import DOZZ.FourPoint.Dual.OuterMassLimit
import DOZZ.FourPoint.Dual.NegativePowerDifference
import Mathlib.Tactic
/-! # The actual retained dual mass and its zero-mass comparison -/
open MeasureTheory Set
namespace DOZZ.Proofs

/-- The dual density is nonnegative, including its prescribed root values. -/
theorem dual_kernel_nonneg (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) :
    0 ≤ dualFusionKernel γ α₁ α₂ α₃ z x := by
  unfold dualFusionKernel
  exact div_nonneg
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (by unfold normPlus; positivity) _))
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))

end DOZZ.Proofs
