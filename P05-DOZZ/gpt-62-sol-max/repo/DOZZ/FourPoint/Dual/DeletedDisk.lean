/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.Kernel
public import DOZZ.FourPoint.TaylorRadialBall
import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.Tactic
/-! # The deterministic deleted-disk estimate for the dual outer correction -/
public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The zero dual kernel near its first root is bounded by the integrable local radial power. -/
theorem dual_zero_kernel_local_bound (γ α₁ α₂ α₃ : ℝ) (x : ℂ) (hx : ‖x‖ < 1 / 2) :
    dualFusionKernel γ α₁ α₂ α₃ 0 x ≤ (2 : ℝ) ^ |γ * α₂| * ‖x‖ ^ (2 - γ * α₁) := by
  by_cases hx0 : x = 0
  · subst x
    simp [dualFusionKernel]
    positivity
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hu := norm_sub_one_rpow_le_of_norm_lt_half hx (-(γ * α₂))
  have he : dualFusionKernel γ α₁ α₂ α₃ 0 x =
      ‖x‖ ^ (2 - γ * α₁) * ‖x - 1‖ ^ (-(γ * α₂)) := by
    unfold dualFusionKernel normPlus
    rw [sub_zero, max_eq_left (by linarith : ‖x‖ ≤ 1), Real.one_rpow, mul_one,
      Real.rpow_sub hp, Real.rpow_two, Real.rpow_neg (norm_nonneg (x - 1))]
    ring
  rw [he]
  simpa only [abs_neg, mul_comm] using mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg hp.le (2 - γ * α₁))

/-- Deleting a small disk has order r^(4−γα₁), with no missing logarithmic endpoint. -/
theorem dual_deleted_disk_spatial_bound (γ α₁ α₂ α₃ : ℝ) (hβ : γ * α₁ < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      (∫⁻ x in Metric.ball (0 : ℂ) r,
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂gmcReferenceMeasure) ≤
          ENNReal.ofReal (C * r ^ (4 - γ * α₁)) := by
  simpa only [show 2 - γ * α₁ + 2 = 4 - γ * α₁ by ring] using
    small_ball_kernel_bound (dualFusionKernel γ α₁ α₂ α₃ 0) (2 - γ * α₁)
      ((2 : ℝ) ^ |γ * α₂|) (by linarith) (by positivity) (dual_zero_kernel_local_bound γ α₁ α₂ α₃)

end DOZZ.Proofs
