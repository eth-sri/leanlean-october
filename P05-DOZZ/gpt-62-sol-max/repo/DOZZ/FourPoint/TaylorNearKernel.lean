/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorAnnularKernel

/-! Absolute one-root Jensen kernel near the moving root. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Away from the origin, the near-root kernel keeps its integrable radial power γ²/2-2. -/
theorem gammaHalf_near_kernel_bound
    (γ α₁ α₂ α₃ : ℝ) (_hγ : 0 < γ) (z x : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4)
    (hnear : ‖x - z‖ ≤ ‖z‖ / 2) :
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (|γ * α₁| + |γ * α₂|) * ‖z‖ ^ (-γ * α₁)) *
        ENNReal.ofReal (‖x - z‖ ^ (γ ^ 2 / 2 - 2)) := by
  by_cases hxz : x = z
  · subst x; simp
  have hzpos := norm_pos_iff.mpr hz
  have hxlow : ‖z‖ / 2 ≤ ‖x‖ := by linarith [norm_sub_norm_le z x, norm_sub_rev z x]
  have hxhigh : ‖x‖ ≤ 2 * ‖z‖ := by linarith [norm_sub_norm_le x z]
  have hxpos := (by positivity : 0 < ‖z‖ / 2).trans_le hxlow
  have h := gammaHalf_kernel_ratio_bound γ α₁ α₂ α₃ 2 z x (by linarith) hxpos
    (Or.inr (norm_pos_iff.mpr (sub_ne_zero.mpr hxz)))
  rw [Real.rpow_two] at h
  have hweight : ‖x‖ ^ (-γ * α₁) ≤ (2 : ℝ) ^ |γ * α₁| * ‖z‖ ^ (-γ * α₁) := by
    simpa only [neg_mul, abs_neg] using
      rpow_distance_comparison ‖x‖ ‖z‖ 2 (-γ * α₁) |-γ * α₁| hzpos (by norm_num)
        hxlow hxhigh (neg_abs_le _) (le_abs_self _)
  rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
  apply ENNReal.ofReal_le_ofReal
  refine h.trans ?_
  convert mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ ‖x - z‖ ^ (γ ^ 2 / 2 - 2)))
    (by positivity : 0 ≤ (2 : ℝ) ^ |γ * α₂|) using 1 <;> ring

end DOZZ.Proofs
