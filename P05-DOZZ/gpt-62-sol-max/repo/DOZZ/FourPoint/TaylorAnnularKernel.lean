/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorLocalKernel
public import DOZZ.FourPoint.TwoRootedExponents

/-! The annular absolute Jensen kernel with the corrected radial exponent. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- On the origin annulus with the moving root separated by half its inner radius,
the precise squared-denominator kernel is bounded by the power κ-4. -/
theorem gammaHalf_annular_kernel_bound
    (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (z x : ℂ) (hx : ‖x‖ ≤ 1 / 2)
    (hxpos : 0 < ‖x‖) (hz : ‖z‖ ≤ ‖x‖ / 2) :
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (|γ * α₂| + |γ ^ 2 / 2 - 2|)) *
        ENNReal.ofReal (‖x‖ ^ (γ * (Q γ - α₁) - 4)) := by
  have hlow : ‖x‖ / 2 ≤ ‖x - z‖ := by linarith [norm_sub_norm_le x z]
  have hhigh : ‖x - z‖ ≤ 2 * ‖x‖ := by linarith [norm_sub_le x z]
  have hxz : 0 < ‖x - z‖ := (by positivity : 0 < ‖x‖ / 2).trans_le hlow
  have h := gammaHalf_kernel_ratio_bound γ α₁ α₂ α₃ 2 z x hx hxpos (Or.inr hxz)
  rw [Real.rpow_two] at h
  have hdist := rpow_distance_comparison ‖x - z‖ ‖x‖ 2
    (γ ^ 2 / 2 - 2) |γ ^ 2 / 2 - 2| hxpos (by norm_num) hlow hhigh (neg_abs_le _) (le_abs_self _)
  have hexp : γ * (Q γ - α₁) - 4 = γ ^ 2 / 2 - 2 + -γ * α₁ := by
    unfold Q
    field_simp [hγ.ne']
    ring
  rw [← ENNReal.ofReal_mul (by positivity), hexp, Real.rpow_add hxpos,
    Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
  apply ENNReal.ofReal_le_ofReal
  refine h.trans ?_
  convert mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdist (by positivity : 0 ≤ ‖x‖ ^ (-γ * α₁)))
    (by positivity : 0 ≤ (2 : ℝ) ^ |γ * α₂|) using 1 <;> ring

end DOZZ.Proofs
