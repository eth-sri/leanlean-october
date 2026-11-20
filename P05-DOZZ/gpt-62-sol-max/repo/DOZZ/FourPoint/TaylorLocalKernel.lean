/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorKernelMass

/-! A small-region Taylor mass is controlled by the sharp one-root weighted GMC mass. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Near the origin the factor from the root at one is bounded, even after
inserting a power of the moving-root distance in the denominator. -/
theorem gammaHalf_kernel_ratio_bound (γ a b c k : ℝ) (z x : ℂ)
    (hx : ‖x‖ ≤ 1 / 2) (hx0 : 0 < ‖x‖) (hd : k = 0 ∨ 0 < ‖x - z‖) :
    gammaHalfKernel γ a b c z x / ‖x - z‖ ^ k ≤
      ‖x - z‖ ^ (γ ^ 2 / 2 - k) * ‖x‖ ^ (-γ * a) * (2 : ℝ) ^ |γ * b| := by
  have hn : normPlus x = 1 := max_eq_left (by linarith)
  have hlo := norm_sub_norm_le (1 : ℂ) x
  rw [norm_one, norm_sub_rev] at hlo
  have hhi := norm_sub_le x (1 : ℂ)
  rw [norm_one] at hhi
  have hp : 0 < ‖x - 1‖ := by linarith
  have ht : ‖x - 1‖ ^ (-γ * b) ≤ (2 : ℝ) ^ |γ * b| := by
    simpa only [neg_mul, abs_neg] using coulombWeight_rpow_le (L := 2) (y := ‖x - 1‖)
      (by norm_num) (by norm_num; linarith) (by linarith) (-γ * b)
  have he : ‖x - z‖ ^ (γ ^ 2 / 2) / ‖x - z‖ ^ k = ‖x - z‖ ^ (γ ^ 2 / 2 - k) := by
    rcases hd with rfl | hd
    · simp
    · rw [Real.rpow_sub hd]
  calc
    _ = (‖x - z‖ ^ (γ ^ 2 / 2) / ‖x - z‖ ^ k) * ‖x‖ ^ (-γ * a) * ‖x - 1‖ ^ (-γ * b) := by
      rw [gammaHalfKernel, hn, Real.one_rpow, mul_one, neg_mul γ a, neg_mul γ b,
        Real.rpow_neg hx0.le, Real.rpow_neg hp.le]
      have hi : (‖x‖ ^ (γ * a) * ‖x - 1‖ ^ (γ * b))⁻¹ =
          (‖x‖ ^ (γ * a))⁻¹ * (‖x - 1‖ ^ (γ * b))⁻¹ := by
        field_simp [(Real.rpow_pos_of_pos hx0 (γ * a)).ne', (Real.rpow_pos_of_pos hp (γ * b)).ne']
      simp only [div_eq_mul_inv, hi]
      ring
    _ ≤ _ := by rw [he]; gcongr

/-- On the small origin disk, the negative degenerate charge supplies its exact radius power. -/
theorem gammaHalf_local_kernel_bound (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (hz : ‖z‖ ≤ ρ) (hx : ‖x‖ ≤ ρ) (hx0 : x ≠ 0) :
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ≤
      ENNReal.ofReal ((2 : ℝ) ^ |γ * α₂| * (2 * ρ) ^ (γ ^ 2 / 2)) *
        (ENNReal.ofReal ‖x‖) ^ (-γ * α₁) := by
  have hxpos := norm_pos_iff.mpr hx0
  have hxz : ‖x - z‖ ≤ 2 * ρ := by linarith [norm_sub_le x z]
  have h := gammaHalf_kernel_ratio_bound γ α₁ α₂ α₃ 0 z x (hx.trans hρ2) hxpos (Or.inl rfl)
  simp only [Real.rpow_zero, div_one, sub_zero] at h
  rw [ENNReal.ofReal_rpow_of_pos hxpos, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  refine h.trans ?_
  rw [show (2 : ℝ) ^ |γ * α₂| * (2 * ρ) ^ (γ ^ 2 / 2) * ‖x‖ ^ (-γ * α₁) =
    (2 * ρ) ^ (γ ^ 2 / 2) * ‖x‖ ^ (-γ * α₁) * 2 ^ |γ * α₂| by ring]
  gcongr

/-- The local mass comparison is valid for atomless measures with the exact extended one-root
weight at the origin. No regularization or replacement measure is used. -/
theorem gammaHalf_local_mass_bound (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (hz : ‖z‖ ≤ ρ) (μ : Measure ℂ) (h0 : μ {0} = 0) :
    (∫⁻ x in Metric.ball 0 ρ, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ |γ * α₂| * (2 * ρ) ^ (γ ^ 2 / 2)) *
        weightedGmcBallMass γ μ α₁ 0 ρ := by
  have hx0 : ∀ᵐ x ∂μ, x ≠ 0 := by apply ae_iff.mpr; simpa using h0
  unfold weightedGmcBallMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae hx0, ae_restrict_mem measurableSet_ball] with x hnonzero hx
  simpa only [sub_zero, ENNReal.rpow_eq_pow] using
    gammaHalf_local_kernel_bound γ α₁ α₂ α₃ z x ρ hρ hρ2 hz (by
    have hh : ‖x‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact hh.le) hnonzero

end DOZZ.Proofs
