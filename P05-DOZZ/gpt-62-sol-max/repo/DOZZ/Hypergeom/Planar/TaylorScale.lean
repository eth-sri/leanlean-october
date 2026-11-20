/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.TaylorTail
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Rotation and scaling identities for the corrected planar Taylor kernel. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs

/-- Multiplication of both points multiplies the norm-power kernel by `‖c‖^(k-β)`.
The coefficient of the counterterm can be any scalar invariant under this change. -/
theorem planar_power_kernel_mul (k β A : ℝ) (c z u : ℂ) (hc : c ≠ 0) :
    (‖c * u - c * z‖ ^ k - ‖c * u‖ ^ k + A * ‖c * u‖ ^ k) / ‖c * u‖ ^ β =
      ‖c‖ ^ (k - β) * ((‖u - z‖ ^ k - ‖u‖ ^ k + A * ‖u‖ ^ k) / ‖u‖ ^ β) := by
  rw [← mul_sub, Real.rpow_sub (norm_pos_iff.mpr hc)]
  simp only [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), div_eq_mul_inv, mul_inv_rev]
  ring

/-- Integrating a homogeneous two-point kernel adds two to the dilation exponent. -/
theorem planar_integral_homogeneous (K : ℂ → ℂ → ℝ) (a : ℝ) (ha : 0 < a + 2)
    (hzero : ∀ u, K 0 u = 0)
    (hscale : ∀ z ≠ 0, ∀ u, K z (z * u) = ‖z‖ ^ a * K 1 u) (z : ℂ) :
    (∫ u : ℂ, K z u) = ‖z‖ ^ (a + 2) * (∫ u : ℂ, K 1 u) := by
  by_cases hz : z = 0
  · simp [hz, hzero, Real.zero_rpow ha.ne']
  let r : ℝ := ‖z‖
  have hr : 0 < r := norm_pos_iff.mpr hz
  let ξ : ℂ := z / (r : ℂ)
  have hξ : ‖ξ‖ = 1 := by
    rw [show ‖ξ‖ = ‖z‖ / ‖(r : ℂ)‖ by exact norm_div _ _, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact div_self hr.ne'
  let c : Circle := ⟨ξ, by simpa [Submonoid.unitSphere] using hξ⟩
  have hrot : (∫ u : ℂ, K z (ξ * u)) = ∫ u : ℂ, K z u := by
    exact (LinearIsometryEquiv.measurePreserving (rotation c)).integral_comp
            ((rotation c).toContinuousLinearEquiv.toHomeomorph).measurableEmbedding (K z)
  have hpoint (u : ℂ) : K z (ξ * u) = r ^ a * K 1 (r⁻¹ • u) := by
    have he : ξ * u = z * (r⁻¹ • u) := by
      simp only [ξ, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_assoc]
    rw [he, hscale z hz]
  calc
    _ = ∫ u : ℂ, K z (ξ * u) := hrot.symm
    _ = r ^ a * (∫ u : ℂ, K 1 (r⁻¹ • u)) := by simp_rw [hpoint, integral_const_mul]
    _ = _ := by
      rw [Measure.integral_comp_inv_smul_of_nonneg volume (K 1) hr.le,
        Complex.finrank_real_complex, smul_eq_mul, ← mul_assoc, ← Real.rpow_natCast,
        ← Real.rpow_add hr]
      norm_num [r]

private theorem planarTaylorRemainder_mul (k β : ℝ) (z u : ℂ) (hz : z ≠ 0) :
    DOZZ.planarTaylorRemainder k β z (z * u) =
      ‖z‖ ^ (k - β) * DOZZ.planarTaylorRemainder k β 1 u := by
  have hstar : star z ≠ 0 := by simpa using hz
  have h := planar_power_kernel_mul k β ((k / 2) * (1 / u + star 1 / star u).re) z 1 u hz
  simp only [mul_one] at h
  unfold DOZZ.planarTaylorRemainder
  rw [show z / (z * u) = 1 / u by simpa using mul_div_mul_left 1 u hz,
    star_mul, show star z / (star u * star z) = star 1 / star u by
      simpa using mul_div_mul_right 1 (star u) hstar]
  convert h using 1 <;> ring

/-- The corrected Taylor integral is homogeneous of degree `2 + k - β`, including at zero. -/
theorem planarTaylorRemainder_integral_scale_norm (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (z : ℂ) :
    (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) =
      ‖z‖ ^ (2 + k - β) * (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by
  rw [show 2 + k - β = k - β + 2 by ring]
  exact planar_integral_homogeneous _ _ (by linarith) (fun u => by simp [DOZZ.planarTaylorRemainder])
    (fun z hz u => planarTaylorRemainder_mul k β z u hz) z

end DOZZ.Proofs
