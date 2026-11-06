/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.DifferenceIntegrable
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Rotation and scaling of the first-order-subtracted difference integral. -/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs





theorem planarDifferenceKernel_integral_scale_norm k β
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) :
    ∀ z : ℂ,
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) =
        ‖z‖ ^ (2 + k - β) *
          (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
  have planarDifferenceKernel_integral_scale ξ (hξ : ‖ξ‖ = 1) (r : ℝ) (hr : 0 < r) z (hz : ξ * (r : ℂ) = z) : (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) = r ^ (2 + k - β) * (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
    have planarDifferenceKernel_rotated_scale v : DOZZ.planarDifferenceKernel k β z (ξ * (r • v)) = r ^ (k - β) * DOZZ.planarDifferenceKernel k β 1 v := by
      have planarDifferenceKernel_real_scale : DOZZ.planarDifferenceKernel k β (r : ℂ) (r • v) = r ^ (k - β) * DOZZ.planarDifferenceKernel k β 1 v := by
        by_cases hv : v = 0
        · subst v
          simp [DOZZ.planarDifferenceKernel, Real.zero_rpow, ne_of_gt hk, ne_of_gt (lt_trans hk hβ)]
        · have hnormv : ‖r • v‖ = r * ‖v‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
          change (‖r • v - (r : ℂ)‖ ^ k - ‖r • v‖ ^ k) / ‖r • v‖ ^ β =
            r ^ (k - β) * ((‖v - 1‖ ^ k - ‖v‖ ^ k) / ‖v‖ ^ β)
          rw [(show ‖r • v - (r : ℂ)‖ ^ k - ‖r • v‖ ^ k = r ^ k * (‖v - 1‖ ^ k - ‖v‖ ^ k) by rw [(show ‖r • v - (r : ℂ)‖ = r * ‖v - 1‖ by rw [(show r • v - (r : ℂ) = (r : ℂ) * (v - 1) by change (r : ℂ) * v - (r : ℂ) = (r : ℂ) * (v - 1); ring), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]), hnormv, (Real.mul_rpow hr.le (norm_nonneg (v - 1))), (Real.mul_rpow hr.le (norm_nonneg v))]; ring), hnormv, (Real.mul_rpow hr.le (norm_nonneg v))]
          calc
            _ = (r ^ k / r ^ β) * ((‖v - 1‖ ^ k - ‖v‖ ^ k) / ‖v‖ ^ β) := by
              field_simp [(Real.rpow_pos_of_pos hr β).ne', (Real.rpow_pos_of_pos (norm_pos_iff.mpr hv) β).ne']
            _ = _ := by rw [← Real.rpow_sub hr k β]
      have planarDifferenceKernel_rotate z v (hξ : ‖ξ‖ = 1) : DOZZ.planarDifferenceKernel k β (ξ * z) (ξ * v) = DOZZ.planarDifferenceKernel k β z v := by
        rw [DOZZ.planarDifferenceKernel, DOZZ.planarDifferenceKernel, (show ξ * v - ξ * z = ξ * (v - z) by ring)]
        simp only [norm_mul, hξ, one_mul]
      calc
        DOZZ.planarDifferenceKernel k β z (ξ * (r • v)) =
            DOZZ.planarDifferenceKernel k β (ξ * (r : ℂ)) (ξ * (r • v)) := by rw [hz]
        _ = DOZZ.planarDifferenceKernel k β (r : ℂ) (r • v) :=
          planarDifferenceKernel_rotate (r : ℂ) (r • v) hξ
        _ = r ^ (k - β) * DOZZ.planarDifferenceKernel k β 1 v :=
          planarDifferenceKernel_real_scale
    let g : ℂ → ℝ := fun u => DOZZ.planarDifferenceKernel k β z (ξ * u)
    have hrotation : (∫ u : ℂ, g u) =
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) := by
      change (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z (ξ * u)) = _
      let c : Circle := ⟨ξ, by simpa [Submonoid.unitSphere] using hξ⟩
      simpa only [rotation_apply] using
        (LinearIsometryEquiv.measurePreserving (rotation c)).integral_comp
          ((rotation c).toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
          (fun u => DOZZ.planarDifferenceKernel k β z u)
    have hscaling :
        (∫ u : ℂ, g (r • u)) = (r ^ 2)⁻¹ * (∫ u : ℂ, g u) := by
      simpa only [Complex.finrank_real_complex, smul_eq_mul] using (Measure.integral_comp_smul_of_nonneg volume g r (hR := hr.le))
    rw [(show (fun u => g (r • u)) = fun u => r ^ (k - β) * DOZZ.planarDifferenceKernel k β 1 u by funext u; exact planarDifferenceKernel_rotated_scale u), integral_const_mul] at hscaling
    rw [hrotation] at hscaling
    have hleft : r ^ 2 * (r ^ (k - β) *
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u)) =
        r ^ (2 + k - β) *
          (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
      calc
        _ = (r ^ 2 * r ^ (k - β)) *
            (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by ring
        _ = r ^ (2 + (k - β)) *
            (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by rw [(show r ^ 2 * r ^ (k - β) = r ^ (2 + (k - β)) by rw [← Real.rpow_natCast r 2]; exact (Real.rpow_add hr 2 (k - β)).symm)]
        _ = _ := by congr 1; congr 1; ring
    calc
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) =
          r ^ 2 * ((r ^ 2)⁻¹ *
            (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u)) := by rw [(show r ^ 2 * ((r ^ 2)⁻¹ * (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u)) = (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) by field_simp [(pow_ne_zero 2 hr.ne')])]
      _ = r ^ 2 * (r ^ (k - β) *
          (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u)) := (congrArg (fun x : ℝ => r ^ 2 * x) hscaling).symm
      _ = _ := hleft
  intro z
  by_cases hz : z = 0
  · subst z
    rw [(show DOZZ.planarDifferenceKernel k β 0 = fun _ : ℂ => (0 : ℝ) by funext u; simp [DOZZ.planarDifferenceKernel])]
    simp [Real.zero_rpow, (show 0 < 2 + k - β by linarith).ne']
  · let r : ℝ := ‖z‖
    let ξ : ℂ := z / (r : ℂ)
    have hr : 0 < r := by dsimp [r]; exact norm_pos_iff.mpr hz
    simpa [r] using (planarDifferenceKernel_integral_scale ξ (by dsimp [ξ]; rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; dsimp [r]; exact div_self (norm_ne_zero_iff.mpr hz)) r hr z (show ξ * (r : ℂ) = z by dsimp [ξ]; field_simp [(by exact_mod_cast hr.ne')]))

end DOZZ.Proofs
