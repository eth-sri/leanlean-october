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





theorem planarDifferenceKernel_integral_scale_norm (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) :
    ∀ z : ℂ,
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) =
        ‖z‖ ^ (2 + k - β) *
          (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
  have planarDifferenceKernel_rotated_scale (ξ : ℂ) (hξ : ‖ξ‖ = 1) (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ξ * (r : ℂ) = z) (v : ℂ) : DOZZ.planarDifferenceKernel k β z (ξ * (r • v)) =
        r ^ (k - β) * DOZZ.planarDifferenceKernel k β 1 v := by
    have planarDifferenceKernel_real_scale : DOZZ.planarDifferenceKernel k β (r : ℂ) (r • v) =
          r ^ (k - β) * DOZZ.planarDifferenceKernel k β 1 v := by
      by_cases hv : v = 0
      · subst v
        simp [DOZZ.planarDifferenceKernel, Real.zero_rpow, ne_of_gt hk, ne_of_gt (lt_trans hk hβ)]
      · have hnormv : ‖r • v‖ = r * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        have hshift : r • v - (r : ℂ) = (r : ℂ) * (v - 1) := by
          change (r : ℂ) * v - (r : ℂ) = (r : ℂ) * (v - 1)
          ring
        have hnormshift : ‖r • v - (r : ℂ)‖ = r * ‖v - 1‖ := by
          rw [hshift, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        have hpowerV : (r * ‖v‖) ^ k = r ^ k * ‖v‖ ^ k :=
          Real.mul_rpow hr.le (norm_nonneg v)
        have hpowerShift : (r * ‖v - 1‖) ^ k = r ^ k * ‖v - 1‖ ^ k :=
          Real.mul_rpow hr.le (norm_nonneg (v - 1))
        have hpowerDen : (r * ‖v‖) ^ β = r ^ β * ‖v‖ ^ β :=
          Real.mul_rpow hr.le (norm_nonneg v)
        have hnum : ‖r • v - (r : ℂ)‖ ^ k - ‖r • v‖ ^ k =
            r ^ k * (‖v - 1‖ ^ k - ‖v‖ ^ k) := by
          rw [hnormshift, hnormv, hpowerShift, hpowerV]
          ring
        change (‖r • v - (r : ℂ)‖ ^ k - ‖r • v‖ ^ k) / ‖r • v‖ ^ β =
          r ^ (k - β) * ((‖v - 1‖ ^ k - ‖v‖ ^ k) / ‖v‖ ^ β)
        rw [hnum, hnormv, hpowerDen]
        calc
          _ = (r ^ k / r ^ β) * ((‖v - 1‖ ^ k - ‖v‖ ^ k) / ‖v‖ ^ β) := by
            field_simp [(Real.rpow_pos_of_pos hr β).ne', (Real.rpow_pos_of_pos (norm_pos_iff.mpr hv) β).ne']
          _ = _ := by rw [← Real.rpow_sub hr k β]
    have planarDifferenceKernel_rotate (z v : ℂ) (hξ : ‖ξ‖ = 1) : DOZZ.planarDifferenceKernel k β (ξ * z) (ξ * v) =
          DOZZ.planarDifferenceKernel k β z v := by
      have hshift : ξ * v - ξ * z = ξ * (v - z) := by ring
      rw [DOZZ.planarDifferenceKernel, DOZZ.planarDifferenceKernel, hshift]
      simp only [norm_mul, hξ, one_mul]
    calc
      DOZZ.planarDifferenceKernel k β z (ξ * (r • v)) =
          DOZZ.planarDifferenceKernel k β (ξ * (r : ℂ)) (ξ * (r • v)) := by rw [hz]
      _ = DOZZ.planarDifferenceKernel k β (r : ℂ) (r • v) :=
        planarDifferenceKernel_rotate (r : ℂ) (r • v) hξ
      _ = r ^ (k - β) * DOZZ.planarDifferenceKernel k β 1 v :=
        planarDifferenceKernel_real_scale
  have planarDifferenceKernel_integral_scale (ξ : ℂ) (hξ : ‖ξ‖ = 1) (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ξ * (r : ℂ) = z) : (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) =
        r ^ (2 + k - β) *
          (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
    let g : ℂ → ℝ := fun u => DOZZ.planarDifferenceKernel k β z (ξ * u)
    have hrotation : (∫ u : ℂ, g u) =
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) := by
      change (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z (ξ * u)) = _
      let c : Circle := ⟨ξ, by simpa [Submonoid.unitSphere] using hξ⟩
      simpa only [rotation_apply] using
        (LinearIsometryEquiv.measurePreserving (rotation c)).integral_comp
          ((rotation c).toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
          (fun u : ℂ => DOZZ.planarDifferenceKernel k β z u)
    have hscaling :
        (∫ u : ℂ, g (r • u)) = (r ^ 2)⁻¹ * (∫ u : ℂ, g u) := by
      simpa only [Complex.finrank_real_complex, smul_eq_mul] using Measure.integral_comp_smul_of_nonneg volume g r (hR := hr.le)
    have hpoint : (fun u : ℂ => g (r • u)) = fun u =>
        r ^ (k - β) * DOZZ.planarDifferenceKernel k β 1 u := by
      funext u
      exact planarDifferenceKernel_rotated_scale ξ hξ r hr z hz u
    rw [hpoint, integral_const_mul] at hscaling
    rw [hrotation] at hscaling
    have hleft : r ^ 2 * (r ^ (k - β) *
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u)) =
        r ^ (2 + k - β) *
          (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
      have hp : r ^ 2 * r ^ (k - β) = r ^ (2 + (k - β)) := by
        rw [← Real.rpow_natCast r 2]
        exact (Real.rpow_add hr 2 (k - β)).symm
      calc
        _ = (r ^ 2 * r ^ (k - β)) *
            (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by ring
        _ = r ^ (2 + (k - β)) *
            (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by rw [hp]
        _ = _ := by congr 1; congr 1; ring
    have hright : r ^ 2 * ((r ^ 2)⁻¹ *
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u)) =
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) := by
      field_simp [pow_ne_zero 2 hr.ne']
    calc
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) =
          r ^ 2 * ((r ^ 2)⁻¹ *
            (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u)) := by rw [hright]
      _ = r ^ 2 * (r ^ (k - β) *
          (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u)) := (congrArg (fun x : ℝ => r ^ 2 * x) hscaling).symm
      _ = _ := hleft
  intro z
  have hα : 0 < 2 + k - β := by linarith
  by_cases hz : z = 0
  · subst z
    have hzero : DOZZ.planarDifferenceKernel k β 0 = fun _ : ℂ => (0 : ℝ) := by
      funext u
      simp [DOZZ.planarDifferenceKernel]
    rw [hzero]
    simp [Real.zero_rpow, hα.ne']
  · let r : ℝ := ‖z‖
    let ξ := z / (r : ℂ)
    have hr : 0 < r := by positivity
    have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hξ : ‖ξ‖ = 1 := by
      dsimp [ξ]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      dsimp [r]
      exact div_self (norm_ne_zero_iff.mpr hz)
    have hξr : ξ * (r : ℂ) = z := by grind
    simpa [r] using planarDifferenceKernel_integral_scale ξ hξ r hr z hξr

end DOZZ.Proofs
