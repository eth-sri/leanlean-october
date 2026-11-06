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




theorem planarTaylorRemainder_integral_scale k β (hk : 0 < k) (hβ : k < β)
    ξ (hξ : ‖ξ‖ = 1) (r : ℝ) (hr : 0 < r) z
    (hz : ξ * (r : ℂ) = z) :
    (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) =
      r ^ (2 + k - β) *
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by
  have planarTaylorRemainder_rotated_scale v : DOZZ.planarTaylorRemainder k β z (ξ * (r • v)) = r ^ (k - β) * DOZZ.planarTaylorRemainder k β 1 v := by
    have planarTaylorRemainder_real_scale : DOZZ.planarTaylorRemainder k β (r : ℂ) (r • v) = r ^ (k - β) * DOZZ.planarTaylorRemainder k β 1 v := by
      by_cases hv : v = 0
      · subst v
        simp [DOZZ.planarTaylorRemainder, Real.zero_rpow, ne_of_gt hk, ne_of_gt (lt_trans hk hβ)]
      · have hnormv : ‖r • v‖ = r * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        have hquot : (r : ℂ) / (r • v) = 1 / v := by
          change (r : ℂ) / ((r : ℂ) * v) = 1 / v
          field_simp [(by exact_mod_cast hr.ne'), hv]
        change (‖r • v - (r : ℂ)‖ ^ k - ‖r • v‖ ^ k +
            (k / 2) * ‖r • v‖ ^ k *
              ((r : ℂ) / (r • v) + star (r : ℂ) / star (r • v)).re) /
            ‖r • v‖ ^ β =
          r ^ (k - β) *
            ((‖v - 1‖ ^ k - ‖v‖ ^ k + (k / 2) * ‖v‖ ^ k *
              (1 / v + star 1 / star v).re) / ‖v‖ ^ β)
        rw [(show ‖r • v - (r : ℂ)‖ ^ k - ‖r • v‖ ^ k + (k / 2) * ‖r • v‖ ^ k * ((r : ℂ) / (r • v) + star (r : ℂ) / star (r • v)).re = r ^ k * (‖v - 1‖ ^ k - ‖v‖ ^ k + (k / 2) * ‖v‖ ^ k * (1 / v + star 1 / star v).re) by rw [(show ‖r • v - (r : ℂ)‖ = r * ‖v - 1‖ by rw [(show r • v - (r : ℂ) = (r : ℂ) * (v - 1) by change (r : ℂ) * v - (r : ℂ) = (r : ℂ) * (v - 1); ring), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]), hnormv, hquot, (show star (r : ℂ) / star (r • v) = star 1 / star v by simpa only [star_div₀, star_one] using (congrArg star hquot)), (Real.mul_rpow hr.le (norm_nonneg (v - 1))), (Real.mul_rpow hr.le (norm_nonneg v))]; ring), hnormv, (Real.mul_rpow hr.le (norm_nonneg v))]
        calc
          _ = (r ^ k / r ^ β) *
              ((‖v - 1‖ ^ k - ‖v‖ ^ k + (k / 2) * ‖v‖ ^ k *
                (1 / v + star 1 / star v).re) / ‖v‖ ^ β) := by
                  field_simp [(Real.rpow_pos_of_pos hr β).ne', (Real.rpow_pos_of_pos (norm_pos_iff.mpr hv) β).ne']
          _ = _ := by rw [← Real.rpow_sub hr k β]
    have planarTaylorRemainder_rotate z v (hξ : ‖ξ‖ = 1) : DOZZ.planarTaylorRemainder k β (ξ * z) (ξ * v) = DOZZ.planarTaylorRemainder k β z v := by
      by_cases hv : v = 0
      · subst v
        simp [DOZZ.planarTaylorRemainder, Real.zero_rpow, ne_of_gt hk, ne_of_gt (lt_trans hk hβ)]
      · have hξ0 : ξ ≠ 0 := by
          intro h
          simp [h] at hξ
        have hquot : (ξ * z) / (ξ * v) = z / v := by
          field_simp [hξ0, hv]
        rw [DOZZ.planarTaylorRemainder, DOZZ.planarTaylorRemainder,
          (show ‖ξ * v - ξ * z‖ = ‖v - z‖ by rw [(show ξ * v - ξ * z = ξ * (v - z) by ring), norm_mul, hξ, one_mul]), (show ‖ξ * v‖ = ‖v‖ by rw [norm_mul, hξ, one_mul]), hquot, (show star (ξ * z) / star (ξ * v) = star z / star v by simpa only [star_div₀, star_mul] using (congrArg star hquot))]
    calc
      DOZZ.planarTaylorRemainder k β z (ξ * (r • v)) =
          DOZZ.planarTaylorRemainder k β (ξ * (r : ℂ)) (ξ * (r • v)) := by rw [hz]
      _ = DOZZ.planarTaylorRemainder k β (r : ℂ) (r • v) :=
        planarTaylorRemainder_rotate (r : ℂ) (r • v) hξ
      _ = r ^ (k - β) * DOZZ.planarTaylorRemainder k β 1 v :=
        planarTaylorRemainder_real_scale
  let g : ℂ → ℝ := fun u => DOZZ.planarTaylorRemainder k β z (ξ * u)
  have hrotation : (∫ u : ℂ, g u) =
      (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) := by
    change (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z (ξ * u)) = _
    let c : Circle := ⟨ξ, by simpa [Submonoid.unitSphere] using hξ⟩
    simpa only [rotation_apply] using
      (LinearIsometryEquiv.measurePreserving (rotation c)).integral_comp
        ((rotation c).toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
        (fun u => DOZZ.planarTaylorRemainder k β z u)
  have hscaling :
      (∫ u : ℂ, g (r • u)) = (r ^ 2)⁻¹ * (∫ u : ℂ, g u) := by
    simpa only [Complex.finrank_real_complex, smul_eq_mul] using (Measure.integral_comp_smul_of_nonneg volume g r (hR := hr.le))
  rw [(show (fun u => g (r • u)) = fun u => r ^ (k - β) * DOZZ.planarTaylorRemainder k β 1 u by funext u; exact planarTaylorRemainder_rotated_scale u), integral_const_mul] at hscaling
  rw [hrotation] at hscaling
  have hleft : r ^ 2 * (r ^ (k - β) *
      (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u)) =
      r ^ (2 + k - β) *
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by
    calc
      _ = (r ^ 2 * r ^ (k - β)) *
          (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by ring
      _ = r ^ (2 + (k - β)) *
          (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by rw [(show r ^ 2 * r ^ (k - β) = r ^ (2 + (k - β)) by rw [← Real.rpow_natCast r 2]; exact (Real.rpow_add hr 2 (k - β)).symm)]
      _ = _ := by congr 1; congr 1; ring
  calc
    (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) =
        r ^ 2 * ((r ^ 2)⁻¹ *
          (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u)) := by rw [(show r ^ 2 * ((r ^ 2)⁻¹ * (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u)) = (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) by field_simp [(pow_ne_zero 2 hr.ne')])]
    _ = r ^ 2 * (r ^ (k - β) *
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u)) := (congrArg (fun x : ℝ => r ^ 2 * x) hscaling).symm
    _ = _ := hleft

end DOZZ.Proofs
