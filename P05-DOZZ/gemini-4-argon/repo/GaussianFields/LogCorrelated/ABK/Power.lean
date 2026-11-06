/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Dilation
public import GaussianFields.LogCorrelated.ABK.Radial

/-!
# GaussianFields.LogCorrelated/ABK/Power

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- Reciprocal-change-of-variables form of `M_α^{-1}`:
`∫ r^{-1-α} (ζ*ζ)(1/r) dr = ∫ t^{α-1} (ζ*ζ)(t) dt`. -/
theorem abkMAlphaInv_eq_integral_rpow_selfConvolution {d}
    ζ (α : ℝ) :
    abkMAlphaInv ζ α =
      ∫ t in Set.Ioi (0 : ℝ),
        t ^ (α - 1) * abkCutoffSelfConvolution ζ (abkRadialPoint d t)
        ∂(volume : Measure ℝ) := by
  unfold abkMAlphaInv
  rw [← (integral_comp_rpow_Ioi (fun t => t ^ (α - 1) * abkCutoffSelfConvolution ζ (abkRadialPoint d t)) (by norm_num : (-1 : ℝ) ≠ 0))]
  refine integral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hr_pos := hr
  have hpow :
      r ^ (-(1 + α)) = r ^ (-2 : ℝ) * (r⁻¹) ^ (α - 1) := by
    calc
      r ^ (-(1 + α)) = r ^ ((-2 : ℝ) + -(α - 1)) := by
        congr 1
        ring
      _ = r ^ (-2 : ℝ) * r ^ (-(α - 1)) := by
        rw [Real.rpow_add hr_pos]
      _ = r ^ (-2 : ℝ) * (r⁻¹) ^ (α - 1) := by
        rw [Real.inv_rpow hr_pos.le, ← Real.rpow_neg hr_pos.le]
  change
    r ^ (-(1 + α)) *
        abkCutoffSelfConvolution ζ (abkRadialPoint d r⁻¹) =
      ((|(-1 : ℝ)| * r ^ ((-1 : ℝ) - 1)) *
        ((r ^ (-1 : ℝ)) ^ (α - 1) *
          abkCutoffSelfConvolution ζ (abkRadialPoint d (r ^ (-1 : ℝ)))))
  rw [hpow, Real.rpow_neg_one]
  norm_num
  ring


/-- Full vector form of the ABK power-decomposition integral. -/
theorem abk_powerDecomposition_integral_eq {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (α : ℝ) {x} (hx : 0 < euclideanNorm x) :
    (∫ r in Set.Ioi (0 : ℝ),
        r ^ (-(1 + (d : ℝ) + α)) *
          abkScaledCutoffSelfConvolution ζ r x
        ∂(volume : Measure ℝ)) =
      (euclideanNorm x) ^ (-α) * abkMAlphaInv ζ α := by
  have abkMAlphaInv_radial_scale {ρ : ℝ} (hρ : 0 < ρ) : (∫ r in Set.Ioi (0 : ℝ), r ^ (-(1 + α)) * abkCutoffSelfConvolution ζ (abkRadialPoint d (ρ * r⁻¹)) ∂(volume : Measure ℝ)) = ρ ^ (-α) * abkMAlphaInv ζ α := by
    let G : ℝ → ℝ := fun s =>
      s ^ (-(1 + α)) * abkCutoffSelfConvolution ζ (abkRadialPoint d s⁻¹)
    let H : ℝ → ℝ := fun r =>
      r ^ (-(1 + α)) * abkCutoffSelfConvolution ζ (abkRadialPoint d (ρ * r⁻¹))
    have hpoint :
        ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
          G (ρ⁻¹ * r) = ρ ^ (1 + α) * H r := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      have hr := hr
      have hpow :
          (ρ⁻¹ * r) ^ (-(1 + α)) =
            ρ ^ (1 + α) * r ^ (-(1 + α)) := by
        calc
          (ρ⁻¹ * r) ^ (-(1 + α))
              = (ρ⁻¹) ^ (-(1 + α)) * r ^ (-(1 + α)) := by
                rw [Real.mul_rpow (inv_nonneg.mpr hρ.le) hr.le]
          _ = ρ ^ (1 + α) * r ^ (-(1 + α)) := by
                rw [(show (ρ⁻¹) ^ (-(1 + α)) = ρ ^ (1 + α) by rw [Real.inv_rpow hρ.le, Real.rpow_neg hρ.le, inv_inv])]
      change
        (ρ⁻¹ * r) ^ (-(1 + α)) *
            abkCutoffSelfConvolution ζ (abkRadialPoint d ((ρ⁻¹ * r)⁻¹)) =
          ρ ^ (1 + α) *
            (r ^ (-(1 + α)) *
              abkCutoffSelfConvolution ζ (abkRadialPoint d (ρ * r⁻¹)))
      rw [hpow, (show (ρ⁻¹ * r)⁻¹ = ρ * r⁻¹ by field_simp [hρ.ne', hr.ne'])]
      ring
    have hpow_coef : (ρ ^ (1 + α))⁻¹ * ρ = ρ ^ (-α) := by
      rw [Real.rpow_add hρ 1 α, Real.rpow_one]
      calc
        (ρ * ρ ^ α)⁻¹ * ρ = (ρ ^ α)⁻¹ := by
          field_simp [hρ.ne', (Real.rpow_pos_of_pos hρ α).ne']
        _ = ρ ^ (-α) := by
          rw [Real.rpow_neg hρ.le]
    calc
      (∫ r in Set.Ioi (0 : ℝ), H r ∂(volume : Measure ℝ))
          = (ρ ^ (1 + α))⁻¹ *
              (∫ r in Set.Ioi (0 : ℝ), G (ρ⁻¹ * r) ∂(volume : Measure ℝ)) := by
            rw [(show (∫ r in Set.Ioi (0 : ℝ), G (ρ⁻¹ * r) ∂(volume : Measure ℝ)) = ρ ^ (1 + α) * (∫ r in Set.Ioi (0 : ℝ), H r ∂(volume : Measure ℝ)) by rw [← integral_const_mul]; exact integral_congr_ae hpoint)]
            field_simp [((Real.rpow_pos_of_pos hρ (1 + α)).ne')]
      _ = (ρ ^ (1 + α))⁻¹ * (ρ * abkMAlphaInv ζ α) := by
            rw [(show (∫ r in Set.Ioi (0 : ℝ), G (ρ⁻¹ * r) ∂(volume : Measure ℝ)) = ρ * abkMAlphaInv ζ α by simpa [G, abkMAlphaInv, smul_eq_mul, hρ.ne'] using (integral_comp_mul_left_Ioi G 0 (inv_pos.mpr hρ)))]
      _ = ρ ^ (-α) * abkMAlphaInv ζ α := by
            rw [← mul_assoc, hpow_coef]
  have abk_powerDecomposition_integrand_eq {α : ℝ} {r : ℝ} (hr : 0 < r) x : r ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ r x = r ^ (-(1 + α)) * abkCutoffSelfConvolution ζ (r⁻¹ • x) := by
    rw [abkScaledCutoffSelfConvolution_eq_pow_mul ζ hr x]
    have hpow :
        r ^ (-(1 + (d : ℝ) + α)) * r ^ d = r ^ (-(1 + α)) := by
      rw [(show r ^ d = r ^ (d : ℝ) by rw [Real.rpow_natCast]), ← Real.rpow_add hr]
      congr 1
      ring
    calc
      r ^ (-(1 + (d : ℝ) + α)) *
          (r ^ d * abkCutoffSelfConvolution ζ (r⁻¹ • x))
          = (r ^ (-(1 + (d : ℝ) + α)) * r ^ d) *
              abkCutoffSelfConvolution ζ (r⁻¹ • x) := by ring
      _ = r ^ (-(1 + α)) * abkCutoffSelfConvolution ζ (r⁻¹ • x) := by rw [hpow]
  rw [← abkMAlphaInv_radial_scale hx]
  refine integral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hr_pos := hr
  have hinv_nonneg := inv_nonneg.mpr hr_pos.le
  rw [abk_powerDecomposition_integrand_eq hr_pos x, abkCutoffSelfConvolution_radial ζ (show euclideanNorm (r⁻¹ • x) = euclideanNorm (abkRadialPoint d (euclideanNorm x * r⁻¹)) by rw [euclideanNorm_inv_smul, abs_of_nonneg hinv_nonneg, euclideanNorm_abkRadialPoint_of_nonneg hd (mul_nonneg (euclideanNorm_nonneg x) hinv_nonneg)]; ring)]

end GaussianFields

end
