/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.OuterMassLimit
public import DOZZ.FourPoint.Reflected.FreezingInput
public import DOZZ.FourPoint.RootedPairMoments
import Mathlib.Tactic
/-! # The actual outer mass retains the freezing annulus -/
public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- On the small annulus separated from the moving insertion, the literal kernel bounds the
radial freezing weight from below, uniformly in the annular radius. -/
theorem reflected_outer_annular_kernel_lower (γ α₁ α₂ α₃ : ℝ) (z x : ℂ)
    (hx : 0 < ‖x‖) (hxh : ‖x‖ < 1 / 2) (hz : ‖z‖ ≤ ‖x‖ / 2) :
    ((1 / 2 : ℝ) ^ (γ ^ 2 / 2) * (2 : ℝ) ^ (-|γ * α₂|)) *
      ‖x‖ ^ (-(γ * (α₁ - γ / 2))) ≤ gammaHalfKernel γ α₁ α₂ α₃ z x := by
  have hk : 0 ≤ γ ^ 2 / 2 := by positivity
  have hd : ‖x‖ / 2 ≤ ‖x - z‖ := by
    have hh := norm_sub_norm_le x z
    linarith
  have hd1 : 2⁻¹ ≤ ‖x - 1‖ := by
    have hh := norm_sub_norm_le 1 x
    rw [norm_one, norm_sub_rev] at hh
    linarith
  have hd2 : ‖x - 1‖ ≤ 2 := by
    have hh := norm_sub_le x 1
    rw [norm_one] at hh
    linarith
  have hb := coulombWeight_le_rpow (by norm_num) hd1 hd2 (-γ * α₂)
  have hbase : 0 < ‖x - 1‖ := by positivity
  have hpow := Real.rpow_le_rpow (by positivity) hd hk
  rw [div_eq_mul_inv, mul_comm ‖x‖, Real.mul_rpow (by norm_num)
    hx.le] at hpow
  have hp : ‖x‖ ^ (γ ^ 2 / 2) * ‖x‖ ^ (-(γ * α₁)) =
      ‖x‖ ^ (-(γ * (α₁ - γ / 2))) := by
    rw [← Real.rpow_add hx]
    ring
  have hkernel : gammaHalfKernel γ α₁ α₂ α₃ z x =
      ‖x - z‖ ^ (γ ^ 2 / 2) * ‖x‖ ^ (-(γ * α₁)) * ‖x - 1‖ ^ (-(γ * α₂)) := by
    unfold gammaHalfKernel normPlus
    rw [max_eq_left (by linarith), Real.one_rpow, mul_one,
      Real.rpow_neg hx.le, Real.rpow_neg hbase.le]
    ring
  rw [hkernel, ← hp]
  have hb' : 2 ^ (-|γ * α₂|) ≤ ‖x - 1‖ ^ (-(γ * α₂)) := by
    simpa using hb
  have hh' := mul_le_mul (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hx.le (-(γ * α₁)))) hb'
    (Real.rpow_nonneg (by norm_num) _) (by positivity)
  calc
    _ = (2⁻¹ ^ (γ ^ 2 / 2) * ‖x‖ ^ (γ ^ 2 / 2) *
        ‖x‖ ^ (-(γ * α₁))) * 2 ^ (-|γ * α₂|) := by
      rw [one_div]
      ring
    _ ≤ _ := hh'


/-- The freezing annulus is genuinely included in the actual retained Coulomb mass. -/
theorem reflected_outerMass_freezing_lower (γ α₁ α₂ α₃ ξ : ℝ) (μ : Measure ℂ) (z : ℂ)
    (he : 0 < ‖z‖ ^ (1 - ξ)) (hz : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2) :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ (γ ^ 2 / 2) * (2 : ℝ) ^ (-|γ * α₂|)) *
      freezingAnnulusMassLocal γ (α₁ - γ / 2) μ 0 (‖z‖ ^ (1 - ξ)) (1 / 2) ≤
        gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ := by
  let E : Set ℂ := {x | ‖z‖ ^ (1 - ξ) < ‖x‖ ∧ ‖x‖ < 1 / 2}
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hE : MeasurableSet E := by measurability
  have hsub : E ⊆ D := by grind
  have hc : 0 ≤ (1 / 2) ^ (γ ^ 2 / 2) * (2 : ℝ) ^ (-|γ * α₂|) := by positivity
  have hpoint (x : ℂ) (hx : x ∈ E) :
      ENNReal.ofReal ((1 / 2) ^ (γ ^ 2 / 2) * 2 ^ (-|γ * α₂|)) *
        ENNReal.ofReal (‖x‖ ^ (-(γ * (α₁ - γ / 2)))) ≤
          coulombWeight γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ x := by
    have hn := he.trans hx.1
    have hsep := hz.trans (div_le_div_of_nonneg_right hx.1.le (by norm_num))
    have hx1 : x ≠ 1 := by
      intro hh
      have hhx := hx.2
      rw [hh, norm_one] at hhx
      norm_num at hhx
    have hxz : x ≠ z := by
      intro hh
      rw [hh] at hsep hn
      linarith only [hsep, hn]
    rw [gammaHalfKernel_coulombWeight γ α₁ α₂ α₃ z x hxz (norm_pos_iff.mp hn) hx1,
      ← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal
      (reflected_outer_annular_kernel_lower γ α₁ α₂ α₃ z x hn hx.2 hsep)
  have heq : freezingAnnulusMassLocal γ (α₁ - γ / 2) μ 0 (‖z‖ ^ (1 - ξ)) (1 / 2) =
      ∫⁻ x in E, ENNReal.ofReal (‖x‖ ^ (-(γ * (α₁ - γ / 2)))) ∂μ := by
    simp only [freezingAnnulusMassLocal, sub_zero, E]
  rw [heq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ∫⁻ x in E, coulombWeight γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ x ∂μ :=
      setLIntegral_mono' hE hpoint
    _ ≤ ∫⁻ x in D, coulombWeight γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ x ∂μ :=
      lintegral_mono' (Measure.restrict_mono hsub le_rfl) (fun _ => le_rfl)
    _ = _ := rfl

end DOZZ.Proofs
