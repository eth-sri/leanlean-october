/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.KernelIntegrability
import BergmanWeakType.Weighted.BetaIntegral
import BergmanWeakType.Weighted.CircleMobius
import BergmanWeakType.Weighted.PolarPotential
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Tactic

variable {r α R : ℝ}

/-! # The circular boundary-kernel normalizer

The normalizer is the average of the actual positive boundary kernel. Its sharp
bound requires a circle change of variables and a beta integral; neither estimate
is included as a hypothesis or an axiom here.
-/



noncomputable section




namespace BergmanWeakType

/-- Circular power moment of the boundary kernel. -/
def boundaryMoment (p : ℝ) :=
  Real.circleAverage (fun z : ℂ ↦ ‖1 - z‖ ^ p) 0

/-- The normalizing moment for the weighted Bergman kernel. -/
def normalizer (α : ℝ) := boundaryMoment (-(α + 2))

@[fun_prop] theorem measurable_normalizer (α ) : Measurable (normalizer α) := by
  unfold normalizer boundaryMoment
  apply Weighted.measurable_circleAverage measurable_id
  fun_prop

theorem normalizer_nonneg (α r ) : 0 ≤ normalizer α r := Real.circleAverage_nonneg_of_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

def continuousOn_normalizer (α)  :=
  by
  change ContinuousOn (normalizer α) unitIco
  unfold normalizer boundaryMoment
  apply Real.ContinuousOn.circleAverage
  · apply ContinuousOn.rpow_const (by fun_prop)
    aesop (add norm [sub_eq_zero])
  · simp_all

theorem circleAverage_boundary_power (hα : -1 < α) :
    Real.circleAverage (fun ζ : ℂ ↦ ‖1 - ζ‖ ^ α) 0 1 = gammaConstant α :=
  by
  rw [Real.circleAverage_def]
  have heq : ∫ θ in 0..2 * Real.pi, ‖1 - circleMap 0 1 θ‖ ^ α = 2 ^ α * ∫ θ in 0..2 * Real.pi, Real.sin (θ / 2) ^ α :=
    by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
    intro θ hθ
    dsimp only
    have hs : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by grind) (by grind)
    rw [circleMap, zero_add, Complex.ofReal_one, one_mul, norm_sub_rev, mul_comm _ Complex.I,
      Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg zero_le_two hs), Real.mul_rpow zero_le_two hs]
  rw [heq, intervalIntegral.integral_comp_div (fun θ ↦ Real.sin θ ^ α) two_ne_zero]
  simp
  rw [integral_sin_rpow hα]
  field

theorem norm_boundaryKernel_circleMap_rpow (p r θ : ℝ) :
    ‖1 - r * circleMap 0 1 θ‖ ^ p =
      circleDenominator r (Real.cos θ) ^ (p / 2) := by
  conv_lhs =>
    rw [show p = 2 * (p / 2) by ring, Real.rpow_mul (norm_nonneg _), Real.rpow_two]
  congr 1
  convert (Weighted.polarDenominator_eq_norm_sq 1 r θ).symm using 1 <;>
    simp [Weighted.polarDenominator, Weighted.radialComponent, circleDenominator, circleMap] <;> ring

theorem circleAverage_radialKernel_eq_arcsine (p : ℝ) (hr : |r| < 1) :
    boundaryMoment p r =
      Real.pi⁻¹ * ∫ x in -1..1, circleDenominator r x ^ (p / 2) / Real.sqrt (1 - x ^ 2) :=
  by
  let F := fun x ↦ circleDenominator r x ^ (p / 2)
  have hc : Continuous (fun θ ↦ F (Real.cos θ)) :=
    by
    apply Continuous.rpow_const (by unfold circleDenominator; fun_prop)
    exact fun θ ↦ Or.inl (circleDenominator_pos hr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩).ne'
  have heq : ∫ θ in Real.pi..2 * Real.pi, F (Real.cos θ) = ∫ θ in 0..Real.pi, F (Real.cos θ) :=
    by
    conv_lhs => arg 1; intro θ; rw [← Real.cos_two_pi_sub θ]
    rw [intervalIntegral.integral_comp_sub_left (fun θ ↦ F _), sub_self,
      show 2 * Real.pi - Real.pi = Real.pi by ring]
  rw [boundaryMoment, Real.circleAverage_eq_circleAverage_zero_one, Real.circleAverage_def]
  simp_rw [add_zero, norm_boundaryKernel_circleMap_rpow]
  change (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, F (Real.cos θ) = _
  rw [←
    intervalIntegral.integral_add_adjacent_intervals   
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    heq]
  calc
    _ = Real.pi⁻¹ * ∫ θ in 0..Real.pi, F _ := by ring
    _ = _ := by
      congr 1
      have hsub :=
        intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos     (g := fun x ↦ F x / Real.sqrt (1 - x ^ 2)) Real.continuous_cos.continuousOn
          (fun θ _ ↦ Real.hasDerivAt_cos θ)
          (fun θ hθ ↦ by
            rw [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hθ
            exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le))
      rw [Real.cos_zero, Real.cos_pi, intervalIntegral.integral_symm (f := fun x ↦ F x / Real.sqrt _)] at hsub
      apply neg_injective
      rw [← intervalIntegral.integral_neg]
      convert hsub using 1
      apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
      intro θ hθ
      dsimp
      have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
      rw [show 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 by exact?, Real.sqrt_sq_eq_abs, abs_of_pos hs]
      field_simp

/-- The exact Möbius identity for the weighted boundary-kernel normalizer. -/
theorem radialMass_mul_normalizer (α) (hr : |r| < 1) :
    (1 - r ^ 2) ^ (α + 1) * normalizer α r = boundaryMoment α r :=
  by
  unfold normalizer
  rw [circleAverage_radialKernel_eq_arcsine _ hr, circleAverage_radialKernel_eq_arcsine _ hr]
  calc
    _ =
        Real.pi⁻¹ *
          ((1 - r ^ 2) ^ (α + 1) * ∫ x in -1..1, circleDenominator r x ^ (-(α + 2) / 2) / Real.sqrt (1 - x ^ 2)) :=
      by ring
    _ = _ := by
      congr 1
      have hsub :=
        intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (a := -1) (b := 1)  (f' := fun x ↦
          -(1 - r ^ 2) ^ 2 / circleDenominator r x ^ 2) (g := fun x ↦
          circleDenominator r x ^ (α / 2) / Real.sqrt (1 - x ^ 2)) (by simpa using continuousOn_circleMobius hr)
          (fun x hx ↦ by
          have hd := circleDenominator_pos (x := x) hr (by grind)
          unfold circleMobius circleDenominator at *
          differentiate)
          (fun x _ ↦ div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _))
      rw [circleMobius_neg_one hr, circleMobius_one hr,
        intervalIntegral.integral_symm (f := fun x ↦ circleDenominator r x ^ (α / 2) / Real.sqrt _)] at hsub
      rw [← intervalIntegral.integral_const_mul]
      apply neg_injective
      rw [← intervalIntegral.integral_neg]
      convert hsub using 1
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro x hx
      dsimp
      simp [neg_div]
      rw [sqrt_one_sub_circleMobius_sq hr ⟨hx.1.le, hx.2.le⟩, circleDenominator_circleMobius hr ⟨hx.1.le, hx.2.le⟩]
      have hδ : 0 < 1 - r ^ 2 := by simp_all
      have hD := circleDenominator_pos hr ⟨hx.1.le, hx.2.le⟩
      have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.mpr (by simpa [sub_pos] using abs_lt.mpr hx)
      rpow_ring

theorem circleAverage_boundaryPower_mono (α : ℝ)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1) :
    boundaryMoment α r ≤ boundaryMoment α R := by
  have heq (s ) : boundaryMoment α s =
      Weighted.angularMean (Weighted.polarKernel (α / 2) 1) s := by
    rw [boundaryMoment, Real.circleAverage_eq_circleAverage_zero_one, Real.circleAverage_def, Weighted.angularMean]
    simp_rw [add_zero, norm_boundaryKernel_circleMap_rpow]
    simp_all [Weighted.polarKernel, circleDenominator, Weighted.polarDenominator, Weighted.radialComponent] <;> ring
  simp_rw [heq]
  exact Weighted.monotoneOn_angularMean_polarKernel _ 1 (by norm_num)
    ⟨hr, hrR.trans_lt hR⟩ ⟨hr.trans hrR, hR⟩ hrR

theorem normalizer_pos (hr : |r| < 1) : 0 < normalizer α r :=
  by
  apply lt_of_lt_of_le zero_lt_one
  simpa [normalizer, boundaryMoment, Real.circleAverage_abs_radius] using
    circleAverage_boundaryPower_mono _ le_rfl (abs_nonneg r) hr

end BergmanWeakType
