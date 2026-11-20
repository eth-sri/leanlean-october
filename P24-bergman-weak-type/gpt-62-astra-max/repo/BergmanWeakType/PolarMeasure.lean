/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import BergmanWeakType.Calculus
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Polar disintegration in the radial mass coordinate

A sample from the weighted disk is a uniform angle and an independent radius.
The exterior mass is the primitive of the radial density, giving both normalization
and the exact mass of every outer annulus. -/
@[expose] public section
noncomputable section
open Set MeasureTheory Real
open scoped ENNReal
namespace BergmanWeakType

abbrev angularInterval := Ioo (-π) π
def angleMeasure : Measure ℝ := ENNReal.ofReal (2*π)⁻¹ • volume.restrict angularInterval
def exteriorMass (α r : ℝ) := (1-r^2)^(α+1)
def radialDensity (α r : ℝ) := 2*r*((α+1)*(1-r^2)^α)

def radialLaw (α : ℝ) := (volume.restrict unitInterval).withDensity fun r ↦ ENNReal.ofReal (radialDensity α r)

instance : IsProbabilityMeasure angleMeasure := by
  constructor
  simp [angleMeasure, two_mul]
  rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]

theorem ae_angle : ∀ᵐ θ ∂angleMeasure, θ ∈ Icc (-π) π :=
  Measure.ae_smul_measure (Filter.Eventually.mono (ae_restrict_mem measurableSet_Ioo) (by grind)) _

theorem radialDensity_nonneg {α r : ℝ} (h : -1 < α) (hr : r ∈ Icc 0 1) : 0 ≤ radialDensity α r := by
  have := hr.1; have : 0 ≤ 1-r^2 := by nlinarith [hr.2]
  unfold radialDensity; have : 0 < α+1 := by linarith
  positivity

theorem exteriorMass_deriv {α r : ℝ} (hr : r^2 < 1) : HasDerivAt (exteriorMass α) (-radialDensity α r) r := by
  have := sub_pos.mpr hr
  unfold exteriorMass radialDensity; scalar_deriv; grind

theorem mass_anti {α : ℝ} (h : -1 < α) : StrictAntiOn (exteriorMass α) (Icc 0 1) := by
  intro x hx y hy hxy; apply rpow_lt_rpow _ _ (by linarith : 0 < α+1) <;> nlinarith [hx.1,hy.1,hy.2]

theorem radialLaw_tail {α r : ℝ} (h : -1 < α) (hr : r ∈ radii) :
    radialLaw α (Ioo r 1) = ENNReal.ofReal (exteriorMass α r) := by
  have cm : Continuous (exteriorMass α) := by unfold exteriorMass; fun_prop (disch := linarith)
  have m := (mass_anti h).mono (show Icc r 1 ⊆ Icc 0 1 by grind)
  have ms : Ioo r 1 ⊆ unitInterval := by grind
  have H := lintegral_deriv_eq_volume_image_of_antitoneOn measurableSet_Ioo
    (fun u hu ↦ (exteriorMass_deriv (α := α) (inner_sq (ms hu))).hasDerivWithinAt)
    (m.antitoneOn.mono Ioo_subset_Icc_self)
  rw [cm.continuousOn.image_Ioo_of_strictAntiOn hr.2.le m] at H
  simpa [radialLaw, withDensity_apply _ measurableSet_Ioo, Measure.restrict_restrict_of_subset ms,
    exteriorMass, Real.zero_rpow (by linarith : α+1 ≠ 0)] using H

theorem ae_radial (α : ℝ) : ∀ᵐ r ∂radialLaw α, r ∈ unitInterval :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

theorem radialLaw_prob {α : ℝ} (h : -1 < α) : IsProbabilityMeasure (radialLaw α) := by
  constructor; rw [← measure_congr (ae_eq_univ.mpr (ae_radial α))]
  change radialLaw α (Ioo 0 1) = 1; rw [radialLaw_tail h (by simp)]; simp [exteriorMass]

abbrev polarLaw (α : ℝ) := (radialLaw α).prod angleMeasure

def sample (p : ℝ × ℝ) := circleMap 0 p.1 p.2

@[fun_prop] theorem measurable_sample : Measurable sample := by unfold sample; fun_prop

theorem weightedArea_map {α : ℝ} (h : -1 < α) : weightedArea α = (polarLaw α).map sample := by
  let := radialLaw_prob h
  apply Measure.ext_of_lintegral _
  intro f hf
  have hd : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  have hset : {p : ℝ × ℝ | p.1 < 1} ∩ (Ioi 0 ×ˢ angularInterval) = unitInterval ×ˢ angularInterval := by grind
  rw [weightedArea, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf,
    diskArea, area, Measure.restrict_smul, lintegral_smul_measure, ← lintegral_indicator hd, ← Complex.lintegral_comp_polarCoord_symm,
    lintegral_map hf measurable_sample, polarLaw, angleMeasure, Measure.prod_smul_right, radialLaw,
    prod_withDensity_left (by unfold radialDensity; fun_prop), Measure.prod_restrict, ← Measure.volume_eq_prod,
    lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ (by unfold radialDensity; fun_prop) (by fun_prop),
    smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← hset, ← setLIntegral_indicator (by measurability)]
  apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo); intro p hp
  have hr := hp.1
  by_cases h : p.1 < 1 <;> simp [disk,abs_of_pos hr,h,sample,circleMap,Complex.exp_mul_I,radialDensity]
  rw [ENNReal.ofReal_mul (mul_nonneg zero_le_two hr.le), ENNReal.ofReal_mul zero_le_two]
  have e : ENNReal.ofReal π⁻¹ = ENNReal.ofReal (2*π)⁻¹ * 2 := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by positivity)]; field_simp
  simp [e]; ring

theorem integral_angle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℂ → E) (r : ℝ) :
    ∫ θ, f (circleMap 0 r θ) ∂angleMeasure = circleAverage f 0 r := by
  rw [angleMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    circleAverage_eq_integral_add (-π), intervalIntegral.integral_comp_add_right (fun θ ↦ f (circleMap 0 r θ)) (-π), zero_add,
    show 2*π + -π = π by ring, intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo]

theorem integral_radialLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ}
    (h : -1 < α) (f : ℝ → E) : ∫ r, f r ∂radialLaw α = ∫ r in unitInterval, radialDensity α r • f r := by
  rw [radialLaw, integral_withDensity_eq_integral_toReal_smul (by unfold radialDensity; fun_prop) (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  exact setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ by grind [radialDensity_nonneg, ENNReal.toReal_ofReal]

theorem weighted_polar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α : ℝ}
    (h : -1 < α) {f : ℂ → E} (hf : Integrable f (weightedArea α)) :
    ∫ z, f z ∂weightedArea α = ∫ r, circleAverage f 0 r ∂radialLaw α := by
  let := radialLaw_prob h
  rw [weightedArea_map h] at hf ⊢
  rw [integral_map (by fun_prop) hf.1, integral_prod (fun p ↦ f (sample p)) (hf.comp_aemeasurable (by fun_prop))]
  simp [sample,integral_angle]

theorem unit_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ y in (0 : ℝ)..1, f y = ∫ y in unitInterval, f y := by
  grind [integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le]

theorem weightedArea_isProbabilityMeasure (α : ℝ) (h : -1 < α) : IsProbabilityMeasure (weightedArea α) := by
  rw [weightedArea_map h]
  let := radialLaw_prob h
  infer_instance

end BergmanWeakType
