/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelGaussianIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Gaussian half-line primitives for the last-exit density

The explicit heat-kernel primitive evaluates the boundary terms in the deterministic-time
last-exit calculation. Its time derivative is the Gaussian boundary flux.
-/

@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs

/-- The standard heat-kernel upper tail, expressed by its finite-interval primitive. -/
noncomputable def brownianStandardHeatTail (z : ℝ) : ℝ :=
  (∫ y in Ioi (0 : ℝ), brownianHeatDensity 1 y) - ∫ y in (0 : ℝ)..z, brownianHeatDensity 1 y

/-- The upper heat-kernel tail at variance `t`. -/
noncomputable def brownianHeatTail (t z : ℝ) : ℝ :=
  brownianStandardHeatTail (z / Real.sqrt t)

theorem continuous_brownianHeatDensity {t : ℝ} (ht : 0 < t) :
    Continuous (brownianHeatDensity t) := by
  change Continuous (fun x => if 0 < t then
    Real.exp _ / Real.sqrt _ else 0)
  continuity

/-- The spatial derivative of the standard Gaussian upper tail. -/
theorem hasDerivAt_brownianStandardHeatTail (z : ℝ) :
    HasDerivAt brownianStandardHeatTail (-brownianHeatDensity 1 z) z := by
  convert (hasDerivAt_const z (∫ y in Ioi (0 : ℝ), brownianHeatDensity 1 y)).sub
    ((continuous_brownianHeatDensity (by norm_num : (0 : ℝ) < 1)).integral_hasStrictDerivAt 0 z).hasDerivAt using 1
  · rfl
  · simp
section
variable {t : ℝ}
section
variable (ht : 0 < t)
include ht
section
variable (z : ℝ)

/-- Scaling the Gaussian density by its standard deviation. -/
theorem brownianHeatDensity_standard_scale :
    brownianHeatDensity 1 (z / Real.sqrt t) / Real.sqrt t = brownianHeatDensity t z := by
  have hs : Real.sqrt t ≠ 0 := by positivity
  have he : -(z / Real.sqrt t)^2 / (2 * 1) = -z^2 / (2*t) := by
    grind
  simp only [brownianHeatDensity, ite_eq_left (by norm_num : (0 : ℝ) < 1), ite_eq_left ht]
  rw [he, show 2 * Real.pi * t = (2 * Real.pi) * t by ring,
    Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  field_simp
  rw [Real.sqrt_one, mul_one, show 2*t*Real.pi = 2*Real.pi*t by ring,
    Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi)]

/-- The heat tail is the actual half-line integral of the explicit density. -/
theorem brownianHeatTail_eq_integral :
    brownianHeatTail t z = ∫ y in Ioi z, brownianHeatDensity t y := by
  have hhalf (u : ℝ) (hu : 0 < u) :
      (∫ y in Ioi 0, brownianHeatDensity u y) = (1/2) := by
    have h := integral_brownianHeatDensity_halfline_pair (t := u) (a := 0) hu
    grind
  have hscale : (∫ y in 0..z, brownianHeatDensity t y) =
      ∫ y in 0..(z / Real.sqrt t), brownianHeatDensity 1 y := by
    simp_rw [← brownianHeatDensity_standard_scale ht]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_div _
      (Real.sqrt_pos.2 ht).ne']
    simp [smul_eq_mul, (Real.sqrt_pos.2 ht).ne']
  have hi := intervalIntegral.integral_Ioi_sub_Ioi'
    (a := 0) (b := z)
    (integrable_brownianHeatDensity ht).integrableOn
    (integrable_brownianHeatDensity ht).integrableOn
  unfold brownianHeatTail brownianStandardHeatTail
  grind

end

/-- A translated heat density is integrable on the full real line. -/
theorem integrable_brownianHeatDensity_sub_const (a : ℝ) :
    Integrable (fun y : ℝ => brownianHeatDensity t (y-a)) (volume : Measure ℝ) := by
  have he : MeasurableEmbedding (fun y => y + -a) :=
    (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding
  have hm : (volume : Measure ℝ).map (fun y => y + -a) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self (-a)
  have hi : Integrable (brownianHeatDensity t)
      ((volume : Measure ℝ).map (fun y => y + -a)) := by
    rw [hm]
    exact integrable_brownianHeatDensity ht
  simpa only [sub_eq_add_neg, Function.comp_def] using he.integrable_map_iff.mp hi

/-- Translation of a Gaussian half-line integral is its shifted upper tail. -/
theorem integral_brownianHeatDensity_sub_const_Ioi (a c : ℝ) :
    (∫ y in Ioi c, brownianHeatDensity t (y-a)) = brownianHeatTail t (c-a) := by
  have he : MeasurableEmbedding (fun y => y + -a) :=
    (Homeomorph.addRight (-a)).isClosedEmbedding.measurableEmbedding
  have hm : (volume : Measure ℝ).map (fun y => y + -a) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self (-a)
  have h := he.setIntegral_map (μ := (volume : Measure ℝ))
    (brownianHeatDensity t) (Ioi (c-a))
  have hp : (fun y => y + -a) ⁻¹' Ioi (c-a) = Ioi c := by
    simp
  rw [hm, hp] at h
  rw [brownianHeatTail_eq_integral ht]
  tauto

end

end

/-- Time differentiation of a Gaussian tail with an affine moving boundary. -/
theorem hasDerivAt_brownianHeatTail_affine (a b t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => brownianHeatTail u (a + b*u))
      (brownianHeatDensity t (a+b*t) * (a/(2*t)-b/2)) t := by
  have hn : HasDerivAt (fun u => a+b*u) b t := by
    convert (hasDerivAt_id t).const_mul b |>.const_add a using 1 <;> simp
  have hq := hn.div (Real.hasDerivAt_sqrt ht.ne') ((Real.sqrt_pos.2 ht).ne')
  convert ((hasDerivAt_brownianStandardHeatTail ((a+b*t)/Real.sqrt t)).comp t hq) using 1
  · rfl
  · rw [← brownianHeatDensity_standard_scale ht (a+b*t)]
    grind

end DOZZ.Proofs

end
