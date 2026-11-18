/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelShiftedRatio
public import DOZZ.Brownian.ConditionedKernelProbability
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Shifted stochastic order for conditioned transition kernels

The positive-drift start comparison for conditioned Brownian kernels shifts the larger-start
endpoint left by the difference in starting states. The shifted likelihood ratio is antitone, and
the shifted law's mass below zero supplies the other half of the single-crossing argument.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Set Topology
open scoped ENNReal

namespace DOZZ.Proofs

private lemma shifted_density_props {ν t x d : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x)
    (hd : 0 ≤ d) :
    let g := fun y => conditionedPositiveTransitionDensity ν t x (y + d)
    Integrable g volume ∧ (∀ y, 0 ≤ g y) ∧ (∫ y, g y = 1) ∧
      0 < (∫ y in Ioi 0, g y) ∧ (∫ y in Ioi 0, g y) ≤ 1 := by
  intro g
  have he : MeasurableEmbedding fun y : ℝ => y + d :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self d
  have hfx : Integrable (conditionedPositiveTransitionDensity ν t x)
      ((volume : Measure ℝ).map (fun y : ℝ => y + d)) := by
    rw [hmap]; exact integrable_conditionedPositiveTransitionDensity hν ht hx
  have hg : Integrable g volume := he.integrable_map_iff.mp hfx
  have hng (y : ℝ) : 0 ≤ g y := conditionedPositiveTransitionDensity_nonneg hν ht hx (y + d)
  have hunit : ∫ y, g y = 1 := by
    have h1 := he.integral_map (μ := (volume : Measure ℝ)) (conditionedPositiveTransitionDensity ν t x)
    rw [hmap] at h1
    exact h1.symm.trans (conditionedPositiveTransitionDensity_integral_eq_one hν ht hx)
  have hmpos : 0 < ∫ y in Ioi 0, g y := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hng) hg.integrableOn]
    refine lt_of_lt_of_le (by rw [Real.volume_Ioc]; norm_num : (0 : ℝ≥0∞) < volume (Ioc (1 : ℝ) 2))
      (measure_mono fun y hy => ⟨ne_of_gt (conditionedPositiveTransitionDensity_pos hν ht hx
        (by have := hy.1; linarith)), show 0 < y by have := hy.1; linarith⟩)
  have hmle : (∫ y in Ioi 0, g y) ≤ 1 := by
    have hsp := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hg
    rw [compl_Ioi, hunit] at hsp
    have h0 : 0 ≤ ∫ y in Iic (0 : ℝ), g y := setIntegral_nonneg measurableSet_Iic fun y _ => hng y
    linarith
  exact ⟨hg, hng, hunit, hmpos, hmle⟩

section
variable {ν₁ ν₂ t x₁ x₂ d u : ℝ} (hν₁ : 0 ≤ ν₁) (hν₂ : 0 ≤ ν₂) (ht : 0 < t) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
include d u hν₁ hν₂ ht hx₁ hx₂

private lemma quantile_le_add_of_shifted_cdf_ge
 (hu : 0 < u) (hu1 : u < 1)
    (hcdf : ∀ z, (∫ y in Iic z, conditionedPositiveTransitionDensity ν₁ t x₁ y) ≤
      ∫ y in Iic z, conditionedPositiveTransitionDensity ν₂ t x₂ (y + d)) :
    cdfGeneralizedQuantile (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν₂ t x₂)) u ≤
      cdfGeneralizedQuantile (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν₁ t x₁)) u + d := by
  let μ₁ := conditionedPositiveTransitionMeasure ν₁ t x₁
  let μ₂ := conditionedPositiveTransitionMeasure ν₂ t x₂
  have := isProbabilityMeasure_conditionedPositiveTransitionMeasure ν₁ t x₁ hν₁ ht hx₁
  have := isProbabilityMeasure_conditionedPositiveTransitionMeasure ν₂ t x₂ hν₂ ht hx₂
  have hne₁ : {z | u ≤ ProbabilityTheory.cdf μ₁ z}.Nonempty := by
    obtain ⟨a, ha⟩ := eventually_atTop.1 ((ProbabilityTheory.tendsto_cdf_atTop μ₁).eventually (Ioi_mem_nhds hu1))
    exact ⟨a, (ha a le_rfl).le⟩
  have hbdd₂ : BddBelow {z | u ≤ ProbabilityTheory.cdf μ₂ z} := ⟨0, fun z hz => by
    by_contra hlt
    have hz0 : ProbabilityTheory.cdf μ₂ z = 0 := by
      rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν₂ ht hx₂,
        setIntegral_congr_fun measurableSet_Iic fun y hy =>
          conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν₂ ht hx₂ (hy.trans (not_le.1 hlt).le)]
      simp
    linarith [show u ≤ ProbabilityTheory.cdf μ₂ z from hz]⟩
  unfold cdfGeneralizedQuantile
  refine sub_le_iff_le_add.mp (le_csInf hne₁ fun z hz => sub_le_iff_le_add.mpr (csInf_le hbdd₂ ?_))
  show u ≤ ProbabilityTheory.cdf μ₂ (z + d)
  have he : MeasurableEmbedding fun y : ℝ => y + d :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have hshift : (∫ y in Iic z, conditionedPositiveTransitionDensity ν₂ t x₂ (y + d)) =
      ∫ y in Iic (z + d), conditionedPositiveTransitionDensity ν₂ t x₂ y := by
    have h := he.setIntegral_map (μ := (volume : Measure ℝ))
      (conditionedPositiveTransitionDensity ν₂ t x₂) (Iic (z + d))
    rw [Measure.IsAddRightInvariant.map_add_right_eq_self d,
      show (fun y : ℝ => y + d) ⁻¹' Iic (z + d) = Iic z by ext; simp] at h
    exact h.symm
  rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν₂ ht hx₂, ← hshift]
  have hz' : u ≤ ∫ y in Iic z, conditionedPositiveTransitionDensity ν₁ t x₁ y := by
    rwa [← conditionedPositiveTransitionMeasure_cdf_eq_integral hν₁ ht hx₁]
  exact hz'.trans (hcdf z)

private lemma quantile_le_add_of_shifted_antitone_ratio
 (hd : 0 ≤ d) (hu : 0 < u) (hu1 : u < 1)
    {r : ℝ → ℝ} (hrpos : ∀ y, 0 < y → 0 < r y) (hranti : AntitoneOn r (Ioi 0))
    (hfac : ∀ y, 0 < y → conditionedPositiveTransitionDensity ν₂ t x₂ (y + d) =
      r y * conditionedPositiveTransitionDensity ν₁ t x₁ y) :
    cdfGeneralizedQuantile (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν₂ t x₂)) u ≤
      cdfGeneralizedQuantile (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν₁ t x₁)) u + d := by
  obtain ⟨hg, hng, hunitg, hmpos, hmle⟩ := shifted_density_props hν₂ ht hx₂ hd
  refine quantile_le_add_of_shifted_cdf_ge hν₁ hν₂ ht hx₁ hx₂ hu hu1 fun z => ?_
  exact integral_Iic_ge_of_shiftedAntitoneDensityRatio
    (integrable_conditionedPositiveTransitionDensity hν₁ ht hx₁) hg hng
    (fun _ => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν₁ ht hx₁)
    (conditionedPositiveTransitionDensity_integral_eq_one hν₁ ht hx₁)
    hunitg hmpos hmle rfl hfac hrpos hranti z


end
private lemma shifted_ratio_antitoneOn_of_factor
    {c c' t d : ℝ} (hc' : 0 < c') (hcc' : c' ≤ c) (hd : 0 ≤ d) (hshift : d / t = c - c')
    {φ s : ℝ → ℝ} (hφ_cont : ContinuousOn φ (Ioi 0)) (hφ_nn : ∀ y > 0, 0 ≤ φ y)
    (hφ_deriv : ∀ y > 0, HasDerivAt φ (φ y * s y) y) (hs_le : ∀ y > 0, s y ≤ 0) :
    AntitoneOn (fun y => Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * φ y *
      (Real.sinh (c * (y + d)) / Real.sinh (c' * y))) (Ioi 0) := by
  have hc := lt_of_lt_of_le hc' hcc'
  have hcont : ContinuousOn (fun y => Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * φ y *
      (Real.sinh (c * (y + d)) / Real.sinh (c' * y))) (Ioi 0) :=
    ((Continuous.continuousOn (by fun_prop)).mul hφ_cont).mul
      ((Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop))
        fun y hy => (Real.sinh_pos_iff.mpr (mul_pos hc' hy)).ne')
  have hd_at {y : ℝ} (hy : 0 < y) : HasDerivAt
      (fun z => Real.exp (-(d / t) * z - d ^ 2 / (2 * t)) * φ z *
        (Real.sinh (c * (z + d)) / Real.sinh (c' * z)))
      ((Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * φ y *
        (Real.sinh (c * (y + d)) / Real.sinh (c' * y))) *
        (-(d / t) + s y + (conditionedKernelScore c (y + d) - conditionedKernelScore c' y))) y := by
    have hlin : HasDerivAt (fun z : ℝ => -(d / t) * z - d ^ 2 / (2 * t)) (-(d / t)) y := by
      simpa using ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t))
    exact ((((Real.hasDerivAt_exp _).comp y hlin).mul (hφ_deriv y hy)).mul
      (hasDerivAt_sinhShift_ratio hc' hc hy hd)).congr_deriv (by dsimp; ring)
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont
    (fun y hy => (hd_at (by simpa using hy)).differentiableAt.differentiableWithinAt) fun y hy => ?_
  have hy' : 0 < y := by simpa using hy
  rw [(hd_at hy').deriv]
  have hm := conditionedKernelScore_mixed_increment_upper hc' hy' (z := y + d) (by linarith) hcc'
  have hnn : 0 ≤ Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * φ y *
      (Real.sinh (c * (y + d)) / Real.sinh (c' * y)) :=
    mul_nonneg (mul_nonneg (Real.exp_nonneg _) (hφ_nn y hy'))
      (div_nonneg (Real.sinh_nonneg_iff.mpr (by nlinarith)) (Real.sinh_nonneg_iff.mpr (by nlinarith)))
  exact mul_nonpos_of_nonneg_of_nonpos hnn (by linarith [hs_le y hy'])

/-- The common-uniform upper start bound for positive-drift conditioned transitions:
increasing the initial state by `d` raises the endpoint quantile by at most `d`. -/
theorem conditionedPositiveTransitionQuantile_start_add
    {ν t x x' u : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x')) u + (x - x') := by
  have hx := lt_of_lt_of_le hx' hxx'
  let d := x - x'
  have hd : 0 ≤ d := sub_nonneg.mpr hxx'
  let C := Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) * (Real.sinh (ν * x') / Real.sinh (ν * x))
  have hC : 0 < C := mul_pos (Real.exp_pos _)
    (div_pos (Real.sinh_pos_iff.mpr (mul_pos hν hx')) (Real.sinh_pos_iff.mpr (mul_pos hν hx)))
  have hanti := shifted_ratio_antitoneOn_of_factor (t := t) (div_pos hx' ht)
    (div_le_div_of_nonneg_right hxx' ht.le) hd (by dsimp [d]; field_simp [ht.ne'])
    (φ := fun y => Real.sinh (ν * (y + d)) / Real.sinh (ν * y))
    (s := fun y => conditionedKernelScore ν (y + d) - conditionedKernelScore ν y)
    ((Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop))
      fun y hy => (Real.sinh_pos_iff.mpr (mul_pos hν hy)).ne')
    (fun y hy => div_nonneg (Real.sinh_nonneg_iff.mpr (by nlinarith)) (Real.sinh_nonneg_iff.mpr (by nlinarith)))
    (fun y hy => hasDerivAt_sinhShift_ratio hν hν hy hd)
    (fun y hy => sub_nonpos.mpr ((conditionedKernelScore_strictAntiOn_state hν).antitoneOn
      hy (by show 0 < y + d; linarith) (by linarith)))
  refine quantile_le_add_of_shifted_antitone_ratio hν.le hν.le ht hx' hx hd hu hu1
    (r := fun y => C * (Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
      (Real.sinh (ν * (y + d)) / Real.sinh (ν * y)) *
      (Real.sinh (x / t * (y + d)) / Real.sinh (x' / t * y)))) ?_
    (fun y₁ hy₁ y₂ hy₂ h12 => mul_le_mul_of_nonneg_left (hanti hy₁ hy₂ h12) hC.le) ?_
  · intro y hy
    have : 0 < y + d := by linarith
    have : 0 < Real.sinh (ν * (y + d)) := Real.sinh_pos_iff.mpr (by positivity)
    have : 0 < Real.sinh (ν * y) := Real.sinh_pos_iff.mpr (by positivity)
    have : 0 < Real.sinh (x / t * (y + d)) := Real.sinh_pos_iff.mpr (by positivity)
    have : 0 < Real.sinh (x' / t * y) := Real.sinh_pos_iff.mpr (by positivity)
    positivity
  · intro y hy
    have hyD : 0 < y + d := by linarith
    rw [conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hν ht hx hyD,
      conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hν ht hx' hy]
    dsimp [C]
    have h1 := (Real.sinh_pos_iff.mpr (mul_pos hν hx)).ne'
    have h2 := (Real.sinh_pos_iff.mpr (mul_pos hν hx')).ne'
    have h3 := (Real.sinh_pos_iff.mpr (mul_pos hν hy)).ne'
    have h4 := (Real.sinh_pos_iff.mpr (mul_pos (div_pos hx' ht) hy)).ne'
    have hexp : Real.exp (-(y + d) ^ 2 / (2 * t)) =
        Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * Real.exp (-y ^ 2 / (2 * t)) := by
      rw [← Real.exp_add]; congr 1; field_simp [ht.ne']; ring
    rw [hexp]
    field_simp [h1, h2, h3, h4]
    rw [← Real.exp_add]; congr 1; field_simp [ht.ne']; ring

/-- The common-uniform upper start bound for the zero-drift BES(3) transition: increasing the
initial state by `d` raises the endpoint quantile by at most `d`. -/
theorem conditionedPositiveTransitionQuantile_start_add_zero
    {t x x' u : ℝ} (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure 0 t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure 0 t x')) u + (x - x') := by
  have hx := lt_of_lt_of_le hx' hxx'
  let d := x - x'
  have hd : 0 ≤ d := sub_nonneg.mpr hxx'
  let C := Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) * (x' / x)
  have hC : 0 < C := by positivity
  have hanti := shifted_ratio_antitoneOn_of_factor (t := t) (div_pos hx' ht)
    (div_le_div_of_nonneg_right hxx' ht.le) hd (by dsimp [d]; field_simp [ht.ne'])
    (φ := fun y => (y + d) / y) (s := fun y => 1 / (y + d) - 1 / y)
    ((continuous_id.add continuous_const).continuousOn.div continuous_id.continuousOn fun _ hy => ne_of_gt hy)
    (fun y hy => by positivity)
    (fun y hy => by
      have hyD : y + d ≠ 0 := by linarith
      exact (((hasDerivAt_id y).add_const d).div (hasDerivAt_id y) hy.ne').congr_deriv
        (by dsimp; field_simp [hy.ne', hyD]))
    (fun y hy => sub_nonpos.mpr (one_div_le_one_div_of_le hy (by linarith)))
  refine quantile_le_add_of_shifted_antitone_ratio le_rfl le_rfl ht hx' hx hd hu hu1
    (r := fun y => C * (Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
      ((y + d) / y) * (Real.sinh (x / t * (y + d)) / Real.sinh (x' / t * y)))) ?_
    (fun y₁ hy₁ y₂ hy₂ h12 => mul_le_mul_of_nonneg_left (hanti hy₁ hy₂ h12) hC.le) ?_
  · intro y hy
    have : 0 < y + d := by linarith
    have : 0 < Real.sinh (x / t * (y + d)) := Real.sinh_pos_iff.mpr (by positivity)
    have : 0 < Real.sinh (x' / t * y) := Real.sinh_pos_iff.mpr (by positivity)
    positivity
  · intro y hy
    have hyD : 0 < y + d := by linarith
    rw [conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx hyD,
      conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx' hy]
    dsimp [C]
    have h4 := (Real.sinh_pos_iff.mpr (mul_pos (div_pos hx' ht) hy)).ne'
    have hexp : Real.exp (-(y + d) ^ 2 / (2 * t)) =
        Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * Real.exp (-y ^ 2 / (2 * t)) := by
      rw [← Real.exp_add]; congr 1; field_simp [ht.ne']; ring
    rw [hexp]
    field_simp [hx.ne', hx'.ne', hy.ne', h4, (show Real.sqrt (2 * Real.pi * t) ≠ 0 by positivity)]
    rw [← Real.exp_add]; congr 1; field_simp [ht.ne']; ring

/-- The common-uniform upper drift bound for positive conditioned transitions. Increasing drift
by `b-a` raises the endpoint quantile by at most `(b-a)t`. -/
theorem conditionedPositiveTransitionQuantile_drift_add
    {a b t x u : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure b t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure a t x)) u +
          (b - a) * t := by
  have hb := lt_of_lt_of_le ha hab
  let d := (b - a) * t
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr hab) ht.le
  refine quantile_le_add_of_shifted_antitone_ratio ha.le hb.le ht hx hx hd hu hu1
    (r := fun y => conditionedPositiveTransitionDensity b t x (y + d) /
      conditionedPositiveTransitionDensity a t x y)
    (fun y hy => div_pos (conditionedPositiveTransitionDensity_pos hb.le ht hx (by linarith))
      (conditionedPositiveTransitionDensity_pos ha.le ht hx hy))
    (conditionedPositiveTransitionDensity_shifted_ratio_antitoneOn ha hab ht hx hd
      (by dsimp [d]; field_simp [ht.ne']))
    (fun y hy => (div_mul_cancel₀ _ (conditionedPositiveTransitionDensity_pos ha.le ht hx hy).ne').symm)

/-- The common-uniform upper drift bound from the zero-drift BES(3) endpoint. Increasing the
positive drift by `b` raises the endpoint quantile by at most `b * t`. -/
theorem conditionedPositiveTransitionQuantile_drift_add_zero
    {b t x u : ℝ} (hb : 0 < b) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure b t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure 0 t x)) u + b * t := by
  let d := b * t
  have hd : 0 ≤ d := mul_nonneg hb.le ht.le
  obtain ⟨hg, hng, hunitg, hmpos, hmle⟩ := shifted_density_props hb.le ht hx hd
  refine quantile_le_add_of_shifted_cdf_ge le_rfl hb.le ht hx hx hu hu1 fun z => ?_
  exact conditionedPositiveTransitionDensity_shifted_zero_cdf_ge hb ht hx hd
    (by dsimp [d]; field_simp [ht.ne'])
    (integrable_conditionedPositiveTransitionDensity le_rfl ht hx) hg hng
    (conditionedPositiveTransitionDensity_integral_eq_one le_rfl ht hx)
    hunitg hmpos hmle rfl z

end DOZZ.Proofs
