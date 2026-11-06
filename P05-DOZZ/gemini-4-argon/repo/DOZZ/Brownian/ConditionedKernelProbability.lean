/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelZeroDriftNormalization
public import DOZZ.Brownian.ConditionedKernelStartRatio
public import DOZZ.Brownian.ConditionedKernelParameterRatio
public import DOZZ.Brownian.ConditionedKernelCDFOrder
public import Mathlib.Probability.CDF

/-!
# Probability-density bounds for the conditioned transition kernels

The ordered coupling compares normalized endpoint laws. This module provides the pointwise
nonnegativity and Lebesgue integrability needed to regard the explicit Doob kernels as probability
densities; their unit-mass identities are proved in the imported normalization modules.
-/

@[expose] public section

open Filter MeasureTheory Topology

namespace DOZZ.Proofs

@[fun_prop] private theorem measurable_brownianHeatDensity_probability t :
    Measurable (brownianHeatDensity t) := by
  unfold brownianHeatDensity
  split_ifs <;> fun_prop

@[fun_prop] private theorem measurable_conditionedH_probability ν :
    Measurable (conditionedH ν) := by
  unfold conditionedH
  split_ifs <;> fun_prop


theorem brownianHeatDensity_sub_factor_probability
    {t x y} (ht : 0 < t) :
    brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) =
      Real.exp (-(x ^ 2 + y ^ 2) / (2 * t)) *
        (2 * Real.sinh (x * y / t) / Real.sqrt (2 * Real.pi * t)) := by
  simp only [brownianHeatDensity, ht, ite_true]
  rw [(show -((y - x) ^ 2) / (2 * t) = -(x ^ 2 + y ^ 2) / (2 * t) + x * y / t by field_simp [ht.ne']; ring), (show -((y + x) ^ 2) / (2 * t) = -(x ^ 2 + y ^ 2) / (2 * t) - x * y / t by field_simp [ht.ne']; ring)]
  rw [show -(x ^ 2 + y ^ 2) / (2 * t) - x * y / t =
      -(x ^ 2 + y ^ 2) / (2 * t) + -(x * y / t) by ring]
  rw [Real.exp_add, Real.exp_add, Real.sinh_eq]
  field_simp [(show Real.sqrt (2 * Real.pi * t) ≠ 0 by positivity)]

private theorem conditionedH_pos_of_pos_drift
    {ν x} (hν : 0 < ν) (hx : 0 < x) : 0 < conditionedH ν x := by
  rw [conditionedH, ite_eq_right hν.ne']
  apply sub_pos.mpr
  apply (Real.exp_lt_one_iff).2
  nlinarith

private theorem conditionedH_bounds_of_pos_drift
    {ν x} (hν : 0 < ν) (hx : 0 < x) :
    0 ≤ conditionedH ν x ∧ conditionedH ν x ≤ 1 := by
  rw [conditionedH, ite_eq_right hν.ne']
  constructor <;> linarith [(show Real.exp (-2 * ν * x) < 1 by apply (Real.exp_lt_one_iff).2; nlinarith), (Real.exp_pos _ : 0 < Real.exp (-2 * ν * x))]

/-- The explicit conditioned transition density is strictly positive at every positive endpoint. -/
theorem conditionedPositiveTransitionDensity_pos
    {ν t x y} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    0 < conditionedPositiveTransitionDensity ν t x y := by
  have hHx : 0 < conditionedH ν x := by
    by_cases hνzero : ν = 0
    · simpa [conditionedH, hνzero] using hx
    · exact conditionedH_pos_of_pos_drift (lt_of_le_of_ne hν (Ne.symm hνzero)) hx
  have hHy : 0 < conditionedH ν y := by
    by_cases hνzero : ν = 0
    · simpa [conditionedH, hνzero] using hy
    · exact conditionedH_pos_of_pos_drift (lt_of_le_of_ne hν (Ne.symm hνzero)) hy
  simp only [conditionedPositiveTransitionDensity, hν, ht, hx, hy,
    and_self, ite_true]
  exact div_pos (mul_pos (mul_pos (Real.exp_pos _) (by rw [brownianHeatDensity_sub_factor_probability ht]; positivity)) hHy) hHx



/-- The explicit conditioned transition density is nonnegative on all of `ℝ` for every
nonnegative drift, positive elapsed time, and positive starting state. -/
theorem conditionedPositiveTransitionDensity_nonneg
    {ν t x} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) y :
    0 ≤ conditionedPositiveTransitionDensity ν t x y := by
  by_cases hy : 0 < y
  · have hdiff : 0 ≤ brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) := by
      rw [brownianHeatDensity_sub_factor_probability ht]
      positivity
    by_cases hνzero : ν = 0
    · have hH : conditionedH ν x = x := by simp [conditionedH, hνzero]
      rw [conditionedPositiveTransitionDensity, ite_eq_left ⟨hν, ht, hx, hy⟩, hH, (show conditionedH ν y = y by simp [conditionedH, hνzero])]
      positivity
    · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
      simp only [conditionedPositiveTransitionDensity, hν, ht, hx, hy,
        and_self, ite_true]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (Real.exp_nonneg _) hdiff) (conditionedH_bounds_of_pos_drift hνpos hy).1)
        (le_of_lt (conditionedH_pos_of_pos_drift hνpos hx))
  · have hy' : ¬ 0 < y := not_lt.mpr (le_of_not_gt hy)
    simp [conditionedPositiveTransitionDensity, hν, ht, hx, hy']


/-- Every nonnegative-drift conditioned transition density is Lebesgue integrable on `ℝ` when
extended by zero outside the positive half-line. -/
theorem integrable_conditionedPositiveTransitionDensity
    {ν t x} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    Integrable (conditionedPositiveTransitionDensity ν t x) (volume : Measure ℝ) := by
  have conditionedPositiveTransitionDensity_zero_formula y : conditionedPositiveTransitionDensity 0 t x y = if 0 < y then (y / x) * (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) else 0 := by
    by_cases hy : 0 < y
    · simp [conditionedPositiveTransitionDensity, conditionedH, ht, hx, hy]
      ring_nf
    · simp [conditionedPositiveTransitionDensity, ht, hx, hy]
  have integrable_heatDensity_translate_probability {t} {a} (ht : 0 < t) : Integrable (fun y => brownianHeatDensity t (y + a)) (volume : Measure ℝ) := ((Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding).integrable_map_iff.mp (show Integrable (brownianHeatDensity t) ((volume : Measure ℝ).map (fun y => y + a)) by rw [(Measure.IsAddRightInvariant.map_add_right_eq_self a)]; exact integrable_brownianHeatDensity ht)
  have brownianHeatDensity_nonneg z : 0 ≤ brownianHeatDensity t z := by
    simp only [brownianHeatDensity, ite_eq_left ht]
    positivity
  have integrable_mul_heatDensity_translate_probability {t} {a} (ht : 0 < t) : Integrable (fun y => (y + a) * brownianHeatDensity t (y + a)) (volume : Measure ℝ) := ((Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding).integrable_map_iff.mp (show Integrable (fun z => z * brownianHeatDensity t z) ((volume : Measure ℝ).map (fun y => y + a)) by rw [(Measure.IsAddRightInvariant.map_add_right_eq_self a)]; exact integrable_mul_brownianHeatDensity ht)
  have hmeasKernel : Measurable (fun y => conditionedPositiveTransitionDensity ν t x y) := by
    unfold conditionedPositiveTransitionDensity
    rw [(show (fun y => if 0 ≤ ν ∧ 0 < t ∧ 0 < x ∧ 0 < y then Real.exp (ν * (y - x) - ν ^ 2 * t / 2) * (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) * conditionedH ν y / conditionedH ν x else 0) = fun y => if 0 < y then Real.exp (ν * (y - x) - ν ^ 2 * t / 2) * (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) * conditionedH ν y / conditionedH ν x else 0 by funext y; simp [hν, ht, hx])]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (by fun_prop) measurable_const
  by_cases hνzero : ν = 0
  · subst ν
    let C : ℝ := x⁻¹
    let g : ℝ → ℝ := fun y => C *
      (‖(y - x) * brownianHeatDensity t (y - x)‖ +
        x * brownianHeatDensity t (y - x))
    have hbound : ∀ y : ℝ,
        ‖conditionedPositiveTransitionDensity 0 t x y‖ ≤ g y := by
      intro y
      by_cases hy : 0 < y
      · rw [conditionedPositiveTransitionDensity_zero_formula y, ite_eq_left hy]
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (le_of_lt hy) (le_of_lt hx)) (show 0 ≤ brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) by rw [brownianHeatDensity_sub_factor_probability ht]; positivity))]
        have hsum : y * brownianHeatDensity t (y - x) ≤
            ‖(y - x) * brownianHeatDensity t (y - x)‖ +
              x * brownianHeatDensity t (y - x) := by
          have hfirst : (y - x) * brownianHeatDensity t (y - x) ≤
              ‖(y - x) * brownianHeatDensity t (y - x)‖ := le_abs_self _
          calc
            y * brownianHeatDensity t (y - x) =
                (y - x) * brownianHeatDensity t (y - x) +
                  x * brownianHeatDensity t (y - x) := by ring
            _ ≤ _ := by nlinarith [hfirst]
        calc
          (y / x) * (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) ≤
              (y / x) * brownianHeatDensity t (y - x) :=
            mul_le_mul_of_nonneg_left (by linarith [brownianHeatDensity_nonneg (y + x)]) (div_nonneg (le_of_lt hy) (le_of_lt hx))
          _ = C * (y * brownianHeatDensity t (y - x)) := by dsimp [C]; ring
          _ ≤ g y := by
            dsimp [g, C]
            exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hx.le)
      · have hy' : ¬ 0 < y := not_lt.mpr (le_of_not_gt hy)
        rw [conditionedPositiveTransitionDensity_zero_formula y, ite_eq_right hy']
        simp only [Real.norm_eq_abs, abs_zero]
        dsimp [g, C]
        have := brownianHeatDensity_nonneg (y - x)
        positivity
    exact Integrable.mono' (by dsimp [g, C]; exact ((show Integrable (fun y => (y - x) * brownianHeatDensity t (y - x)) (volume : Measure ℝ) by simpa only [sub_eq_add_neg] using integrable_mul_heatDensity_translate_probability (t := t) (a := -x) ht).norm.add ((show Integrable (fun y => brownianHeatDensity t (y - x)) (volume : Measure ℝ) by simpa only [sub_eq_add_neg] using integrable_heatDensity_translate_probability (t := t) (a := -x) ht).const_mul x)).const_mul x⁻¹) hmeasKernel.aestronglyMeasurable (ae_of_all _ hbound)
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
    let Hx := conditionedH ν x
    let C := Hx⁻¹
    let g : ℝ → ℝ := fun y => C * brownianHeatDensity t (y - (x + ν * t))
    have hHx := conditionedH_pos_of_pos_drift hνpos hx
    have hbound : ∀ y : ℝ,
        ‖conditionedPositiveTransitionDensity ν t x y‖ ≤ g y := by
      intro y
      by_cases hy : 0 < y
      · have hdiff : 0 ≤ brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) := by
          rw [brownianHeatDensity_sub_factor_probability ht]
          positivity
        have hHy := conditionedH_bounds_of_pos_drift hνpos hy
        have hU : 0 < Real.exp (ν * (y - x) - ν ^ 2 * t / 2) := Real.exp_pos _
        have hnum :
            Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
                (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) *
                conditionedH ν y ≤
              Real.exp (ν * (y - x) - ν ^ 2 * t / 2) * brownianHeatDensity t (y - x) := by
          calc
            _ ≤ (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
                  brownianHeatDensity t (y - x)) * conditionedH ν y := by
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left (by linarith [brownianHeatDensity_nonneg (y + x)]) hU.le) hHy.1
            _ = (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
                  brownianHeatDensity t (y - x)) * conditionedH ν y := by ring
            _ ≤ (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
                  brownianHeatDensity t (y - x)) * 1 :=
              mul_le_mul_of_nonneg_left hHy.2 (mul_nonneg hU.le (brownianHeatDensity_nonneg (y - x)))
            _ = _ := by ring
        rw [Real.norm_eq_abs, abs_of_nonneg
          (conditionedPositiveTransitionDensity_nonneg hν ht hx y), (show conditionedPositiveTransitionDensity ν t x y = (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) * (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) * conditionedH ν y) / Hx by simp [conditionedPositiveTransitionDensity, hν, ht, hx, hy, Hx])]
        calc
          (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
              (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) *
              conditionedH ν y) / Hx ≤
            (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
              brownianHeatDensity t (y - x)) / Hx :=
                div_le_div_of_nonneg_right hnum hHx.le
          _ = g y := by
            rw [(show Real.exp (ν * (y - x) - ν ^ 2 * t / 2) * brownianHeatDensity t (y - x) = brownianHeatDensity t (y - (x + ν * t)) by simpa only [show y - x - ν * t = y - (x + ν * t) by ring] using (brownianHeatDensity_tilt (t := t) (ν := ν) (z := y - x) ht))]
            dsimp [g, C, Hx]
            ring
      · have hy' : ¬ 0 < y := not_lt.mpr (le_of_not_gt hy)
        rw [(show conditionedPositiveTransitionDensity ν t x y = 0 by simp [conditionedPositiveTransitionDensity, hν, ht, hx, hy'])]
        simp only [Real.norm_eq_abs, abs_zero]
        dsimp [g, C]
        exact mul_nonneg (inv_nonneg.mpr hHx.le) (brownianHeatDensity_nonneg _)
    exact Integrable.mono' (show Integrable g (volume : Measure ℝ) by dsimp [g]; exact (show Integrable (fun y => brownianHeatDensity t (y - (x + ν * t))) (volume : Measure ℝ) by simpa only [sub_eq_add_neg] using integrable_heatDensity_translate_probability (t := t) (a := -(x + ν * t)) ht).const_mul C) hmeasKernel.aestronglyMeasurable (ae_of_all _ hbound)

theorem conditionedPositiveTransitionDensity_eq_zero_of_nonpos
    {ν t x y} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) (hy : y ≤ 0) :
    conditionedPositiveTransitionDensity ν t x y = 0 := by
  simp [conditionedPositiveTransitionDensity, hν, ht, hx, not_lt.mpr hy]

/-- The full-line Lebesgue integral of the zero-extended conditioned transition density is one.
The imported kernel calculations evaluate its positive-half-line mass separately for positive
drift and for the BES(3) zero-drift endpoint. -/
theorem conditionedPositiveTransitionDensity_integral_eq_one
    {ν t x} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    ∫ y : ℝ, conditionedPositiveTransitionDensity ν t x y = 1 := by
  have hIoi : ∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity ν t x y = 1 := by
    by_cases hνzero : ν = 0
    · subst ν
      exact conditionedPositiveTransitionDensity_integral_eq_one_zero ht hx
    · exact conditionedPositiveTransitionDensity_integral_eq_one_pos
        (lt_of_le_of_ne hν (Ne.symm hνzero)) ht hx
  have hIic : ∫ y in Set.Iic 0, conditionedPositiveTransitionDensity ν t x y = 0 := by
    calc
      ∫ y in Set.Iic 0, conditionedPositiveTransitionDensity ν t x y =
          ∫ y in Set.Iic 0, (fun _ : ℝ => (0 : ℝ)) y := by
            apply setIntegral_congr_fun measurableSet_Iic
            intro y hy
            exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx hy
      _ = 0 := by simp
  calc
    ∫ y : ℝ, conditionedPositiveTransitionDensity ν t x y =
        (∫ y in Set.Iic 0, conditionedPositiveTransitionDensity ν t x y) +
          ∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity ν t x y := by
            simpa [Set.compl_Iic] using (integral_add_compl (μ := (volume : Measure ℝ)) (f := conditionedPositiveTransitionDensity ν t x) (s := Set.Iic 0) measurableSet_Iic (integrable_conditionedPositiveTransitionDensity hν ht hx)).symm
    _ = 1 := by rw [hIic, hIoi]; norm_num

/-- The probability measure whose density is the explicit positive conditioned transition
kernel, extended by zero to the whole real line. -/
noncomputable def conditionedPositiveTransitionMeasure (ν t x : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal (conditionedPositiveTransitionDensity ν t x y))

theorem isProbabilityMeasure_conditionedPositiveTransitionMeasure
    ν t x (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    IsProbabilityMeasure (conditionedPositiveTransitionMeasure ν t x) := by
  rw [isProbabilityMeasure_iff]
  rw [conditionedPositiveTransitionMeasure,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, ← (ofReal_integral_eq_lintegral_ofReal (integrable_conditionedPositiveTransitionDensity hν ht hx) (ae_of_all _ (conditionedPositiveTransitionDensity_nonneg hν ht hx))),
    conditionedPositiveTransitionDensity_integral_eq_one hν ht hx]
  norm_num

/-- Increasing endpoint likelihood ratio for a larger start yields lower-tail CDF order: the
transition law from the larger positive state puts less mass below every fixed threshold. -/
theorem conditionedPositiveTransitionDensity_start_cdf_le
    {ν t x x'} (hν : 0 ≤ ν) (ht : 0 < t)
    (hx' : 0 < x') (hxx' : x' ≤ x) z :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x' y := by
  have hx := lt_of_lt_of_le hx' hxx'
  let r : ℝ → ℝ := fun y =>
    conditionedPositiveTransitionDensity ν t x y /
      conditionedPositiveTransitionDensity ν t x' y
  exact integral_Iic_le_of_monotoneDensityRatio (integrable_conditionedPositiveTransitionDensity hν ht hx') (integrable_conditionedPositiveTransitionDensity hν ht hx) (conditionedPositiveTransitionDensity_nonneg hν ht hx')
    (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx' hy) (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx hy) (conditionedPositiveTransitionDensity_integral_eq_one hν ht hx') (conditionedPositiveTransitionDensity_integral_eq_one hν ht hx) (by intro y hy; dsimp [r]; field_simp [(conditionedPositiveTransitionDensity_pos hν ht hx' hy).ne']) (show MonotoneOn r (Set.Ioi 0) by simpa only [r] using conditionedPositiveTransitionDensity_start_ratio_monotoneOn_state hν ht hx' hxx') z


/-- The CDF of the kernel probability measure is the integral of its explicit density. -/
theorem conditionedPositiveTransitionMeasure_cdf_eq_integral
    {ν t x z} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x) z =
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x y := by
  have hμ : IsProbabilityMeasure (conditionedPositiveTransitionMeasure ν t x) :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  rw [@ProbabilityTheory.cdf_eq_real
    (conditionedPositiveTransitionMeasure ν t x) hμ z]
  rw [measureReal_def, conditionedPositiveTransitionMeasure,
    withDensity_apply _ measurableSet_Iic]
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (conditionedPositiveTransitionDensity_nonneg hν ht hx)) ((integrable_conditionedPositiveTransitionDensity hν ht hx).integrableOn.aestronglyMeasurable)]

private theorem probability_cdf_superlevel_nonempty
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {u} (hu : u < 1) :
    {x | u ≤ ProbabilityTheory.cdf μ x}.Nonempty := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 ((ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu))
  refine ⟨max a 0, ?_⟩
  change u ≤ ProbabilityTheory.cdf μ (max a 0)
  apply le_of_lt
  exact ha (max a 0) (le_max_left _ _)

private theorem probability_cdf_superlevel_bddBelow_of_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {u} (hu : 0 < u)
    (hzero : ∀ x ≤ 0, ProbabilityTheory.cdf μ x = 0) :
    BddBelow {x | u ≤ ProbabilityTheory.cdf μ x} := by
  refine ⟨0, ?_⟩
  intro x hx
  change u ≤ ProbabilityTheory.cdf μ x at hx
  by_contra hxlt
  rw [hzero x (le_of_lt (lt_of_not_ge hxlt))] at hx
  linarith

private theorem conditionedPositiveTransitionMeasure_cdf_eq_zero_of_nonpos
    {ν t x z} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) (hz : z ≤ 0) :
    ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x) z = 0 := by
  rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx]
  rw [setIntegral_congr_fun measurableSet_Iic
    (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx
      (hy.trans hz))]
  simp

/-- Every common-level quantile of a positive-start conditioned transition kernel is strictly
positive. -/
theorem conditionedPositiveTransitionQuantile_pos
    {ν t x u} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    0 < cdfGeneralizedQuantile
      (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u := by
  have hμ : IsProbabilityMeasure (conditionedPositiveTransitionMeasure ν t x) :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  exact @cdfGeneralizedQuantile_pos_of_cdf_zero_nonpos
    (conditionedPositiveTransitionMeasure ν t x) hμ u hu hu1
    (fun z hz => conditionedPositiveTransitionMeasure_cdf_eq_zero_of_nonpos
      hν ht hx hz)

/-- The one-step probability kernels are stochastically increasing in the starting state, in
quantile form. The same uniform variable can therefore order the next endpoint at every fixed
time step. -/
theorem conditionedPositiveTransitionQuantile_start_le
    {ν t x x' u} (hν : 0 ≤ ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x')) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u := by
  have hx := lt_of_lt_of_le hx' hxx'
  let μsmall := conditionedPositiveTransitionMeasure ν t x'
  let μlarge := conditionedPositiveTransitionMeasure ν t x
  have hμsmall : IsProbabilityMeasure μsmall :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x' hν ht hx'
  have hμlarge : IsProbabilityMeasure μlarge :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  exact cdfGeneralizedQuantile_antitone (by intro z; rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx, conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx']; exact conditionedPositiveTransitionDensity_start_cdf_le hν ht hx' hxx' z) (@probability_cdf_superlevel_nonempty μlarge hμlarge u hu1) (@probability_cdf_superlevel_bddBelow_of_zero μsmall hμsmall u hu (fun z hz => conditionedPositiveTransitionMeasure_cdf_eq_zero_of_nonpos hν ht hx' hz))

/-- Increasing the drift parameter moves every common-uniform quantile of the conditioned
transition law to the right. -/
theorem conditionedPositiveTransitionQuantile_drift_le
    {ν ν' t x u} (hν : 0 ≤ ν) (hνν' : ν ≤ ν') (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν' t x)) u := by
  have conditionedPositiveTransitionDensity_drift_cdf_le z : (∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν' t x y) ≤ ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x y := by
    have hν' := hν.trans hνν'
    let r : ℝ → ℝ := fun y =>
      conditionedPositiveTransitionDensity ν' t x y /
        conditionedPositiveTransitionDensity ν t x y
    have hratio : MonotoneOn r (Set.Ioi 0) := by
      by_cases hνzero : ν = 0
      · subst ν
        by_cases hν'zero : ν' = 0
        · subst ν'
          intro y hy z hz _
          dsimp [r]
          field_simp [(conditionedPositiveTransitionDensity_pos (ν := 0) (t := t) (x := x) (y := y) (by norm_num) ht hx (by simpa using hy)).ne', (conditionedPositiveTransitionDensity_pos (ν := 0) (t := t) (x := x) (y := z) (by norm_num) ht hx (by simpa using hz)).ne']
          norm_num
        · have hν'pos : 0 < ν' := lt_of_le_of_ne hνν' (Ne.symm hν'zero)
          simpa only [r] using
            conditionedPositiveTransitionDensity_zero_ratio_monotoneOn_state
              hν'pos ht hx
      · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
        simpa only [r] using conditionedPositiveTransitionDensity_ratio_monotoneOn_state
          hνpos hνν' ht hx
    exact integral_Iic_le_of_monotoneDensityRatio (integrable_conditionedPositiveTransitionDensity hν ht hx) (integrable_conditionedPositiveTransitionDensity hν' ht hx) (conditionedPositiveTransitionDensity_nonneg hν ht hx)
      (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx hy) (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν' ht hx hy) (conditionedPositiveTransitionDensity_integral_eq_one hν ht hx) (conditionedPositiveTransitionDensity_integral_eq_one hν' ht hx) (by intro y hy; dsimp [r]; field_simp [(conditionedPositiveTransitionDensity_pos hν ht hx hy).ne']) hratio z
  have hν' := hν.trans hνν'
  let μlow := conditionedPositiveTransitionMeasure ν t x
  let μhigh := conditionedPositiveTransitionMeasure ν' t x
  have hμlow : IsProbabilityMeasure μlow :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  have hμhigh : IsProbabilityMeasure μhigh :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν' t x hν' ht hx
  exact cdfGeneralizedQuantile_antitone (by intro z; rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν' ht hx, conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx]; exact conditionedPositiveTransitionDensity_drift_cdf_le z) (@probability_cdf_superlevel_nonempty μhigh hμhigh u hu1) (@probability_cdf_superlevel_bddBelow_of_zero μlow hμlow u hu (fun z hz => conditionedPositiveTransitionMeasure_cdf_eq_zero_of_nonpos hν ht hx hz))

end DOZZ.Proofs

end
