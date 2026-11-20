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

/-- The explicit conditioned transition density is nonnegative on all of `ℝ` for every
nonnegative drift, positive elapsed time, and positive starting state. -/
theorem conditionedPositiveTransitionDensity_nonneg
    {ν t x : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) (y : ℝ) :
    0 ≤ conditionedPositiveTransitionDensity ν t x y := by
  by_cases hy : 0 < y
  · exact (conditionedPositiveTransitionDensity_pos hν ht hx hy).le
  · simp [conditionedPositiveTransitionDensity, hy]

theorem conditionedPositiveTransitionDensity_eq_zero_of_nonpos
    {ν t x y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) (hy : y ≤ 0) :
    conditionedPositiveTransitionDensity ν t x y = 0 := by
  simp [conditionedPositiveTransitionDensity, hν, ht, hx, not_lt.mpr hy]

section
variable {ν t x : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x)
include hν ht hx

/-- The full-line Lebesgue integral of the zero-extended conditioned transition density is one.
The imported kernel calculations evaluate its positive-half-line mass separately for positive
drift and for the BES(3) zero-drift endpoint. -/
theorem conditionedPositiveTransitionDensity_integral_eq_one :
    ∫ y : ℝ, conditionedPositiveTransitionDensity ν t x y = 1 := by
  have he : (Set.Ioi (0 : ℝ)).indicator (conditionedPositiveTransitionDensity ν t x) =
      conditionedPositiveTransitionDensity ν t x := by
    ext y
    by_cases hy : y ∈ Set.Ioi (0 : ℝ)
    · exact Set.indicator_of_mem hy _
    · rw [Set.indicator_of_notMem hy, conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx
        (le_of_not_gt hy)]
  rw [← he, integral_indicator measurableSet_Ioi]
  rcases hν.eq_or_lt with rfl | hν
  · exact conditionedPositiveTransitionDensity_integral_eq_one_zero ht hx
  · exact conditionedPositiveTransitionDensity_integral_eq_one_pos hν ht hx

/-- The normalized zero-extended density is integrable on the full line. -/
theorem integrable_conditionedPositiveTransitionDensity :
    Integrable (conditionedPositiveTransitionDensity ν t x) :=
  integrable_of_integral_eq_one (conditionedPositiveTransitionDensity_integral_eq_one hν ht hx)

end

/-- The probability measure whose density is the explicit positive conditioned transition
kernel, extended by zero to the whole real line. -/
noncomputable def conditionedPositiveTransitionMeasure (ν t x : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal (conditionedPositiveTransitionDensity ν t x y))

theorem isProbabilityMeasure_conditionedPositiveTransitionMeasure
    (ν t x : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    IsProbabilityMeasure (conditionedPositiveTransitionMeasure ν t x) := by
  rw [isProbabilityMeasure_iff]
  have hkernel := integrable_conditionedPositiveTransitionDensity hν ht hx
  have hnonneg : 0 ≤ᵐ[volume] conditionedPositiveTransitionDensity ν t x :=
    ae_of_all _ (conditionedPositiveTransitionDensity_nonneg hν ht hx)
  have hlin := ofReal_integral_eq_lintegral_ofReal hkernel hnonneg
  rw [conditionedPositiveTransitionMeasure,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, ← hlin,
    conditionedPositiveTransitionDensity_integral_eq_one hν ht hx]
  norm_num

/-- Increasing endpoint likelihood ratio for a larger start yields lower-tail CDF order: the
transition law from the larger positive state puts less mass below every fixed threshold. -/
theorem conditionedPositiveTransitionDensity_start_cdf_le
    {ν t x x' : ℝ} (hν : 0 ≤ ν) (ht : 0 < t)
    (hx' : 0 < x') (hxx' : x' ≤ x) (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x' y := by
  have hx  := lt_of_lt_of_le hx' hxx'
  have hf := integrable_conditionedPositiveTransitionDensity hν ht hx'
  have hg := integrable_conditionedPositiveTransitionDensity hν ht hx
  have hfnonneg  :=
    conditionedPositiveTransitionDensity_nonneg hν ht hx'
  have hzeroF : ∀ y, y ≤ 0 → conditionedPositiveTransitionDensity ν t x' y = 0 :=
    fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx' hy
  have hzeroG : ∀ y, y ≤ 0 → conditionedPositiveTransitionDensity ν t x y = 0 :=
    fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx hy
  have hunitF := conditionedPositiveTransitionDensity_integral_eq_one hν ht hx'
  have hunitG := conditionedPositiveTransitionDensity_integral_eq_one hν ht hx
  let r  := fun y =>
    conditionedPositiveTransitionDensity ν t x y /
      conditionedPositiveTransitionDensity ν t x' y
  have hfactor : ∀ y, 0 < y →
      conditionedPositiveTransitionDensity ν t x y = r y *
        conditionedPositiveTransitionDensity ν t x' y := by
    intro y hy
    have hden := conditionedPositiveTransitionDensity_pos hν ht hx' hy
    dsimp [r]
    field_simp [hden.ne']
  have hratio : MonotoneOn r (Set.Ioi 0) := by
    simpa only [r] using
      conditionedPositiveTransitionDensity_start_ratio_monotoneOn_state
        hν ht hx' hxx'
  apply integral_Iic_le_of_monotoneDensityRatio <;> assumption

/-- Increasing drift likelihood ratio yields lower-tail CDF order for the positive conditioned
transition kernels at a fixed start. -/
theorem conditionedPositiveTransitionDensity_drift_cdf_le
    {ν ν' t x : ℝ} (hν : 0 ≤ ν) (hνν' : ν ≤ ν')
    (ht : 0 < t) (hx : 0 < x) (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν' t x y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x y := by
  have hν'  := hν.trans hνν'
  have hf := integrable_conditionedPositiveTransitionDensity hν ht hx
  have hg := integrable_conditionedPositiveTransitionDensity hν' ht hx
  have hfnonneg  :=
    conditionedPositiveTransitionDensity_nonneg hν ht hx
  have hzeroF : ∀ y, y ≤ 0 → conditionedPositiveTransitionDensity ν t x y = 0 :=
    fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx hy
  have hzeroG : ∀ y, y ≤ 0 → conditionedPositiveTransitionDensity ν' t x y = 0 :=
    fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν' ht hx hy
  have hunitF := conditionedPositiveTransitionDensity_integral_eq_one hν ht hx
  have hunitG := conditionedPositiveTransitionDensity_integral_eq_one hν' ht hx
  let r  := fun y =>
    conditionedPositiveTransitionDensity ν' t x y /
      conditionedPositiveTransitionDensity ν t x y
  have hfactor : ∀ y, 0 < y →
      conditionedPositiveTransitionDensity ν' t x y = r y *
        conditionedPositiveTransitionDensity ν t x y := by
    intro y hy
    have hden := conditionedPositiveTransitionDensity_pos hν ht hx hy
    dsimp [r]
    field_simp [hden.ne']
  have hratio : MonotoneOn r (Set.Ioi 0) := by
    by_cases hνzero : ν = 0
    · subst ν
      by_cases hν'zero : ν' = 0
      · subst ν'
        intro y hy z hz _
        have hpy := conditionedPositiveTransitionDensity_pos (ν := 0) (t := t)
          (x := x) (y := y) (by norm_num) ht hx (by simpa using hy)
        have hpz := conditionedPositiveTransitionDensity_pos (ν := 0) (t := t)
          (x := x) (y := z) (by norm_num) ht hx (by simpa using hz)
        dsimp [r]
        field_simp [hpy.ne', hpz.ne']
        norm_num
      · have hν'pos  := lt_of_le_of_ne hνν' (Ne.symm hν'zero)
        simpa only [r] using
          conditionedPositiveTransitionDensity_zero_ratio_monotoneOn_state
            hν'pos ht hx
    · have hνpos  := lt_of_le_of_ne hν (Ne.symm hνzero)
      simpa only [r] using conditionedPositiveTransitionDensity_ratio_monotoneOn_state
        hνpos hνν' ht hx
  apply integral_Iic_le_of_monotoneDensityRatio <;> assumption

section
variable {ν t x z : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x)
include hν ht hx

/-- The CDF of the kernel probability measure is the integral of its explicit density. -/
theorem conditionedPositiveTransitionMeasure_cdf_eq_integral :
    ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x) z =
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x y := by
  have hμ  :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  rw [@ProbabilityTheory.cdf_eq_real
      (conditionedPositiveTransitionMeasure ν t x) hμ z, measureReal_def, conditionedPositiveTransitionMeasure, withDensity_apply _ measurableSet_Iic]
  have hkernel := integrable_conditionedPositiveTransitionDensity hν ht hx
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Iic z)]
      conditionedPositiveTransitionDensity ν t x :=
    ae_of_all _ (conditionedPositiveTransitionDensity_nonneg hν ht hx)
  have hmeas : AEStronglyMeasurable (conditionedPositiveTransitionDensity ν t x)
      ((volume : Measure ℝ).restrict (Set.Iic z)) := hkernel.integrableOn.aestronglyMeasurable
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]

private theorem conditionedPositiveTransitionMeasure_cdf_eq_zero_of_nonpos (hz : z ≤ 0) :
    ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x) z = 0 := by
  rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx, setIntegral_congr_fun measurableSet_Iic
      (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx
        (hy.trans hz))]
  simp

end

/-- Every common-level quantile of a positive-start conditioned transition kernel is strictly
positive. -/
theorem conditionedPositiveTransitionQuantile_pos
    {ν t x u : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    0 < cdfGeneralizedQuantile
      (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u := by
  have hμ  :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  exact @cdfGeneralizedQuantile_pos_of_cdf_zero_nonpos
    (conditionedPositiveTransitionMeasure ν t x) hμ u hu hu1
    (fun z hz => conditionedPositiveTransitionMeasure_cdf_eq_zero_of_nonpos
      hν ht hx hz)

/-- The one-step probability kernels are stochastically increasing in the starting state, in
quantile form. The same uniform variable can therefore order the next endpoint at every fixed
time step. -/
theorem conditionedPositiveTransitionQuantile_start_le
    {ν t x x' u : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x')) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u := by
  have hx  := lt_of_lt_of_le hx' hxx'
  let μsmall := conditionedPositiveTransitionMeasure ν t x'
  let μlarge := conditionedPositiveTransitionMeasure ν t x
  have hμsmall  :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x' hν ht hx'
  have hμlarge  :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  have horder : ∀ z, ProbabilityTheory.cdf μlarge z ≤ ProbabilityTheory.cdf μsmall z := by
    intro z
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx,
      conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx']
    apply conditionedPositiveTransitionDensity_start_cdf_le <;> assumption
  have hF := @probability_cdf_superlevel_nonempty μlarge hμlarge u hu1
  have hG  :=
    @probability_cdf_superlevel_bddBelow μsmall hμsmall u hu
  exact cdfGeneralizedQuantile_antitone horder hF hG

/-- Increasing the drift parameter moves every common-uniform quantile of the conditioned
transition law to the right. -/
theorem conditionedPositiveTransitionQuantile_drift_le
    {ν ν' t x u : ℝ} (hν : 0 ≤ ν) (hνν' : ν ≤ ν') (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν' t x)) u := by
  have hν'  := hν.trans hνν'
  let μlow := conditionedPositiveTransitionMeasure ν t x
  let μhigh := conditionedPositiveTransitionMeasure ν' t x
  have hμlow  :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  have hμhigh  :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν' t x hν' ht hx
  have horder : ∀ z, ProbabilityTheory.cdf μhigh z ≤ ProbabilityTheory.cdf μlow z := by
    intro z
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν' ht hx,
      conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx]
    apply conditionedPositiveTransitionDensity_drift_cdf_le <;> assumption
  have hF := @probability_cdf_superlevel_nonempty μhigh hμhigh u hu1
  have hG  :=
    @probability_cdf_superlevel_bddBelow μlow hμlow u hu
  exact cdfGeneralizedQuantile_antitone horder hF hG

end DOZZ.Proofs

end
