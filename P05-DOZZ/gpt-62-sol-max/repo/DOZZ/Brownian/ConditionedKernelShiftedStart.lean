/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelShiftedRatio
public import DOZZ.Brownian.ConditionedKernelProbability
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Upper quantile bounds from the shifted density comparison. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Topology Set
namespace DOZZ.Proofs

private theorem transition_cdf_shift_ge {a b t x' x d z : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t) (hx' : 0 < x') (hxx' : x' ≤ x) (hd : 0 ≤ d)
    (hshift : b - a + (x / t - x' / t) ≤ d / t) :
    (∫ y in Iic z, conditionedPositiveTransitionDensity a t x' y) ≤
      ∫ y in Iic z, conditionedPositiveTransitionDensity b t x (y + d) := by
  have hb := ha.trans hab
  have hx := hx'.trans_le hxx'
  refine integral_Iic_ge_of_shiftedAntitoneDensityRatio d z
    (integrable_conditionedPositiveTransitionDensity ha ht hx')
    (integrable_conditionedPositiveTransitionDensity hb ht hx)
    (conditionedPositiveTransitionDensity_nonneg ha ht hx')
    (conditionedPositiveTransitionDensity_nonneg hb ht hx)
    (fun _ => conditionedPositiveTransitionDensity_eq_zero_of_nonpos ha ht hx')
    (conditionedPositiveTransitionDensity_integral_eq_one ha ht hx')
    (conditionedPositiveTransitionDensity_integral_eq_one hb ht hx)
    (fun _ hy => conditionedTransitionDensity_shift_eq ha hb ht hx' hx hd hy) ?_
  intro y₁ hy₁ y₂ hy₂ hle
  exact mul_le_mul_of_nonneg_left (conditionedShiftRatio_antitoneOn ha hab (div_nonneg hx'.le ht.le)
    (div_le_div_of_nonneg_right hxx' ht.le) hd hshift hy₁ hy₂ hle)
    (conditionedShiftScale_nonneg ha hb hx' hx)

/-- A start increment and a drift increment together give an upper bound on the
common-uniform endpoint increment. -/
theorem conditionedPositiveTransitionQuantile_shift_le
    {a b t x' x u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t)
    (hx' : 0 < x') (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure b t x)) u ≤
      cdfGeneralizedQuantile (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure a t x')) u +
        ((b - a) * t + (x - x')) := by
  have hb := ha.trans hab
  have hx := hx'.trans_le hxx'
  letI := isProbabilityMeasure_conditionedPositiveTransitionMeasure a t x' ha ht hx'
  letI := isProbabilityMeasure_conditionedPositiveTransitionMeasure b t x hb ht hx
  refine cdfGeneralizedQuantile_le_add hu hu1 (fun z => ?_)
  rw [conditionedPositiveTransitionMeasure_cdf_eq_integral ha ht hx',
    conditionedPositiveTransitionMeasure_cdf_eq_integral hb ht hx, ← integral_Iic_add_shift]
  apply transition_cdf_shift_ge ha hab ht hx' hxx' (by positivity)
  rw [add_div, mul_div_cancel_right₀ _ ht.ne', sub_div]

end DOZZ.Proofs
