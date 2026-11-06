/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DOZZ.GFFStructure.GaussianIntegration
/-!
# Off-center radial orthogonality and the correlated pin

The literal lateral family is Gaussian and independent of the full radial Brownian path. Its
radial-origin pairing retains the correlated equator pin. The lateral covariance is expanded into
the radial projection and two separable pin terms; evaluating the remaining projection integral as
the logarithmic lateral kernel of `DOZZ.circleAverage_offCenter_decomposition` is the final assembly
step.
-/


open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- A truncated logarithm converts directly into Brownian radial time. -/
theorem neg_log_max_exp_eq_min {a t : ℝ} (ha : 0 < a) :
    -Real.log (max (Real.exp (-t)) a) = min t (-Real.log a) := by
  rcases le_total (Real.exp (-t)) a with h | h
  · have ht := Real.log_le_log (Real.exp_pos (-t)) h
    rw [Real.log_exp] at ht
    rw [max_eq_right h, min_eq_right (by linarith)]
  · have ht := Real.log_le_log ha h
    rw [Real.log_exp] at ht
    rw [max_eq_left h, Real.log_exp, neg_neg, min_eq_left (by linarith)]

omit [IsProbabilityMeasure P] in
/-- The off-center radial origin has the exact variance. -/
theorem offCenter_origin_variance (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (z : ℂ) (hz : 2 ≤ ‖z‖) :
    covariance (fun ω => Xc ω z 0) (fun ω => Xc ω z 0) P = 2 * Real.log ‖z‖ := by
  simpa [min_self, zero_add] using
    circleAverage_covariance_exterior P X Xc hX hc z hz (r := 0) (s := 0) le_rfl le_rfl

omit [IsProbabilityMeasure P] in
/-- Concentric Brownian times correspond to the logarithm of the larger geometric radius. -/
theorem min_neg_log_eq_neg_log_max {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    min (-Real.log a) (-Real.log b) = -Real.log (max a b) := by
  rcases le_total a b with h | h
  · have hl := Real.log_le_log ha h
    rw [max_eq_right h, min_eq_right (neg_le_neg hl)]
  · have hl := Real.log_le_log hb h
    rw [max_eq_left h, min_eq_left (neg_le_neg hl)]

end DOZZ.Proofs
