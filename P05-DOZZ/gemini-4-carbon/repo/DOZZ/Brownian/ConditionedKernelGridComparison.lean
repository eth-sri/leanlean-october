/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.Brownian.ConditionedKernelShiftedStart

/-!
# Pathwise comparison of common-uniform conditioned kernel grids

The explicit one-step quantile inequalities propagate by induction along any shared sequence of
uniform levels. This is the finite-grid order estimate needed before constructing a measurable
uniform-driven chain and passing to continuous paths.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace DOZZ.Proofs

/-- The generalized-inverse quantile of the positive conditioned transition kernel. -/
noncomputable def conditionedTransitionQuantile (ν t x u : ℝ) : ℝ :=
  cdfGeneralizedQuantile
    (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u

/-- Increasing a positive start raises the common-uniform transition quantile. -/
theorem conditionedTransitionQuantile_start_mono
    {ν t x x' u : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    conditionedTransitionQuantile ν t x' u ≤ conditionedTransitionQuantile ν t x u := by
  exact conditionedPositiveTransitionQuantile_start_le hν ht hx' hxx' hu hu1

/-- Increasing the start by `d` raises the common-uniform transition quantile by at most `d`,
including the BES(3) zero-drift endpoint. -/
theorem conditionedTransitionQuantile_start_add
    {ν t x x' u : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    conditionedTransitionQuantile ν t x u ≤
      conditionedTransitionQuantile ν t x' u + (x - x') := by
  by_cases hνzero : ν = 0
  · subst ν
    simpa [conditionedTransitionQuantile] using
      conditionedPositiveTransitionQuantile_start_add_zero ht hx' hxx' hu hu1
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
    simpa [conditionedTransitionQuantile] using
      conditionedPositiveTransitionQuantile_start_add hνpos ht hx' hxx' hu hu1

/-- Increasing the drift raises the common-uniform transition quantile. -/
theorem conditionedTransitionQuantile_drift_mono
    {a b t x u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    conditionedTransitionQuantile a t x u ≤ conditionedTransitionQuantile b t x u := by
  exact conditionedPositiveTransitionQuantile_drift_le ha hab ht hx hu hu1

/-- Increasing the drift from `a` to `b` raises the common-uniform transition quantile by at most
`(b-a)t`, including `a=0`. -/
theorem conditionedTransitionQuantile_drift_add
    {a b t x u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    conditionedTransitionQuantile b t x u ≤
      conditionedTransitionQuantile a t x u + (b - a) * t := by
  by_cases hazero : a = 0
  · subst a
    by_cases hbzero : b = 0
    · subst b
      simp [conditionedTransitionQuantile]
    · have hbpos : 0 < b := lt_of_le_of_ne (by positivity) (Ne.symm hbzero)
      simpa [conditionedTransitionQuantile] using
        conditionedPositiveTransitionQuantile_drift_add_zero hbpos ht hx hu hu1
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hazero)
    simpa [conditionedTransitionQuantile] using
      conditionedPositiveTransitionQuantile_drift_add hapos hab ht hx hu hu1

end DOZZ.Proofs

end
