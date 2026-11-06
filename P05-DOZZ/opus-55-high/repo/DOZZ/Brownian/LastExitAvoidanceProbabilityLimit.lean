/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitCellHistory
public import DOZZ.Brownian.LastExitAvoidanceStateLimit

/-!
# Late-time rational survival probability

The full-history avoidance identity identifies the probability of staying above a fixed level at
all positive rational future offsets with the mean Doob avoidance factor.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal Topology

namespace DOZZ.Proofs
section
variable {ν : ℝ} {P B : Measure BrownianPath} [SFinite B] (hP : IsNegativeConditionedBrownianLaw ν P) (hB : IsBrownianReal (fun t p => p t) B) (hν : 0 < ν)
include hP hB hν

/-- The rational future survival event has probability equal to the mean deterministic-time
avoidance factor. -/
theorem conditionedPositiveFutureRationalAvoidance_realMeasure_eq_integral_factor
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    P.real (conditionedPositiveFutureRationalAvoidance t c) =
      ∫ p, lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) ∂P := by
  let : IsProbabilityMeasure P := hP.2.1
  let E := conditionedPositiveFutureRationalAvoidance t c
  have hE : MeasurableSet E := by
    change MeasurableSet (⋂ q : ℚ,
      conditionedPositiveFutureAvoidanceCoordinate t c q)
    exact MeasurableSet.iInter fun q =>
      measurableSet_conditionedPositiveFutureAvoidanceCoordinate t c q
  have hfactorization := conditionedPositiveHistory_avoidance_shift_setIntegral
    hP B hB t ht hν c hc Set.univ MeasurableSet.univ
    Set.univ MeasurableSet.univ
  have hleft :
      (∫ p in Set.univ,
        E.indicator (fun p => lastExitShiftedFutureTest c Set.univ
          (conditionedPositiveFutureRationalEvals t p)) p ∂P) = P.real E := by
    rw [setIntegral_univ]
    have htest : (fun p : BrownianPath =>
        lastExitShiftedFutureTest c Set.univ
          (conditionedPositiveFutureRationalEvals t p)) = fun _ => 1 := by
      funext p
      simp [lastExitShiftedFutureTest]
    simp_all
  have hmass (p : BrownianPath) :
      lastExitAvoidanceFactor ν c (conditionedPositiveStateAt t p) *
        (brownianUpperConditionedReferenceFutureKernel B ν hν
          (conditionedPositiveStateAt t p - c)).real Set.univ =
        lastExitAvoidanceFactor ν c (conditionedPositiveStateAt t p) := by
    by_cases hcx : c < conditionedPositiveStateAt t p
    · have hx := sub_pos.mpr hcx
      have : IsProbabilityMeasure
          (brownianBelowConditionedLaw B ν
            (conditionedPositiveStateAt t p - c)) :=
        isProbabilityMeasure_brownianBelowConditionedLaw B hB ν
          (conditionedPositiveStateAt t p - c) hν hx
      have : IsProbabilityMeasure
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - c)) := by
        rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned
          B ν _ hν hx]
        infer_instance
      simp
    · simp [lastExitAvoidanceFactor, hcx]
  have hright :
      (∫ p in Set.univ,
        lastExitAvoidanceFactor ν c (conditionedPositiveStateAt t p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - c)).real Set.univ ∂P) =
      ∫ p, lastExitAvoidanceFactor ν c
          (conditionedPositiveStateAt t p) ∂P := by
    rw [setIntegral_univ]
    apply integral_congr_ae
    exact ae_of_all P hmass
  rw [← hleft, hfactorization, hright]

/-- The rational future survival probability tends to one at large deterministic times. -/
theorem conditionedPositiveFutureRationalAvoidance_realMeasure_tendsto_one_atTop
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    Tendsto (fun t : ℝ≥0 =>
      P.real (conditionedPositiveFutureRationalAvoidance t c)) atTop (𝓝 1) := by
  apply (tendsto_integral_lastExitAvoidanceFactor_atTop hP hν c hc).congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  simpa [conditionedPositiveStateAt] using
    (conditionedPositiveFutureRationalAvoidance_realMeasure_eq_integral_factor
      hP hB hν t (by exact_mod_cast ht) c hc).symm

end

end DOZZ.Proofs

end
