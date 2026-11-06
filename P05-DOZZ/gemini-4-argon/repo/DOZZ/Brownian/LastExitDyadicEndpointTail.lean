/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitDyadicCellSum
public import DOZZ.Brownian.LastExitDyadicEndpoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Concentration of the dyadic endpoint state

The selected dyadic endpoint state converges to the barrier almost surely. Hence its positive
excess over the barrier vanishes in probability. The dyadic cell sum uses exactly this tail bound
to pass reference-kernel tests to their entrance limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace DOZZ.Proofs

/-- The selected dyadic endpoint state above the barrier. -/
noncomputable def dyadicLastExitEndpointExcess
    (n : ℕ) (c : ℝ≥0) (p : BrownianPath) : ℝ :=
  conditionedPositiveStateAt
    (dyadicLastExitCeilingTime n (negativeLastExitTime p (c : ℝ))) p - (c : ℝ)



/-- The cell-sum event that the selected future starts at least `δ` above the barrier has
probability tending to zero. -/
theorem tendsto_measureReal_dyadicPositiveLastExitRationalEvent_zero_eval_ge
    {ν} {P B : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (c : ℝ≥0) (hc : 0 < (c : ℝ)) δ (hδ : 0 < δ) :
    Tendsto
      (fun n => P.real (dyadicPositiveLastExitRationalEvent n (c : ℝ)
        {y | δ ≤ y 0})) atTop (𝓝 0) := by
  have dyadicPositiveLastExitRationalEvent_zero_eval_eq_endpoint_excess n (c : ℝ≥0) p : dyadicPositiveLastExitRationalEvals n (c : ℝ) p 0 = dyadicLastExitEndpointExcess n c p := by
    let T := dyadicLastExitCeilingTime n (negativeLastExitTime p (c : ℝ))
    have hEval : dyadicPositiveLastExitRationalEvals n (c : ℝ) p 0 =
        -(dyadicLastExitPathApproximation n (c : ℝ) p 0) := by
      simp only [dyadicPositiveLastExitRationalEvals, brownianPathRationalEvals]
      apply congrArg Neg.neg
      apply congrArg (dyadicLastExitPathApproximation n (c : ℝ) p)
      apply Subtype.ext
      norm_num
    rw [hEval, (show dyadicLastExitPathApproximation n (c : ℝ) p 0 = p T + (c : ℝ) by simp [dyadicLastExitPathApproximation, shiftPathAddConstant, T])]
    simp only [dyadicLastExitEndpointExcess, conditionedPositiveStateAt]
    ring
  have tendsto_measureReal_dyadicLastExitEndpointExcess_ge : Tendsto (fun n => P.real {p | δ ≤ dyadicLastExitEndpointExcess n c p}) atTop (𝓝 0) := by
    have : IsProbabilityMeasure P := hP.2.1
    let E : ℕ → Set BrownianPath := fun n =>
      {p | δ ≤ dyadicLastExitEndpointExcess n c p}
    have hY n : Measurable (dyadicLastExitEndpointExcess n c) := by
      change Measurable (fun p => conditionedPositiveStateAt
        (dyadicLastExitCeilingTime n (negativeLastExitTime p (c : ℝ))) p - (c : ℝ))
      exact ((show Measurable (fun z : ℝ≥0 × BrownianPath => conditionedPositiveStateAt z.1 z.2) by change Measurable (fun z : ℝ≥0 × BrownianPath => -(z.2 z.1)); exact measurable_brownianPath_evaluation.neg).comp
        (((measurable_dyadicLastExitCeilingTime n).comp
          (measurable_negativeLastExitTime_joint.comp
            ((measurable_const (a := (c : ℝ))).prodMk measurable_id))).prodMk
              measurable_id)).sub measurable_const
    have hE n : MeasurableSet (E n) :=
      measurableSet_le measurable_const (hY n)
    have hbound : ∀ n, ∀ᵐ p ∂P,
        ‖(E n).indicator (fun _ => (1 : ℝ)) p‖ ≤ 1 := by
      intro n
      filter_upwards [] with p
      by_cases hp : p ∈ E n <;> simp [hp]
    have hIntegral : Tendsto
        (fun n => ∫ p, (E n).indicator (fun _ => (1 : ℝ)) p ∂P)
        atTop (𝓝 0) :=
      by
        simpa using (tendsto_integral_filter_of_norm_le_const
          (l := atTop) (Filter.Eventually.of_forall (show ∀ n, AEStronglyMeasurable (fun p => (E n).indicator (fun _ => (1 : ℝ)) p) P by intro n; exact (measurable_const.indicator (hE n)).aestronglyMeasurable))
          ⟨1, Filter.Eventually.of_forall (fun n => hbound n)⟩ (show ∀ᵐ p ∂P, Tendsto (fun n => (E n).indicator (fun _ => (1 : ℝ)) p) atTop (𝓝 0) by filter_upwards [(show ∀ᵐ p ∂P, Tendsto (fun n => dyadicLastExitEndpointExcess n c p) atTop (𝓝 0) by simpa [dyadicLastExitEndpointExcess] using ae_conditionedPositiveStateAt_dyadicLastExit_sub_tendsto_zero hP hB hν c hc)] with p hp; exact tendsto_const_nhds.congr' (show (fun n : ℕ => (E n).indicator (fun _ => (1 : ℝ)) p) =ᶠ[atTop] fun _ => (0 : ℝ) by filter_upwards [(hp.eventually (Iio_mem_nhds hδ))] with n hn; simp [E, not_le_of_gt hn]).symm))
    have hmass n :
        (∫ p, (E n).indicator (fun _ => (1 : ℝ)) p ∂P) = P.real (E n) :=
      integral_indicator_one (hE n)
    rw [(show (fun n => ∫ p, (E n).indicator (fun _ => (1 : ℝ)) p ∂P) = fun n => P.real (E n) by funext n; exact hmass n)] at hIntegral
    simpa [E] using hIntegral
  have hset n :
      dyadicPositiveLastExitRationalEvent n (c : ℝ) {y | δ ≤ y 0} =
        {p | δ ≤ dyadicLastExitEndpointExcess n c p} := by
    ext p
    simp only [dyadicPositiveLastExitRationalEvent, Set.mem_ofPred_eq]
    rw [dyadicPositiveLastExitRationalEvent_zero_eval_eq_endpoint_excess]
  simpa only [hset] using
    tendsto_measureReal_dyadicLastExitEndpointExcess_ge

end DOZZ.Proofs

end
