/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitConditionalAvoidanceAllStates

/-!
# Deterministic-time past/future avoidance factorization

Integrating the full-history conditional avoidance identity over any event measurable at a
deterministic time gives the past/future factorization needed on each dyadic last-exit cell.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs


/-- For a deterministic-time history event, the joint probability of future avoidance and an
arbitrary measurable recentered rational-future event factors through the current state. -/
theorem conditionedPositiveHistory_avoidance_shift_setIntegral
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν)
    (c : ℝ≥0) (hc : 0 < (c : ℝ))
    C (hC : MeasurableSet C)
    A
    (hA : MeasurableSet[conditionedPositiveNaturalFiltration t] A) :
    (∫ p in A, (conditionedPositiveFutureRationalAvoidance t c).indicator
      (fun p => lastExitShiftedFutureTest (c : ℝ) C
        (conditionedPositiveFutureRationalEvals t p)) p ∂P) =
      (∫ p in A, lastExitAvoidanceFactor ν (c : ℝ)
        (conditionedPositiveStateAt t p) *
        (brownianUpperConditionedReferenceFutureKernel B ν hν
          (conditionedPositiveStateAt t p - c)).real C ∂P) := by
  classical
  have conditionedPositiveNaturalFiltration_le : conditionedPositiveNaturalFiltration t ≤ ContinuousMap.measurableSpace := by
    refine iSup_le fun s => iSup_le fun _ => ?_
    exact (measurable_conditionedPositiveProcessValue s).comap_le
  let eval := conditionedPositiveFutureRationalEvals t
  let shift := lastExitRationalShift (c : ℝ)
  let shiftedEval : BrownianPath → (ℚ → ℝ) := fun p => shift (eval p)
  let avoid := conditionedPositiveFutureRationalAvoidance t c
  let f : BrownianPath → ℝ := fun p => avoid.indicator
    (fun p => lastExitShiftedFutureTest (c : ℝ) C (eval p)) p
  have hshift : Measurable shift := by
    apply measurable_pi_iff.mpr
    intro r
    exact (measurable_pi_apply r).sub measurable_const
  have heval := measurable_conditionedPositiveFutureRationalEvals t
  have havoid : MeasurableSet avoid := by
    change MeasurableSet (⋂ q : ℚ,
      conditionedPositiveFutureAvoidanceCoordinate t c q)
    apply MeasurableSet.iInter
    intro q
    by_cases hq : 0 < (q : ℝ)
    · simp only [conditionedPositiveFutureAvoidanceCoordinate, hq]
      exact measurableSet_lt measurable_const
        ((measurable_pi_apply q).comp heval)
    · simp [conditionedPositiveFutureAvoidanceCoordinate, hq]
  have hf_eq : f = (avoid ∩ shiftedEval ⁻¹' C).indicator (fun _ => (1 : ℝ)) := by
    funext p
    by_cases hp : p ∈ avoid
    · by_cases hq : shiftedEval p ∈ C
      · simp [f, avoid, shiftedEval, shift, eval, hp, hq,
          lastExitShiftedFutureTest]
      · simp [f, avoid, shiftedEval, shift, eval, hp, hq,
          lastExitShiftedFutureTest]
    · simp [f, avoid, hp]
  have hm := conditionedPositiveNaturalFiltration_le
  calc
    (∫ p in A, f p ∂P) =
        ∫ p in A, P[f | conditionedPositiveNaturalFiltration t] p ∂P :=
          (setIntegral_condExp hm (by rw [hf_eq]; exact (integrable_const (1 : ℝ)).indicator (havoid.inter (hC.preimage (hshift.comp heval)))) hA).symm
    _ = ∫ p in A, lastExitAvoidanceFactor ν (c : ℝ)
        (conditionedPositiveStateAt t p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - c)).real C ∂P := by
      exact setIntegral_congr_ae (hm A hA)
        ((conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift hP B hB t ht hν c hc C hC).mono fun p hp _ => hp)

end DOZZ.Proofs

end
