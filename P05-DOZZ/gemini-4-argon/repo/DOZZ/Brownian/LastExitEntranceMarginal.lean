/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedFDDMarkovKernel

/-!
# Deterministic entrance marginals

The finite-dimensional characterization identifies the positive-coordinate state at each
positive deterministic time with the explicit entrance measure. This is the marginal input for
the large-time last-exit estimates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DOZZ.Proofs



/-- The state event has the corresponding real probability measure, hence its mass is the
entrance CDF. -/
theorem conditionedPositiveStateAt_measureReal_Iic
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) z :
    P.real {p | -(p t) ≤ z} =
      ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν (t : ℝ)) z := by
  have conditionedPositiveStateAt_map_eq_entranceMeasure : P.map (fun p => -(p t)) = conditionedPositiveEntranceMeasure ν (t : ℝ) := by
    let X : BrownianPath → ℝ := fun p => -(p t)
    let Y : BrownianPath → ℝ := fun p => -(p (t + 1))
    have hX : Measurable X := (ContinuousMap.measurable_eval t).neg
    have hY : Measurable Y := (ContinuousMap.measurable_eval (t + 1)).neg
    have : IsProbabilityMeasure (conditionedPositiveEntranceMeasure ν (t : ℝ)) :=
      isProbabilityMeasure_conditionedPositiveEntranceMeasure ν (t : ℝ) hP.1 ht
    have : IsMarkovKernel (conditionedPositiveTransitionKernelOnReal ν (1 : ℝ)) :=
      isMarkovKernel_conditionedPositiveTransitionKernelOnReal ν 1 hP.1 (by norm_num)
    calc
      P.map (fun p => -(p t)) = P.map X := by rfl
      _ = (P.map fun p => (X p, Y p)).fst := (by rw [Measure.fst_map_prodMk hX hY])
      _ = (conditionedPositiveEntranceMeasure ν (t : ℝ) ⊗ₘ
          conditionedPositiveTransitionKernelOnReal ν (1 : ℝ)).fst := by
            exact congrArg Measure.fst (by simpa [X, Y, NNReal.coe_one] using (negativeConditionedLaw_twoTime_compProd hP t 1 ht (by norm_num)))
      _ = conditionedPositiveEntranceMeasure ν (t : ℝ) := Measure.fst_compProd _ _
  let X : BrownianPath → ℝ := fun p => -(p t)
  have hX : Measurable X := (ContinuousMap.measurable_eval t).neg
  have : IsProbabilityMeasure P := hP.2.1
  have : IsProbabilityMeasure (conditionedPositiveEntranceMeasure ν (t : ℝ)) :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν (t : ℝ) hP.1 ht
  change P.real (X ⁻¹' Set.Iic z) = _
  rw [← map_measureReal_apply hX measurableSet_Iic,
    conditionedPositiveStateAt_map_eq_entranceMeasure,
    ProbabilityTheory.cdf_eq_real]

end DOZZ.Proofs

end
