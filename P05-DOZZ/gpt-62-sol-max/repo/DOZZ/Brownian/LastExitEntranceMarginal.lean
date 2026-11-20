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

section
variable {ν : ℝ} {P : Measure BrownianPath} (hP : IsNegativeConditionedBrownianLaw ν P) (t : ℝ≥0)
  (ht : 0 < (t : ℝ))
include hP ht

/-- The positive-coordinate state at a deterministic positive time has the entrance law. -/
theorem conditionedPositiveStateAt_map_eq_entranceMeasure :
    P.map (fun p => -(p t)) = conditionedPositiveEntranceMeasure ν (t : ℝ) := by
  let X : BrownianPath → ℝ := fun p => -(p t)
  let Y : BrownianPath → ℝ := fun p => -(p (t + 1))
  have hX : Measurable X := (ContinuousMap.measurable_eval t).neg
  have hY : Measurable Y := (ContinuousMap.measurable_eval (t + 1)).neg
  have hpair := negativeConditionedLaw_twoTime_compProd hP t 1 ht (by norm_num)
  have hpair' : P.map (fun p => (X p, Y p)) =
      conditionedPositiveEntranceMeasure ν (t : ℝ) ⊗ₘ
        conditionedPositiveTransitionKernelOnReal ν (1 : ℝ) := by
    assumption
  have  :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν (t : ℝ) hP.1 ht
  have  :=
    isMarkovKernel_conditionedPositiveTransitionKernelOnReal ν 1 hP.1 (by norm_num)
  exact Trans.trans
    (Trans.trans
      (Trans.trans (Eq.refl (Measure.map (fun p => -p t) P))
        (Eq.mpr (id (congrArg (fun _a => Measure.map X P = _a) (Measure.fst_map_prodMk hX hY)))
          (Eq.refl (Measure.map X P))))
      (congrArg Measure.fst hpair'))
    (Measure.fst_compProd (conditionedPositiveEntranceMeasure ν ↑t) (conditionedPositiveTransitionKernelOnReal ν 1))


/-- The state event has the corresponding real probability measure, hence its mass is the
entrance CDF. -/
theorem conditionedPositiveStateAt_measureReal_Iic (z : ℝ) :
    P.real {p | -(p t) ≤ z} =
      ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν (t : ℝ)) z := by
  let X : BrownianPath → ℝ := fun p => -(p t)
  have hX : Measurable X := (ContinuousMap.measurable_eval t).neg
  have  :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν (t : ℝ) hP.1 ht
  change P.real (X ⁻¹' Set.Iic z) = _
  rw [← map_measureReal_apply hX measurableSet_Iic,
    conditionedPositiveStateAt_map_eq_entranceMeasure hP t ht,
    ProbabilityTheory.cdf_eq_real]

end

end DOZZ.Proofs

end
