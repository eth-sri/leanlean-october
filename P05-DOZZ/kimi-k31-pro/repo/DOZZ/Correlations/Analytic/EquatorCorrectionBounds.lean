/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Correlations.Analytic.EquatorIncrementCovariance
import DOZZ.GMC.CirclePotential

/-! Exponential decay and exact charge degree of the equator correction. -/

open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- The regular circle pin differs from its center value by at most the circle radius. -/
theorem equator_circle_mean_abs_le (z : ℂ) (r : ℝ) :
    |equatorCircleMean z r - Real.log (normPlus z)| ≤ Real.exp (-r) := by
  unfold equatorCircleMean
  rw [CirclePotential.integral_circleMeasure_eq_circleAverage
    CirclePotential.continuous_log_normPlus.measurable]
  exact CirclePotential.abs_circleAverage_log_normPlus_sub_le z (Real.exp_pos _)

end DOZZ.Proofs
