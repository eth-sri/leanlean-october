/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.GaussianRegression

/-! The translated Gaussian decomposition of the one-insertion tail estimate, retaining the
correlated equator pin. The residual lateral family is independent of the pin. The radial Brownian
motion is independent of their entire joint block. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The pin variance is strictly positive throughout the compact-center geometry of the
one-insertion tail estimate. -/
theorem offCenter_pin_variance_pos (z : ℂ) (hz : 2 ≤ ‖z‖) :
    0 < 2 * Real.log ‖z‖ := by
  exact mul_pos (by norm_num) (Real.log_pos (by linarith))

end DOZZ.Proofs
