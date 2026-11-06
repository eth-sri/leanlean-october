/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Correlations.Tails.PinWickBound
import DOZZ.GFFStructure.HarmonicMoments

/-! Gaussian moments for the spatial correction envelope in the one-insertion tail estimate.
The two pins may be correlated; the bound only uses their centered Gaussian marginals. -/


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The correction exponent is dominated by absolute pin values with a fixed coefficient. -/
theorem pin_envelope_bound (z : ℂ) (γ N Nbar a : ℝ)
    (hz : 2 ≤ ‖z‖) (ha : |γ| / (2 * Real.log ‖z‖) ≤ a) :
    pinCorrectionEnvelope z γ N Nbar ≤ a * (|Nbar| + |N|) + γ ^ 2 := by
  unfold pinCorrectionEnvelope
  apply add_le_add _ le_rfl
  exact (mul_le_mul_of_nonneg_left (abs_sub Nbar N)
    (div_nonneg (abs_nonneg γ) (offCenter_pin_variance_pos z hz).le)).trans
    (mul_le_mul_of_nonneg_right ha (add_nonneg (abs_nonneg _) (abs_nonneg _)))

end DOZZ.Proofs
