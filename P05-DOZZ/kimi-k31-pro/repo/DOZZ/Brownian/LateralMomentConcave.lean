/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Brownian.LateralIntervalFirstMoment
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Positive lateral moments through order one

The exact first-moment intensity and the probability normalization imply all nonnegative moments
through order one by the concave-power form of Hölder's inequality. This gives a uniform strip of
the lateral interval moment theorem without invoking any higher-order chaos estimate.
-/


open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- On a probability space, the moment of order `q ∈ [0,1]` is bounded by the first moment to the
power `q`. -/
theorem lintegral_rpow_le_mean_rpow
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hP : IsProbabilityMeasure P)
    (X : Ω → ℝ≥0∞) (hX : AEMeasurable X P) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫⁻ ω, X ω ^ q ∂P) ≤ (∫⁻ ω, X ω ∂P) ^ q := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    hX (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) P)
    hq0 (by linarith) (by linarith : q + (1 - q) = 1)
  simpa [lintegral_const, hP.measure_univ] using h

end DOZZ.Proofs

