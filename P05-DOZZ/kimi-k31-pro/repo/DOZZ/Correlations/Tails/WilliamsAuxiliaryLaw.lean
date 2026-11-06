/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Correlations.Tails.WilliamsReversedPrefix
import DOZZ.Brownian.Lateral.RadialWindowUniform

/-! Williams splitting retains the independent auxiliary chaos, including its complete law. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The maximum, reversed lifetime-marked prefix and conditioned future of one Brownian path. -/
noncomputable def williamsReversedMark (ν : ℝ) (p : BrownianPath) :
    (ℝ × StoppedBrownianPath) × BrownianPath :=
  (reverseMarkedSegment
    (driftedBrownianMaximum ν p, brownianPreMaximumSegment ν p),
      brownianPostMaximumPath ν p)

theorem williamsReversedMark_aemeasurable
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (ν : ℝ) (hν : 0 < ν) : AEMeasurable (williamsReversedMark ν) P :=
  (measurable_reverseMarkedSegment.comp_aemeasurable
    ((aemeasurable_driftedBrownianMaximum P hB ν hν).prodMk
      (aemeasurable_brownianPreMaximumSegment P hB ν hν))).prodMk
        (aemeasurable_brownianPostMaximumPath P hB ν hν)

end DOZZ.Proofs
