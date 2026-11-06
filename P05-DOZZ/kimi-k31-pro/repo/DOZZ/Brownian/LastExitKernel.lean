/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Brownian.ConditionedPositiveEntranceDensity

/-!
# Deterministic last-exit kernel cancellation

This is the kernel algebra in the post-last-exit part of `thm:reversal`. Conditioning the
positive Doob process to avoid `c` changes its killed kernel to the same Doob kernel shifted by
`c`. The probabilistic conditioning itself is at a deterministic time.
-/


open MeasureTheory ProbabilityTheory

namespace DOZZ.Proofs

/-- The avoidance probability, conditional on the current positive state. -/
noncomputable def lastExitAvoidanceFactor (ν c y : ℝ) : ℝ :=
  if c < y then conditionedH ν (y - c) / conditionedH ν y else 0

end DOZZ.Proofs

