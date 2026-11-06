/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Defs.Q
import DOZZ.Statements.Defs.GffKernel
import Mathlib.Probability.Distributions.Gaussian.Real

/-! Scalar Gaussian calculation in the exact-scale moment identity. -/


open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace DOZZ.Proofs


/-- The exponential moment of a centered Gaussian, in the normalization used by GMC scaling. -/
theorem gaussian_exponential_moment_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : Ω → ℝ}
    {v : ℝ≥0} (hW : HasLaw W (gaussianReal 0 v) P) (t : ℝ) :
    (∫ ω, Real.exp (t * W ω) ∂P) =
      Real.exp ((v : ℝ) * t ^ 2 / 2) := by
  have h := mgf_gaussianReal hW t
  simpa [mgf, NNReal.coe_zero, zero_mul, zero_add] using h


end DOZZ.Proofs
