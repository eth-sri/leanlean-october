/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def

/-! The definition `DOZZ.complexPolydisc`. -/


open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Literal finite-coordinate polydisc. -/
def complexPolydisc {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ) : Set (Fin N → ℂ) :=
  {z | ∀ i, ‖z i - a i‖ < R i}

end DOZZ
