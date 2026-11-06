/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.DiscreteSubset

/-! The definition `DOZZ.Q`. -/


open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `Q = 2/γ + γ/2` ([KRV, (valueQ)]). -/
noncomputable def Q (γ : ℝ) : ℝ := 2 / γ + γ / 2

end DOZZ
