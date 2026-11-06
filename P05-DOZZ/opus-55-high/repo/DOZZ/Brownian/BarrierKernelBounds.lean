/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Analytic bound for the drifted killed Gaussian kernel

The probability barrier estimates still need the reflection identity identifying the path event
with the killed kernel. This file proves the explicit Gaussian difference estimate used after that
identity, with its exact dependence on the barrier height and time.
-/

@[expose] public section

open Real MeasureTheory Set

namespace DOZZ.Proofs

/-- The reflected Gaussian difference is nonnegative for a nonnegative endpoint and barrier. -/
theorem gaussianKernelDifference_nonneg
    (t y β : ℝ) (ht : 0 < t) (hy : 0 ≤ y) (hβ : 0 ≤ β) :
    0 ≤ exp (-((y - β) ^ 2 / (2 * t))) -
      exp (-((y + β) ^ 2 / (2 * t))) := by
  have hz : 0 ≤ 2 * y * β / t := by positivity
  have hfactor :
      exp (-((y + β) ^ 2 / (2 * t))) =
        exp (-((y - β) ^ 2 / (2 * t))) * exp (-(2 * y * β / t)) := by
    rw [← exp_add]
    ring
  have hexp : exp (-(2 * y * β / t)) ≤ 1 :=
    by simp_all
  rw [hfactor]
  bound

end DOZZ.Proofs

end
