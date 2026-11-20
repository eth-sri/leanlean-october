/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Endpoint comparison for the finite Gaussian interpolation. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A differentiable interpolation with nonpositive derivative on the interior has the Kahane
endpoint order. This isolates the one-dimensional real-analysis step from the Gaussian IBP proof. -/
theorem kahaneInterpolation_endpoint_le_of_derivative
    (φ d : ℝ → ℝ)
    (hcont : ContinuousOn φ (Set.Icc 0 1))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (d t) t)
    (hsign : ∀ t ∈ Set.Ioo (0 : ℝ) 1, d t ≤ 0) :
    φ 1 ≤ φ 0 := by
  exact (antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hcont
      (fun t ht => (hderiv t (by simpa using ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hderiv t (by simpa using ht)).deriv]
        exact hsign t (by simpa using ht))) (by simp) (by simp) (by norm_num)

end DOZZ.Proofs
