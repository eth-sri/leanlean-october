/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Hyperbolic score estimates for conditioned Brownian kernels

The comparison proof for conditioned Brownian kernels uses the logarithmic derivative
`a * coth (a*y)`. This file records its state monotonicity, the score estimate needed for shifted
kernel ratios.
-/

@[expose] public section

namespace DOZZ.Proofs

/-- The logarithmic derivative of the hyperbolic factor `sinh (a*y)` in the transition kernel. -/
noncomputable def conditionedKernelScore (a y : ℝ) : ℝ :=
  a * Real.cosh (a * y) / Real.sinh (a * y)

/-- The derivative of the hyperbolic cotangent away from zero. -/
theorem hasDerivAt_cosh_div_sinh {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun x => Real.cosh x / Real.sinh x) (-1 / Real.sinh u ^ 2) u := by
  convert (Real.hasDerivAt_cosh u).div (Real.hasDerivAt_sinh u) (Real.sinh_ne_zero.mpr hu)
    using 1
  congr 1
  nlinarith [Real.cosh_sq_sub_sinh_sq u]

/-- Derivative of the hyperbolic score in the state variable. -/
theorem hasDerivAt_conditionedKernelScore_state
    {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
  HasDerivAt (conditionedKernelScore a)
      (-a ^ 2 / Real.sinh (a * y) ^ 2) y := by
  have h : HasDerivAt (fun z => a * z) a y := by
    simpa using (hasDerivAt_id y).const_mul a
  convert ((hasDerivAt_cosh_div_sinh (mul_ne_zero ha.ne' hy.ne')).comp y h).const_mul a using 1
  · ext x
    simp [conditionedKernelScore, mul_div_assoc]
  · ring

/-- For a positive kernel parameter, its hyperbolic score strictly decreases with the state. -/
theorem conditionedKernelScore_strictAntiOn_state {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (conditionedKernelScore a) (Set.Ioi 0) := by
  have hd (y : ℝ) (hy : y ∈ Set.Ioi 0) := hasDerivAt_conditionedKernelScore_state ha hy
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) (fun y hy => (hd y hy).continuousAt.continuousWithinAt) ?_
  intro y hy
  have hy' := interior_subset hy
  rw [(hd y hy').deriv]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (sq_pos_of_pos ha))
    (sq_pos_of_pos (Real.sinh_pos_iff.mpr (mul_pos ha hy')))

end DOZZ.Proofs

end
