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

/-- Derivative of the hyperbolic score in the state variable. -/
theorem hasDerivAt_conditionedKernelScore_state
    {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
  HasDerivAt (conditionedKernelScore a)
      (-a ^ 2 / Real.sinh (a * y) ^ 2) y := by
  have harg : HasDerivAt (fun z : ℝ => a * z) a y :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul a
  have hcosh' : HasDerivAt (fun z => Real.cosh (a * z))
      (Real.sinh (a * y) * a) y := by
    convert ((Real.hasDerivAt_cosh (a * y)).comp y harg) using 1
    · rfl
  have hquot := (hcosh'.const_mul a).div ((Real.hasDerivAt_sinh (a * y)).comp y harg) (Real.sinh_pos_iff.mpr (mul_pos ha hy)).ne'
  have hquot' : HasDerivAt (fun z : ℝ =>
      a * Real.cosh (a * z) / Real.sinh (a * z))
      ((a * (Real.sinh (a * y) * a) * Real.sinh (a * y) -
          a * Real.cosh (a * y) * (Real.cosh (a * y) * a)) /
        Real.sinh (a * y) ^ 2) y := by
    convert hquot using 1
    · rfl
    · rfl
  have htrig : Real.sinh (a * y) ^ 2 - Real.cosh (a * y) ^ 2 = -1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (a * y)]
  have hderiv :
      (a * (Real.sinh (a * y) * a) * Real.sinh (a * y) -
          a * Real.cosh (a * y) * (Real.cosh (a * y) * a)) /
        Real.sinh (a * y) ^ 2 =
      -a ^ 2 / Real.sinh (a * y) ^ 2 := by
    calc
      _ =
          a ^ 2 * (Real.sinh (a * y) ^ 2 - Real.cosh (a * y) ^ 2) /
            Real.sinh (a * y) ^ 2 := by ring
      _ = _ := by simp [*]
  change HasDerivAt (fun z : ℝ =>
    a * Real.cosh (a * z) / Real.sinh (a * z))
      (-a ^ 2 / Real.sinh (a * y) ^ 2) y
  convert hquot' using 1
  exact hderiv.symm

/-- For a positive kernel parameter, its hyperbolic score strictly decreases with the state. -/
theorem conditionedKernelScore_strictAntiOn_state {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (conditionedKernelScore a) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · have hnum : Continuous (fun y => a * Real.cosh (a * y)) := by
      fun_prop
    have hden : Continuous (fun y => Real.sinh (a * y)) := by
      fun_prop
    apply hnum.continuousOn.div hden.continuousOn
    aesop
  · intro y hy
    have hy' : 0 < y := by simpa using hy
    rw [(hasDerivAt_conditionedKernelScore_state ha hy').deriv]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos ha))
          (sq_pos_of_pos (Real.sinh_pos_iff.mpr (mul_pos ha hy')))

end DOZZ.Proofs

end
