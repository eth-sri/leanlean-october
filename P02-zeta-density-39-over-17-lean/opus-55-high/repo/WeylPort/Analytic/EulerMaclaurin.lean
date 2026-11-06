module
/- From PNT pin 4ecb950126c4290293c5662dfe0e884123171df5, Apache-2.0. -/

public import Mathlib.NumberTheory.AbelSummation
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.EulerMaclaurin

@[expose] public section

-- Lean 4.34 elaborator compatibility; kernel checking stays enabled.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

export GuthMaynard.NativePNT (integral_deriv_mul_floor_add_one sum_eq_integral_add_integral_deriv intervalIntegrable_deriv_mul_B1 abs_B1_le_half B1 aestronglyMeasurable_B1)

export GuthMaynard.NativePNT (integral_deriv_mul_add_const)
