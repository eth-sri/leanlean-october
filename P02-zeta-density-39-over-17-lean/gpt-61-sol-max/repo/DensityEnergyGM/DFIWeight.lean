module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

@[expose] public section

open Set
open scoped ContDiff Topology

namespace GuthMaynard.NativeMoment

/-!
# The source weight in Duke--Friedlander--Iwaniec

This file formalizes equation (2) of Duke--Friedlander--Iwaniec, *A
quadratic divisor problem*.  The paper considers a smooth compactly supported
weight on the positive quadrant and assumes, for every pair of derivative
orders `i,j`,

`x^i y^j ‖f^(i,j)(x,y)‖ ≪_(i,j)
  (1+x/X)⁻¹ (1+y/Y)⁻¹ P^(i+j)`.

The order-dependent constant is exposed by `DFIEquation2.derivativeBound`.
It is not a uniform constant and it is not allowed to depend on `x` or `y`.
-/

/-- The mixed derivative `∂ₓ^i ∂ᵧ^j f(x,y)` occurring in DFI equation (2).
The definition differentiates first in `y` and then in `x`; smoothness makes
this agree with the paper's ordinary mixed partial derivative. -/
noncomputable def dfiMixedDeriv (i j : ℕ) (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ :=
  iteratedDeriv i (fun x' => iteratedDeriv j (f x') y) x

@[simp]
theorem dfiMixedDeriv_zero_zero (f : ℝ → ℝ → ℂ) (x y : ℝ) :
    dfiMixedDeriv 0 0 f x y = f x y := by
  simp [dfiMixedDeriv]

end GuthMaynard.NativeMoment
