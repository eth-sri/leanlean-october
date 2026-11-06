module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

public section

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

end GuthMaynard.NativeMoment
