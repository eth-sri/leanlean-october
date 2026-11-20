module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# One-dimensional interval primitives

This file records the honest primitive half of the one-dimensional Sobolev
foundation.  It deliberately does **not** identify a distributional weak
derivative with the derivative of this primitive; that is a separate theorem.

The public estimates use the Lebesgue representative `t ↦ ∫_a^t g`.  Thus
they are available before any choice of a Sobolev representative.
-/

@[expose] public section

open scoped ENNReal Topology Interval

namespace PDE

open MeasureTheory Set

noncomputable section

section
variable (a : ℝ) (g : ℝ → ℝ)

include a g in
/-- The interval primitive of a scalar function, based at `a`. -/
def intervalPrimitive (t : ℝ) : ℝ :=
  ∫ x in a..t, g x

end

end

end PDE
