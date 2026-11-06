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

open scoped Interval

namespace PDE

open MeasureTheory Set

noncomputable section

/-- The interval primitive of a scalar function, based at `a`. -/
def intervalPrimitive (a : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in a..t, g x



/-- A locally integrable interval primitive is continuous.  This is a
continuity theorem only; the later weak-derivative bridge must still establish
the a.e. derivative identity separately. -/
theorem continuousOn_intervalPrimitive
    {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Icc a b) ) :
    ContinuousOn (intervalPrimitive a g) (Icc a b) := by

  change ContinuousOn (fun t => ∫ x in a..t, g x) (Icc a b)
  rw [← uIcc_of_le hab]
  exact intervalIntegral.continuousOn_primitive_interval
        (by
            simpa [uIcc_of_le hab] using hg)

end

end PDE
