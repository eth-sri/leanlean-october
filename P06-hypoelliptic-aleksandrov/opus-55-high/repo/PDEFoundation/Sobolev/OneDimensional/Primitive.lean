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

/-- The interval primitive of a scalar function, based at `a`. -/
def intervalPrimitive (a : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in a..t, g x

@[simp] theorem intervalPrimitive_self (a : ℝ) (g : ℝ → ℝ) :
    intervalPrimitive a g a = 0 := by
  simp [intervalPrimitive]

/-- A locally integrable interval primitive is continuous.  This is a
continuity theorem only; the later weak-derivative bridge must still establish
the a.e. derivative identity separately. -/
theorem continuousOn_intervalPrimitive
    {a b : ℝ} {g : ℝ → ℝ} (hab : a ≤ b)
    (hg : IntegrableOn g (Icc a b) volume) :
    ContinuousOn (intervalPrimitive a g) (Icc a b) := by
  have hg' : IntegrableOn g (uIcc a b) volume := by
    simp_all
  rw [← uIcc_of_le hab]
  exact intervalIntegral.continuousOn_primitive_interval
    (μ := volume) (f := g) (a := a) (b := b) hg'

end

end PDE
