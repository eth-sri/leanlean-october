module
public import GafniTao.FordSpacingCount
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

@[expose] public section

/-!
# Ford's tent and sinc-square weights

These are the literal weights between equations (5.3) and (5.4).  The tent
uses the norm on `UnitAddCircle`, which is exactly distance to the nearest
integer.  No unspecified cutoff is introduced.
-/

open Real

namespace GafniTao

noncomputable section

/-- Ford's periodic tent `ℓ(x;w)`. -/
def fordTent (x w : ℝ) : ℝ :=
  max 0 (1 - ‖(x : UnitAddCircle)‖ / w)

/-- Ford's non-periodic sinc-square weight `f_j`. -/
def fordSincSquareWeight (r M j : ℕ) (x : ℝ) : ℝ :=
  (Real.pi / 2 *
      Real.sinc (Real.pi * x / (2 * ((r * M ^ j : ℕ) : ℝ)))) ^ 2

@[simp]
theorem fordSincSquareWeight_zero (r M j : ℕ) :
    fordSincSquareWeight r M j 0 = (Real.pi / 2) ^ 2 := by
  simp [fordSincSquareWeight]

end

end GafniTao
