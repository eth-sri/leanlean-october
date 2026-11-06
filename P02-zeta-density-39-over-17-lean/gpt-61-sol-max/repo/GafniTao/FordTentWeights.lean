module
import Mathlib
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

/- Ford's periodic tent `ℓ(x;w)`. -/
def fordTent (x w : ℝ) : ℝ :=
  max 0 (1 - ‖(x : UnitAddCircle)‖ / w)








