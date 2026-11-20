module

public import NearlyMinimax.HighFrameDesignEnergy
public import NearlyMinimax.PoissonEnergyBounds

@[expose] public section

/-! Exact passage from the actual finite window/design count sum to the
local factorial series, retaining the geometric overlap and window factors. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {d k n : ℕ} [NeZero k]

theorem high_design_factorial_parameter
    (Csharp : ℝ) {mu : ℝ} (hmu : mu = n / k ^ d) :
    n * Csharp * (2 / k) ^ d =
      (Csharp * 2 ^ d) * mu := by
  rw [hmu]
  ring

end NearlyMinimax
