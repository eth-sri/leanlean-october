module

public import NearlyMinimax.HighFrameDesignEnergy
public import NearlyMinimax.LocalEnergySeries

@[expose] public section

/-! Exact passage from the actual finite window/design count sum to the
local factorial series, retaining the geometric overlap and window factors. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem highWindowLabels_card {d k } [NeZero k] :
    Fintype.card (HighWindowLabels d k) = k ^ d := by
  simp only [HighWindowLabels, Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem high_design_factorial_parameter {d k n : ℕ} [NeZero k]
    Csharp mu (hmu : mu = (n : ℝ) / k ^ d) :
    n * Csharp * (2 / k) ^ d =
      (Csharp * 2 ^ d) * mu := by
  rw [hmu, div_pow]
  ring

end NearlyMinimax
