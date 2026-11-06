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
attribute [local instance] Classical.propDecidable

theorem highWindowLabels_card {d k : ℕ} [NeZero k] :
    Fintype.card (HighWindowLabels d k) = k ^ d := by
  simp only [HighWindowLabels, Fintype.card_fun, Fintype.card_fin, ZMod.card]

theorem high_design_factorial_parameter {d k n : ℕ} [NeZero k]
    (Csharp mu : ℝ) (hmu : mu = (n : ℝ) / (k : ℝ) ^ d) :
    (n : ℝ) * Csharp * (2 / (k : ℝ)) ^ d =
      (Csharp * (2 : ℝ) ^ d) * mu := by
  rw [hmu, div_pow]
  ring

end NearlyMinimax
