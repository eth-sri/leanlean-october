module

public import NearlyMinimax.HighFrameDesignEnergy
public import RoughRegime.Macro
public import NearlyMinimax.PoissonEnergyBounds
public import RoughRegime.Notation

𝗌

/-! Exact passage from the actual finite window/design count sum to the
local factorial series, retaining the geometric overlap and window factors. -/
𝚯
𝚪
𝚨
𝚩
𝚬

theorem highWindowLabels_card [NeZero k] :
    Fintype.card 𝙯 = 𝗋 := by
  simp

theorem high_design_factorial_parameter [NeZero k]
    (Csharp mu : ℝ) (hmu : mu = 𝙒 / 𝙦 ^ d) :
    n * Csharp * 𝗄 =
       Csharp * 𝖥 * mu := by
  rw [hmu, div_pow]
  ring
