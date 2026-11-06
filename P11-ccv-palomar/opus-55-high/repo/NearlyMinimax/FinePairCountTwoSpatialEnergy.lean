module

public import NearlyMinimax.FinePairCountTwoEnergy
public import RoughRegime.Macro
public import NearlyMinimax.FinePairAliasSpatialEnergy
public import RoughRegime.Notation

𝗌

/-! Actual spatial energy of the complete three-row count-two numerator,
including the single heat correction and the true radial defect. -/
𝚫
𝚪
𝚨
𝚩
set_option maxHeartbeats 100000

 def finePairCountTwoSpatialBudget (d : ℕ) (bd a ρ η N : ℝ) : ℝ :=
  (𝙎*bd^2*(𝗠/𝗅)^2)^2 * (6*𝙉^d*spatialExponentialConstant d/𝚝₂)
