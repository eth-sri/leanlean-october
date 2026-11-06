module

public import NearlyMinimax.HighWindowGeometry
public import RoughRegime.Macro
public import NearlyMinimax.HighFrameCoefficientBridge
public import NearlyMinimax.HighDensityUpdates
public import NearlyMinimax.HistoryReferenceMeasure
public import RoughRegime.Notation

𝗌

/-! Actual density/coefficient state maps for the high-regime marked prior. -/
𝛋
𝚪
𝚨
𝚩
𝚭
𝚬

abbrev HighRawState (d k D : ℕ) :=
  𝙀 × (𝙯 → 𝙮 → ℝ )
