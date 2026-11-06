module

public import NearlyMinimax.LocalizationL2
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Independent pilot fluctuation estimates. These estimates integrate the
actual product law of the two pilots; no bilinear variance estimate is assumed. -/
𝚯
𝚻
namespace NearlyMinimax.PilotFluctuation

𝚩

variable {Ω H : Type*} [MeasurableSpace Ω]
𝛓
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem three_square_le (a b c : ℝ) :
    (𝗓₁ + c) ^ 2 ≤ 3 * (𝗅 + 𝘺 + 𝗆₂) := by
  nlinarith [sq_nonneg $ a - c , sq_nonneg $ b - c ]
