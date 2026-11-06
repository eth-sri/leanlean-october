module

public import NearlyMinimax.LocalizationL2

@[expose] public section

/-! Independent pilot fluctuation estimates. These estimates integrate the
actual product law of the two pilots; no bilinear variance estimate is assumed. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace NearlyMinimax.PilotFluctuation


variable {Ω H : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem three_square_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

end NearlyMinimax.PilotFluctuation
