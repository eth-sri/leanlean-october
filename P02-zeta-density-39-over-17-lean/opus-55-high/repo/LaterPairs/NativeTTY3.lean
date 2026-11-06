module
public import LaterPairs.Native.HuxleyLinearForms
public import LaterPairs.NativeTTY4
public import LaterPairs.NativeSargosAD
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace TaoTrudgianYang2025
open Expdb
open scoped NNReal

/-- The third genuine new pair, from complete beta coverage and both closed
Huxley short intervals; no analytic estimate is assumed in the signature. -/
theorem exponentPair_taoTrudgianYang_thirdNew :
    ExponentPair (10769/351096) (609317/702192) := by
  pm_2072
  pm_8546 hαone
  by_cases hlo : (α:ℝ) ≤ 890/3277
  · have hh := exponentSumGrowthExponent_le_exponentPairLine_closed
      exponentPair_taoTrudgianYang_fourthNew α hαone
    unfold exponentPairLine at hh ⊢
    grind
  by_cases hmiddle : (α:ℝ) ≤ 391838/1377271
  · have hh := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_thirdPair_lowerRange
      (le_of_not_ge hlo) hmiddle
    unfold exponentPairLine
    grind
  by_cases hupper : (α:ℝ) ≤ 754/2579
  · have hh := HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_thirdPair_upperRange
      (le_of_not_ge hmiddle) hupper
    unfold exponentPairLine
    grind
  have hh := exponentSumGrowthExponent_le_exponentPairLine_closed
    CubicJointCount.exponentPair_sargosAD_bourgain α hαone
  unfold exponentPairLine at hh ⊢
  grind

/-- Exact B image used by the fourth target density row. This pair alone does
not assert the missing short-trace estimate for that row. -/
theorem exponentPair_BTTY3 : ExponentPair (258221/702192) (186317/351096) := by
  convert exponentPair_taoTrudgianYang_thirdNew.bProcess using 1 <;> norm_num
end TaoTrudgianYang2025
