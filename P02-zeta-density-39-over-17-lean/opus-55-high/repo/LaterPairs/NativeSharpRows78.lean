module
public import LaterPairs.Native.HuxleyCore
public import LaterPairs.NativeSharpRow6
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace TaoTrudgianYang2025
open Expdb

theorem exponentPair_taoTrudgianYang_firstNew : ExponentPair (89/1282) (997/1282) := by
  pm_2072
  pm_8546 hα
  pm_7768
  · have h := CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    grind
  pm_7769
  pm_5254 HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_seventhRow hr0
  pm_7770
  pm_5254 HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eighthRow hr1
  pm_7771
  pm_5254 HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow hr2
  pm_2701
  grind

/-- The second new pair in the published theorem, with every beta input discharged. -/
theorem exponentPair_taoTrudgianYang_secondNew : ExponentPair (652397/9713986) (7599781/9713986) := by
  pm_2072
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  pm_7768
  · have h := CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow hα
    unfold exponentPairLine
    linarith only [h,h0]
  pm_7769
  pm_613 HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_seventhRow h0 hr0
  pm_7770
  pm_613 HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eighthRow hr0 hr1
  pm_7771
  pm_613 HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow hr1 hr2
  pm_2701
  linarith only [h,lt_of_not_ge hr4]

/-- Exact B image of the second native new TTY pair. -/
theorem exponentPair_BTTY2 : ExponentPair (1371394/4856993) (2754695/4856993) := by
  convert exponentPair_taoTrudgianYang_secondNew.bProcess using 1 <;> norm_num

/-- Exact B image of the first native new TTY pair. -/
theorem exponentPair_BTTY1 : ExponentPair (178/641) (365/641) := by
  convert exponentPair_taoTrudgianYang_firstNew.bProcess using 1 <;> norm_num
end TaoTrudgianYang2025

namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density

/-- Full closed later row7 for actual symmetric zeros with analytic multiplicity. -/
theorem density_sharp_row7 {σ ε : ℝ}
    (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤
        C*T^(16504356*(1-σ)/(20732766*σ-7623595)+ε) := by
  pm_6780 sharp_row7_tail_budgets sharp_row7_density_exponent TaoTrudgianYang2025.exponentPair_BTTY2 physicalDetectorWindow_row7 sharpCountWindow_row7

/-- Full closed later row8 for actual symmetric zeros with analytic multiplicity. -/
theorem density_sharp_row8 {σ ε : ℝ}
    (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(2172*(1-σ)/(2742*σ-1015)+ε) := by
  pm_6780 sharp_row8_tail_budgets sharp_row8_density_exponent TaoTrudgianYang2025.exponentPair_BTTY1 physicalDetectorWindow_row8 sharpCountWindow_row8
end Montgomery.RationalMoment.RightDetector.Physical
