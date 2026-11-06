module
public import LaterPairs.Native.HuxleyCore
public import LaterPairs.NativeSharpRow6

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace TaoTrudgianYang2025
open Expdb
open scoped NNReal

private theorem exponentPair_of_huxley_sargos {k l : ℝ}
    (htri : InExponentPairTriangle k l) (hlk : 1/2 ≤ l - k)
    (h0 : ∀ x : ℝ, 0 ≤ x → x ≤ 861996/2811205 → 2371/43205+52209*x/69128 ≤ exponentPairLine k l x)
    (h1 : ∀ x : ℝ, 861996/2811205 ≤ x → x ≤ 87/275 → (13+94*x)/146 ≤ exponentPairLine k l x)
    (h2 : ∀ x : ℝ, 87/275 ≤ x → x ≤ 423/1295 → (11+191*x)/244 ≤ exponentPairLine k l x)
    (h3 : ∀ x : ℝ, 423/1295 ≤ x → x ≤ 227/601 → (89+908*x)/1282 ≤ exponentPairLine k l x)
    (h4 : ∀ x : ℝ, 227/601 ≤ x → x ≤ 12/31 → (29+173*x)/280 ≤ exponentPairLine k l x)
    (h5 : ∀ x : ℝ, 12/31 ≤ x → x ≤ 1508/3825 → (4+103*x)/128 ≤ exponentPairLine k l x)
    (h6 : ∀ x : ℝ, 1508/3825 ≤ x → x ≤ 1/2 → 18/199 + 521/796 * x ≤ exponentPairLine k l x) :
    ExponentPair k l := by
  apply exponentPair_of_beta_bound_half htri hlk
  intro α hhalf
  have hα : (α:ℝ) ≤ 1 := by linarith only [hhalf]
  by_cases c0 : (α:ℝ) ≤ 861996/2811205
  · exact (CubicJointCount.exponentSumGrowthExponent_le_trudgianYang_sixthRow hα).trans (h0 α α.2 c0)
  by_cases c1 : (α:ℝ) ≤ 87/275
  · exact (HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_seventhRow (le_of_not_ge c0) c1).trans (h1 α (le_of_not_ge c0) c1)
  by_cases c2 : (α:ℝ) ≤ 423/1295
  · exact (HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eighthRow (le_of_not_ge c1) c2).trans (h2 α (le_of_not_ge c1) c2)
  by_cases c3 : (α:ℝ) ≤ 227/601
  · exact (HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_ninthRow (le_of_not_ge c2) c3).trans (h3 α (le_of_not_ge c2) c3)
  by_cases c4 : (α:ℝ) ≤ 12/31
  · exact (HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_tenthRow (le_of_not_ge c3) c4).trans (h4 α (le_of_not_ge c3) c4)
  by_cases c5 : (α:ℝ) ≤ 1508/3825
  · exact (HuxleyRationalPhase.exponentSumGrowthExponent_le_huxley_eleventhRow (le_of_not_ge c4) c5).trans (h5 α (le_of_not_ge c4) c5)
  · exact (CubicJointCount.exponentSumGrowthExponent_le_sargosD_bourgain hα).trans (h6 α (le_of_not_ge c5) hhalf)

theorem exponentPair_taoTrudgianYang_firstNew : ExponentPair (89/1282) (997/1282) := by
  apply exponentPair_of_huxley_sargos (by norm_num [InExponentPairTriangle]) (by norm_num)
  all_goals intro x hx1 hx2; unfold exponentPairLine at *; linarith

theorem exponentPair_taoTrudgianYang_secondNew : ExponentPair (652397/9713986) (7599781/9713986) := by
  apply exponentPair_of_huxley_sargos (by norm_num [InExponentPairTriangle]) (by norm_num)
  all_goals intro x hx1 hx2; unfold exponentPairLine at *; linarith

theorem exponentPair_BTTY2 : ExponentPair (1371394/4856993) (2754695/4856993) := by
  convert exponentPair_taoTrudgianYang_secondNew.bProcess using 1 <;> norm_num

theorem exponentPair_BTTY1 : ExponentPair (178/641) (365/641) := by
  convert exponentPair_taoTrudgianYang_firstNew.bProcess using 1 <;> norm_num
end TaoTrudgianYang2025

namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density

theorem density_sharp_row7 {σ ε : ℝ}
    (hlo : 6482825/7570038 ≤ σ) (hhi : σ ≤ 2905/3354) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤
        C*T^(16504356*(1-σ)/(20732766*σ-7623595)+ε) :=
  density_of_pair_universal_fraction TaoTrudgianYang2025.exponentPair_BTTY2 hε

theorem density_sharp_row8 {σ ε : ℝ}
    (hlo : 2905/3354 ≤ σ) (hhi : σ ≤ 7/8) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(2172*(1-σ)/(2742*σ-1015)+ε) :=
  density_of_pair_universal_fraction TaoTrudgianYang2025.exponentPair_BTTY1 hε
