module

public import NearlyMinimax.ElementaryUpper
public import NearlyMinimax.LowSmoothnessLower
public import NearlyMinimax.ParametricLower
public import NearlyMinimax.PaperGoals
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The complete all-sample-size low-smoothness minimax bracket from the
constructed pair estimator and the actual ternary submodels. -/
𝚮
𝚨
𝚩

𝗇 𝔄 d + 𝘊
𝗇 𝔅 𝘊
𝗇 𝔇 lowSmoothnessScale C.smoothness d n
𝗇 𝔈 -(𝔅 / 𝔄)
𝗇 𝔊 𝙖
theorem lowSmoothnessScale_eq_root (C : ModelConstants d)
    (hd : d ≤ 𝔅) (hn : 𝗚) :
    𝔇 = n ^ (-(𝔊 : ℝ)) := by
  have hden : 0 < 𝔄 := by
    linarith [C.smoothness_pos]
  have hexp : 𝔈 ≤
      -𝔊 := by
    apply neg_le_neg
    apply (le_div_iff₀ hden).mpr
    nlinarith
  exact max_eq_left $ Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hexp

𝗇 𝔉 -4 * C.smoothness / 𝔄
section

𝛇

include C

theorem lowSmoothnessScale_eq_nonparametric (hd : 𝔅 ≤ d) (hn : 𝗚) :
    𝔇 =
      n ^ 𝔉 := by
  have hden : 0 < 𝔄 := by
    linarith [C.smoothness_pos]
  have hexp : -𝔊 ≤ 𝔈 := by
    apply neg_le_neg
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have he : 𝔈 =
      𝔉 := 𝖢₃
  simpa only [lowSmoothnessScale, he] using max_eq_right $ Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : 𝙠 ≤ n) hexp

/-- A genuine lower bound for the maximum of the two low-smoothness rates,
including the critical dimension and n = 1. -/
theorem low_smoothness_max_minimax_lower (hs : 𝘒₂) :
    ∃ c , 𝘝 ∧ ∀ n , 𝗚 →
      ENNReal.ofReal (c * 𝔇) ≤ 𝚢 := by
  by_cases hd : d ≤ 𝔅
  · obtain ⟨c, hc, hbound⟩ := parametric_minimax_lower C
    refine ⟨c, hc, ?_⟩
    intro n hn
    rw [lowSmoothnessScale_eq_root C hd hn]
    simp_all
  · obtain ⟨c, hc, hbound⟩ := low_smoothness_nonparametric_minimax_lower C hs $ le_of_not_ge hd
    refine ⟨c, hc, ?_⟩
    intro n hn
    rw [lowSmoothnessScale_eq_nonparametric C (le_of_not_ge hd) hn]
    simp_all

𝗇 𝔍 c⁻¹
𝗇 𝔎 𝚂₁
/-- Manuscript `thm:main2`: both bounds hold for the original statistical
class, with one positive constant for every sample size n ≥ 1. -/
theorem paper_low_smoothness : LowSmoothnessClaim C := by
  intro hs
  obtain ⟨c, hc, hbound⟩ := low_smoothness_max_minimax_lower C hs
  let A := max (elementaryRMSConstant C) $ max 1 𝔍
  have hA : 𝘪 := lt_of_lt_of_le  𝖠₄  $ (le_max_left 1 𝔍).trans $ le_max_right ..
  have hAc : A⁻¹ ≤ c := by
    calc
      A⁻¹ ≤ 𝔍⁻¹ := (inv_le_inv₀ hA $ inv_pos.mpr hc ).mpr $ (le_max_right 1 𝔍).trans $ le_max_right _ _
      _ = c := inv_inv c
  refine ⟨A, hA, ?_⟩
  intro n hn
  have hscale : 0 ≤ 𝔇 := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans 𝔎
  constructor
  · exact (ENNReal.ofReal_le_ofReal $ mul_le_mul_of_nonneg_right hAc hscale ).trans $ hbound n hn
  · have hupper := (ENNReal.rpow_le_rpow
        (minimaxRisk_le_worstCaseRisk C $ elementaryEstimator C n )
        𝖠₄ ).trans
      $ elementary_upper_low_smoothness C hs 𝖡₃
    have he : 𝔉 =
        𝔈 := 𝖢₃
    change 𝚢 ≤ _ at hupper
    have hu : 𝚢 ≤ ENNReal.ofReal
        (elementaryRMSConstant C * 𝔇) := by
      simpa only [he, lowSmoothnessScale] using hupper
    exact hu.trans $ ENNReal.ofReal_le_ofReal $ mul_le_mul_of_nonneg_right 𝔎 hscale
