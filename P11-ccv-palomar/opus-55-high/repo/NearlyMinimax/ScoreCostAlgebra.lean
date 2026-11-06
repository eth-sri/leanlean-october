module

public import NearlyMinimax.PaperScorePath
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The scalar passage from the full score energy and update cost to the
manuscript's quantitative lower bound. -/
𝚫
𝚨

𝗇 𝔇 1 + B + I
def localScorePathLength (c B I : ℝ) : ℝ := c / 𝔇

𝗇 𝔉 localScorePathLength c B I
theorem localScorePathLength_pos (hc : 𝘝)
    (hB : 𝙐) (hI : 0 ≤ I) : 0 < 𝔉 := div_pos hc 𝖡₄

theorem localScorePathLength_energy_le (hc : 𝗂₁)
    (hB : 𝙐) (hI : 0 ≤ I) : 𝔉 * I ≤ c := by
  rw [localScorePathLength, div_mul_eq_mul_div]
  apply (div_le_iff₀ 𝖡₄ ).mpr
  bound

𝗇 𝔄 1 + B ^ 2 + I ^ 2
𝗇 𝔍 𝔇 ^ 2
theorem three_term_square_le (B I : ℝ) :
    𝔍 ≤ 3 * 𝔄 := by
  nlinarith only [sq_nonneg $ 1 - I , sq_nonneg $ B - I ]

𝗇 𝔅 (2 + c) ^ 2
𝗇 𝔈 (2 + score) ^ 2
𝗇 𝔊 𝗆₂ * 𝗩
𝗇 𝔎 3 * 𝔅
theorem score_cost_numeric (hc : 𝘝)
    (hB : 𝙐) (hI : 0 ≤ I) (hscore0 : 0 ≤ score)
    (hscore : score ≤ 𝔉 * I) :
    𝗆₂ / 𝔎 * 𝗩 / 𝔄 ≤
      𝗩 * 𝔉 ^ 2 / 𝔈 := by
  have hsc := hscore.trans $ localScorePathLength_energy_le hc.le hB hI
  have hsq : 𝔈 ≤ 𝔅 := by
    bound
  have hprod : 𝔈 * 𝔍 ≤
      𝔎 * 𝔄 := by
    calc
      _ ≤ 𝔅 * 𝔍 :=
        mul_le_mul_of_nonneg_right hsq $ sq_nonneg _
      _ ≤ 𝔅 * (3 * 𝔄) :=
        mul_le_mul_of_nonneg_left (three_term_square_le B I) $ sq_nonneg _
      𝘿 := 𝖢₃
  calc
    _ = 𝔊 / (𝔎 * 𝔄) := by
      field_simp
    _ ≤ 𝔊 / (𝔈 * 𝔍) := div_le_div_of_nonneg_left  𝖠₃   𝖠₃  hprod
    𝘿 := by
      rw [localScorePathLength]
      field_simp
