module

public import NearlyMinimax.LowerSaddle
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The rounded deletion degree has a fixed linear bound in the source
resolution. The bound precedes the statistical sample and saddle shift. -/
𝚨

theorem lowerSaddleD_le_fixed_multiple (hd : 0 ≤ d)
    (hM : 1 ≤ (𝗫 : ℝ)) :
    𝙵 ≤ (𝙶+1)*𝗫 := by
  have h := Nat.ceil_lt_add_one
    $ mul_nonneg (by positivity : 0 ≤ 𝙶) $ Nat.cast_nonneg 𝗫
  change 𝙵 < 𝙶*𝗫+1 at h
  linarith
