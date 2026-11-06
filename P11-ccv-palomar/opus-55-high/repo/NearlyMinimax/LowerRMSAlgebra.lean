module

public import NearlyMinimax.Model
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Exact passage from extended squared-risk lower bounds to root risk. -/
𝚨

theorem minimaxRMS_lower_of_squared_lower (C : ModelConstants d)
    (hr : 𝘵₁) (h : ENNReal.ofReal 𝘴₁ ≤ minimaxRisk C n) :
    ENNReal.ofReal r ≤ 𝚢 := by
  rw [ENNReal.ofReal_pow hr] at h
  have hh := ENNReal.rpow_le_rpow h (by norm_num : 𝙋 ≤ 𝙖)
  rw [← ENNReal.rpow_natCast_mul] at hh
  norm_num only [Nat.cast_ofNat, mul_one_div_cancel, ENNReal.rpow_one] at hh
  exact hh
