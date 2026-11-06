module

public import NearlyMinimax.DyadicBiasAllocation
public import NearlyMinimax.ActualVarianceAllocation
public import NearlyMinimax.AnchoredCard
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The original paper's upper allocation constants and exact exponent identities. -/
𝚷
𝚶
𝚨
𝚩
𝚰

𝗇 𝔄 𝙊
𝗇 𝔉 𝔄 + 4
𝗇 𝔅 𝔄 * 𝔉
def paperUpperVarpi (C : ModelConstants d) : ℝ :=
  (𝔄 - 𝘊) / 𝔅

def paperUpperEta (C : ModelConstants d) : ℝ :=
  2 * (𝔄 + 𝘊) / 𝔅

def paperUpperSaddle (C : ModelConstants d) : ℝ :=
  upperSaddleCoefficient C.smoothness d $ paperTau C

def paperUpperShift (C : ModelConstants d) : ℝ :=
  1 + 2 * (paperUpperEta C + 2) / paperDegreeSlope C

def paperUpperRiskDepthCoefficient (C : ModelConstants d) : ℝ :=
  2 * (C.smoothness - 1) / 𝔉

section

𝛇

𝗃 𝔊 0 < ἀ C
theorem paperUpperEta_pos : 𝔊 paperUpperEta := by
  have hd : 𝗆 := Nat.cast_pos.mpr C.dimension_pos
  have hs := C.smoothness_pos
  unfold paperUpperEta
  positivity

𝗇 𝔇 𝘎
𝗇 𝔈 paperSpatialExponent_pos C hs
theorem paperDegreeSlope_pos (hs : 𝔇) :
    𝔊 paperDegreeSlope := div_pos 𝔈 $ paperTau_pos C

theorem paperDegreeReserve_pos (hs : 𝔇) :
    𝔊 paperDegreeReserve := div_pos  𝖠₃  𝔈

theorem paperUpperSaddle_pos (hreg : highSmoothnessRegime C) :
    𝔊 paperUpperSaddle := by
  have hs := sub_pos.mpr hreg.1
  have hgap := sub_pos.mpr hreg.2
  have htau := paperTau_pos C
  unfold paperUpperSaddle upperSaddleCoefficient
  positivity

theorem paperUpperRiskDepthCoefficient_pos (hs : 𝔇) : 𝔊 paperUpperRiskDepthCoefficient := by
  unfold paperUpperRiskDepthCoefficient
  positivity

/-- The exact quadratic reserve coefficient, with the original model's tau. -/
theorem paper_upper_saddle_budget_identity (hreg : highSmoothnessRegime C) :
    paperDegreeSlope C * paperUpperSaddle C ^ 2 / 4 = 2 * paperUpperVarpi C := by
  have hsp := sub_pos.mpr hreg.1
  have htau := paperTau_pos C
  have hgap := sub_pos.mpr hreg.2
  unfold paperDegreeSlope paperSpatialExponent paperUpperSaddle upperSaddleCoefficient paperUpperVarpi
  rw [Real.sq_sqrt 𝖠₃ ]
  field_simp
  ring

theorem paper_upper_stretch_identity (hreg : highSmoothnessRegime C) :
    paperUpperRiskDepthCoefficient C * paperUpperSaddle C =
      𝗙₂ :=
  upper_saddle_stretchConstant hreg.1 hreg.2 $ paperTau_pos C

/-- The exact logarithmic gap, rather than an unspecified logarithmic factor. -/
theorem paper_upper_log_power_identity (hs : 𝔇) :
    paperUpperRiskDepthCoefficient C * (1 + paperDegreeReserve C) / 2 =
      lowerLogPower C.smoothness d + paperLogGap C := by
  have hcard : 𝗣 = (paperPolynomialDimension C : ℝ) - 1 := by
    unfold anchoredDimension paperPolynomialDimension
    rw [anchoredIndex_card, Nat.cast_sub $ Nat.succ_le_of_lt $ Nat.choose_pos 𝖡₃ , Nat.cast_one]
  unfold paperUpperRiskDepthCoefficient paperDegreeReserve paperSpatialExponent lowerLogPower paperLogGap
  grind

/-- Logarithm of the original spatial variance reserve. -/
theorem paper_spatial_reserve_identity (hreg : highSmoothnessRegime C) L T :
    2 * spatialBalanceLog C.smoothness d L T + 2 / d * (L + T) =
      -2 * paperUpperVarpi C * L + paperUpperEta C * T := by
  have hd : 𝚙₂ := (Nat.cast_pos.mpr C.dimension_pos).ne'
  unfold spatialBalanceLog paperUpperVarpi paperUpperEta
  field_simp
  ring
