module

public import NearlyMinimax.DyadicBiasAllocation
public import NearlyMinimax.ActualVarianceAllocation
public import NearlyMinimax.AnchoredCard

@[expose] public section

/-! The original paper's upper allocation constants and exact exponent identities. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax

variable {d : ℕ} (C : ModelConstants d)

def paperUpperVarpi (C : ModelConstants d) : ℝ :=
  ((d : ℝ) - 4 * C.smoothness) / ((d : ℝ) * ((d : ℝ) + 4))

def paperUpperEta (C : ModelConstants d) : ℝ :=
  2 * ((d : ℝ) + 4 * C.smoothness) / ((d : ℝ) * ((d : ℝ) + 4))

def paperUpperSaddle (C : ModelConstants d) : ℝ :=
  upperSaddleCoefficient C.smoothness d (paperTau C)

def paperUpperShift (C : ModelConstants d) : ℝ :=
  1 + 2 * (paperUpperEta C + 2) / paperDegreeSlope C

def paperUpperRiskDepthCoefficient (C : ModelConstants d) : ℝ :=
  2 * (C.smoothness - 1) / ((d : ℝ) + 4)

section
variable (C : ModelConstants d)

theorem paperUpperEta_pos : 0 < paperUpperEta C := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr C.dimension_pos
  have hs := C.smoothness_pos
  unfold paperUpperEta
  positivity

theorem paperDegreeSlope_pos (hs : 1 < C.smoothness) :
    0 < paperDegreeSlope C := div_pos (paperSpatialExponent_pos C hs) (paperTau_pos C)

theorem paperDegreeReserve_pos (hs : 1 < C.smoothness) :
    0 < paperDegreeReserve C := by
  unfold paperDegreeReserve
  exact div_pos (by positivity) (paperSpatialExponent_pos C hs)

theorem paperUpperSaddle_pos (hreg : highSmoothnessRegime C) :
    0 < paperUpperSaddle C := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr C.dimension_pos
  have hs : 0 < C.smoothness - 1 := sub_pos.mpr hreg.1
  have hgap : 0 < (d : ℝ) - 4 * C.smoothness := sub_pos.mpr hreg.2
  have htau := paperTau_pos C
  unfold paperUpperSaddle upperSaddleCoefficient
  positivity

theorem paperUpperRiskDepthCoefficient_pos 
    (hs : 1 < C.smoothness) : 0 < paperUpperRiskDepthCoefficient C := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr C.dimension_pos
  unfold paperUpperRiskDepthCoefficient
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hs)) (by positivity)

/-- The exact quadratic reserve coefficient, with the original model's tau. -/
theorem paper_upper_saddle_budget_identity 
    (hreg : highSmoothnessRegime C) :
    paperDegreeSlope C * paperUpperSaddle C ^ 2 / 4 = 2 * paperUpperVarpi C := by
  have hd : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
  have hdp : (d : ℝ) + 4 ≠ 0 := by positivity
  have hsp : 0 < C.smoothness - 1 := sub_pos.mpr hreg.1
  have hs : C.smoothness - 1 ≠ 0 := hsp.ne'
  have htau := paperTau_pos C
  have hgap : 0 < (d : ℝ) - 4 * C.smoothness := sub_pos.mpr hreg.2
  unfold paperDegreeSlope paperSpatialExponent paperUpperSaddle upperSaddleCoefficient paperUpperVarpi
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

end

theorem paper_upper_stretch_identity 
    (hreg : highSmoothnessRegime C) :
    paperUpperRiskDepthCoefficient C * paperUpperSaddle C =
      stretchConstant C.smoothness d (paperTau C) :=
  upper_saddle_stretchConstant hreg.1 hreg.2 (paperTau_pos C)

/-- The exact logarithmic gap, rather than an unspecified logarithmic factor. -/
theorem paper_upper_log_power_identity 
    (hs : 1 < C.smoothness) :
    paperUpperRiskDepthCoefficient C * (1 + paperDegreeReserve C) / 2 =
      lowerLogPower C.smoothness d + paperLogGap C := by
  have hd : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
  have hdp : (d : ℝ) + 4 ≠ 0 := by positivity
  have hs0 : C.smoothness - 1 ≠ 0 := (sub_pos.mpr hs).ne'
  have hq : 1 ≤ (d + C.order).choose d := Nat.succ_le_of_lt (Nat.choose_pos (by omega))
  have hcard : (anchoredDimension d C.order : ℝ) = (paperPolynomialDimension C : ℝ) - 1 := by
    unfold anchoredDimension paperPolynomialDimension
    rw [anchoredIndex_card, Nat.cast_sub hq, Nat.cast_one]
  unfold paperUpperRiskDepthCoefficient paperDegreeReserve paperSpatialExponent lowerLogPower paperLogGap
  rw [hcard]
  field_simp
  ring

/-- Logarithm of the original spatial variance reserve. -/
theorem paper_spatial_reserve_identity 
    (hreg : highSmoothnessRegime C) (L T : ℝ) :
    2 * spatialBalanceLog C.smoothness d L T + 2 / (d : ℝ) * (L + T) =
      -2 * paperUpperVarpi C * L + paperUpperEta C * T := by
  have hd : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
  have hdp : (d : ℝ) + 4 ≠ 0 := by positivity
  unfold spatialBalanceLog paperUpperVarpi paperUpperEta
  field_simp
  ring

end NearlyMinimax
