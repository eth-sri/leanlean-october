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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section
variable {d : ℕ} (C : ModelConstants d)
include C

def paperUpperVarpi   :=
  ((d : ℝ) - 4 * C.smoothness) / ((d : ℝ) * ((d : ℝ) + 4))

def paperUpperEta   :=
  2 * ((d : ℝ) + 4 * C.smoothness) / ((d : ℝ) * ((d : ℝ) + 4))

def paperUpperSaddle   :=
  upperSaddleCoefficient C.smoothness d (paperTau C)
end


def paperUpperShift {d } (C : ModelConstants d)  :=
  1 + 2 * (paperUpperEta C + 2) / paperDegreeSlope C

section
variable {d : ℕ} (C : ModelConstants d)
include C

def paperUpperRiskDepthCoefficient   :=
  2 * (C.smoothness - 1) / ((d : ℝ) + 4)

theorem paperUpperEta_pos  : 0 < paperUpperEta C := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr C.dimension_pos
  have hs := C.smoothness_pos
  unfold paperUpperEta
  positivity

section
variable (hs : 1 < C.smoothness)
include hs

theorem paperDegreeSlope_pos   :
    0 < paperDegreeSlope C := div_pos (paperSpatialExponent_pos C hs) (paperTau_pos C)

theorem paperDegreeReserve_pos   :
    0 < paperDegreeReserve C := div_pos (by positivity) (paperSpatialExponent_pos C hs)
end


theorem paperUpperSaddle_pos  (hreg : highSmoothnessRegime C) :
    0 < paperUpperSaddle C := by
  
  have hs : 0 < C.smoothness - 1 := sub_pos.mpr hreg.1
  have hgap : 0 < (d : ℝ) - 4 * C.smoothness := sub_pos.mpr hreg.2
  have htau := paperTau_pos C
  unfold paperUpperSaddle upperSaddleCoefficient
  positivity

theorem paperUpperRiskDepthCoefficient_pos 
    (hs : 1 < C.smoothness) : 0 < paperUpperRiskDepthCoefficient C := by
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr C.dimension_pos
  unfold paperUpperRiskDepthCoefficient
  positivity

section
variable (hreg : highSmoothnessRegime C)
include hreg

/-- The exact quadratic reserve coefficient, with the original model's tau. -/
theorem paper_upper_saddle_budget_identity 
     :
    paperDegreeSlope C * paperUpperSaddle C ^ 2 / 4 = 2 * paperUpperVarpi C := by
  
  
  have hsp : 0 < C.smoothness - 1 := sub_pos.mpr hreg.1
  
  have htau := paperTau_pos C
  have hgap : 0 < (d : ℝ) - 4 * C.smoothness := sub_pos.mpr hreg.2
  unfold paperDegreeSlope paperSpatialExponent paperUpperSaddle upperSaddleCoefficient paperUpperVarpi
  rw [Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem paper_upper_stretch_identity 
     :
    paperUpperRiskDepthCoefficient C * paperUpperSaddle C =
      stretchConstant C.smoothness d (paperTau C) :=
  upper_saddle_stretchConstant hreg.1 hreg.2 (paperTau_pos C)
end


/-- The exact logarithmic gap, rather than an unspecified logarithmic factor. -/
theorem paper_upper_log_power_identity 
    (hs : 1 < C.smoothness) :
    paperUpperRiskDepthCoefficient C * (1 + paperDegreeReserve C) / 2 =
      lowerLogPower C.smoothness d + paperLogGap C := by
  
  
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
    (hreg : highSmoothnessRegime C) L T :
    2 * spatialBalanceLog C.smoothness d L T + 2 / d * (L + T) =
      -2 * paperUpperVarpi C * L + paperUpperEta C * T := by
  have hd : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
  
  unfold spatialBalanceLog paperUpperVarpi paperUpperEta
  field_simp
  ring
end


end NearlyMinimax
