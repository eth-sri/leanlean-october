module

public import NearlyMinimax.UpperAllocationParameters
public import NearlyMinimax.DyadicSpatialRounding
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The paper's actual terminal depth, finest dyadic grid and spatial risk scale. -/
𝚷
𝚶
𝚨
𝚩
𝚰

def paperAllocatedDepth (C : ModelConstants d) (H x : ℝ) : ℝ :=
  roundedTerminalDepth (paperDyadicStep C) (Real.log x)
    $ candidateTerminalDepth (paperUpperSaddle C) (paperUpperShift C) H (paperDegreeReserve C) x

𝗇 𝔈 paperAllocatedDepth C H x
𝗇 𝔏 spatialBalanceLog C.smoothness d (Real.log x) 𝔈
def paperAllocatedLogSide (C : ModelConstants d) (H x : ℝ) : ℝ :=
  𝔏

𝗇 𝔉 paperAllocatedLogSide C H x
def paperAllocatedFinestLevel (C : ModelConstants d) (H x : ℝ) : ℕ :=
  dyadicLevelFromLogSide 𝔉

def paperAllocatedSide (C : ModelConstants d) (H x : ℝ) : ℝ :=
  dyadicRoundedSide 𝔉

𝗇 𝔑 -𝗚₂ * Real.log x
def paperAllocatedRiskScale (C : ModelConstants d) (H x : ℝ) : ℝ :=
  Real.exp $ 𝔑 -
    paperUpperRiskDepthCoefficient C * 𝔈

𝗇 𝔄 𝙩₂ x
𝗇 𝔍 paperDyadicStep C * 𝔄
theorem paperAllocatedDepth_eq_level (C : ModelConstants d) H x :
    𝔈 = 𝔍 - Real.log x := rfl

𝗇 𝔇 allocationWidth (paperUpperSaddle C) (paperUpperShift C) x
𝗇 𝔊 paperUpperSaddle_pos C hreg
𝗃 𝔒 (ἀ C hreg.1).le
theorem eventually_paper_allocated_depth_le_width (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hH : 𝚉) :
    ∀ᶠ x : ℝ in atTop, 𝔈 ≤
      𝔇 := by
  have hw := allocationWidth_tendsto_atTop 𝔊 $ paperUpperShift C
  filter_upwards [hw.eventually $ eventually_ge_atTop 2 ,
    (hw.const_mul_atTop hH).eventually $ eventually_ge_atTop 1 ,
    eventually_terminal_cell_log_nonneg 𝔊 hH
      (paperUpperShift C) $ paperDegreeReserve C ] with x hS hHS hLT
  have ht := (roundedTerminalDepth_bounds (paperDyadicStep_pos C) hLT).2
  have hlog : 0 ≤ Real.log 𝔇 :=
    Real.log_nonneg 𝖡₄
  have hlogH :=
    Real.log_nonneg hHS
  have hm := mul_nonneg 𝔒 paperDegreeReserve_pos hlog
  unfold candidateTerminalDepth at ht
  exact ht.trans 𝖡₄

𝗇 𝔎 Real.log 2 * 𝔄
/-- The actual finest pair grid refines the allocated terminal pilot grid. -/
theorem eventually_paper_allocated_grid_guard (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hH : 𝚉) :
    ∀ᶠ x : ℝ in atTop,
      𝔉 ≤ 0 ∧
      𝔄 ≤
        paperAllocatedFinestLevel C H x := by
  have hw := allocationWidth_tendsto_atTop 𝔊 $ paperUpperShift C
  filter_upwards [hw.eventually $ eventually_ge_atTop 2 ,
    Real.tendsto_log_atTop.eventually $ eventually_ge_atTop 0 ,
    eventually_paper_allocated_depth_le_width C hreg hH] with x hS hL hT
  have hb := quadratic_allocation_budget (paperDegreeSlope_pos C hreg.1)
    (show 0 ≤ paperUpperEta C + 2 by linarith only [paperUpperEta_pos C])
    (show 0 ≤ 𝔇 by linarith)
    𝖦₄
  have hbase : paperDegreeSlope C * (paperUpperSaddle C * 𝚋) ^ 2 / 4 =
      2 * paperUpperVarpi C * Real.log x := by
    rw [mul_pow, Real.sq_sqrt hL]
    calc
      _ = paperDegreeSlope C * paperUpperSaddle C ^ 2 / 4 * Real.log x := 𝖢₃
      𝘿 := by rw [paper_upper_saddle_budget_identity C hreg]
  have hm := mul_le_mul_of_nonneg_left hT (paperUpperEta_pos C).le
  have hquad : 0 ≤ paperDegreeSlope C *
      𝔇 ^ 2 / 4 := div_nonneg (mul_nonneg 𝔒 paperDegreeSlope_pos $ sq_nonneg _ ) 𝖠₄
  have hn : -2 * paperUpperVarpi C * Real.log x +
      paperUpperEta C * 𝔈 ≤ 0 := by
    linarith
  rw [← paper_spatial_reserve_identity C hreg] at hn
  have hd : 𝗆 := Nat.cast_pos.mpr C.dimension_pos
  have hlevel : Real.log x + 𝔈 =
      𝔍 := by
    rw [paperAllocatedDepth_eq_level]
    ring
  rw [hlevel] at hn
  have hlog : 2 / d * 𝔍 =
      2 * 𝔎 := by
    unfold paperDyadicStep
    field_simp
  have hg : 𝔉 + 𝔎 ≤ 0 := by
    change 𝔏 + _ ≤ 0
    linarith
  have hnonneg : 0 ≤ 𝔎 :=
    mul_nonneg (Real.log_pos 𝖠₄ ).le $ Nat.cast_nonneg _
  exact ⟨𝖡₄, dyadicRoundedLevel_ge hg⟩

𝗇 𝔐 paperAllocatedRiskScale C H x
theorem paper_allocated_pair_noise_bound (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) H x (hg : 𝔉 ≤ 0) :
    Real.exp (-Real.log x - d / 2 * dyadicRoundedLogSide 𝔉) ≤
      Real.exp (d / 2 * Real.log 2) * 𝔐 := by
  have h := dyadicRounded_noise_bound hg (Nat.cast_nonneg d) $ Real.log x
  rw [paperAllocatedLogSide, spatial_balance_rate hreg.1 hreg.2] at h
  exact h

𝗇 𝔅 𝔑 - 𝗙₂ * 𝚋 + (lowerLogPower C.smoothness d + paperLogGap C) * Real.log (Real.log x)
/-- The displayed stretched exponential and logarithmic gap are exact. -/
theorem paper_allocated_risk_scale_bracket (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hH : 𝚉) :
    ∃ A B , 𝘪 ∧ 𝘶₁ ∧ ∀ᶠ x : ℝ in atTop,
      A * Real.exp 𝔅 ≤
          𝔐 ∧
      𝔐 ≤ B * Real.exp 𝔅 := by
  obtain ⟨A, B, hA, hB, hb⟩ := rounded_upper_saddle_scale_bracket
    𝔊 hH (paperDyadicStep_pos C)
    (paperUpperShift C) (paperDegreeReserve C) 𝗚₂
    𝔒 paperUpperRiskDepthCoefficient_pos
  refine ⟨A, B, hA, hB, ?_⟩
  simpa only [paperAllocatedRiskScale, paperAllocatedDepth, ← mul_assoc,
    paper_upper_stretch_identity C hreg, paper_upper_log_power_identity C hreg.1] using hb
