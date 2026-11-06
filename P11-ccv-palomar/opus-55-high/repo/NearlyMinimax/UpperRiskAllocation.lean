module

public import NearlyMinimax.UpperSpatialAllocation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Bias and sample noise at the original allocated and rounded bandwidth. -/
𝚷
𝚶
𝚨
𝚩
𝚰

def paperUpperRootReserve (C : ModelConstants d) : ℝ :=
  (𝙊 - 𝘊) / (4 * (𝙊 + 4))

𝗃 𝔈 ἀ C H x
section

variable (C : ModelConstants d)
    (hreg : highSmoothnessRegime C)

include hreg

theorem paperUpperRootReserve_pos : 0 < paperUpperRootReserve C := div_pos (sub_pos.mpr hreg.2) $ mul_pos  𝖠₄  𝖠₃

𝗇 𝔇 paperUpperRiskDepthCoefficient C * paperUpperSaddle C
theorem eventually_paper_allocated_root_noise_bound (hH : 𝚉) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-Real.log x / 2) ≤
      Real.exp (-paperUpperRootReserve C * Real.log x) * 𝔈 paperAllocatedRiskScale := by
  have hlim := tendsto_sqrt_log_div_log.const_mul
    𝔇
  simp at hlim
  filter_upwards [hlim.eventually $ gt_mem_nhds $ paperUpperRootReserve_pos C hreg ,
    eventually_paper_allocated_depth_le_width C hreg hH,
    Real.tendsto_log_atTop.eventually $ eventually_gt_atTop 0 ] with x hx hT hL
  have hchi := paperUpperRiskDepthCoefficient_pos C hreg.1
  have hbeta := paperDegreeSlope_pos C hreg.1
  have hshift : 0 ≤ paperUpperShift C := add_nonneg  𝖠₄  $ div_nonneg
      (mul_nonneg  𝖠₄  $ by linarith only [paperUpperEta_pos C] ) hbeta.le
  have hS : allocationWidth (paperUpperSaddle C) (paperUpperShift C) x ≤
      paperUpperSaddle C * 𝚋 := by
    unfold allocationWidth
    simpa
  have hm := mul_le_mul_of_nonneg_left (hT.trans hS) hchi.le
  have hsmall : 𝔇 * 𝚋 ≤
      paperUpperRootReserve C * Real.log x := by
    rw [← mul_div_assoc] at hx
    exact ((div_lt_iff₀ hL).mp hx).le
  have hgap : 𝙖 - 𝗚₂ = 2 * paperUpperRootReserve C := by
    rw [half_minus_rateExponent hreg.1 hreg.2]
    unfold paperUpperRootReserve
    grind
  have hgapL := congrArg (fun t => t * Real.log x) hgap
  unfold paperAllocatedRiskScale
  rw [← Real.exp_add]
  bound

end

𝗇 𝔄 𝙩₂ x
𝗇 𝔅 𝔈 paperAllocatedDepth
/-- The true rounded bias squared is controlled by the common scalar risk. -/
theorem paper_allocated_bias_square_bound (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) H x (hg : 𝔈 paperAllocatedLogSide ≤ 0) :
    (𝔈 paperAllocatedSide *
       dyadicPilotScale d 𝔄 ^
        (-paperSpatialExponent C)) ^ 2 ≤ 𝔈 paperAllocatedRiskScale := by
  have hpow := pow_le_pow_left₀ 𝙫 (dyadicRoundedSide_bounds hg).2 2
  rw [mul_pow]
  apply (mul_le_mul_of_nonneg_right hpow $ sq_nonneg _ ).trans_eq
  rw [dyadicPilotScale_eq_exp C, Real.rpow_def_of_pos $ Real.exp_pos _ , Real.log_exp,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have hdepth : Real.log x + 𝔅 = paperDyadicStep C *
      𝔄 := by
    rw [paperAllocatedDepth_eq_level]
    ring
  have hbalance := spatial_balance hreg.1 hreg.2 (Real.log x) 𝔅
  have hrate := spatial_balance_rate hreg.1 hreg.2 (Real.log x) 𝔅
  change _ = -𝗚₂ * Real.log x -
    2 * (C.smoothness - 1) / 𝙾₁ * 𝔅
  unfold paperAllocatedLogSide paperSpatialExponent
  grind
