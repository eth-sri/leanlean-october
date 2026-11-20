module

public import NearlyMinimax.UpperSpatialAllocation


@[expose] public section

/-! Bias and sample noise at the original allocated and rounded bandwidth. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def paperUpperRootReserve {d : ℕ} (C : ModelConstants d) : ℝ :=
  (d - 4 * C.smoothness) / (4 * (d + 4))

variable {d : ℕ} {C : ModelConstants d} (hreg : highSmoothnessRegime C) {H : ℝ}
include hreg

theorem paperUpperRootReserve_pos : 0 < paperUpperRootReserve C := div_pos (sub_pos.mpr hreg.2) (mul_pos (by norm_num) (by positivity))

theorem eventually_paper_allocated_root_noise_bound (hH : 0 < H) :
    ∀ᶠ x in atTop, Real.exp (-Real.log x / 2) ≤
      Real.exp (-paperUpperRootReserve C * Real.log x) * paperAllocatedRiskScale C H x := by
  have hlim := tendsto_sqrt_log_div_log.const_mul
    (paperUpperRiskDepthCoefficient C * paperUpperSaddle C)
  simp at hlim
  filter_upwards [hlim.eventually (gt_mem_nhds (paperUpperRootReserve_pos hreg)),
    eventually_paper_allocated_depth_le_width hreg hH,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0)] with x hx hT hL
  have hchi := paperUpperRiskDepthCoefficient_pos hreg.1
  have hshift : 0 ≤ paperUpperShift C := add_nonneg (by norm_num) (div_nonneg
      (mul_nonneg (by norm_num) (by linarith only [paperUpperEta_pos C])) (paperDegreeSlope_pos hreg.1).le)
  have hS : allocationWidth (paperUpperSaddle C) (paperUpperShift C) x ≤
      paperUpperSaddle C * Real.sqrt (Real.log x) := by
    unfold allocationWidth
    linarith only [hshift]
  have hm := mul_le_mul_of_nonneg_left (hT.trans hS) hchi.le
  have hsmall : paperUpperRiskDepthCoefficient C * paperUpperSaddle C * Real.sqrt (Real.log x) ≤
      paperUpperRootReserve C * Real.log x := by
    rw [← mul_div_assoc] at hx
    exact ((div_lt_iff₀ hL).mp hx).le
  have hgap : 1 / 2 - rateExponent C.smoothness d = 2 * paperUpperRootReserve C := by
    rw [half_minus_rateExponent hreg.1 hreg.2]
    unfold paperUpperRootReserve
    grind
  have hgapL := congrArg (fun t => t * Real.log x) hgap
  unfold paperAllocatedRiskScale
  rw [← Real.exp_add]
  bound

/-- The true rounded bias squared is controlled by the common scalar risk. -/
theorem paper_allocated_bias_square_bound {x : ℝ} (hg : paperAllocatedLogSide C H x ≤ 0) :
    (paperAllocatedSide C H x *
      (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x)) ^
        (-paperSpatialExponent C)) ^ 2 ≤ paperAllocatedRiskScale C H x := by
  have hs := (dyadicRoundedSide_bounds hg).2
  rw [mul_pow]
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ((Real.exp_pos _).le) hs 2) (sq_nonneg _)).trans_eq
  rw [dyadicPilotScale_eq_exp C, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have hdepth : Real.log x + paperAllocatedDepth C H x = paperDyadicStep C *
      (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H x) := by
    rw [paperAllocatedDepth_eq_level]
    ring
  have hbalance := spatial_balance hreg.1 hreg.2 (Real.log x) (paperAllocatedDepth C H x)
  have hrate := spatial_balance_rate hreg.1 hreg.2 (Real.log x) (paperAllocatedDepth C H x)
  change _ = _ -
    2 * (C.smoothness - 1) / (d + 4) * paperAllocatedDepth C H x
  unfold paperAllocatedLogSide paperSpatialExponent
  grind

end NearlyMinimax
