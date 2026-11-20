module

public import NearlyMinimax.PaperSeriesAllocation
public import NearlyMinimax.UpperSpatialAllocation
public import NearlyMinimax.DyadicPilotMultilevel


@[expose] public section

/-! The true statistical multilevel variance budget at the original allocation
converges to zero. Its maximum factorial series is never assumed bounded. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable {d : ℕ} (C : ModelConstants d) (A C₀ C_D : ℝ) (n : ℕ)

def paperAllocatedPilotSeries : ℝ :=
  dyadicSeriesEnvelope C A ((threeBlockSize n) / 2)
    (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
    (paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)

def paperAllocatedPilotBudget : ℝ :=
  dyadicMultilevelBudget (paperAllocatedPilotSeries C A C₀ C_D n)
    (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n)
    (paperAllocatedFinestLevel C (C₀ * C_D) n)

theorem paperAllocatedPilotBudget_nonneg : 0 ≤ paperAllocatedPilotBudget C A C₀ C_D n := mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (dyadicSeriesEnvelope_nonneg C A _ (by positivity) _ _)

end

variable {d : ℕ} {C : ModelConstants d} (hreg : highSmoothnessRegime C) {A C₀ C_D : ℝ} (hC : 1 ≤ C₀)
    (hD : 1 ≤ C_D) (hDβ : 4 * paperDegreeSlope C ≤ C_D) (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀)
include hreg hC hD hcoef

/-- The actual pilot variance budget is eventually dominated by the scalar
variance reserve, with the true finest-grid rounding supplied explicitly. -/
theorem eventually_paperAllocatedPilotBudget_le_scalar :
    ∀ᶠ n in atTop,
      paperAllocatedPilotBudget C A C₀ C_D n ≤
      actualAllocationVarianceRatio (paperDyadicStep C) (paperUpperSaddle C) (paperUpperShift C)
        C₀ C_D (paperDegreeReserve C) (paperDegreeSlope C) (paperUpperEta C) (paperUpperVarpi C) n := by
  have hgrid  :=
    tendsto_natCast_atTop_atTop.eventually
      ((eventually_paper_allocated_grid_guard hreg (mul_pos (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hD))).mono fun _ h => h.1)
  filter_upwards [eventually_paper_dyadic_series_envelope_le hreg.1 A _ (paperUpperShift C) C₀ C_D (paperUpperSaddle_pos hreg) (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hD) hcoef, hgrid] with n hseries hside
  have hsquare := pow_le_pow_left₀ (Real.exp_pos _).le ((dyadicRoundedSide_bounds hside).2) 2
  let level := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) (C₀ * C_D) n
  have hj : (2 ^ level) ^ 2 =
      Real.exp (2 / d * (Real.log n + paperAllocatedDepth C (C₀ * C_D) n)) := by
    rw [paperAllocatedDepth_eq_level]
    have hd : d ≠ 0 := (Nat.cast_pos.mpr C.dimension_pos).ne'
    have he : 2 / d * (Real.log n +
        (paperDyadicStep C * (level) - Real.log n)) =
      (level) * Real.log 2 * 2 := by
      unfold paperDyadicStep
      field_simp
      ring
    rw [he]
    have hJ : Real.exp ((level) * Real.log 2) =
        2 ^ level := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [← hJ]
    simpa only [Nat.cast_ofNat, mul_comm] using (Real.exp_nat_mul
      ((level) * Real.log 2) 2).symm
  unfold paperAllocatedPilotBudget dyadicMultilevelBudget
  rw [paperAllocatedFinestLevel, ← dyadicRoundedSide_eq_inv_pow]
  exact mul_le_mul (by
    calc
      _ ≤ _ :=
          mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
      _ = _ := by
        rw [hj, ← Real.exp_nat_mul, ← Real.exp_add]
        solve_by_elim [paper_spatial_reserve_identity]) hseries
    (dyadicSeriesEnvelope_nonneg C A _ (by positivity) _ _)
    (Real.exp_pos _).le

include hDβ in
/-- Actual U13: the allocated statistical pilot budget tends to zero. -/
theorem paperAllocatedPilotBudget_tends_zero :
    Tendsto (paperAllocatedPilotBudget C A C₀ C_D) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (paperAllocatedPilotBudget_nonneg C A C₀ C_D))
    (eventually_paperAllocatedPilotBudget_le_scalar hreg hC hD hcoef)
  exact (actualAllocationVarianceRatio_tends_zero (paperDyadicStep_pos C) (paperUpperSaddle_pos hreg)
    hC hD hDβ (paperDegreeSlope_pos hreg.1) (paperDegreeReserve_pos hreg.1).le
    (paperUpperEta_pos C).le (paperUpperShift C) rfl
    (paper_upper_saddle_budget_identity hreg)).comp tendsto_natCast_atTop_atTop

include hDβ in
theorem eventually_paperAllocatedPilotBudget_le_one :
    ∀ᶠ n in atTop, paperAllocatedPilotBudget C A C₀ C_D n ≤ 1 :=
  ((paperAllocatedPilotBudget_tends_zero hreg hC hD hDβ hcoef).eventually
    (gt_mem_nhds (by norm_num))).mono fun _ h => h.le

end NearlyMinimax
