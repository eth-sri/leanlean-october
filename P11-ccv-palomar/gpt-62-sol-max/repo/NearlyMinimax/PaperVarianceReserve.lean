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

def paperAllocatedPilotSeries {d : ℕ} (C : ModelConstants d) (A C₀ C_D : ℝ) (n : ℕ) : ℝ :=
  dyadicSeriesEnvelope C A ((threeBlockSize n : ℝ) / 2)
    (paperAllocatedPilotLevel C (C₀ * C_D) n)
    (paperAllocatedPilotDegree C (C₀ * C_D) n)

def paperAllocatedPilotBudget {d : ℕ} (C : ModelConstants d) (A C₀ C_D : ℝ) (n : ℕ) : ℝ :=
  dyadicMultilevelBudget (paperAllocatedPilotSeries C A C₀ C_D n)
    (paperAllocatedPilotLevel C (C₀ * C_D) n)
    (paperAllocatedFinestLevel C (C₀ * C_D) n)

section
variable {d : ℕ} (C : ModelConstants d)

theorem paperAllocatedPilotBudget_nonneg
    (A C₀ C_D : ℝ) (n : ℕ) : 0 ≤ paperAllocatedPilotBudget C A C₀ C_D n := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (dyadicSeriesEnvelope_nonneg C A _ (by positivity) _ _)

section
variable (hreg : highSmoothnessRegime C) (A C₀ C_D : ℝ)
    (hC : 1 ≤ C₀) (hD : 1 ≤ C_D)
include hreg hC hD

/-- The actual pilot variance budget is eventually dominated by the scalar
variance reserve, with the true finest-grid rounding supplied explicitly. -/
theorem eventually_paperAllocatedPilotBudget_le_scalar
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀) :
    ∀ᶠ n : ℕ in atTop,
      paperAllocatedPilotBudget C A C₀ C_D n ≤
      actualAllocationVarianceRatio (paperDyadicStep C) (paperUpperSaddle C) (paperUpperShift C)
        C₀ C_D (paperDegreeReserve C) (paperDegreeSlope C) (paperUpperEta C) (paperUpperVarpi C) n := by
  have hH := mul_pos (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hD)
  have hgrid :=
    tendsto_natCast_atTop_atTop.eventually
      ((eventually_paper_allocated_grid_guard C hreg hH).mono fun _ h => h.1)
  filter_upwards [eventually_paper_dyadic_series_envelope_le C hreg.1 A
    (paperUpperSaddle C) (paperUpperShift C) C₀ C_D (paperUpperSaddle_pos C hreg)
    (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hD) hcoef, hgrid] with n hseries hside
  have hround := (dyadicRoundedSide_bounds hside).2
  have hsquare := pow_le_pow_left₀ (Real.exp_pos _).le hround 2
  have hscale : (paperAllocatedSide C (C₀ * C_D) n) ^ 2 *
      ((2 : ℝ) ^ paperAllocatedPilotLevel C (C₀ * C_D) n) ^ 2 ≤
      Real.exp (-2 * paperUpperVarpi C * Real.log n + paperUpperEta C * paperAllocatedDepth C (C₀ * C_D) n) := by
    apply (mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)).trans_eq
    rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul,
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    rw [Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← paper_allocated_spatial_reserve C (C₀ * C_D) n]
    ring
  change _ ≤ Real.exp _ * _
  unfold paperAllocatedPilotBudget dyadicMultilevelBudget
  rw [paperAllocatedFinestLevel, ← dyadicRoundedSide_eq_inv_pow]
  exact mul_le_mul hscale hseries
    (dyadicSeriesEnvelope_nonneg C A _ (by positivity) _ _)
    (Real.exp_pos _).le

section
variable (hDβ : 4 * paperDegreeSlope C ≤ C_D)
    (hcoef : 12 * paperPilotMomentFactor C A ≤ C₀)
include hDβ hcoef

/-- Actual U13: the allocated statistical pilot budget tends to zero. -/
theorem paperAllocatedPilotBudget_tends_zero :
    Tendsto (paperAllocatedPilotBudget C A C₀ C_D) atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (paperAllocatedPilotBudget_nonneg C A C₀ C_D))
    (eventually_paperAllocatedPilotBudget_le_scalar C hreg A C₀ C_D hC hD hcoef)
  exact (actualAllocationVarianceRatio_tends_zero (paperDyadicStep_pos C) (paperUpperSaddle_pos C hreg)
    hC hD hDβ (paperDegreeSlope_pos C hreg.1) (paperDegreeReserve_pos C hreg.1).le
    (paperUpperEta_pos C).le (paperUpperShift C) rfl
    (paper_upper_saddle_budget_identity C hreg)).comp tendsto_natCast_atTop_atTop

theorem eventually_paperAllocatedPilotBudget_le_one :
    ∀ᶠ n : ℕ in atTop, paperAllocatedPilotBudget C A C₀ C_D n ≤ 1 :=
  ((paperAllocatedPilotBudget_tends_zero C hreg A C₀ C_D hC hD hDβ hcoef).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le

end

end

end

end NearlyMinimax
