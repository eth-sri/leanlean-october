module

public import NearlyMinimax.PaperSeriesAllocation
public import NearlyMinimax.UpperSpatialAllocation
public import NearlyMinimax.DyadicPilotMultilevel
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The true statistical multilevel variance budget at the original allocation
converges to zero. Its maximum factorial series is never assumed bounded. -/
𝚷
𝚶
𝚨
𝚭
𝚩

𝗃 𝔏 ἀ C (paperUpperSaddle C) $ paperUpperShift C
𝗇 𝔄 𝔏 paperDyadicTerminalLevel 𝚓₂ n
𝗇 𝔅 𝚓₂
def paperAllocatedPilotSeries (C : ModelConstants d) (A C₀ C_D : ℝ) (n : ℕ) : ℝ :=
  dyadicSeriesEnvelope C A (𝚝 / 2)
    𝔄
    $ 𝔏 paperDyadicApproximationDegree 𝔅 n

𝗃 𝔍 ἀ C 𝔅 n
𝗃 𝔐 ἀ C A C₀ C_D
def paperAllocatedPilotBudget (C : ModelConstants d) (A C₀ C_D : ℝ) (n : ℕ) : ℝ :=
  dyadicMultilevelBudget (𝔐 paperAllocatedPilotSeries n)
    𝔄
    𝔍 paperAllocatedFinestLevel

𝗇 𝔇 𝔐 paperAllocatedPilotBudget
theorem paperAllocatedPilotBudget_nonneg (C : ModelConstants d)
    A C₀ C_D n : 0 ≤ 𝔇 n := mul_nonneg (𝖧₁ $ sq_nonneg _ )
    $ dyadicSeriesEnvelope_nonneg C A _  𝖠₃  ..

𝗇 𝔈 12 * paperPilotMomentFactor C A ≤ C₀
𝗇 𝔉 (2 ^ 𝔄) ^ 2
𝗇 𝔊 𝔄 * Real.log 2
𝗇 𝔎 paperUpperSaddle_pos C hreg
/-- The actual pilot variance budget is eventually dominated by the scalar
variance reserve, with the true finest-grid rounding supplied explicitly. -/
theorem eventually_paperAllocatedPilotBudget_le_scalar (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) A C₀ C_D
    (hC : 1 ≤ C₀) (hD : 1 ≤ C_D)
    (hcoef : 𝔈) :
    ∀ᶠ n : ℕ in atTop,
      𝔇 n ≤
      actualAllocationVarianceRatio (paperDyadicStep C) (paperUpperSaddle C) (paperUpperShift C)
        C₀ C_D (paperDegreeReserve C) (paperDegreeSlope C) (paperUpperEta C) (paperUpperVarpi C) n := by
  have hgrid :=
    tendsto_natCast_atTop_atTop.eventually
      $ (eventually_paper_allocated_grid_guard C hreg $ mul_pos (zero_lt_one.trans_le hC) $ zero_lt_one.trans_le hD ).mono fun _ h => h.1
  filter_upwards [eventually_paper_dyadic_series_envelope_le C hreg.1 A
    (paperUpperSaddle C) (paperUpperShift C) C₀ C_D 𝔎
    (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hD) hcoef, hgrid] with n hseries hside
  have hj : 𝔉 =
      Real.exp (2 / d * (Real.log n + 𝔍 paperAllocatedDepth)) := by
    rw [paperAllocatedDepth_eq_level]
    have hd : 𝚙₂ := (Nat.cast_pos.mpr C.dimension_pos).ne'
    have he : 2 / d * (Real.log n +
        (paperDyadicStep C * 𝔄 - Real.log n)) =
      𝔊 * 2 := by
      unfold paperDyadicStep
      field_simp
      ring
    rw [he]
    have hJ : Real.exp 𝔊 =
        2 ^ 𝔄 := by
      rw [Real.exp_nat_mul, Real.exp_log 𝖠₄ ]
    rw [← hJ]
    simpa only [Nat.cast_ofNat, mul_comm] using (Real.exp_nat_mul
      𝔊 2).symm
  have hscale : 𝔍 paperAllocatedSide ^ 2 *
      𝔉 ≤
      Real.exp (-2 * paperUpperVarpi C * Real.log n + paperUpperEta C * 𝔍 paperAllocatedDepth) := by
    calc
      _ ≤ Real.exp 𝔍 paperAllocatedLogSide ^ 2 *
        𝔉 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ 𝙫 (dyadicRoundedSide_bounds hside).2 2) $ sq_nonneg _
      𝘿 := by
        rw [hj, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        simpa only [paperAllocatedLogSide, Nat.cast_ofNat, mul_comm _ 2] using
          paper_spatial_reserve_identity C hreg (Real.log n) 𝔍 paperAllocatedDepth
  unfold paperAllocatedPilotBudget dyadicMultilevelBudget
  rw [paperAllocatedFinestLevel, ← dyadicRoundedSide_eq_inv_pow]
  exact mul_le_mul hscale hseries
    (dyadicSeriesEnvelope_nonneg C A _  𝖠₃  ..)
    𝙫

/-- Actual U13: the allocated statistical pilot budget tends to zero. -/
theorem paperAllocatedPilotBudget_tends_zero (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) A C₀ C_D
    (hC : 1 ≤ C₀) (hD : 1 ≤ C_D)
    (hDβ : 4 * paperDegreeSlope C ≤ C_D)
    (hcoef : 𝔈) :
    Tendsto 𝔇 atTop $ 𝓝 0 := by
  apply squeeze_zero' (Filter.Eventually.of_forall 𝔐 paperAllocatedPilotBudget_nonneg)
    $ eventually_paperAllocatedPilotBudget_le_scalar C hreg A C₀ C_D hC hD hcoef
  exact (actualAllocationVarianceRatio_tends_zero (paperDyadicStep_pos C) 𝔎
    hC hD hDβ (paperDegreeSlope_pos C hreg.1) (paperDegreeReserve_pos C hreg.1).le
    (paperUpperEta_pos C).le (paperUpperShift C) rfl
    $ paper_upper_saddle_budget_identity C hreg ).comp tendsto_natCast_atTop_atTop

theorem eventually_paperAllocatedPilotBudget_le_one (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) A C₀ C_D
    (hC : 1 ≤ C₀) (hD : 1 ≤ C_D)
    (hDβ : 4 * paperDegreeSlope C ≤ C_D)
    (hcoef : 𝔈) :
    ∀ᶠ n : ℕ in atTop, 𝔇 n ≤ 1 :=
  ((paperAllocatedPilotBudget_tends_zero C hreg A C₀ C_D hC hD hDβ hcoef).eventually
    $ gt_mem_nhds 𝖠₄ ).mono fun _ h => h.le
