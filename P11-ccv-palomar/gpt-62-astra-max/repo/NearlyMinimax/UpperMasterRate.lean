module

public import NearlyMinimax.UpperRiskAllocation
public import NearlyMinimax.PairRateAlgebra


@[expose] public section

/-! The actual master pair-risk expression at the paper's rounded allocation. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem pairFluctuationScale_dyadic_eq {d n : ℕ} (hn : 0 < n) (L : ℕ) :
    pairFluctuationScale (d := d) n (2 ^ L) =
      Real.exp (-Real.log n / 2) +
        Real.exp (-Real.log n - d / 2 * (-Real.log 2 * L)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpair : Real.sqrt ((2 ^ L : ℕ) ^ d) / n =
      Real.exp (-Real.log n - d / 2 * (-Real.log 2 * L)) := by
    rw [Nat.cast_pow,  Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos (by positivity), Real.log_pow, Real.log_pow]
    rw [show n = Real.exp (Real.log n) from (Real.exp_log hnR).symm,
      ← Real.exp_sub, Real.log_exp]
    congr 1
    ring
  exact congrArg₂ (· + ·) (by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnR, ← Real.exp_neg]
    congr 1
    ring) hpair

def paperAllocatedMasterConstant {d : ℕ} (C : ModelConstants d) (B : ℝ) : ℝ :=
  B ^ 2 * d + 2 * (1 + Real.exp (d / 2 * Real.log 2))

variable {d : ℕ} {C : ModelConstants d} (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H)
include hH hreg

theorem eventually_paper_allocated_fluctuation_bound :
    ∀ᶠ n in atTop,
      pairFluctuationScale (d := d) n (2 ^ paperAllocatedFinestLevel C H n) ≤
        (1 + Real.exp (d / 2 * Real.log 2)) * paperAllocatedRiskScale C H n := by
  filter_upwards [(tendsto_natCast_atTop_atTop.eventually (eventually_paper_allocated_grid_guard hreg hH)), (tendsto_natCast_atTop_atTop.eventually (eventually_paper_allocated_root_noise_bound hreg hH)), eventually_ge_atTop 1] with n hgrid hroot hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hroot' := hroot.trans (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (paperUpperRootReserve_pos hreg).le) hlog)) ((Real.exp_pos _).le))
  rw [pairFluctuationScale_dyadic_eq (by omega)]
  exact (add_le_add hroot' ((by have h := dyadicRounded_noise_bound (hgrid.1) (Nat.cast_nonneg d) (Real.log (↑n)); rw [paperAllocatedLogSide, spatial_balance_rate hreg.1 hreg.2] at h; exact h : Real.exp (-Real.log ↑n - ↑d / 2 * dyadicRoundedLogSide (paperAllocatedLogSide C H ↑n)) ≤ Real.exp (↑d / 2 * Real.log 2) * paperAllocatedRiskScale C H ↑n))).trans_eq (by ring)

/-- U15 with every bandwidth factor and degree profile explicitly instantiated.
Only the already-derived nonnegative statistical budget W≤1 is needed here. -/
theorem eventually_paper_allocated_master_rate (B : ℝ) :
    let level := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H
    ∀ᶠ n : ℕ in atTop, ∀ W, 0 ≤ W → W ≤ 1 →
      (B * Real.sqrt d * paperAllocatedSide C H n *
        (dyadicPilotScale d (level n)) ^
          (-paperSpatialExponent C)) ^ 2 +
        pairFluctuationScale (d := d) n (2 ^ paperAllocatedFinestLevel C H n) * (1 + W) ≤
      paperAllocatedMasterConstant C B * paperAllocatedRiskScale C H n := by
  intro level
  filter_upwards [(tendsto_natCast_atTop_atTop.eventually (eventually_paper_allocated_grid_guard hreg hH)), eventually_paper_allocated_fluctuation_bound hreg hH] with n hgrid hfl
  intro W hW hW1
  have hmul := mul_le_mul_of_nonneg_left (paper_allocated_bias_square_bound hreg hgrid.1) (by positivity : 0 ≤ B ^ 2 * d)
  have hsq : (B * Real.sqrt d * paperAllocatedSide C H n *
      (dyadicPilotScale d (level n)) ^
        (-paperSpatialExponent C)) ^ 2 =
      (B ^ 2 * d) * (paperAllocatedSide C H n *
        (dyadicPilotScale d (level n)) ^
          (-paperSpatialExponent C)) ^ 2 := by
    simp [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  have hWmul := mul_le_mul_of_nonneg_left (show 1 + W ≤ 2 by linarith only [hW1]) (pairFluctuationScale_nonneg (d := d) n (2 ^ paperAllocatedFinestLevel C H n))
  unfold paperAllocatedMasterConstant <;> bound

theorem paper_allocated_risk_scale_upper :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      paperAllocatedRiskScale C H n ≤ A * paperUpperScale C n := by
  obtain ⟨_, A, _, hA, ha⟩ := paper_allocated_risk_scale_bracket hreg hH
  refine ⟨A, hA, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually ha, eventually_ge_atTop 2] with n hn hn2
  rw [paperUpperScale_eq_rateScale C hn2]
  exact hn.2

end NearlyMinimax
