module

public import NearlyMinimax.UpperRiskAllocation
public import NearlyMinimax.PairRateAlgebra


@[expose] public section

/-! The actual master pair-risk expression at the paper's rounded allocation. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax

theorem pairFluctuationScale_dyadic_eq {d n : ℕ} (hn : 0 < n) (L : ℕ) :
    pairFluctuationScale (d := d) n ((2 : ℕ) ^ L) =
      Real.exp (-Real.log n / 2) +
        Real.exp (-Real.log n - (d : ℝ) / 2 * (-Real.log 2 * (L : ℝ))) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hroot : (Real.sqrt (n : ℝ))⁻¹ = Real.exp (-Real.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnR, ← Real.exp_neg]
    congr 1
    ring
  have hpair : Real.sqrt ((((2 : ℕ) ^ L : ℕ) : ℝ) ^ d) / (n : ℝ) =
      Real.exp (-Real.log n - (d : ℝ) / 2 * (-Real.log 2 * (L : ℝ))) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos (by positivity), Real.log_pow, Real.log_pow]
    rw [show (n : ℝ) = Real.exp (Real.log n) from (Real.exp_log hnR).symm,
      ← Real.exp_sub, Real.log_exp]
    congr 1
    ring
  exact congrArg₂ (· + ·) hroot hpair

variable {d : ℕ} (C : ModelConstants d)

def paperAllocatedMasterConstant (C : ModelConstants d) (B : ℝ) : ℝ :=
  B ^ 2 * (d : ℝ) + 2 * (1 + Real.exp ((d : ℝ) / 2 * Real.log 2))

theorem paperAllocatedMasterConstant_pos (C : ModelConstants d) (B : ℝ) :
    0 < paperAllocatedMasterConstant C B := by
  unfold paperAllocatedMasterConstant
  positivity

theorem eventually_paper_allocated_fluctuation_bound 
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∀ᶠ n : ℕ in atTop,
      pairFluctuationScale (d := d) n ((2 : ℕ) ^ paperAllocatedFinestLevel C H n) ≤
        (1 + Real.exp ((d : ℝ) / 2 * Real.log 2)) * paperAllocatedRiskScale C H n := by
  filter_upwards [(tendsto_natCast_atTop_atTop.eventually (eventually_paper_allocated_grid_guard C hreg hH)), (tendsto_natCast_atTop_atTop.eventually (eventually_paper_allocated_root_noise_bound C hreg hH)), eventually_ge_atTop (1 : ℕ)] with n hgrid hroot hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hr0 : Real.exp (-paperUpperRootReserve C * Real.log n) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (paperUpperRootReserve_pos C hreg).le) hlog)
  have hR : 0 ≤ paperAllocatedRiskScale C H n := (Real.exp_pos _).le
  rw [pairFluctuationScale_dyadic_eq (by omega : 0 < n)]
  change _ + Real.exp (-Real.log n - (d : ℝ) / 2 *
    dyadicRoundedLogSide (paperAllocatedLogSide C H n)) ≤ _
  exact (add_le_add (hroot.trans (mul_le_mul_of_nonneg_right hr0 hR)) (paper_allocated_pair_noise_bound C hreg H n hgrid.1)).trans_eq (by ring)

/-- U15 with every bandwidth factor and degree profile explicitly instantiated.
Only the already-derived nonnegative statistical budget W≤1 is needed here. -/
theorem eventually_paper_allocated_master_rate 
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ W : ℝ, 0 ≤ W → W ≤ 1 →
      (B * Real.sqrt (d : ℝ) * paperAllocatedSide C H n *
        (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
          (-paperSpatialExponent C)) ^ 2 +
        pairFluctuationScale (d := d) n ((2 : ℕ) ^ paperAllocatedFinestLevel C H n) * (1 + W) ≤
      paperAllocatedMasterConstant C B * paperAllocatedRiskScale C H n := by
  filter_upwards [(tendsto_natCast_atTop_atTop.eventually (eventually_paper_allocated_grid_guard C hreg hH)), eventually_paper_allocated_fluctuation_bound C hreg hH] with n hgrid hfl
  intro W hW hW1
  have hmul := mul_le_mul_of_nonneg_left (paper_allocated_bias_square_bound C hreg H n hgrid.1) (by positivity : 0 ≤ B ^ 2 * (d : ℝ))
  have hsq : (B * Real.sqrt (d : ℝ) * paperAllocatedSide C H n *
      (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
        (-paperSpatialExponent C)) ^ 2 =
      (B ^ 2 * (d : ℝ)) * (paperAllocatedSide C H n *
        (dyadicPilotScale d (paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n)) ^
          (-paperSpatialExponent C)) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  rw [← hsq] at hmul
  unfold paperAllocatedMasterConstant
  nlinarith only [hmul, (mul_le_mul_of_nonneg_left (show 1 + W ≤ 2 by linarith only [hW1]) (pairFluctuationScale_nonneg (d := d) n ((2 : ℕ) ^ paperAllocatedFinestLevel C H n))), hfl]

theorem paper_allocated_risk_scale_upper (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) {H : ℝ} (hH : 0 < H) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop,
      paperAllocatedRiskScale C H n ≤ A * paperUpperScale C n := by
  obtain ⟨_, A, _, hA, ha⟩ := paper_allocated_risk_scale_bracket C hreg hH
  refine ⟨A, hA, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually ha, eventually_ge_atTop (2 : ℕ)] with n hn hn2
  rw [paperUpperScale_eq_rateScale C hn2]
  exact hn.2

end NearlyMinimax
