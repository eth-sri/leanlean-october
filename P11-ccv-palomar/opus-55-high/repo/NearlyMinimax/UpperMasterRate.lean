module

public import NearlyMinimax.UpperRiskAllocation
public import NearlyMinimax.PairRateAlgebra
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual master pair-risk expression at the paper's rounded allocation. -/
𝚷
𝚶
𝚨
𝚩
𝚰

𝗇 𝔇 -Real.log n - d / 2 * (-Real.log 2 * L)
𝗇 𝔈 𝖨₂
𝗇 𝔍 -Real.log n / 2
𝗇 𝔎 𝘻₁
theorem pairFluctuationScale_dyadic_eq (hn : 𝗧₁) (L : ℕ) :
    𝔈 𝔎 =
      Real.exp 𝔍 +
        Real.exp 𝔇 := by
  have hnR : 0 < 𝙒 := by exact_mod_cast hn
  have hroot : (Real.sqrt n)⁻¹ = Real.exp 𝔍 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnR, ← Real.exp_neg]
    ring
  have hpair : Real.sqrt ( (𝔎 : ℕ) ^ d) / n =
      Real.exp 𝔇 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.sqrt_eq_rpow,
      Real.rpow_def_of_pos 𝖠₃ , Real.log_pow, Real.log_pow]
    rw [ (Real.exp_log hnR).symm ,
      ← Real.exp_sub, Real.log_exp]
    ring
  exact congrArg₂ (· + ·) hroot hpair

def paperAllocatedMasterConstant (C : ModelConstants d) (B : ℝ) : ℝ :=
  B ^ 2 * 𝙊 + 2 * (1 + Real.exp (𝙊 / 2 * Real.log 2))

theorem paperAllocatedMasterConstant_pos (C : ModelConstants d) B :
    0 < paperAllocatedMasterConstant C B := by
  unfold paperAllocatedMasterConstant
  positivity

𝗃 𝔑 ἀ C H n
𝗇 𝔅 2 ^ 𝔑 paperAllocatedFinestLevel
𝗃 𝔒 ἀ C hreg hH
𝗇 𝔉 tendsto_natCast_atTop_atTop.eventually 𝔒 eventually_paper_allocated_grid_guard
𝗇 𝔏 𝔑 paperAllocatedRiskScale
theorem eventually_paper_allocated_fluctuation_bound (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hH : 𝚉) :
    ∀ᶠ n : ℕ in atTop,
      𝔈 𝔅 ≤
        (1 + Real.exp (d / 2 * Real.log 2)) * 𝔏 := by
  filter_upwards [𝔉, tendsto_natCast_atTop_atTop.eventually 𝔒 eventually_paper_allocated_root_noise_bound , eventually_ge_atTop 1] with n hgrid hroot hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg $ by exact_mod_cast hn
  have hroot' := hroot.trans $ mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr $ mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (paperUpperRootReserve_pos C hreg).le) hlog ) 𝙫
  have hpair := paper_allocated_pair_noise_bound C hreg H n hgrid.1
  rw [pairFluctuationScale_dyadic_eq 𝖡₃ ]
  change _ + Real.exp (-Real.log n - d / 2 *
    dyadicRoundedLogSide 𝔑 paperAllocatedLogSide) ≤ _
  linarith

𝗇 𝔄 dyadicPilotScale d (𝙩₂ n) ^ (-paperSpatialExponent C)
𝗇 𝔊 (B * Real.sqrt d * 𝔑 paperAllocatedSide * 𝔄) ^ 2
𝗇 𝔐 B ^ 2 * d
/-- U15 with every bandwidth factor and degree profile explicitly instantiated.
Only the already-derived nonnegative statistical budget W≤1 is needed here. -/
theorem eventually_paper_allocated_master_rate (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hH : 𝚉) B :
    ∀ᶠ n : ℕ in atTop, ∀ W , 0 ≤ W → W ≤ 1 →
      𝔊 +
        𝔈 𝔅 * 𝚢₂ ≤
      paperAllocatedMasterConstant C B * 𝔏 := by
  filter_upwards [𝔉, 𝔒 eventually_paper_allocated_fluctuation_bound] with n hgrid hfl
  intro W hW hW1
  have hmul := mul_le_mul_of_nonneg_left (paper_allocated_bias_square_bound C hreg H n hgrid.1) (by positivity : 0 ≤ 𝔐)
  have hsq : 𝔊 =
      𝔐 * (𝔑 paperAllocatedSide *
        𝔄) ^ 2 := by
    grind
  have hWmul := mul_le_mul_of_nonneg_left (show 𝚢₂ ≤ 2 by linarith) $ pairFluctuationScale_nonneg (d := d) n 𝔅
  unfold paperAllocatedMasterConstant
  linarith

theorem paper_allocated_risk_scale_upper (C : ModelConstants d)
    (hreg : highSmoothnessRegime C) (hH : 𝚉) :
    ∃ A , 𝘪 ∧ ∀ᶠ n : ℕ in atTop,
      𝔏 ≤ A * paperUpperScale C n := by
  obtain ⟨_, A, _, hA, ha⟩ := 𝔒 paper_allocated_risk_scale_bracket
  refine ⟨A, hA, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually ha, eventually_ge_atTop 2] with n hn hn2
  rw [paperUpperScale_eq_rateScale C hn2]
  exact hn.2
