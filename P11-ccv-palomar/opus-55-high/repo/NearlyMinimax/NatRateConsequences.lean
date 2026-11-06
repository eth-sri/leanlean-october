module

public import NearlyMinimax.Rates
public import RoughRegime.Macro

𝗍

/-! Analytic consequences for the paper's natural sample-size sequence. -/
𝚷
𝚶
𝚨

𝗇 𝔄 -lam*Real.log n
𝗇 𝔅 n^(-lam-epsilon)
theorem polynomial_bounds_nat_of_rateBracket
    (hk : 0 < kappa) (h : HasNatRateBracket risk lam kappa a Gamma) :
    ∃ c A , 0 < c ∧ 0 < A ∧ ∀ epsilon , 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c*𝔅 ≤ risk n ∧ risk n ≤ A*n^(-lam) := by
  obtain ⟨c,A,hc,hA,hb⟩ := h
  refine ⟨c,A,hc,hA,fun epsilon he => ?_⟩
  have hu := tendsto_stretched_log_factor hk $ a+Gamma
  filter_upwards [hb,tendsto_natCast_atTop_atTop.eventually
    $ eventually_correction_between_powers kappa a he ,
    tendsto_natCast_atTop_atTop.eventually
      $ hu.eventually $ gt_mem_nhds (by norm_num : (0 : ℝ)<1) ,
    tendsto_natCast_atTop_atTop.eventually $ eventually_gt_atTop (1 : ℝ) ]
    with n hn hlow hupp hn1
  have hn0 : 0 < (n : ℝ) := by linarith only [hn1]
  constructor
  · apply le_trans _ hn.1
    rw [rateScale_eq_base_mul_correction]
    have hr : 𝔅 = Real.exp 𝔄*n^(-epsilon) := by
      rw [Real.rpow_def_of_pos hn0,Real.rpow_def_of_pos hn0,←Real.exp_add]
      ring
    rw [hr]
    simp only [←mul_assoc]
    exact mul_le_mul_of_nonneg_left hlow.1 (mul_pos hc $ Real.exp_pos _ ).le
  · apply le_trans hn.2
    rw [rateScale_eq_base_mul_correction,Real.rpow_def_of_pos hn0]
    calc
      _ ≤ A*(Real.exp 𝔄*1) := by gcongr
      _ = _ := by ring
