module

public import NearlyMinimax.Rates

@[expose] public section

/-! Analytic consequences for the paper's natural sample-size sequence. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax

theorem polynomial_bounds_nat_of_rateBracket {risk : ℕ → ℝ} {lam kappa a Gamma : ℝ}
    (hk : 0 < kappa) (h : HasNatRateBracket risk lam kappa a Gamma) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c*(n : ℝ)^(-lam-epsilon) ≤ risk n ∧ risk n ≤ A*(n : ℝ)^(-lam) := by
  obtain ⟨c,A,hc,hA,hb⟩ := h
  refine ⟨c,A,hc,hA,fun epsilon he => ?_⟩
  have hu := tendsto_stretched_log_factor hk (a+Gamma)
  filter_upwards [hb,tendsto_natCast_atTop_atTop.eventually
    (eventually_correction_between_powers kappa a he),
    tendsto_natCast_atTop_atTop.eventually
      (hu.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))),
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
    with n hn hlow hupp hn1
  have hn0 : 0 < (n : ℝ) := by linarith only [hn1]
  have hp : 0 < Real.exp (-lam*Real.log n) := Real.exp_pos _
  constructor
  · apply le_trans _ hn.1
    rw [rateScale_eq_base_mul_correction]
    have hr : (n : ℝ)^(-lam-epsilon) = Real.exp (-lam*Real.log n)*(n : ℝ)^(-epsilon) := by
      rw [Real.rpow_def_of_pos hn0,Real.rpow_def_of_pos hn0,←Real.exp_add]
      congr 1
      ring
    rw [hr]
    simp only [←mul_assoc]
    exact mul_le_mul_of_nonneg_left hlow.1 (mul_pos hc hp).le
  · apply le_trans hn.2
    rw [rateScale_eq_base_mul_correction,Real.rpow_def_of_pos hn0]
    rw [mul_comm (Real.log (n : ℝ)) (-lam)]
    calc
      _ ≤ A*(Real.exp (-lam*Real.log n)*1) := by gcongr
      _ = _ := by ring

end NearlyMinimax
