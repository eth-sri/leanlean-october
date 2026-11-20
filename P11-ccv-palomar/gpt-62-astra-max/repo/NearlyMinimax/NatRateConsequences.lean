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
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ epsilon, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        c*n^(-lam-epsilon) ≤ risk n ∧ risk n ≤ A*n^(-lam) := by
  obtain ⟨c,A,hc,hA,hb⟩ := h
  refine ⟨c,A,hc,hA,fun epsilon he => ?_⟩
  filter_upwards [hb,tendsto_natCast_atTop_atTop.eventually
    (eventually_correction_between_powers kappa a he),
    tendsto_natCast_atTop_atTop.eventually
      ((tendsto_stretched_log_factor hk (a+Gamma)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))),
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop 1)]
    with n hn hlow hupp hn1
  have hn0 : 0 < (n : ℝ) := by positivity
  constructor
  · apply le_trans _ hn.1
    rw [rateScale_eq_base_mul_correction]
    have hr : n^(-lam-epsilon) = Real.exp (-lam*Real.log n)*n^(-epsilon) := by
      rw [Real.rpow_def_of_pos hn0,Real.rpow_def_of_pos hn0,←Real.exp_add]
      ring
    rw [hr]
    bound
  · apply le_trans hn.2
    rw [rateScale_eq_base_mul_correction,Real.rpow_def_of_pos hn0, mul_comm (Real.log n) (-lam)]
    bound

end NearlyMinimax
