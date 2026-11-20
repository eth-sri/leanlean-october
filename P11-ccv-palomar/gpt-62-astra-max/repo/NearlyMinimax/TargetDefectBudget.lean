module

public import NearlyMinimax.LocalCutoffAlgebra


@[expose] public section

/-! Genuine cutoff comparisons for selected and omitted target rows. -/
noncomputable section
namespace NearlyMinimax

variable {d : ℕ} (hd : d ≠ 0) {N mu : ℝ}

include hd in
theorem target_cutoff_defect_budget_le (hN : 0 < N) (hmu : 0 < mu) {j : ℕ}
    (hT : 1 ≤ N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d))
    (hTN : N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) ≤ N) :
    let logScale := Real.log (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d))
    (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) ^ (-(d : ℝ)) *
      (1 + logScale) ^ j ≤
        N ^ (-(d : ℝ)) / mu ^ j := by
  intro logScale
  have hH : 0 < 1 + Real.log N := by linarith [Real.log_nonneg (hT.trans hTN)]
  have hlog : 1 + logScale ≤ 1 + Real.log N := by
    bound
  have hlog0 : 0 ≤ 1 + logScale :=
    by bound
  have hp : 0 ≤ (N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d)) ^ (-(d : ℝ)) :=
    by positivity
  have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog j) hp
  exact h.trans_eq (target_cutoff_inverse_budget hd hN hmu hH j)

include hd in
theorem omitted_target_inverse_budget_ge_one (hN1 : 1 ≤ N) (hmu : 0 < mu) {j : ℕ}
    (hT : N * (mu * (1 + Real.log N)) ^ ((j : ℝ) / d) < 1) :
    1 ≤ N ^ (-(d : ℝ)) / mu ^ j := by
  have hN : 0 < N := by positivity
  have hH : 0 < 1 + Real.log N := by linarith [Real.log_nonneg hN1]
  rw [← target_cutoff_inverse_budget hd hN hmu hH j]
  have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) hT.le
    (neg_nonpos.mpr (Nat.cast_nonneg d))
  bound

end NearlyMinimax
