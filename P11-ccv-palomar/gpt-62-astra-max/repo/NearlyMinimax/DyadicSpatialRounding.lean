module

public import NearlyMinimax.Rates

@[expose] public section

/-! The actual finest dyadic bandwidth and its one-cell rounding loss. -/
noncomputable section
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

section
variable (ell : ℝ)

def dyadicLevelFromLogSide : ℕ := Nat.ceil (-ell / Real.log 2)

def dyadicRoundedLogSide : ℝ := -Real.log 2 * (dyadicLevelFromLogSide ell)

def dyadicRoundedSide : ℝ := Real.exp (dyadicRoundedLogSide ell)

end

variable {ell d : ℝ} (hell : ell ≤ 0)

include hell in
theorem dyadicRoundedLogSide_bounds :
    ell - Real.log 2 < dyadicRoundedLogSide ell ∧ dyadicRoundedLogSide ell ≤ ell := by
  have hl : 0 < Real.log 2 := by positivity
  have hlo := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one (div_nonneg (neg_nonneg.mpr hell) hl.le)) hl
  have hhi := mul_le_mul_of_nonneg_right (Nat.le_ceil (-ell / Real.log 2)) hl.le
  rw [div_mul_cancel₀ _ hl.ne'] at hhi
  rw [add_mul, div_mul_cancel₀ _ hl.ne', one_mul] at hlo
  grind [dyadicRoundedLogSide, dyadicLevelFromLogSide]

theorem dyadicRoundedSide_eq_inv_pow (ell : ℝ) :
    dyadicRoundedSide ell = (2 ^ dyadicLevelFromLogSide ell)⁻¹ := by
  unfold dyadicRoundedSide dyadicRoundedLogSide
  rw [neg_mul, Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]

include hell in
theorem dyadicRoundedSide_bounds :
    Real.exp ell / 2 < dyadicRoundedSide ell ∧ dyadicRoundedSide ell ≤ Real.exp ell := by
  obtain ⟨hlo, hhi⟩ := dyadicRoundedLogSide_bounds hell
  constructor
  · have h := Real.exp_lt_exp.mpr hlo
    rw [Real.exp_sub, Real.exp_log (by norm_num)] at h
    exact h
  · exact Real.exp_le_exp.mpr hhi

include hell in
theorem dyadicRounded_noise_bound (hd : 0 ≤ d) (L : ℝ) :
    Real.exp (-L - d / 2 * dyadicRoundedLogSide ell) ≤
      Real.exp (d / 2 * Real.log 2) * Real.exp (-L - d / 2 * ell) := by
  have hm := mul_le_mul_of_nonneg_left ((dyadicRoundedLogSide_bounds hell).1.le) (by positivity : 0 ≤ d / 2)
  rw [← Real.exp_add]
  bound

theorem dyadicRoundedLevel_ge {j : ℕ}
    (hguard : ell + Real.log 2 * j ≤ 0) : j ≤ dyadicLevelFromLogSide ell := by
  have hl : 0 < Real.log 2 := by positivity
  have hj : j ≤ -ell / Real.log 2 := (le_div_iff₀ hl).mpr (by linarith only [hguard])
  exact_mod_cast hj.trans (Nat.le_ceil _)

end NearlyMinimax
