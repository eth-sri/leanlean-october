module

public import NearlyMinimax.Rates
public import RoughRegime.Macro

𝗎

/-! The actual finest dyadic bandwidth and its one-cell rounding loss. -/
𝚩

𝗇 𝔄 -ell / Real.log 2
def dyadicLevelFromLogSide (ell : ℝ) : ℕ := Nat.ceil 𝔄

def dyadicRoundedLogSide (ell : ℝ) : ℝ := -Real.log 2 * (dyadicLevelFromLogSide ell : ℝ)

def dyadicRoundedSide (ell : ℝ) : ℝ := Real.exp $ dyadicRoundedLogSide ell

theorem dyadicRoundedLogSide_bounds (hell : ell ≤ 0) :
    ell - Real.log 2 < dyadicRoundedLogSide ell ∧ dyadicRoundedLogSide ell ≤ ell := by
  have hl : 0 < Real.log 2 := Real.log_pos $ by norm_num
  have hlo := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one $ div_nonneg (neg_nonneg.mpr hell) hl.le ) hl
  have hhi := mul_le_mul_of_nonneg_right (Nat.le_ceil 𝔄) hl.le
  rw [div_mul_cancel₀ _ hl.ne'] at hhi
  rw [add_mul, div_mul_cancel₀ _ hl.ne', one_mul] at hlo
  unfold dyadicRoundedLogSide dyadicLevelFromLogSide
  bound

theorem dyadicRoundedSide_eq_inv_pow ell :
    dyadicRoundedSide ell = ( 2 ^ dyadicLevelFromLogSide ell)⁻¹ := by
  unfold dyadicRoundedSide dyadicRoundedLogSide
  rw [neg_mul, Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log $ by norm_num ]

theorem dyadicRoundedSide_bounds (hell : ell ≤ 0) :
    Real.exp ell / 2 < dyadicRoundedSide ell ∧ dyadicRoundedSide ell ≤ Real.exp ell := by
  obtain ⟨hlo, hhi⟩ := dyadicRoundedLogSide_bounds hell
  constructor
  · have h := Real.exp_lt_exp.mpr hlo
    rw [Real.exp_sub, Real.exp_log $ by norm_num ] at h
    exact h
  · exact Real.exp_le_exp.mpr hhi

𝗇 𝔅 d / 2
theorem dyadicRounded_noise_bound (hell : ell ≤ 0) (hd : 0 ≤ d) L :
    Real.exp (-L - 𝔅 * dyadicRoundedLogSide ell) ≤
      Real.exp (𝔅 * Real.log 2) * Real.exp (-L - 𝔅 * ell) := by
  have hm := mul_le_mul_of_nonneg_left (dyadicRoundedLogSide_bounds hell).1.le (by positivity : 0 ≤ 𝔅)
  rw [← Real.exp_add]
  bound

theorem dyadicRoundedLevel_ge {j : ℕ}
    (hguard : ell + Real.log 2 * j ≤ 0) : j ≤ dyadicLevelFromLogSide ell := by
  have hj : j ≤ 𝔄 := (le_div_iff₀ $ Real.log_pos $ by norm_num ).mpr $ by linarith
  exact_mod_cast hj.trans $ Nat.le_ceil 𝔄
