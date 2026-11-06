module

public import NearlyMinimax.Rates

@[expose] public section

/-! The actual finest dyadic bandwidth and its one-cell rounding loss. -/
noncomputable section
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

def dyadicLevelFromLogSide ell  := Nat.ceil (-ell / Real.log 2)

def dyadicRoundedLogSide ell  := -Real.log 2 * (dyadicLevelFromLogSide ell : ℝ)

def dyadicRoundedSide ell  := Real.exp (dyadicRoundedLogSide ell)

theorem dyadicRoundedLogSide_bounds {ell } (hell : ell ≤ 0) :
    ell - Real.log 2 < dyadicRoundedLogSide ell ∧ dyadicRoundedLogSide ell ≤ ell := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq  := div_nonneg (neg_nonneg.mpr hell) hl.le
  have hlo := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hq) hl
  have hhi := mul_le_mul_of_nonneg_right (Nat.le_ceil (-ell / Real.log 2)) hl.le
  rw [div_mul_cancel₀ _ hl.ne'] at hhi
  rw [add_mul, div_mul_cancel₀ _ hl.ne', one_mul] at hlo
  unfold dyadicRoundedLogSide dyadicLevelFromLogSide
  constructor <;> linarith only [hlo, hhi]

theorem dyadicRoundedSide_eq_inv_pow ell :
    dyadicRoundedSide ell = (2 ^ dyadicLevelFromLogSide ell)⁻¹ := by
  unfold dyadicRoundedSide dyadicRoundedLogSide
  rw [neg_mul, Real.exp_neg, mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]

theorem dyadicRoundedSide_bounds {ell } (hell : ell ≤ 0) :
    Real.exp ell / 2 < dyadicRoundedSide ell ∧ dyadicRoundedSide ell ≤ Real.exp ell := by
  obtain ⟨hlo, hhi⟩ := dyadicRoundedLogSide_bounds hell
  constructor
  · have h := Real.exp_lt_exp.mpr hlo
    rw [Real.exp_sub, Real.exp_log (by norm_num)] at h
    exact h
  · exact Real.exp_le_exp.mpr hhi

theorem dyadicRounded_noise_bound {ell d } (hell : ell ≤ 0) (hd : 0 ≤ d) L :
    Real.exp (-L - d / 2 * dyadicRoundedLogSide ell) ≤
      Real.exp (d / 2 * Real.log 2) * Real.exp (-L - d / 2 * ell) := by
  have hlo := (dyadicRoundedLogSide_bounds hell).1.le
  have hm := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ d / 2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hm]

theorem dyadicRoundedLevel_ge {ell } {j : ℕ}
    (hguard : ell + Real.log 2 * j ≤ 0) : j ≤ dyadicLevelFromLogSide ell := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj : (j : ℝ) ≤ -ell / Real.log 2 := (le_div_iff₀ hl).mpr (by linarith only [hguard])
  exact_mod_cast hj.trans (Nat.le_ceil (-ell / Real.log 2))

end NearlyMinimax
