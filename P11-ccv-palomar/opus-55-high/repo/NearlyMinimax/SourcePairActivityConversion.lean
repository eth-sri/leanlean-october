module

public import NearlyMinimax.FinePairRowActivity
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Actual source-scale absorption of the unit/coarse/fine pair caps.
No degree-dependent exponential is added to the local activity. -/
𝚨
𝚩
𝚰

theorem source_pair_polynomial_exponential_le (hD : 0 ≤ D) :
    𝘔*Real.exp (-D) ≤ 2 := by
  have hp := Real.pow_div_factorial_le_exp D hD 2
  have hs : 𝘔 ≤ 2*Real.exp D := 𝖡₄
  have h := mul_le_mul_of_nonneg_right hs (Real.exp_pos $ -D ).le
  have he : Real.exp D * Real.exp (-D) = 1 := by rw [← Real.exp_add]; simp
  linarith

/-- The actual common cutoff cancels both scale powers and one exterior exponent. -/
theorem source_pair_coarse_scale_le (hD : 0 ≤ D)
    (hc0 : 1 ≤ c0) (htau : tau ≤ c0) :
    𝘔*Real.exp (tau*D)*𝗐^2 ≤ 2*𝘚₂ := by
  have he : Real.exp 𝙦₂ ≤ Real.exp (-D) :=
    Real.exp_le_exp.mpr 𝖥₃
  have hp := source_pair_polynomial_exponential_le hD
  have hm := mul_le_mul_of_nonneg_left he $ sq_nonneg D
  have hid : 𝘔*Real.exp (tau*D)*𝗐^2 =
      𝘚₂*(𝘔*Real.exp 𝙦₂) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [show 𝙦₂ = tau*D+ 2 *(-c0*D) by ring, Real.exp_add]
    ring
  nlinarith
