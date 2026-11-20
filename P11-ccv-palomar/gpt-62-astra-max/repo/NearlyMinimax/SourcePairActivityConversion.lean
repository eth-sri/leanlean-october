module

public import NearlyMinimax.FinePairRowActivity

@[expose] public section

/-! Actual source-scale absorption of the unit/coarse/fine pair caps.
No degree-dependent exponential is added to the local activity. -/
noncomputable section
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem source_pair_polynomial_exponential_le {D : ℝ} (hD : 0 ≤ D) :
    D^2*Real.exp (-D) ≤ 2 := by
  have hp := Real.pow_div_factorial_le_exp D hD 2
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one] at hp
  have hs : D^2 ≤ 2*Real.exp D := by linarith
  have h := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-D)).le
  have he : Real.exp D * Real.exp (-D) = 1 := by rw [← Real.exp_add]; simp
  calc _ ≤ 2*Real.exp D*Real.exp (-D) := h
       _ = 2 := by rw [mul_assoc,he,mul_one]

/-- The actual common cutoff cancels both scale powers and one exterior exponent. -/
theorem source_pair_coarse_scale_le {D N tau c0 : ℝ} (hD : 0 ≤ D)
    (hc0 : 1 ≤ c0) (htau : tau ≤ c0) :
    D^2*Real.exp (tau*D)*(N*Real.exp (-c0*D))^2 ≤ 2*N^2 := by
  have he : Real.exp ((tau-2*c0)*D) ≤ Real.exp (-D) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hp := source_pair_polynomial_exponential_le hD
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg D)
  have hbound : D^2*Real.exp ((tau-2*c0)*D) ≤ 2 := hm.trans hp
  have hid : D^2*Real.exp (tau*D)*(N*Real.exp (-c0*D))^2 =
      N^2*(D^2*Real.exp ((tau-2*c0)*D)) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [show (tau-2*c0)*D = tau*D+((2:ℕ):ℝ)*(-c0*D) by norm_num; ring, Real.exp_add]
    ring
  rw [hid]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound (sq_nonneg N)

end NearlyMinimax
