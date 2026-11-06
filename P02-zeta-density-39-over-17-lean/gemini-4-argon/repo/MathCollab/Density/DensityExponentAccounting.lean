module
public import MathCollab.Density.DetectorAdmissibility

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Exact exponent accounting for normalized polynomial heights. -/
theorem normalizedHeight_quotient {T L σ η : ℝ} (hT : 0 < T) (hL : 0 < L)
    (m k : ℕ) :
    L^m/(L^σ*T^(-2*η))^k = L^((m : ℝ)-σ*k)*T^(2*η*k) := by
  rw [mul_pow, div_mul_eq_div_div, ← Real.rpow_mul_natCast hL.le,
    ← Real.rpow_natCast L m, ← Real.rpow_sub hL,
    ← Real.rpow_mul_natCast hT.le, div_eq_mul_inv, ← Real.rpow_neg hT.le]
  congr 1
  congr 1
  ring

/-- For q in [0,1/2], the ambient logarithmic enlargement costs at most one log. -/
theorem densityAmbient_small_rpow {T q : ℝ} (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T)
    (_hq : 0 ≤ q) (hq' : q ≤ 1/2) :
    (densityAmbient T)^q ≤ 32*T^q*Real.log T := by
  have hTpos : 0 < T := by linarith
  have hlogpos : 0 < Real.log T := by linarith
  have hc : (32 : ℝ)^q ≤ 32 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 32) (show q ≤ 1 by linarith)
  have hl : ((Real.log T)^2)^q ≤ Real.log T := by
    rw [← Real.rpow_natCast_mul hlogpos.le]
    have hh := Real.rpow_le_rpow_of_exponent_le hlog (show (2 : ℝ)*q ≤ 1 by linarith)
    simpa only [Real.rpow_one, Nat.cast_ofNat] using hh
  rw [densityAmbient, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by norm_num) hTpos.le]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity)) hl (by positivity) (by positivity)


/-- The remaining four logarithms cost exactly 2eta, independently of sigma. -/
theorem density_logarithms_eventually {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, (Real.log T)^4 ≤ T^(2*η) := by
  have hl := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (show 0 < 2*η by positivity)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (1 : ℝ), hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with T hT hh
  exact ((div_lt_iff₀ (by positivity : 0 < T^(2*η))).mp hh).le.trans_eq (one_mul _)


