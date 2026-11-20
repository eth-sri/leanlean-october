module

public import NearlyMinimax.LowSmoothnessPrior

@[expose] public section

/-! Raw-density normalization for the manuscript's high-smoothness prior.
The mass-concentration guard is a scalar event; density normalization and
original density bounds are consequences proved here. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {d : ℕ} {C : ModelConstants d} {M cm : ℝ} (p : Covariate d → ℝ) {m : ℝ} (hM : 2 ≤ M)
    (hcm : 0 ≤ cm) (hcmU : cm ≤ 1 / C.densityUpper)

include hM hcm hcmU in
theorem high_raw_mass_lower
    (hm : |m - 1| ≤ cm / M) : 1 / 2 ≤ m := by
  have hcm1 : cm ≤ 1 := by
    apply hcmU.trans
    exact (div_le_one (lt_trans (by norm_num) C.one_lt_densityUpper)).mpr C.one_lt_densityUpper.le
  have hhalf : cm / M ≤ 1 / 2 := by
    bound
  have := (abs_le.mp hm).1
  linarith

theorem high_normalized_density_interval {p : ℝ} (hM : 2 ≤ M) (hcm : 0 ≤ cm)
    (hcmU : cm ≤ 1 / C.densityUpper) (hm : |m - 1| ≤ cm / M)
    (hp : C.densityLower + 1 / M ≤ p ∧ p ≤ C.densityUpper - 1 / M) :
    C.densityLower ≤ p / m ∧ p / m ≤ C.densityUpper := by
  have hU : 0 < C.densityUpper := lt_trans (by norm_num) C.one_lt_densityUpper
  have hM0 : 0 < M := by linarith
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num) (high_raw_mass_lower hM hcm hcmU hm)
  have hcmprod : C.densityUpper * cm ≤ 1 := by
    linarith [(le_div_iff₀ hU).mp hcmU]
  have hLcm  := (mul_le_mul_of_nonneg_right (C.densityLower_lt_one.le.trans C.one_lt_densityUpper.le) hcm).trans hcmprod
  have hmass := abs_le.mp hm
  have hmulU : C.densityUpper * (cm / M) ≤ 1 / M := by
    grind [div_le_div_of_nonneg_right hcmprod hM0.le]
  have hmulL : C.densityLower * (cm / M) ≤ 1 / M := by
    grind [div_le_div_of_nonneg_right hLcm hM0.le]
  constructor
  · apply (le_div_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass.2 C.densityLower_pos.le]
  · apply (div_le_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass.1 hU.le]

def highRawDensityMass : ℝ :=
  ∫ x, p x ∂cubeVolume d

def highNormalizedDensity (x : Covariate d) : ℝ :=
  p x / highRawDensityMass p

theorem highRawDensity_integrable
    (hM : 0 < M) {p : Covariate d → ℝ} (hp : Measurable p)
    (hb : ∀ᵐ x ∂cubeVolume d,
      C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M) :
    Integrable p (cubeVolume d) := by
  have hfin : IsFiniteMeasure (cubeVolume d) := by
    constructor
    rw [cubeVolume_univ]
    exact ENNReal.one_lt_top
  have hbound : ∀ᵐ x ∂cubeVolume d, ‖p x‖ ≤ C.densityUpper := by
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [C.densityLower_pos, one_div_pos.mpr hM])]
    linarith [one_div_pos.mpr hM]
  exact (integrable_const C.densityUpper).mono' hp.aestronglyMeasurable hbound

theorem highNormalizedDensity_normalized {p : Covariate d → ℝ}
    (hp : Integrable p (cubeVolume d)) (hp0 : 0 ≤ᵐ[cubeVolume d] p)
    (hm : 0 < highRawDensityMass p) :
    (∫⁻ x, ENNReal.ofReal (highNormalizedDensity p x) ∂cubeVolume d) = 1 := by
  unfold highNormalizedDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (hp.div_const _) (hp0.mono
    (fun x hx => div_nonneg hx hm.le)), integral_div]
  change ENNReal.ofReal (highRawDensityMass p / highRawDensityMass p) = 1
  simp [div_self hm.ne', ENNReal.ofReal_one]

/-- Actual ternary regression model with a normalized, nonuniform design. -/
abbrev normalizedDensityTernaryParameter {F : Covariate d → ℝ}
    {a V : ℝ} (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) : RegressionParameter d :=
  ternaryParameter (highNormalizedDensity p) hF ha hp



end NearlyMinimax
