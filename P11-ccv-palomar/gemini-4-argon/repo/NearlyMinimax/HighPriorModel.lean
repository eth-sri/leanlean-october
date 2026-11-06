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

theorem high_raw_mass_lower  (C : ModelConstants d) (M cm m )
    (hM : 2 ≤ M) (hcm : 0 ≤ cm) (hcmU : cm ≤ 1 / C.densityUpper)
    (hm : |m - 1| ≤ cm / M) : 1 / 2 ≤ m := by
  have : cm ≤ 1 := by
    apply hcmU.trans
    exact (div_le_one (lt_trans (by norm_num) C.one_lt_densityUpper)).mpr C.one_lt_densityUpper.le
  have : cm / M ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith
  have := (abs_le.mp hm).1
  linarith

def highRawDensityMass  (p : Covariate d → ℝ) : ℝ :=
  ∫ x, p x ∂cubeVolume d

def highNormalizedDensity  (p : Covariate d → ℝ) (x : Covariate d) : ℝ :=
  p x / highRawDensityMass p

theorem highNormalizedDensity_measurable {d : ℕ} (p : Covariate d → ℝ)
    (hp : Measurable p) : Measurable (highNormalizedDensity p) := hp.div_const _

theorem highNormalizedDensity_normalized  (p )
    (hp : Integrable p (cubeVolume d)) (hp0 : 0 ≤ᵐ[cubeVolume d] p)
    (hm : 0 < highRawDensityMass p) :
    (∫⁻ x, ENNReal.ofReal (highNormalizedDensity p x) ∂cubeVolume d) = 1 := by
  unfold highNormalizedDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (hp.div_const _) (hp0.mono
    (fun x hx => div_nonneg hx hm.le)), integral_div]
  change ENNReal.ofReal (highRawDensityMass p / highRawDensityMass p) = 1
  simp only [div_self hm.ne', ENNReal.ofReal_one]

theorem highNormalizedDensity_bounds  (C : ModelConstants d) (M cm )
    (hM : 2 ≤ M) (hcm : 0 ≤ cm) (hcmU : cm ≤ 1 / C.densityUpper)
    (p )
    (hb : ∀ᵐ x ∂cubeVolume d,
      C.densityLower + 1 / M ≤ p x ∧ p x ≤ C.densityUpper - 1 / M)
    (hm : |highRawDensityMass p - 1| ≤ cm / M) :
    ∀ᵐ x ∂cubeVolume d,
      C.densityLower ≤ highNormalizedDensity p x ∧
        highNormalizedDensity p x ≤ C.densityUpper := by
  filter_upwards [hb] with x hx
  have hU : 0 < C.densityUpper := lt_trans (by norm_num) C.one_lt_densityUpper
  have hM0 : 0 < M := by linarith
  have hm0 : 0 < (highRawDensityMass p) := lt_of_lt_of_le (by norm_num) (high_raw_mass_lower C M cm (highRawDensityMass p) hM hcm hcmU hm)
  have hcmprod : C.densityUpper * cm ≤ 1 := by
    have h := (le_div_iff₀ hU).mp hcmU
    nlinarith
  have hLcm := (mul_le_mul_of_nonneg_right (C.densityLower_lt_one.le.trans C.one_lt_densityUpper.le) hcm).trans hcmprod
  have hmass := abs_le.mp hm
  have : C.densityUpper * (cm / M) ≤ 1 / M := by
    have h := div_le_div_of_nonneg_right hcmprod hM0.le
    simpa only [mul_div_assoc, one_div] using h
  have : C.densityLower * (cm / M) ≤ 1 / M := by
    simpa only [mul_div_assoc, one_div] using (div_le_div_of_nonneg_right hLcm hM0.le)
  constructor
  · apply (le_div_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass.2 C.densityLower_pos.le]
  · apply (div_le_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass.1 hU.le]

/-- Actual ternary regression model with a normalized, nonuniform design. -/
def normalizedDensityTernaryParameter  (p F : Covariate d → ℝ)
    (a V ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) : RegressionParameter d where
  density := highNormalizedDensity p
  regression := F
  variance := V
  errors := ternaryErrorKernel a V F hF
  errors_markov := ternaryErrorKernel_markov a V F hF ha hp

end NearlyMinimax
