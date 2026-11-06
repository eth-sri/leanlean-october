module

public import NearlyMinimax.LowSmoothnessPrior
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Raw-density normalization for the manuscript's high-smoothness prior.
The mass-concentration guard is a scalar event; density normalization and
original density bounds are consequences proved here. -/
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff
𝚨
𝚩
𝚰

𝗇 𝔉 cm / M
𝗇 𝔏 𝘉₂
theorem high_raw_mass_lower (C : ModelConstants d) M cm m
    (hM : 𝗜₁) (hcm : 0 ≤ cm) (hcmU : 𝔏)
    (hm : |m - 1| ≤ 𝔉) : 𝙖 ≤ m := by
  have hcm1 : cm ≤ 1 := by
    apply hcmU.trans
    exact (div_le_one $ lt_trans  𝖠₄  C.one_lt_densityUpper ).mpr C.one_lt_densityUpper.le
  have hhalf : 𝔉 ≤ 𝙖 := by
    bound
  grind

𝗇 𝔎 𝗙
theorem high_normalized_density_interval (C : ModelConstants d)
    M cm m p (hM : 𝗜₁) (hcm : 0 ≤ cm)
    (hcmU : 𝔏) (hm : |m - 1| ≤ 𝔉)
    (hp : C.densityLower + 𝔎 ≤ p ∧ p ≤ C.densityUpper - 𝔎) :
    C.densityLower ≤ p / m ∧ p / m ≤ C.densityUpper := by
  have hU : 0 < C.densityUpper := lt_trans  𝖠₄  C.one_lt_densityUpper
  have hM0 : 𝚌 := 𝖡₄
  have hm0 : 0 < m := lt_of_lt_of_le  𝖠₄  $ high_raw_mass_lower C M cm m hM hcm hcmU hm
  have hcmprod : C.densityUpper * cm ≤ 1 := by
    have h := (le_div_iff₀ hU).mp hcmU
    nlinarith
  have hLcm : C.densityLower * cm ≤ 1 := by
    have hLU :=
      C.densityLower_lt_one.le.trans C.one_lt_densityUpper.le
    nlinarith
  have hmass := abs_le.mp hm
  have hmulU : C.densityUpper * 𝔉 ≤ 𝔎 := by
    have h := div_le_div_of_nonneg_right hcmprod hM0.le
    grind
  have hmulL : C.densityLower * 𝔉 ≤ 𝔎 := by
    have h := div_le_div_of_nonneg_right hLcm hM0.le
    grind
  constructor
  · apply (le_div_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass.2 C.densityLower_pos.le]
  · apply (div_le_iff₀ hm0).mpr
    nlinarith

𝗇 𝔊 𝙀
def highRawDensityMass (p : 𝔊) : ℝ :=
  ∫ x, p x ∂cubeVolume d

def highNormalizedDensity (p : 𝔊) (x : Covariate d) : ℝ :=
  p x / highRawDensityMass p

theorem highNormalizedDensity_measurable (p : 𝔊)
    (hp : Measurable p) : Measurable $ highNormalizedDensity p := hp.div_const _

𝗇 𝔈 ∀ᵐ x ∂cubeVolume d, C.densityLower + 𝔎 ≤ p x ∧ p x ≤ C.densityUpper - 𝔎
theorem highRawDensity_integrable (C : ModelConstants d) M
    (hM : 𝚌) p (hp : Measurable p)
    (hb : 𝔈) :
    Integrable p $ cubeVolume d := by
  have hfin : IsFiniteMeasure $ cubeVolume d := by
    constructor
    rw [cubeVolume_univ]
    exact ENNReal.one_lt_top
  have hbound : ∀ᵐ x ∂cubeVolume d, ‖p x‖ ≤ C.densityUpper := by
    filter_upwards [hb] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg $ by linarith [C.densityLower_pos, one_div_pos.mpr hM] ]
    linarith [one_div_pos.mpr hM]
  exact (integrable_const C.densityUpper).mono' hp.aestronglyMeasurable hbound

𝗇 𝔑 highNormalizedDensity p x
theorem highNormalizedDensity_normalized p
    (hp : Integrable p $ cubeVolume d ) (hp0 : 0 ≤ᵐ[cubeVolume d] p)
    (hm : 0 < highRawDensityMass p) :
     ∫⁻ x, ENNReal.ofReal 𝔑 ∂cubeVolume d = 1 := by
  unfold highNormalizedDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (hp.div_const _) $ hp0.mono
     fun x hx => div_nonneg hx hm.le ]
  rw [integral_div]
  change ENNReal.ofReal (highRawDensityMass p / highRawDensityMass p) = 1
  aesop

theorem highNormalizedDensity_bounds (C : ModelConstants d) M cm
    (hM : 𝗜₁) (hcm : 0 ≤ cm) (hcmU : 𝔏)
    p
    (hb : 𝔈)
    (hm : |highRawDensityMass p - 1| ≤ 𝔉) :
    ∀ᵐ x ∂cubeVolume d,
      C.densityLower ≤ 𝔑 ∧
        𝔑 ≤ C.densityUpper := by
  filter_upwards [hb] with x hx
  exact high_normalized_density_interval C M cm (highRawDensityMass p) (p x)
    hM hcm hcmU hm hx

/-- Actual ternary regression model with a normalized, nonuniform design. -/
def normalizedDensityTernaryParameter (p F : 𝔊)
    (a V : ℝ) (hF : Measurable F) (ha : 𝙞)
    (hp : 𝗨) : RegressionParameter d where
  density := highNormalizedDensity p
  regression := F
  variance := V
  errors := ternaryErrorKernel a V F hF
  errors_markov := ternaryErrorKernel_markov a V F hF ha hp

𝗇 𝔄 fun i => 𝘇
𝗇 𝔅 𝘛
𝗇 𝔇 ∑ i, 𝘇
𝗇 𝔒 multiPartial F 𝔄
𝗇 𝔍 𝔒
𝗇 𝔐 (ℓ + 1 : ℕ)
/-- Pointwise mixed-derivative and Euclidean modulus bounds imply the
original sum-over-distinct-multi-indices norm on any extension domain. -/
theorem holderNorm_of_global_mixed_bounds U
    F ℓ α B L (hB : 𝙐) (hL : 𝘨)
    (hsup : ∀ γ : 𝔅, 𝔇 ≤ ℓ →
      ∀ x, |𝔒 x| ≤ B)
    (hmod : ∀ γ : 𝔅, 𝔇 = ℓ → ∀ x y,
      |𝔒 x - 𝔒 y| ≤
        L * euclideanNorm 𝘌 ^ α) :
    𝘍₂ ℓ α ≤ ENNReal.ofReal ((𝔐 : ℝ) ^ d * B + L) := by
  have hs (γ : 𝔅) (hγ : 𝔇 ≤ ℓ) :
      derivativeSup U 𝔍 ≤ ENNReal.ofReal B := by
    apply iSup_le
    simp_all
  have hh (γ : 𝔅) (hγ : 𝔇 = ℓ) :
      holderSeminorm U 𝔍 α ≤ ENNReal.ofReal L := by
    apply iSup_le
    intro x
    apply iSup_le
    intro y
    by_cases hxy : 𝘱₁
    · simp_all
    · simp only [𝚙₁]
      apply ENNReal.ofReal_le_ofReal
      apply 𝘴
      simp_all
  have hsum : (∑ γ : 𝔅,
      if 𝔇 ≤ ℓ then
        derivativeSup U 𝔍 else 0) ≤
      ENNReal.ofReal (𝔐 ^ d * B) := by
    calc
      _ ≤ ∑ _γ : 𝔅, ENNReal.ofReal B := by
        bound
      𝘿 := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => hB ]
        simp
  have hsem : (⨆ γ : 𝔅, if 𝔇 = ℓ then
      holderSeminorm U 𝔍 α else 0) ≤ ENNReal.ofReal L := by
    aesop
  unfold holderNorm
  rw [ENNReal.ofReal_add (mul_nonneg  𝖠₃  hB) hL]
  bound
