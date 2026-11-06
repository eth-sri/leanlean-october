module

public import NearlyMinimax.Risk
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Risk averaging for independent pilots and evaluation observations.
The loss remains an extended-real integral throughout. -/
𝚯
𝚮
𝚨
𝚩

𝗇 𝔄 T z - L z.1
𝗇 𝔅 L z.1 - c
𝗇 𝔇 ∫ p, b p ∂μ
𝗇 𝔈 ∫⁻ z, f z ∂μ.prod ν
𝗇 𝔉 ∫⁻ z, g z ∂μ.prod ν
𝗇 𝔊 (T z - c) ^ 2
𝗇 𝔍 𝔄 ^ 2
𝗇 𝔎 𝔅 ^ 2
𝗇 𝔏 a * 𝔇
theorem two_stage_mean_squared_bound
    [MeasurableSpace P] [MeasurableSpace X]
    (μ : Measure P) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (T : P × X → ℝ) (L b : P → ℝ) (hmT : Measurable T) (hmL : Measurable L)
    (hb : Integrable b μ) (hb0 : ∀ᵐ p ∂μ, 0 ≤ b p)
    (ha : 𝖢₂) (hd : 0 ≤ d)
    (hconditional : ∀ᵐ p ∂μ,
       ∫⁻ x, ENNReal.ofReal ((T (p, x) - L p) ^ 2) ∂ν ≤ ENNReal.ofReal (a * b p))
    (hmean : ∫⁻ p, ENNReal.ofReal ((L p - c) ^ 2) ∂μ ≤ ENNReal.ofReal d) :
     ∫⁻ z, ENNReal.ofReal 𝔊 ∂μ.prod ν ≤
      ENNReal.ofReal (2 * a * 𝔇 + 𝖩₁) := by
  let f := fun z => ENNReal.ofReal 𝔍
  let g : P × X → 𝙉₁ := fun z => ENNReal.ofReal 𝔎
  have hf : Measurable f := ((hmT.sub $ hmL.comp measurable_fst ).pow_const 2).ennreal_ofReal
  have hg : Measurable g := (((hmL.comp measurable_fst).sub measurable_const).pow_const 2).ennreal_ofReal
  have heval : 𝔈 ≤ ENNReal.ofReal 𝔏 := by
    rw [lintegral_prod _ hf.aemeasurable]
    apply (lintegral_mono_ae hconditional).trans
    rw [← ofReal_integral_eq_lintegral_ofReal (hb.const_mul a) $ hb0.mono fun _ hp => mul_nonneg ha hp , integral_const_mul]
  have hmean' : 𝔉 ≤ ENNReal.ofReal d := by
    rw [lintegral_prod _ hg.aemeasurable]
    simp only [g, lintegral_const, measure_univ, mul_one]
    exact hmean
  calc
    _ ≤ ∫⁻ z, 2 * f z + 2 * g z ∂μ.prod ν := by
      apply lintegral_mono
      intro z
      have hs : 𝔊 ≤ 2 * 𝔍 + 2 * 𝔎 := by
        nlinarith [sq_nonneg $ 𝔄 - 𝔅 ]
      simpa only [f, g, ENNReal.ofReal_add (by positivity : 0 ≤ 2 * 𝔍)
        (by positivity : 0 ≤ 2 * 𝔎),
        ENNReal.ofReal_mul (by norm_num : 𝙋 ≤ 2), ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hs
    _ = 2 * 𝔈 + 2 * 𝔉 := by
      have hf2 : Measurable fun z => 2 * f z := measurable_const.mul hf
      rw [lintegral_add_left hf2, lintegral_const_mul _ hf, lintegral_const_mul _ hg]
    _ ≤ 2 * ENNReal.ofReal 𝔏 + 2 * ENNReal.ofReal d := by
      gcongr
    𝘿 := by
      rw [show 2 = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul 𝖠₄ ,
        ← ENNReal.ofReal_mul 𝖠₄ ,
        ← ENNReal.ofReal_add (mul_nonneg  𝖠₄  $ mul_nonneg ha $ integral_nonneg_of_ae hb0 ) $ mul_nonneg  𝖠₄  hd ]
      ring
