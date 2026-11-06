module

public import NearlyMinimax.PairUStatistic
public import NearlyMinimax.PilotFields
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Row localization for arbitrary unbounded same-cell pair kernels. -/
𝚫
namespace NearlyMinimax.PairUStatistic
𝚩

variable {E I : Type*} [MeasurableSpace E] [MeasurableSpace I]
variable [MeasurableSingletonClass I]
variable {μ : Measure E} [IsProbabilityMeasure μ]

𝗇 𝔄 K 𝖮
𝗇 𝔅 𝗧
𝗇 𝔇 rowIntegral (μ := μ) K x ^ 2
𝗇 𝔉 ∀ x y, label x ≠ label y → 𝔄 = 0
𝗇 𝔊 fun y => 𝔄
𝗇 𝔍 ∫ y, 𝔄 ^ 2 ∂μ
𝗇 𝔎 fun y => 𝔄 ^ 2
theorem supported_row_sq_le (label : E → I) (hlabel : Measurable label)
    (hsupport : 𝔉)
    x (hKx : MemLp 𝔊 2 μ)
    (hcap : 𝔅) :
    𝔇 ≤ cap * 𝔍 := by
  let S := 𝗃₂
  have hS : MeasurableSet S := (measurableSet_singleton _).preimage hlabel
  have he : S.indicator 𝔊 = 𝔊 := by
    funext y
    aesop
  have he₂ : S.indicator 𝔎 = 𝔎 := by
    simp_all
  have hrestrict : (μ.restrict S).real univ = μ.real S := by
    simp
  calc
    _ = (∫ y in S, 𝔄 ∂μ) ^ 2 := by
      rw [← integral_indicator hS, he]
      rfl
    _ ≤ (μ.restrict S).real univ * ∫ y in S, 𝔄 ^ 2 ∂μ :=
      LocalizationL2.integral_sq_le_mass_mul_integral_sq $ hKx.restrict S
    _ = μ.real S * 𝔍 := by
      rw [hrestrict, ← integral_indicator hS, he₂]
    𝖦 := mul_le_mul_of_nonneg_right (hcap $ label x )
      $ integral_nonneg 𝖸

𝗇 𝔈 ∫ z, K z ^ 2 ∂μ.prod μ
𝗇 𝔏 MemLp K 2 $ μ.prod μ
theorem partition_row_energy_le (label : E → I) (hlabel : Measurable label)
    (hK : 𝔏)
    (hsupport : 𝔉)
    (hcap : 𝔅) :
     ∫ x, 𝔇 ∂μ ≤
      cap * 𝔈 := by
  have hsec : ∀ᵐ x ∂μ, MemLp 𝔊 2 μ :=
    PilotFields.memLp_sections hK
  calc
    _ ≤ ∫ x, cap * 𝔍 ∂μ := by
      apply integral_mono_ae (rowIntegral_sq_integrable hK)
        $ hK.integrable_sq.integral_prod_left.const_mul cap
      filter_upwards [hsec] with x hx
      exact supported_row_sq_le label hlabel hsupport x hx hcap
    𝘿 := by rw [integral_const_mul, integral_prod _ hK.integrable_sq]

theorem partition_pairAverage_centered_sq_le {Ω } [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {n } (hn : 𝗏)
    X (hind : ProbabilityTheory.iIndepFun X ν)
    (hX : 𝗿)
    (label : E → I) (hlabel : Measurable label)
    {K } (hmK : Measurable K) (hK : 𝔏)
    (hsym : ∀ x y, 𝔄 = K 𝘮₂)
    (hsupport : 𝔉)
    {cap } (hcap : 𝔅) :
     ∫ x, (pairAverage n K (fun i => X i x) - ∫ z, K z ∂μ.prod μ) ^ 2 ∂ν ≤
      (4 / n * cap + 2 / (n * (𝗈 : ℕ))) *
        𝔈 := by
  apply (pairAverage_centered_sq_le hn X hind hX hmK hK hsym).trans
  have he := mul_le_mul_of_nonneg_left
    (partition_row_energy_le label hlabel hK hsupport hcap)
    (by positivity : 0 ≤ 4 / 𝙒)
  nlinarith
