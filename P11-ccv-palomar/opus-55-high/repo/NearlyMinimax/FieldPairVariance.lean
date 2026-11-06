module

public import NearlyMinimax.FieldPairMoments
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Joint Bochner variance bounds with integrability derived from genuine
independent sample observations. -/
𝚵
𝚮
namespace NearlyMinimax.PairUStatistic
𝚩

variable {P Ω E I : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace E] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {π : Measure P} {ν : Measure Ω} {μ : Measure E}
  [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

𝗇 𝔄 fieldPairMean (μ := μ) weight G
𝗇 𝔅 Filter.Eventually.of_forall 𝖸
𝗇 𝔇 fieldPairAverage n weight G X z - c
𝗇 𝔈 (𝔄 p - c) ^ 2
𝗇 𝔉 P × 𝖸₂
𝗇 𝔊 𝘙₁
theorem fieldPairAverage_centered_sq_le (hn : 𝗏)
    X (hind : iIndepFun X ν)
    (hX : 𝗿)
    (label : E → I) (hlabel : Measurable label)

    (hmG : Measurable fun z : 𝔉 => G z.1 z.2 )
    (hG : MemLp (fun z => G z.1 z.2) 2 𝔊)
    (hsupport : ∀ p x y, label x ≠ label y → G p 𝖮 = 0)
    (hw : 0 < weight) (hcap : 0 ≤ cap)
    (hmass : 𝗧) (hbound : weight * cap ≤ bound)
    (hd : 0 ≤ d)
    (hmean2 : MemLp 𝔄 2 π)
    (hmean : ∫ p, 𝔈 ∂π ≤ d) :
     ∫ z, 𝔇 ^ 2 ∂π.prod ν ≤
      2 * (bound / n + weight / (𝘕₁ * (𝗈 : ℕ))) *
        (weight * ∫ z : 𝔉, G z.1 z.2 ^ 2 ∂𝔊) + 𝖩₁ := by
  have hmeanC : MemLp (fun p => fieldPairMean weight G p - c) 2 π :=
    hmean2.sub $ memLp_const c
  have hfieldC : MemLp (fun z => 𝔇) 2 $ π.prod ν :=
    (fieldPairAverage_memLp weight hG X hind hX).sub $ memLp_const c
  have hm : ∫⁻ p, ENNReal.ofReal 𝔈 ∂π ≤
      ENNReal.ofReal d := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      hmeanC.integrable_sq
      𝔅]
    exact ENNReal.ofReal_mono hmean
  have hr := fieldPairAverage_two_stage_mse_le hn X hind hX label hlabel hmG hG
    hsupport hw hcap hmass hbound hd hm
  rw [← ofReal_integral_eq_lintegral_ofReal
    hfieldC.integrable_sq
    𝔅] at hr
  have hbn := (mul_nonneg hw.le hcap).trans hbound
  exact (ENNReal.ofReal_le_ofReal_iff $ by
    positivity ).1 hr
