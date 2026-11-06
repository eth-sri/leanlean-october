module

public import NearlyMinimax.WeightedPair
public import NearlyMinimax.TwoStageRisk
public import NearlyMinimax.PilotFields
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Averaged evaluation risk of an actual two-stage pair statistic. -/
𝚵
𝚳
namespace NearlyMinimax.PairUStatistic
𝚩

variable {P Ω E I : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
  [MeasurableSpace E] [MeasurableSpace I] [MeasurableSingletonClass I]
variable {π : Measure P} {ν : Measure Ω} {μ : Measure E}
  [IsProbabilityMeasure π] [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

𝗇 𝔏 𝖸₂
𝗇 𝔎 P → 𝔏 → ℝ
def fieldPairAverage (n : ℕ) (weight : ℝ) (G : 𝔎)
    (X : Fin n → Ω → E) (z : P × Ω) : ℝ :=
  pairAverage n (weightedSymmetrization weight $ G z.1 ) fun i => X i z.2

𝗇 𝔄 Measurable fun z : P × 𝔏 => G z.1 z.2
𝗇 𝔈 fieldPairAverage n weight G X
theorem fieldPairAverage_measurable n weight
    (hmG : 𝔄)
    (X : Fin n → Ω → E) (hX : 𝘫₁) :
    Measurable 𝔈 := by
  apply Measurable.const_mul
  unfold weightedSymmetrization
  fun_prop

def fieldPairMean (weight : ℝ) (G : 𝔎) (p : P) : ℝ :=
  weight / 2 * ∫ z, G p z ∂μ.prod μ

𝗇 𝔇 fieldPairMean (μ := μ) weight G
theorem fieldPairMean_measurable weight
    (hmG : 𝔄) :
    Measurable 𝔇 :=
  hmG.stronglyMeasurable.integral_prod_right'.measurable.const_mul _

𝗇 𝔐 𝘙₁
𝗇 𝔅 weight * ∫ z : P × 𝔏, G z.1 z.2 ^ 2 ∂𝔐
𝗇 𝔉 bound / n + weight / (𝘕₁ * (𝗈 : ℕ))
𝗇 𝔊 𝔈 (p, x) - 𝔇 p
𝗇 𝔍 𝖸
theorem fieldPairAverage_two_stage_mse_le (hn : 𝗏)
    X (hind : iIndepFun X ν)
    (hX : 𝗿)
    (label : E → I) (hlabel : Measurable label)

    (hmG : 𝔄)
    (hG : MemLp (fun z => G z.1 z.2) 2 𝔐)
    (hsupport : ∀ p x y, label x ≠ label y → G p 𝖮 = 0)
    (hw : 0 < weight) (hcap : 0 ≤ cap)
    (hmass : 𝗧) (hbound : weight * cap ≤ bound)
    (hd : 0 ≤ d)
    (hmean : ∫⁻ p, ENNReal.ofReal ((𝔇 p - c) ^ 2) ∂π ≤
      ENNReal.ofReal d) :
     ∫⁻ z, ENNReal.ofReal ((𝔈 z - c) ^ 2) ∂π.prod ν ≤
      ENNReal.ofReal (2 *
        𝔉 *
        𝔅 + 2 * d) := by
  let a := 𝔉
  let b := fun p => weight * ∫ z, G p z ^ 2 ∂μ.prod μ
  have hb := hG.integrable_sq.integral_prod_left.const_mul weight
  have hb0 : ∀ᵐ p ∂π, 0 ≤ b p := Filter.Eventually.of_forall fun p =>
    mul_nonneg hw.le $ integral_nonneg 𝔍
  have hbn := (mul_nonneg hw.le hcap).trans hbound
  have hc : ∀ᵐ p ∂π, ∫⁻ x, ENNReal.ofReal
      (𝔊 ^ 2) ∂ν ≤
      ENNReal.ofReal (a * b p) := by
    filter_upwards [PilotFields.memLp_sections hG] with p hp
    have hT : MemLp (fun x => 𝔊) 2 ν :=
      (pairAverage_memLp_two X hind hX $ weightedSymmetrization_memLp weight hp ).sub $ memLp_const _
    rw [← ofReal_integral_eq_lintegral_ofReal hT.integrable_sq
      $ Filter.Eventually.of_forall 𝔍 ]
    exact ENNReal.ofReal_mono $ weighted_pair_centered_sq_le hn X hind hX label hlabel
      (hmG.comp $ measurable_const.prodMk measurable_id ) hp (hsupport p) hw hcap hmass hbound
  have hr := NearlyMinimax.two_stage_mean_squared_bound π ν
    𝔈 (fieldPairMean weight G) b
    (fieldPairAverage_measurable n weight hmG X fun i => (hX i).measurable )
    (fieldPairMean_measurable weight hmG) hb hb0  𝖠₃  hd hc hmean
  have he : ∫ p, b p ∂π = 𝔅 := by
    rw [integral_const_mul, integral_prod _ hG.integrable_sq]
  simpa only [he, a] using hr
