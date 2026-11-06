module

public import NearlyMinimax.HighMarginalScoreDerivative
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Genuine observed-data score centering follows from the proved derivative
identity and actual probability normalization. -/
𝚹
𝚶
𝚨
𝚭
𝚩
𝚲

𝗇 𝔐 𝙙
𝗇 𝔑 v - 𝙎*t
𝗇 𝔙 𝘳
𝗇 𝔒 𝔙 t π activation
𝗃 𝔚 highRealSampleKernel n a ἀ p F hp hF
𝗇 𝔄 ∫ z, highMarginalRealScore dependent hsymm 𝔒 π activation n a 𝔑 η p F z ∂𝔚 𝔑 ∘ₘ massPowerTilt 𝔒 𝔐 n = 0
𝗇 𝔅 ∀ u ∈ 𝗺, (𝔙 u π activation).map 𝔐 = (𝔙 0 π activation).map 𝔐
𝗇 𝔘 v - 𝙎 * u
𝗇 𝔇 ∀ u ∈ 𝗺, ∀ ω x y, 0 < 𝙅 𝔘 y
𝗇 𝔈 𝖤
𝗇 𝔉 𝙄
𝗇 𝔊 𝘼
𝗇 𝔍 𝘽
𝗇 𝔎 𝔘
𝗇 𝔏 𝔙 u π activation
𝗃 𝔓 ἀ dependent hrefl hsymm Δ hΔ hlabels T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
𝗇 𝔔 𝘀₁
𝗇 𝔖 𝙗 → 𝙀
𝗇 𝔗 𝙃
theorem historyMarkedPrior_dataScore_centered (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝔊)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔍)
    (T Ba : ℝ) (hBa : 𝙑)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (hactivation : Measurable activation)
    (hcenter : 𝔔) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝔈)
    (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 𝙆) (haRaw : 𝙓)
    (p F : 𝔖)
    hp hF
    (hraw : 𝔉)
    (hq : 𝔇)
    (hmass : 𝔅)
    t (ht : 𝘁₁) (htT : t < T) :
    𝔄 := by
  have hd := 𝔓 historyMarkedPrior_dataMean_score_hasDerivAt 𝔗 measurable_const 1  𝖠₄  fun _ => by norm_num t ht htT
  have he : (fun u => ∫ z, 𝙠 ∂𝔚 𝔎 ∘ₘ
       massPowerTilt 𝔏
        𝔐 n ) =ᶠ[𝓝 t] 𝔗 := by
    filter_upwards [𝗍₂] with u hu
    have hint : Integrable activation π := by
      apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
      exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e
    have hs :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hBa)
        𝘤).trans hsmall
    let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1.le hBa π
      activation hint hcenter habound hs
    have hb ω :=
      𝙕
    let _ := massPowerTilt_isProbability 𝔏
      _ 𝙨 n aRaw bRaw haRaw hb
    let _ := highRealSampleKernel_markov n a 𝔎 p F hp hF aRaw bRaw haRaw hraw ha.ne'
       fun ω x y => (hq u 𝘠₂ ω x y).le
    simp
  simpa only [one_mul] using hd.unique $ (hasDerivAt_const t 1 ).congr_of_eventuallyEq he

theorem historyMarkedPrior_dataScore_centered_ae (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝔊)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔍)
    (T Ba : ℝ) (hBa : 𝙑)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (hactivation : Measurable activation)
    (hcenter : 𝔔) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝔈)
    (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 𝙆) (haRaw : 𝙓)
    (p F : 𝔖)
    hp hF
    (hraw : 𝔉)
    (hq : 𝔇)
    (hmass : 𝔅)
    : ∀ᵐ t ∂volume, t ∈ 𝗺 →
      𝔄 := by
  have h0 : ∀ᵐ t ∂volume, t ≠ 𝙋 := by simp [ae_iff]
  have hT : ∀ᵐ t ∂volume, t ≠ T := by simp [ae_iff]
  filter_upwards [h0, hT] with t ht0 htT
  intro ht
  exact 𝔓 historyMarkedPrior_dataScore_centered t (lt_of_le_of_ne ht.1 $ Ne.symm ht0 ) $ lt_of_le_of_ne ht.2 htT
