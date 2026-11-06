module

public import NearlyMinimax.HighTiltedDataMean
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Genuine observed-data score derivative for the actual high experiment. -/
𝚹
𝚨
𝚲

𝗇 𝔛 𝙙
𝗇 𝔡 𝘳 u π activation
𝗇 𝔥 v - 𝙎*u
𝗃 𝔦 highRealSampleKernel n a ἀ p F hp hF
𝗇 𝔄 ∫ z, H z ∂𝔦 𝔥 ∘ₘ massPowerTilt 𝔡 𝔛 n
𝗇 𝔅 ∀ u ∈ 𝗺, (𝔡).map 𝔛 = (𝘳 0 π activation).map 𝔛
𝗇 𝔞 v - 𝙎*t
𝗇 𝔠 𝘳 t π activation
𝗇 𝔇 ∫ z, H z * highMarginalRealScore dependent hsymm 𝔠 π activation n a 𝔞 η p F z ∂𝔦 𝔞 ∘ₘ massPowerTilt 𝔠 𝔛 n
𝗇 𝔈 𝖤
𝗇 𝔉 𝔥
𝗇 𝔊 𝙄
𝗇 𝔍 𝘼
𝗇 𝔎 𝔡
𝗇 𝔏 𝘽
𝗇 𝔐 𝘀₁
𝗇 𝔑 historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1 hBa π activation hint hcenter habound hs
𝗇 𝔒 𝙗 → 𝙀
𝗇 𝔓 𝗺
𝗇 𝔔 (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hBa) 𝘤).trans hsmall
𝗇 𝔖 ⟨ht.le, htT.le⟩
𝗇 𝔗 𝙂
𝗇 𝔘 F ω x
𝗇 𝔙 𝔞
𝗇 𝔚 𝔠
𝗇 𝔜 fun u => 𝔄
𝗇 𝔟 ∀ u ∈ 𝔓, ∀ ω x y, 0 < ternaryMass a 𝔘 𝔉 y
𝗇 𝔢 highTiltedObservableMean_eq_dataMean 𝔎 n a 𝔉 aRaw bRaw B ha.ne' haRaw hB p F hp hF hraw
𝗃 𝔣 ἀ dependent hrefl hsymm Δ hΔ hlabels T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw
𝗇 𝔤 𝙁
𝗃 𝔧 ἀ t 𝔖
theorem historyMarkedPrior_dataMean_score_hasDerivAt (dependent : 𝔤)
    (hrefl : 𝔗) (hsymm : 𝔍)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔏)
    (T Ba : ℝ) (hBa : 𝙑)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (hactivation : Measurable activation)
    (hcenter : 𝔐) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝔈)
    (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 𝙆) (haRaw : 𝙓)
    (p F : 𝔒)
    hp hF
    (hraw : 𝔊)
    (hq : 𝔟)
    (hmass : 𝔅)
    H (hH : Measurable H)
    B (hB : 𝙐) (hHb : ∀ z, |H z| ≤ B)
    t (ht : 𝘁₁) (htT : t < T) :
    HasDerivAt 𝔜
      𝔇 t := by
  have hq0 u hu ω x y :=
    (hq u hu ω x y).le
  have hint : Integrable activation π := by
    apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
    exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e
  have hprob u (hu : u ∈ 𝔓) :
      IsProbabilityMeasure 𝔎 := by
    have hs :=
      𝔔
    exact 𝔑
  let _ := 𝔧 hprob
  have hd := 𝔣 historyMarkedPrior_tiltedObservable_hasDerivAt hq0 hmass H hH B hB hHb t ht htT
  have hpb ω x : |𝗃₁| ≤ |bRaw| := by
    grind
  have he := highMarginalRealScore_integral dependent hsymm
    𝔚 π activation hactivation Ba hBa habound
    n a 𝔙 η aRaw bRaw B ha haRaw hB p F hp hF hraw
    𝔧 hq H hH hHb
  have hi := highHistoryLikelihoodDerivative_observable π dependent hsymm
    𝔚 activation hactivation Ba hBa habound
    n a 𝔙 η |bRaw| B (abs_nonneg _) hB ha p F hp hF hpb
    𝔧 hq0 H hH hHb
  rw [hi, massPowerNormalizer_eq_of_massLaw _ _ _ 𝙨
    n 𝔧 hmass] at he
  rw [he]
  apply hd.congr_of_eventuallyEq
  filter_upwards [𝗍₂] with u hu
  let _ := hprob u 𝘠₂
  exact (𝔢
    (hq0 u 𝘠₂) H hH hHb).symm

𝗃 𝔨 𝔣 ἀ hq hmass H hH B hB hHb
theorem historyMarkedPrior_dataMean_absolutelyContinuous (dependent : 𝔤)
    (hrefl : 𝔗) (hsymm : 𝔍)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔏)
    (T Ba : ℝ) (hBa : 𝙑)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (hactivation : Measurable activation)
    (hcenter : 𝔐) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝔈)
    (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 𝙆) (haRaw : 𝙓)
    (p F : 𝔒)
    hp hF
    (hraw : 𝔊)
    (hq : ∀ u ∈ 𝔓, ∀ ω x y, 0 ≤ ternaryMass a 𝔘 𝔉 y)
    (hmass : 𝔅)
    H (hH : Measurable H)
    (B : ℝ) (hB : 𝙐) (hHb : ∀ z, |H z| ≤ B)
    (hT : 𝚞) :
    AbsolutelyContinuousOnInterval
      𝔜 0 T := by
  obtain ⟨K, hK⟩ := 𝔨 historyMarkedPrior_tiltedObservable_exists_lipschitz
  have hint : Integrable activation π := by
    apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
    exact Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e
  have he (u : ℝ) (hu : u ∈ 𝔓) :
      highTiltedObservableMean 𝔎
        n a 𝔉 p F hp hF H =
      𝔄 := by
    have hs :=
      𝔔
    let _ := 𝔑
    exact 𝔢 (hq u hu) H hH hHb
  have hKd : LipschitzOnWith K
      𝔜 𝔓 := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu w hw
    rw [← he u hu, ← he w hw]
    exact hK.dist_le_mul u hu w hw
  rw [← uIcc_of_le hT] at hKd
  exact hKd.absolutelyContinuousOnInterval

𝗃 𝔩 ∀ᵐ t ∂volume, t ≠ ἀ
theorem historyMarkedPrior_dataMean_score_hasDerivAt_ae (dependent : 𝔤)
    (hrefl : 𝔗) (hsymm : 𝔍)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔏)
    (T Ba : ℝ) (hBa : 𝙑)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (hactivation : Measurable activation)
    (hcenter : 𝔐) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝔈)
    (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 𝙆) (haRaw : 𝙓)
    (p F : 𝔒)
    hp hF
    (hraw : 𝔊)
    (hq : 𝔟)
    (hmass : 𝔅)
    H (hH : Measurable H)
    B (hB : 𝙐) (hHb : ∀ z, |H z| ≤ B)
    : ∀ᵐ t ∂volume, t ∈ 𝔓 →
      HasDerivAt 𝔜
        𝔇 t := by
  have h0 : 𝔩 𝙋 := by simp [ae_iff]
  have hT : 𝔩 T := by simp [ae_iff]
  filter_upwards [h0, hT] with t ht0 htT
  intro ht
  exact 𝔨 historyMarkedPrior_dataMean_score_hasDerivAt t (lt_of_le_of_ne ht.1 $ Ne.symm ht0 ) $ lt_of_le_of_ne ht.2 htT
