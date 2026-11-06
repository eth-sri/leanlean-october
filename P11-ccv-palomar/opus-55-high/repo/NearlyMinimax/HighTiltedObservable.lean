module

public import NearlyMinimax.HighPriorObservableDerivative
public import NearlyMinimax.HighRawObservableRegularity
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual mass-tilted original data means: normalization cancellation,
variance heat and the genuine marked append generator. -/
𝚹
𝚨
𝚭
𝚩

𝗇 𝔄 𝙙
def highTiltedObservableMean [MeasurableSpace Ω]
    (ν : Measure Ω) (n : ℕ) (a V : ℝ) (p F : Ω → 𝙀)
    (hp : 𝘍) (hF : 𝗴)
    (H : 𝙌 → ℝ) : ℝ :=
  ∫ ω, ∫ z, H z ∂highRealSampleKernel n a V p F hp hF ω
    ∂massPowerTilt ν 𝔄 n

𝚲

𝗇 𝔙 v - 𝙎 * u
𝗇 𝔅 ∀ u ∈ 𝗺, ∀ ω x y, 0 ≤ 𝙅 𝔙 y
𝗇 𝔇 𝖤
𝗇 𝔈 𝘳 0 π activation
𝗇 𝔉 v - 𝙎 * t
𝗇 𝔟 𝗃₁
𝗇 𝔍 ∀ ω x, aRaw ≤ 𝔟 ∧ 𝔟 ≤ bRaw
𝗇 𝔎 𝘼
𝗇 𝔏 𝘽
𝗇 𝔐 𝘳 t π activation
𝗇 𝔑 𝘀₁
𝗇 𝔓 𝙗 → 𝙀
𝗇 𝔔 𝙂
𝗇 𝔖 𝗺
𝗇 𝔞 𝘳 u π activation
𝗇 𝔒 ∀ u ∈ 𝔖, (𝔞).map 𝔄 = (𝔈).map 𝔄
𝗇 𝔗 (massPowerNormalizer 𝔈 𝔄 n)⁻¹
𝗃 𝔡 ἀ n a 𝔉 (p ω) (F ω) H
𝗇 𝔘 𝔡 highRawObservable
𝗇 𝔛 𝙁
𝗃 𝔠 ἀ dependent hrefl hsymm Δ hΔ hlabels
𝗃 𝔢 ἀ 𝔐 n a 𝔉 p F hp hF
theorem historyMarkedPrior_tiltedObservable_eq_raw (dependent : 𝔛)
    (hrefl : 𝔔) (hsymm : 𝔎)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔏)
    (T Ba : ℝ) (hBa : 𝙑)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (hactivation : Measurable activation)
    (hcenter : 𝔑) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝔇)
    (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 𝙆) (haRaw : 𝙓)
    (p F : 𝔓)
    hp hF
    (hraw : 𝔍)
    (hq : 𝔅)
    (hmass : 𝔒)
    H (hH : Measurable H)
    B (hB : 𝙐) (hHb : ∀ z, |H z| ≤ B)
    t (ht : t ∈ 𝔖) :
    𝔢 highTiltedObservableMean H =
      𝔗 *
        ∫ ω, 𝔘
          ∂𝔐 := by
  have hint : Integrable activation π := by
    apply Integrable.of_bound hactivation.aestronglyMeasurable Ba
    simp_all
  have hs :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hBa)
      𝘤).trans hsmall
  let _ := 𝔠 historyMarkedPrior_probability t Ba ht.1 hBa π
    activation hint hcenter habound hs
  rw [highTiltedObservableMean, 𝔢 massPowerTilt_highReal_observable_mean
      aRaw bRaw haRaw hraw ha.ne' (hq t ht) H hH B hB hHb,
    massPowerNormalizer_eq_of_massLaw _ _ _ 𝙨 n $ hmass t ht ]

𝗇 𝔊 fun u => highTiltedObservableMean 𝔞 n a 𝔙 p F hp hF H
𝗇 𝔚 𝔠 historyMarkedPrior_tiltedObservable_eq_raw T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass H hH B hB hHb
theorem historyMarkedPrior_tiltedObservable_hasDerivAt (dependent : 𝔛)
    (hrefl : 𝔔) (hsymm : 𝔎)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔏)
    (T Ba : ℝ) (hBa : 𝙑)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (hactivation : Measurable activation)
    (hcenter : 𝔑) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝔇)
    (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 𝙆) (haRaw : 𝙓)
    (p F : 𝔓)
    hp hF
    (hraw : 𝔍)
    (hq : 𝔅)
    (hmass : 𝔒)
    H (hH : Measurable H)
    B (hB : 𝙐) (hHb : ∀ z, |H z| ≤ B)
    t (ht : 𝘁₁) (htT : t < T) :
    HasDerivAt 𝔊
      (𝔗 *
        ( -𝙎 * ∫ ω, 𝔡 highRawObservableVarianceDerivative
          ∂𝔐 +
          𝚄₂ activation
             fun ω => 𝔘 )) t := by
  have hpb ω x : |𝔟| ≤ |bRaw| := by
    grind
  have hd := 𝔠 historyMarkedPrior_rawObservable_hasDerivAt
    T Ba t ht htT hBa π activation hactivation habound hsmall n a v η |bRaw| B ha
    (abs_nonneg _) hB p F hp hF hpb (fun u hu => hq u 𝘠₂) H hH hHb
  have hc := hd.const_mul 𝔗
  apply hc.congr_of_eventuallyEq
  filter_upwards [𝗍₂] with u hu
  exact 𝔚 u 𝘠₂

𝗇 𝔜 c * _
theorem historyMarkedPrior_tiltedObservable_exists_lipschitz (dependent : 𝔛)
    (hrefl : 𝔔) (hsymm : 𝔎)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔏)
    (T Ba : ℝ) (hBa : 𝙑)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏) (hactivation : Measurable activation)
    (hcenter : 𝔑) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝔇)
    (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 𝙆) (haRaw : 𝙓)
    (p F : 𝔓)
    hp hF
    (hraw : 𝔍)
    (hq : 𝔅)
    (hmass : 𝔒)
    H (hH : Measurable H)
    B (hB : 𝙐) (hHb : ∀ z, |H z| ≤ B)
    : ∃ K , LipschitzOnWith K
      𝔊 𝔖 := by
  have hpb ω x : |𝔟| ≤ |bRaw| := by
    grind
  obtain ⟨K, hK⟩ := 𝔠 historyMarkedPrior_rawObservable_exists_lipschitz
    T Ba hBa π activation hactivation habound hsmall n a v η |bRaw| B ha (abs_nonneg _) hB
    p F hp hF hpb hq H hH hHb
  let c := 𝔗
  refine ⟨⟨|c| * K, mul_nonneg (abs_nonneg _) K.coe_nonneg⟩, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu w hw
  rw [𝔚 u hu,
    𝔚 w hw]
  change dist 𝔜 𝔜 ≤ |c| * K * dist u w
  rw [Real.dist_eq, ← mul_sub, abs_mul]
  have hh := hK.dist_le_mul u hu w hw
  rw [Real.dist_eq] at hh
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh $ abs_nonneg c
