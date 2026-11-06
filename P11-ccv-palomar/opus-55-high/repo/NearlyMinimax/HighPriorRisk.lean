module

public import NearlyMinimax.HighScoreTimeKernel
public import NearlyMinimax.PaperScorePath
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The source marked-history prior, its genuine normalized observation law,
and its observed posterior score imply the manuscript's path-risk comparison.
The analytical score assumptions are proved from the actual likelihood. -/
𝚹
𝚮
𝚨
𝚭
𝛀
𝚲
attribute [local irreducible] highMarginalRealScore highRealSampleKernel historyMarkedPrior
  massPowerTilt massPowerNormalizer highRawDensityMass

𝗇 𝔄 v-𝙎*t
𝗇 𝔅 𝙙
𝗇 𝔇 𝘳 t π activation
𝗇 𝔈 𝗺
𝗃 𝔙 ἀ t ht
𝗇 𝔉 (𝔙 hq ω x y).le
𝗇 𝔗 𝙗
𝗇 𝔊 𝔗 × 𝙇 × 𝙈
𝗇 𝔍 θ t ω
𝗇 𝔎 C.varianceLower_pos.le.trans (S.property z).1
𝗇 𝔏 𝗿₁ 𝔄 η p F z.1 z.2 ^2 / highRawSampleLikelihood n a 𝔄 (p z.1) (F z.1) z.2
𝗇 𝔐 (𝔇).prod 𝘱
𝗇 𝔑 t ∈ 𝔈
𝗃 𝔘 ἀ n a 𝔄 p F hp hF
𝗇 𝔒 𝔘 highRealSampleKernel
𝗇 𝔓 fun ω x y => 𝔉
𝗃 𝔚 ἀ dependent hrefl hsymm Δ hΔ hlabels
𝗃 𝔔 𝔚 ἀ T Ba hBa π activation ham hact hab hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw
𝗇 𝔖 𝗩*𝖫₁
𝗃 𝔛 ἀ dependent hsymm (ν t) π activation
theorem historyMarkedPrior_original_minimax_path_bound
    (dependent : 𝙁) (hrefl : 𝙂)
    (hsymm : 𝘼)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝘽)
    [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝙏)
    (ham : Measurable activation) (hact : 𝘀₁)
    (Ba T : ℝ) (hBa : 𝙑) (hT : 𝚞) (hab : ∀ e, |activation e| ≤ Ba)
    (hsmall : 𝖤)
    (C : ModelConstants d) (n : ℕ) (a v η aRaw bRaw M ε : ℝ)
    (ha : 𝙆) (haRaw : 𝙓)
    p F
    hp hF
    (hraw : 𝙄)
    (hq : ∀ t ∈ 𝔈, ∀ ω x y, 0 < 𝙅 𝔄 y)
    (hmass : ∀ t ∈ 𝔈,
      (𝔇).map 𝔅 =
      (𝘳 0 π activation).map 𝔅)
    (θ : ℝ → 𝔗 → RegressionParameter d)
    (hθ : ∀ (t : ℝ) ht, ∀ ω, 𝔍 =
      𝙼 𝔄 hF.of_uncurry_left
        ha.ne' fun x y => 𝔉 )
    (hV : ∀ t ∈ 𝔈, 𝔄 ∈ 𝙸₁)
    (bad : ℝ → Set 𝔗)
    (hbad : ∀ t ∈ 𝔈, MeasurableSet $ bad t )
    (hlegal : ∀ t ∈ 𝔈, ∀ ω ∉ bad t, Admissible C 𝔍)
    (hbadmass : ∀ t ∈ 𝔈,
      (massPowerTilt 𝔇
        𝔅 n).real (bad t) ≤ ε)
    (hE : ∀ t ∈ 𝔈, Integrable
      (fun z : 𝔊 =>
        𝔏)
      𝔐)
    (hbudget : ∀ t ∈ 𝔈,
      (massPowerNormalizer 𝔇
        𝔅 n)⁻¹ *
        ∫ z : 𝔊,
          𝔏
          ∂𝔐 ≤ M) :
    let P (t : ℝ) := 𝔒 ∘ₘ
      massPowerTilt 𝔇
        𝔅 n
    let R (t : ℝ) := highMarginalRealScore dependent hsymm
      𝔇 π activation n a 𝔄 η p F
    ENNReal.ofReal (𝔖 /
      (2 + ∫ t in 0..T, Real.sqrt (∫ z, R t z ^2 ∂P t))^2 -
      𝙰^2*ε) ≤ minimaxRisk C n := by
  let ν (t : ℝ) := 𝔇
  let σ (t : ℝ) := massPowerTilt (ν t) 𝔅 n
  let L (t : ℝ) := 𝔒
  let R (t : ℝ) := 𝔛 highMarginalRealScore n a 𝔄 η p F
  let _ := 𝔚 historyMarkedReference_probability π
  have hai : Integrable activation π := Integrable.of_bound ham.aestronglyMeasurable Ba
    $ Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using hab e
  have hν (t : ℝ) (ht : 𝔑) : IsProbabilityMeasure $ ν t := by
    have hs :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hBa)
        𝘤).trans hsmall
    exact 𝔚 historyMarkedPrior_probability t Ba ht.1 hBa
      π activation hai hact hab hs
  have hσ (t : ℝ) (ht : 𝔑) : IsProbabilityMeasure $ σ t := by
    let _ := 𝔙 hν
    exact massPowerTilt_isProbability (ν t) _ 𝙨
      n aRaw bRaw haRaw fun ω => 𝙕
  have hL (t : ℝ) (ht : 𝔑) :=
    𝔘 highRealSampleKernel_markov aRaw bRaw haRaw hraw ha.ne'
      𝔓
  have hsample (t : ℝ) (ht : 𝔑) ω : L t ω = sampleLaw 𝔍 n := by
    rw [𝔙 hθ ω]
    exact 𝔘 highRealSampleKernel_eq_sampleLaw aRaw bRaw haRaw hraw
      ha.ne' 𝔓 ω
  have hvariance (t : ℝ) (ht : 𝔑) ω : (𝔍).variance = 𝔄 := by
    rw [𝔙 hθ ω]
    rfl
  have hR : ∀ᵐ t ∂volume, 𝔑 → MemLp (R t) 2 (L t ∘ₘ σ t) :=
    Eventually.of_forall fun t ht => by
      let _ := 𝔙 hν
      exact (𝔛 highMarginalRealScore_memLp_energy ham
        Ba hBa hab n a 𝔄 η aRaw bRaw ha haRaw p F hp hF hraw 𝔙 hq 𝔙 hE).1
  have hc := 𝔔 historyMarkedPrior_dataScore_centered_ae hq hmass
  have hB :=
    C.varianceLower_pos.le.trans (effective_variance_interval_nondegenerate C).le
  have hAC (S : 𝖧₂) :=
    𝔔 historyMarkedPrior_dataMean_absolutelyContinuous
      (fun t ht ω x y => 𝔉) hmass S.val.val S.val.property
      (effectiveVarianceUpper C) hB (fun z => by
        rw [abs_of_nonneg 𝔎]
        exact (S.property z).2) hT
  have hd (S : 𝖧₂) :=
    𝔔 historyMarkedPrior_dataMean_score_hasDerivAt_ae hq hmass
      S.val.val S.val.property (effectiveVarianceUpper C) hB fun z => by
        rw [abs_of_nonneg 𝔎]
        exact (S.property z).2
  have hi := highHistoryScore_sqrt_energy_intervalIntegrable dependent hsymm Δ π activation ham
    Ba hBa hab n a v η aRaw bRaw T M ha haRaw hT p F hp hF hν hraw hq hE hbudget
  have hh := paper_score_to_risk C σ L θ (fun t => 𝔄) R T ε hT hσ hL hsample hvariance
    hV bad hbad hlegal hbadmass hR hc hAC hd hi
  have he : ( v-𝙎*T -(v-𝙎*0))^2 = 𝔖 := 𝖢₃
  rw [he] at hh
  exact hh
