module

public import NearlyMinimax.HighTimeMarginal
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! A genuine Borel time kernel for the observed high experiment and
measurability of its posterior Fisher-energy path. -/
𝚹
𝚮
𝚨
𝚭
𝛀
𝚲

𝗇 𝔄 v-𝙎*t
𝗇 𝔅 𝘳 t π activation
𝗇 𝔇 𝙗 → 𝙀
𝗇 𝔈 SFinite 𝙤
𝗇 𝔉 𝙙
𝗇 𝔊 𝙇 × 𝙈
𝗇 𝔍 𝙁
𝗇 𝔏 𝘍
𝗇 𝔐 𝗴
𝗇 𝔒 𝙏
𝗇 𝔔 𝘱
𝗇 𝔚 highMarginalRawLikelihood 𝔅 n a 𝔄 p F z / massPowerNormalizer 𝔅 𝔉 n
def highHistoryIndexTimeKernel [MeasurableSpace E]
    (dependent : 𝔍) (Δ : ℕ) (π : Measure E)
    [𝔈]
    (activation : 𝔒) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : 𝔇)
    (hp : 𝔏) (hF : 𝔐) :
    Kernel ℝ 𝔊 :=
  (Kernel.const ℝ 𝔔).withDensity
     fun t z => ENNReal.ofReal
      𝔚


𝗃 𝔠 ἀ dependent Δ π activation ham n a v η p F hp hF
𝗇 𝔟 𝔠 highHistoryIndexTimeKernel
𝗇 𝔑 𝔟
instance highHistoryIndexTimeKernel_isSFinite [MeasurableSpace E]
    (dependent : 𝔍) (Δ : ℕ) (π : Measure E)
    [𝔈]
    (activation : 𝔒) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : 𝔇)
    (hp : 𝔏) (hF : 𝔐) :
    IsSFiniteKernel 𝔑 := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _ fun _ _ => ENNReal.ofReal_ne_top

def highHistoryRealTimeKernel [MeasurableSpace E]
    (dependent : 𝔍) (Δ : ℕ) (π : Measure E)
    [𝔈]
    (activation : 𝔒) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : 𝔇)
    (hp : 𝔏) (hF : 𝔐) :
    Kernel ℝ 𝙌 :=
  (𝔑).map $ encodeDesignResponse a

𝗇 𝔞 𝔠 highHistoryRealTimeKernel
instance highHistoryRealTimeKernel_isSFinite [MeasurableSpace E]
    (dependent : 𝔍) (Δ : ℕ) (π : Measure E)
    [𝔈]
    (activation : 𝔒) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : 𝔇)
    (hp : 𝔏) (hF : 𝔐) :
    IsSFiniteKernel 𝔞 := by
  unfold highHistoryRealTimeKernel
  infer_instance

theorem highHistoryIndexTimeKernel_apply [MeasurableSpace E]
    (dependent : 𝔍) (Δ : ℕ) (π : Measure E)
    [𝔈]
    (activation : 𝔒) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : 𝔇)
    hp hF t :
    𝔟 t =
      (𝔔).withDensity fun z => ENNReal.ofReal
        𝔚 := by
  have hd :=
    ((𝔠 highMarginalRawLikelihood_time_measurable).div
      $ (highMassPowerNormalizer_time_measurable dependent Δ π activation ham n p hp).comp measurable_fst ).ennreal_ofReal
  exact Kernel.withDensity_apply _ hd t

𝗇 𝔎 𝔞 t
𝗇 𝔓 𝙄
𝗇 𝔛 highRealSampleKernel n a 𝔄 p F hp hF ∘ₘ massPowerTilt 𝔅 𝔉 n
𝗇 𝔡 𝙅 𝔄 y
theorem highHistoryRealTimeKernel_eq_data [MeasurableSpace E]
    (dependent : 𝔍) (Δ : ℕ) (π : Measure E)
    [𝔈]
    (activation : 𝔒) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : 𝔇)
    (hp : 𝔏) (hF : 𝔐)
    (t : ℝ) [IsProbabilityMeasure 𝔅]
    aRaw bRaw (haRaw : 𝙓) (ha : 𝙞)
    (hraw : 𝔓)
    (hq : ∀ ω x y, 0 ≤ 𝔡) :
    𝔎 =
      𝔛 := by
  rw [highHistoryRealTimeKernel, Kernel.map_apply _ $ encodeDesignResponse_measurable a ,
    highHistoryIndexTimeKernel_apply, ← highMassTilt_index_marginal_density
      𝔅 n a 𝔄 p F hp hF aRaw bRaw haRaw ha hraw hq,
    Measure.map_comp _ _ $ encodeDesignResponse_measurable a ]
  rfl

𝗇 𝔖 𝘼
𝗇 𝔘 highMarginalRealScore dependent hsymm 𝔅 π activation n a 𝔄 η p F z ^2
𝗇 𝔣 ∫ z, 𝔘 ∂𝔎
𝗃 𝔦 ἀ dependent hsymm Δ π activation ham n a v η p F hp hF
theorem highHistoryScoreEnergyProxy_measurable [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔍) (hsymm : 𝔖)
    (Δ : ℕ) (π : Measure E) [SFinite π] [𝔈]
    (activation : 𝔒) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : 𝔇)
    hp hF :
    Measurable fun t => 𝔣 :=
  (((𝔦 highMarginalRealScore_time_measurable).pow_const 2).stronglyMeasurable.integral_kernel_prod_right'
    ).measurable

𝗇 𝔗 𝗺
𝗇 𝔢 ⟨ht.1.le, ht.2⟩
/-- Joint Borel dependence and a genuine energy bound imply the square-root
energy is interval integrable. -/
theorem intervalIntegrable_sqrt_of_measurable_bound f
    (hf : Measurable f) T M (hT : 𝚞)
    (hbound : ∀ t ∈ 𝔗, f t ≤ M) :
    IntervalIntegrable (fun t => Real.sqrt $ f t ) volume 0 T := by
  apply (intervalIntegrable_const ).mono_fun'
    (Real.continuous_sqrt.measurable.comp hf).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hT] at ht
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg $ Real.sqrt_nonneg _ ]
  exact Real.sqrt_le_sqrt $ hbound t 𝔢

𝗇 𝔙 𝗿₁ 𝔄 η p F z.1 z.2 ^2 / highRawSampleLikelihood n a 𝔄 (p z.1) (F z.1) z.2
𝗇 𝔜 𝔠 highHistoryRealTimeKernel_eq_data t aRaw bRaw haRaw ha.ne' hraw
𝗇 𝔤 (𝔅).prod 𝔔
𝗃 𝔥 fun ω x y => (hq t ἀ ω x y).le
𝗃 𝔧 ἀ t ht
/-- The actual observed posterior Fisher-energy path is integrable on the
source time interval as a consequence of its uniform complete-likelihood
energy budget. No path-integrability premise is supplied. -/
theorem highHistoryScore_sqrt_energy_intervalIntegrable [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔍) (hsymm : 𝔖)
    (Δ : ℕ) (π : Measure E) [IsProbabilityMeasure π]
    [𝔈]
    (activation : 𝔒) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 𝙑) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a v η aRaw bRaw T M : ℝ) (ha : 𝙆) (haRaw : 𝙓) (hT : 𝚞)
    (p F : 𝔇)
    hp hF
    (hprob : ∀ t ∈ 𝔗, IsProbabilityMeasure 𝔅)
    (hraw : 𝔓)
    (hq : ∀ t ∈ 𝔗, ∀ ω x y, 0 < 𝔡)
    (hE : ∀ t ∈ 𝔗, Integrable
      (fun z : 𝙗 × 𝔊 =>
        𝔙)
      𝔤)
    (hbudget : ∀ t ∈ 𝔗,
      (massPowerNormalizer 𝔅
        𝔉 n)⁻¹ *
        ∫ z : 𝙗 × 𝔊,
          𝔙
          ∂𝔤 ≤ M) :
    IntervalIntegrable (fun t => Real.sqrt $ ∫ z,
      𝔘
      ∂𝔛 ) volume 0 T := by
  have hb t (ht : t ∈ 𝔗) :
      𝔣 ≤ M := by
    letI := 𝔧 hprob
    rw [𝔜 𝔥 ht]
    exact (highMarginalRealScore_memLp_energy dependent hsymm
      𝔅 π activation ham Ba hBa habound
      n a 𝔄 η aRaw bRaw ha haRaw p F hp hF hraw 𝔧 hq 𝔧 hE).2.trans
      𝔧 hbudget
  have hi := intervalIntegrable_sqrt_of_measurable_bound _
    𝔦 highHistoryScoreEnergyProxy_measurable
    T M hT hb
  apply hi.congr
  intro t ht
  rw [uIoc_of_le hT] at ht
  letI := hprob t 𝔢
  dsimp
  rw [𝔜 𝔥 𝔢]
