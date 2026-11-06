module

public import NearlyMinimax.AbsolutelyContinuousPathRisk
public import NearlyMinimax.Clipping
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Exceptional-state risk control for actual probability mixtures of original
sample laws. Clipping and the exceptional contribution are both derived. -/
𝚴
𝚮
𝚨
𝚩
𝚰

𝗇 𝔍 K ∘ₘ μ
theorem probability_kernel_integral [MeasurableSpace Α] [MeasurableSpace Ω]
    (μ : Measure Α) [IsProbabilityMeasure μ] (K : Kernel Α Ω) [IsMarkovKernel K]
    (f : 𝘄) (hf : Integrable f 𝔍) :
     ∫ x, f x ∂𝔍 = ∫ a, ∫ x, f x ∂K a ∂μ := by
  have h := Kernel.integral_comp (κ := Kernel.const Unit μ) (a := ())
     $ by assumption
  assumption

𝗇 𝔅 𝙰
theorem boundedEstimator_worstCaseRisk_finite (C : ModelConstants d)
    (T : 𝖧₂) : 𝚡₂ < ∞ := by
  have hb : 𝚡₂ ≤
      ENNReal.ofReal (𝔅 ^ 2) :=
    iSup_le fun θ => boundedEstimator_risk_le_diameter C T θ.val θ.property
  exact hb.trans_lt ENNReal.ofReal_lt_top

𝗇 𝔄 𝘔
𝗇 𝔇 T.val.val x - V
𝗇 𝔈 (𝚡₂).toReal
𝗇 𝔉 𝙌
𝗇 𝔊 hfi $ L a
𝗇 𝔎 L ∘ₘ σ
theorem boundedEstimator_mixture_risk_le_of_exceptional_set [MeasurableSpace Α]
    (C : ModelConstants d) (T : 𝖧₂)
    (σ : Measure Α) [IsProbabilityMeasure σ]
    (L : Kernel Α 𝔉) [IsMarkovKernel L]
    (θ : Α → RegressionParameter d) V ε
    (hL : ∀ a, L a = sampleLaw (θ a) n) (hVθ : ∀ a, (θ a).variance = V)
    (hV : V ∈ 𝙸₁)
    bad (hbad : MeasurableSet bad)
    (hlegal : ∀ a ∉ bad, Admissible C $ θ a )
    (hmass : σ.real bad ≤ ε) :
     ∫ x, 𝔇 ^ 2 ∂𝔎 ≤
      𝔈 + 𝔅 ^ 2 * ε := by
  let D := 𝔅
  let f x := 𝔇 ^ 2
  have hfmeas : Measurable f := (T.val.property.sub_const V).pow_const 2
  have hf0 x : 0 ≤ f x := sq_nonneg _
  have hcap x : f x ≤ 𝔄 := by
    have hh : |𝔇| ≤ D := by
      grind
    have hD : 0 ≤ D := sub_nonneg.mpr (effective_variance_interval_nondegenerate C).le
    simpa only [f, sq_abs] using (𝘉 hD).mpr hh
  have hfi (μ : Measure 𝔉) [IsProbabilityMeasure μ] : Integrable f μ := by
    apply (integrable_const 𝔄).mono' hfmeas.aestronglyMeasurable
    aesop
  let e a := ∫ x, f x ∂L a
  have hemeas : Measurable e := hfmeas.stronglyMeasurable.integral_kernel.measurable
  have he0 a : 0 ≤ e a := integral_nonneg hf0
  have hecap a : e a ≤ 𝔄 := by
    simpa only [integral_const, probReal_univ, one_smul] using integral_mono 𝔊 (integrable_const 𝔄) hcap
  have hei : Integrable e σ := by
    apply (integrable_const 𝔄).mono' hemeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg $ he0 a ]
      exact hecap a
  have hgood a (ha : Admissible C $ θ a ) : e a ≤ 𝔈 := by
    have heq : ENNReal.ofReal (e a) = meanSquaredRisk T.val (θ a) := by
      rw [meanSquaredRisk, ← hL a, hVθ a]
      exact ofReal_integral_eq_lintegral_ofReal 𝔊
        $ Filter.Eventually.of_forall hf0
    have h := ENNReal.toReal_mono (boundedEstimator_worstCaseRisk_finite C T).ne
      $ meanSquaredRisk_le_worstCaseRisk C T.val (θ a) ha
    rwa [← heq, ENNReal.toReal_ofReal $ he0 a ] at h
  rw [probability_kernel_integral σ L f $ hfi 𝔎 ]
  exact probability_mixture_exceptional_risk_bound σ e bad hbad
    𝔈 D ε hei ENNReal.toReal_nonneg
    (Filter.Eventually.of_forall fun a ha => hgood a $ hlegal a ha )
    (Filter.Eventually.of_forall fun a _ => hecap a ) hmass
