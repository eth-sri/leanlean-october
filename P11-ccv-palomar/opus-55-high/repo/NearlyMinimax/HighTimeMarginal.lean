module

public import NearlyMinimax.HighTimeLikelihood
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Actual time-varying source-prior averages and posterior scores are jointly Borel. -/
𝚹
𝚮
𝚨
𝚭
𝚩
𝚲

𝗇 𝔄 𝙤
𝗇 𝔅 𝘳 z.1 π activation
𝗇 𝔊 𝙁
𝗇 𝔐 G (z.1,(ω,z.2))
𝗇 𝔑 fun z => ∫ ω, f (z,ω) ∂𝔄
𝗇 𝔔 𝙗
theorem historyMarkedPrior_integral_joint_measurable
    [MeasurableSpace E] [MeasurableSpace Z]
    (dependent : 𝔊) (Δ : ℕ) (π : Measure E)
    [SFinite 𝔄]
    activation (ham : Measurable activation)
    (G : ℝ × 𝔔 × Z → ℝ) (hG : Measurable G) :
    Measurable fun z : ℝ × Z =>
      ∫ ω, 𝔐 ∂𝔅 := by
  let f : (ℝ × Z) × 𝔔 → ℝ := fun z =>
    (ENNReal.ofReal $ 𝚇₂ z.1.1 activation z.2 ).toReal *
      G (z.1.1,(z.2,z.1.2))
  have hm :=
    (((historyMarkedDensity_joint_measurable dependent (historyReferenceRho Δ) activation ham).comp
      𝘙₂).ennreal_ofReal.ennreal_toReal).mul
      $ hG.comp $ (measurable_fst.comp measurable_fst).prodMk
        $ measurable_snd.prodMk $ measurable_snd.comp measurable_fst
  have hi : Measurable 𝔑 :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have he : (fun z => ∫ ω, 𝔐
      ∂𝔅) =
      𝔑 := by
    funext z
    rw [historyMarkedPrior_eq_withDensity dependent Δ z.1 π activation ham,
      integral_withDensity_eq_integral_toReal_smul
        (historyMarkedDensity_measurable dependent _ z.1 activation ham).ennreal_ofReal
        $ Eventually.of_forall 𝘕 ]
    rfl
  simp_all

𝗇 𝔇 𝔔 → 𝙀
𝗇 𝔈 ℝ × 𝙇 × 𝙈
𝗇 𝔉 v-𝙎*z.1
𝗇 𝔍 𝘍
𝗇 𝔎 historyMarkedPrior_integral_joint_measurable dependent Δ π activation ham _
𝗇 𝔒 𝗴
𝗇 𝔓 𝙏
theorem highMarginalRawLikelihood_time_measurable [MeasurableSpace E]
    (dependent : 𝔊) (Δ : ℕ) (π : Measure E)
    [SFinite 𝔄]
    (activation : 𝔓) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : 𝔇)
    (hp : 𝔍) (hF : 𝔒) :
    Measurable fun z : 𝔈 =>
      highMarginalRawLikelihood 𝔅
        n a 𝔉 p F z.2 :=
  𝔎
    $ highRawSampleLikelihood_time_measurable n a v η p F hp hF

𝗇 𝔏 𝘼
𝗃 𝔖 ἀ dependent hsymm 𝔅 π activation n a 𝔉 η p F z.2
theorem highMarginalIndexScore_time_measurable [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔊) (hsymm : 𝔏)
    (Δ : ℕ) (π : Measure E) [SFinite π] [SFinite 𝔄]
    (activation : 𝔓) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : 𝔇)
    (hp : 𝔍) (hF : 𝔒) :
    Measurable fun z : 𝔈 =>
      𝔖 highMarginalIndexScore :=
  (𝔎
    $ highHistoryLikelihoodDerivative_time_measurable dependent hsymm π activation ham n a v η p F hp hF ).div
    $ highMarginalRawLikelihood_time_measurable dependent Δ π activation ham n a v η p F hp hF

𝛀
attribute [local irreducible] highMarginalIndexScore highMarginalRawLikelihood
  historyMarkedPrior highRawDensityMass massPowerNormalizer

theorem highMarginalRealScore_time_measurable [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔊) (hsymm : 𝔏)
    (Δ : ℕ) (π : Measure E) [SFinite π] [SFinite 𝔄]
    (activation : 𝔓) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : 𝔇)
    (hp : 𝔍) (hF : 𝔒) :
    Measurable fun z : ℝ × 𝙌 =>
      𝔖 highMarginalRealScore := (highMarginalIndexScore_time_measurable dependent hsymm Δ π activation ham n a v η p F hp hF).comp
    $ measurable_fst.prodMk $ (decodeDesignResponse_measurable a).comp measurable_snd

theorem highMassPowerNormalizer_time_measurable [MeasurableSpace E]
    (dependent : 𝔊) (Δ : ℕ) (π : Measure E)
    [SFinite 𝔄]
    (activation : 𝔓) (ham : Measurable activation) (n : ℕ)
    (p : 𝔇) (hp : 𝔍) :
    Measurable fun t => massPowerNormalizer (𝘳 t π activation)
      𝙙 n := by
  unfold massPowerNormalizer
  have hG : Measurable fun z : ℝ × 𝔔 × Unit =>
      highRawDensityMass (p z.2.1)^n :=
    ((𝙨).pow_const n).comp $ measurable_fst.comp measurable_snd
  have hi :=
    𝔎 hG
  exact hi.comp $ show Measurable fun t => (t, ()) from
    measurable_id.prodMk measurable_const
