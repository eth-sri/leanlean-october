module

public import NearlyMinimax.HighMarginalScoreEnergy
public import NearlyMinimax.HighMarginalScoreCenter
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Genuine joint time measurability of source priors and likelihood scores. -/
𝚹
𝛉
𝚨
𝚭
𝚩
𝚲

𝗇 𝔍 𝙗
𝗇 𝔓 𝙁
theorem historyMarkedDensity_joint_measurable [MeasurableSpace E]
    (dependent : 𝔓) ρ activation (ham : Measurable activation) :
    Measurable fun z : ℝ × 𝔍 =>
      𝘡₂ z.1 activation z.2 := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun t ω => 𝘡₂ t activation ω)
  · intro ω
    exact continuous_iff_continuousAt.mpr fun t =>
      (historyMarkedDensity_hasDerivAt dependent ρ t activation ω).continuousAt
  · exact fun t => historyMarkedDensity_measurable dependent ρ t activation ham

𝗇 𝔄 𝙇 × 𝙈
𝗇 𝔔 𝙎
𝗇 𝔅 v-𝔔*z.1
𝗇 𝔇 v-𝔔*t
𝗇 𝔈 𝘍
𝗇 𝔉 𝗴
𝗇 𝔎 𝙀
𝗇 𝔐 Ω × 𝔄
𝗃 𝔑 measurable_uncurry_of_continuous_of_measurable (u := fun t (z : 𝔐) => ἀ n a 𝔇 (p z.1) (F z.1) z.2)
𝗃 𝔒 fun z : ℝ × 𝔐 => ἀ n a 𝔅 (p z.2.1) (F z.2.1) z.2.2
𝗃 𝔖 fun t => ἀ n a 𝔇 p F hp hF
theorem highRawSampleLikelihood_time_measurable [MeasurableSpace Ω]
    (n : ℕ) (a v η : ℝ) (p F : Ω → 𝔎)
    (hp : 𝔈) (hF : 𝔉) :
    Measurable 𝔒 highRawSampleLikelihood := by
  apply 𝔑 highRawSampleLikelihood
  · intro z
    exact continuous_iff_continuousAt.mpr fun t =>
      (highRawSampleLikelihood_hasDerivAt_path n a v η t (p z.1) (F z.1) z.2).continuousAt
  · exact 𝔖 highRawSampleLikelihood_joint_measurable

theorem ternaryMass_continuous_variance a f y :
    Continuous fun V => ternaryMass a f V y := by
  fin_cases y <;> simp only [ternaryMass]
  all_goals fun_prop

theorem highRawSampleVarianceDerivative_time_measurable [MeasurableSpace Ω]
    (n : ℕ) (a v η : ℝ) (p F : Ω → 𝔎)
    (hp : 𝔈) (hF : 𝔉) :
    Measurable 𝔒 highRawSampleVarianceDerivative := by
  apply 𝔑 highRawSampleVarianceDerivative
  · intro z
    apply Continuous.mul continuous_const
    apply continuous_finset_sum
    intro i _
    apply Continuous.mul _ continuous_const
    apply continuous_finset_prod
    intro j _
    exact (ternaryMass_continuous_variance a ..).comp 𝖦₃
  · exact 𝔖 highRawSampleVarianceDerivative_joint_measurable

𝗇 𝔊 𝘼
𝗇 𝔏 ℝ × 𝔍 × 𝔄
theorem highAppendLikelihoodAction_time_measurable [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔓) (hsymm : 𝔊)
    (π : Measure E) [SFinite π] (activation : 𝙏) (ham : Measurable activation)
    (n : ℕ) (a v η : ℝ) (p F : 𝔍 → 𝔎)
    (hp : 𝔈) (hF : 𝔉) j :
    Measurable fun z : 𝔏 =>
      highAppendLikelihoodAction dependent hsymm π activation n a 𝔅 p F j z.2.1 z.2.2 := by
  have hc : Measurable fun z :
      𝔏 × E =>
      (z.1.1,(𝙯₁ (z.1.2.1,z.2),z.1.2.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      $ ((historyMarkedAppend_measurable dependent hsymm j).comp
        $ (measurable_fst.comp $ measurable_snd.comp measurable_fst ).prodMk measurable_snd ).prodMk
        $ measurable_snd.comp $ measurable_snd.comp measurable_fst
  have hj :=
    (ham.comp measurable_snd).mul
      $ (highRawSampleLikelihood_time_measurable n a v η p F hp hF).comp hc
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

theorem highHistoryLikelihoodDerivative_time_measurable [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔓) (hsymm : 𝔊)
    (π : Measure E) [SFinite π] (activation : 𝙏) (ham : Measurable activation)
    (n : ℕ) (a v η : ℝ) (p F : 𝔍 → 𝔎)
    (hp : 𝔈) (hF : 𝔉) :
    Measurable fun z : 𝔏 =>
      𝗿₁ 𝔅 η p F z.2.1 z.2.2 := (Finset.measurable_sum _ fun j _ =>
    highAppendLikelihoodAction_time_measurable dependent hsymm π activation ham n a v η p F hp hF j ).sub
      $ (highRawSampleVarianceDerivative_time_measurable n a v η p F hp hF).const_mul 𝔔
