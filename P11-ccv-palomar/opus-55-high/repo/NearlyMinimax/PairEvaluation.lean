module

public import NearlyMinimax.PilotMasking
public import NearlyMinimax.TwoStagePairRisk
public import NearlyMinimax.ResponseOperatorEnergy
public import RoughRegime.Macro


𝗌

/-! Genuine L² and second-moment bounds for the original model's random
pair-score kernel, using independent pilot second moments only. -/
𝚵
𝚻
𝚨
𝚩
𝛃
𝚭

𝗇 𝔄 Observation d × Observation d
𝗇 𝔖 Covariate d × Covariate d
def pairCovariates (z : 𝔄) : 𝔖 :=
  (z.1.1, z.2.1)

𝗃 𝔠 ἀ (d := d)
theorem pairCovariates_measurable d : Measurable 𝔠 pairCovariates :=
  measurable_fst.fst.prodMk measurable_snd.fst

𝗇 𝔉 (observationLaw θ).prod $ observationLaw θ
𝗇 𝔓 (designLaw θ).prod $ designLaw θ
𝗃 𝔗 ἀ C θ hθ
theorem observationPair_covariates_measurePreserving C
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    MeasurePreserving pairCovariates 𝔉
      𝔓 := by
  let := 𝔗 observationLaw_isProbability
  exact (𝔗 observationLaw_fst_measurePreserving).prod
    𝔗 observationLaw_fst_measurePreserving

𝗇 𝔍 Ω → 𝔖 → PairVector
𝗇 𝔎 Ω × Ω
𝗇 𝔚 regularObservationLabel k hk
𝗃 𝔡 c ἀ $ pairCovariates z
def rawModelPairScore (θ : RegressionParameter d)
    (k : ℕ) (hk : 0 < k) (c : 𝔍)
    (p : 𝔎) (z : 𝔄) : ℝ :=
  sameLabelKernel 𝔚 z *
    ⟪𝔡 p.1, pairScoreOperator θ.variance z.1.2 z.2.2
      𝔡 p.2⟫

𝗇 𝔛 𝔄 × PairVector
𝗇 𝔜 pairResponseVector z.1.1.2 z.1.2.2
theorem observationPairScoreOperator_measurable_apply {d } V :
    Measurable fun z : 𝔛 =>
      pairScoreOperator V z.1.1.2 z.1.2.2 z.2 := by
  have hv : Continuous fun z : 𝔛 =>
      𝔜 :=
    pairResponseVector_continuous.comp
      $ continuous_fst.fst.snd.prodMk continuous_fst.snd.snd
  have hi : Continuous fun z : 𝔛 =>
      ⟪𝔜, z.2⟫ := hv.inner continuous_snd
  have hs : Continuous fun z : 𝔛 =>
      ⟪𝔜, z.2⟫ • 𝔜 := hi.smul hv
  simpa only [pairScoreOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.rankOne_apply, starRingEnd_apply, star_trivial,
    Pi.sub_def, Pi.smul_def, Function.comp_def] using
    (hs.sub $ (pairNoiseOperator.continuous.comp continuous_snd).const_smul V ).measurable

𝗇 𝔅 Measurable fun z : Ω × 𝔖 => c z.1 z.2
theorem pilotOnObservations_measurable {Ω } [MeasurableSpace Ω] {d }
    {c : 𝔍}
    (hmc : 𝔅) :
    Measurable fun z : Ω × 𝔄 => c z.1 $ pairCovariates z.2 :=
  hmc.comp $ measurable_fst.prodMk $ (pairCovariates_measurable d).comp measurable_snd

𝗇 𝔊 𝔠 regularObservationLabel k hk
𝗇 𝔏 rawModelPairScore θ k hk c z.1 z.2
𝗇 𝔐 𝔠 regularObservationLabel_measurable k hk
𝗇 𝔑 𝔠 observationPairScoreOperator_measurable_apply θ.variance
𝗇 𝔒 fun x z => 𝔡 x
𝗇 𝔔 fun z : 𝔎 × 𝔄 => 𝔏
𝗇 𝔘 fun z : 𝔄 => pairScoreOperator θ.variance z.1.2 z.2.2
𝗇 𝔞 sameLabelKernel_measurable 𝔊 𝔐
theorem rawModelPairScore_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 0 < k)
    {c : 𝔍}
    (hmc : 𝔅) :
    Measurable 𝔔 := by
  exact PilotFields.maskedPilotKernel_measurable
    (c := 𝔒)
    (A := 𝔘)
    (q := sameLabelKernel 𝔊)
    (pilotOnObservations_measurable hmc)
    𝔑
    𝔞

𝗇 𝔟 sameLabelKernel (regularGridCell k hk) w ≠ 0
𝗇 𝔇 ∀ᵐ w ∂𝔓, 𝔟 → ∫ x, ‖c x w‖ ^ 2 ∂π ≤ L
𝗇 𝔈 ∀ᵐ w ∂𝔓, 𝔟 → MemLp (fun x => c x w) 2 π
𝗇 𝔙 (π.prod π).prod 𝔉
𝗃 𝔢 𝔗 ἀ k hk
theorem rawModelPairScore_memLp {Ω : Type*} [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π] {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) (k : ℕ) (hk : 0 < k)
    {c : 𝔍}
    (hmc : 𝔅)
    (hc : 𝔈)
    {L : ℝ} (hL : 0 ≤ L) (hE : 𝔇) :
    MemLp 𝔔
      2 𝔙 := by
  let := 𝔗 observationLaw_isProbability
  have hmp := 𝔗 observationPair_covariates_measurePreserving
  apply PilotFields.maskedPilotKernel_memLp_of_supported_sections
    (μ := π) (ν := 𝔉)
    (c := 𝔒)
    (A := 𝔘)
    (q := sameLabelKernel 𝔊)
    (pilotOnObservations_measurable hmc)
    𝔑
    𝔞
  · intro z
    unfold sameLabelKernel
    simp
  · exact 𝔢 regularResponseOperatorEnergy_integrable
  · exact hmp.quasiMeasurePreserving.ae hc
  · exact hL
  · exact hmp.quasiMeasurePreserving.ae hE

theorem rawModelPairScore_energy_le {Ω } [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π] {d } C
    θ (hθ : Admissible C θ) k hk
    {c }
    (hmc : 𝔅)
    (hc : 𝔈)
    {L } (hL : 0 ≤ L) (hE : 𝔇) :
     ∫ z : 𝔎 × 𝔄, 𝔏 ^ 2
      ∂𝔙 ≤
      L ^ 2 * (responseOperatorEnergyBound C * (C.densityUpper / k ^ d)) := by
  let := 𝔗 observationLaw_isProbability
  have hmp := 𝔗 observationPair_covariates_measurePreserving
  have he := PilotFields.maskedPilotKernel_energy_le_of_supported_sections




    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply θ.variance)
    (sameLabelKernel_measurable 𝔚
      $ regularObservationLabel_measurable k hk )
     fun z => by unfold sameLabelKernel; simp
    𝔢 regularResponseOperatorEnergy_integrable
    (hmp.quasiMeasurePreserving.ae hc) hL $ hmp.quasiMeasurePreserving.ae hE
  exact he.trans $ mul_le_mul_of_nonneg_left 𝔢 regularResponseOperatorEnergy_le
    $ sq_nonneg L
