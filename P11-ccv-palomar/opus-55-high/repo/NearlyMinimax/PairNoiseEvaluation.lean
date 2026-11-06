module

public import NearlyMinimax.PairEvaluation
public import RoughRegime.Macro


𝗌

/-! The same actual-law pilot-energy argument for the pair denominator. -/
𝚯
𝚻
𝚨
𝚩
𝛃
𝚭

𝗇 𝔅 (observationLaw θ).prod $ observationLaw θ
𝗇 𝔍 regularObservationLabel k hk
𝗇 𝔏 regularObservationLabel_measurable k hk
𝗇 𝔒 observationLaw_isProbability C θ hθ
𝗇 𝔗 sameLabelKernel 𝔍 z * ‖pairNoiseOperator‖ ^ 2
𝗇 𝔙 Admissible C θ
theorem observationPairNoiseOperator_energy_integrable C
    (θ : RegressionParameter d) (hθ : 𝔙) k hk :
    Integrable (fun z =>
      𝔗)
      𝔅 := by
  let := 𝔒
  exact ((sameLabelKernel_memLp (observationLaw θ) _
    𝔏).integrable $ by norm_num ).mul_const _

𝗇 𝔉 Observation d × Observation d
𝗇 𝔐 4 * (C.densityUpper / k ^ d)
𝗃 𝔖 ἀ C θ hθ k hk
theorem observationPairNoiseOperator_energy_le C
    θ (hθ : 𝔙) k hk :
     ∫ z : 𝔉,
      𝔗
      ∂𝔅 ≤ 𝔐 := by
  let := 𝔒
  rw [integral_mul_const, sameLabelKernel_integral (observationLaw θ) _
    𝔏]
  simp_rw [𝔖 regularObservationLabel_mass]
  have hq : 0 ≤ regularGridCollisionMass θ k hk := by
    unfold regularGridCollisionMass
    positivity
  have hN : ‖pairNoiseOperator‖ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) pairNoiseOperator_norm_le 2
    linarith
  calc
    _ ≤ regularGridCollisionMass θ k hk * 4 := mul_le_mul_of_nonneg_left hN hq
    _ ≤ _ := by have h := 𝔖 regularGridCollisionMass_upper; linarith

𝗇 𝔎 Ω × Ω
𝗇 𝔚 0 < k
𝗇 𝔞 Covariate d × Covariate d
𝗃 𝔟 c ἀ $ pairCovariates z
def rawModelPairNoise (k : ℕ) (hk : 𝔚)
    (c : Ω → 𝔞 → PairVector)
    (p : 𝔎) (z : 𝔉) : ℝ :=
  sameLabelKernel 𝔍 z *
    ⟪𝔟 p.1, pairNoiseOperator 𝔟 p.2⟫

𝗇 𝔇 Measurable fun z : Ω × 𝔞 => c z.1 z.2
𝗃 𝔠 ἀ (d := d) k hk
𝗇 𝔊 sameLabelKernel_measurable 𝔠 regularObservationLabel 𝔠 regularObservationLabel_measurable
𝗇 𝔑 rawModelPairNoise k hk c z.1 z.2
𝗇 𝔓 fun x z => 𝔟 x
𝗇 𝔔 fun z : 𝔎 × 𝔉 => 𝔑
theorem rawModelPairNoise_measurable [MeasurableSpace Ω]
    (k : ℕ) (hk : 𝔚)
    (hmc : 𝔇) :
    Measurable 𝔔 := by
  exact PilotFields.maskedPilotKernel_measurable
    (c := 𝔓)
    (A := fun _ : 𝔉 => pairNoiseOperator)

    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    𝔊

𝗇 𝔛 (designLaw θ).prod $ designLaw θ
𝗇 𝔜 sameLabelKernel (regularGridCell k hk) w ≠ 0
𝗇 𝔄 ∀ᵐ w ∂𝔛, 𝔜 → ∫ x, ‖c x w‖ ^ 2 ∂π ≤ L
𝗇 𝔈 ∀ᵐ w ∂𝔛, 𝔜 → MemLp (fun x => c x w) 2 π
𝗇 𝔘 (π.prod π).prod 𝔅
theorem rawModelPairNoise_memLp [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π] (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : 𝔙) (k : ℕ) (hk : 𝔚)

    (hmc : 𝔇)
    (hc : 𝔈)
    (hL : 0 ≤ L) (hE : 𝔄) :
    MemLp 𝔔
      2 𝔘 := by
  let := 𝔒
  have hmp := observationPair_covariates_measurePreserving C θ hθ
  apply PilotFields.maskedPilotKernel_memLp_of_supported_sections
    (μ := π) (ν := 𝔅)
    (c := 𝔓)
    (A := fun _ : 𝔉 => pairNoiseOperator)

    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    𝔊
  · intro z
    unfold sameLabelKernel
    simp
  · exact 𝔖 observationPairNoiseOperator_energy_integrable
  · exact hmp.quasiMeasurePreserving.ae hc
  · exact hL
  · exact hmp.quasiMeasurePreserving.ae hE

theorem rawModelPairNoise_energy_le [MeasurableSpace Ω]
    (π : Measure Ω) [IsProbabilityMeasure π] (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : 𝔙) (k : ℕ) (hk : 𝔚)

    (hmc : 𝔇)
    (hc : 𝔈)
    (hL : 0 ≤ L) (hE : 𝔄) :
     ∫ z : 𝔎 × 𝔉, 𝔑 ^ 2
      ∂𝔘 ≤
      L ^ 2 * 𝔐 := by
  let := 𝔒
  have hmp := observationPair_covariates_measurePreserving C θ hθ
  have he := PilotFields.maskedPilotKernel_energy_le_of_supported_sections




    (pilotOnObservations_measurable hmc)
    (pairNoiseOperator.continuous.measurable.comp measurable_snd)
    (sameLabelKernel_measurable 𝔍
      𝔏)
     fun z => by unfold sameLabelKernel; simp
    𝔖 observationPairNoiseOperator_energy_integrable
    (hmp.quasiMeasurePreserving.ae hc) hL $ hmp.quasiMeasurePreserving.ae hE
  exact he.trans $ mul_le_mul_of_nonneg_left 𝔖 observationPairNoiseOperator_energy_le
    $ sq_nonneg L
