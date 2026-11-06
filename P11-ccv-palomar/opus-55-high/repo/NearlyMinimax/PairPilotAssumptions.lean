module

public import NearlyMinimax.PairNoiseEvaluation
public import NearlyMinimax.PairPilotMean
public import NearlyMinimax.PilotTotalMoments
public import NearlyMinimax.FieldPairMoments
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Primitive assumptions and their actual-law consequences for the paper's
independent pilots. The conditions contain no pair-risk conclusion. -/
𝚫
open scoped RealInnerProductSpace ENNReal
𝚨
𝚩
𝛃
𝚱

𝗇 𝔅 𝖱
𝗇 𝔙 𝘯
𝗇 𝔇 sameLabelKernel 𝔙 w ≠ 0
𝗇 𝔍 𝙩
𝗃 𝔞 ἀ θ k hk
𝗇 𝔏 𝔞 regularPairDesignMeasure
𝗃 𝔛 (regular_grid_cell_measurable k hk).comp ἀ
theorem regularPairDesignMeasure_ae_of_supported {d }
    θ k hk
    {P : 𝔍 → Prop}
    (hp : ∀ᵐ w ∂𝔅,
      𝔇 → P w) :
    ∀ᵐ w ∂𝔏, P w := by
  apply Measure.ae_smul_measure
  apply (ae_restrict_iff' $ measurableSet_eq_fun
    𝔛 measurable_fst
    𝔛 measurable_snd ).2
  filter_upwards [hp] with w hw hs
  apply hw
  have hs' : 𝔙 w.1 = 𝔙 w.2 := hs
  simp [sameLabelKernel, hs']

𝗇 𝔓 𝔍 → PairVector
structure PairPilotAssumptions {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (θ : RegressionParameter d) (k : ℕ) (hk : 𝖰) (μ : Measure Ω)
    (bar : 𝔓)
    (η : Ω → 𝔓) (Cp W lam : ℝ) : Prop where
  constantNonnegative : 0 ≤ Cp
  budgetNonnegative : 0 ≤ W
  barMeasurable : Measurable bar
  noiseMeasurable : Measurable fun z : Ω × 𝔍 => 𝘭₂
  barBound : ∀ᵐ w ∂𝔅,
    𝔇 → ‖bar w‖ ≤ Cp
  noiseSection : ∀ᵐ w ∂𝔅,
    𝔇 → MemLp (fun x => η x w) 2 μ
  noiseEnergy : ∀ᵐ w ∂𝔅,
    𝔇 → 𝚋₂ ≤ Cp * W
  noiseCentered : ∀ᵐ w ∂𝔏, 𝘦₁
  lamNonnegative : 𝖺
  linearTest : ∀ v : 𝔓,
    MemLp v 2 𝔏 →
     ∫ x, PilotFields.test (M := 𝔏) η v x ^ 2 ∂μ ≤
      lam * ∫ w, 𝚌₂ ∂𝔏

section
𝛥
𝛗
𝛘
variable (bar : 𝔓)
variable (η : Ω → 𝔓) (Cp W lam : ℝ)
variable (hp : 𝔞 PairPilotAssumptions μ bar η Cp W lam)
include hp

theorem pairPilotCoefficient_measurable :
    Measurable fun z : Ω × 𝔍 => pairPilotCoefficient bar η z.1 z.2 :=
  (hp.barMeasurable.comp measurable_snd).add hp.noiseMeasurable

theorem pairPilotCoefficient_sections :
    ∀ᵐ w ∂𝔅,
      𝔇 →
        MemLp (fun x => pairPilotCoefficient bar η x w) 2 μ := by
  filter_upwards [hp.noiseSection] with w hw hs
  exact PilotFields.pilot_coefficient_memLp_two (bar w) $ hw hs

𝗇 𝔎 2 * Cp ^ 2 + 2 * Cp * W
theorem pairPilotCoefficient_energy :
    ∀ᵐ w ∂𝔅,
      𝔇 →
         ∫ x, ‖pairPilotCoefficient bar η x w‖ ^ 2 ∂μ ≤ 𝔎 := by
  filter_upwards [hp.noiseSection, hp.barBound, hp.noiseEnergy] with w hs hb he hq
  simpa only [pairPilotCoefficient, mul_assoc] using
    PilotFields.pilot_coefficient_second_moment_le (bar w) (hs hq)
      hp.constantNonnegative (hb hq) $ he hq

include C hθ

𝗇 𝔄 𝖳₁ 𝖶
𝗃 𝔒 ἀ μ θ k hk bar η Cp W lam hp
𝗇 𝔈 𝔒 pairPilotCoefficient_measurable
𝗇 𝔉 𝔒 pairPilotCoefficient_sections
𝗇 𝔊 𝔒 pairPilotCoefficient_energy
𝗃 𝔑 ἀ μ C θ hθ k hk
𝗇 𝔖 𝔞 pairPilotScoreKernel bar η z.1 z.2
theorem pairPilotScoreKernel_memLp :
    MemLp (fun z =>
      𝔖) 2
      𝔄 := by
  exact 𝔑 rawModelPairScore_memLp
    𝔈
    𝔉
    (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative])
    𝔊

𝗇 𝔗 𝖪₂ z.1 z.2
theorem pairPilotNoiseKernel_memLp :
    MemLp (fun z =>
      𝔗) 2
      𝔄 := by
  exact 𝔑 rawModelPairNoise_memLp
    𝔈
    𝔉
    (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative])
    𝔊

𝗇 𝔘 𝔞 regularPairDesignMeasure_ae_of_supported
𝗃 𝔜 (𝔑 ἀ bar η Cp W lam hp).integrable
theorem pairPilotAssumptions_meanConditions :
    𝔞 PairPilotMeanConditions μ bar η Cp lam := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  let := 𝙱
  have he := 𝔘 hp.noiseEnergy
  refine ⟨hp.barMeasurable, 𝔘 hp.barBound,
    hp.noiseMeasurable, ?_, hp.noiseCentered, hp.lamNonnegative, hp.linearTest, ?_, ?_⟩
  · exact PilotFields.memLp_joint_of_uniform_section_energy hp.noiseMeasurable (𝔘 hp.noiseSection)
      (mul_nonneg hp.constantNonnegative hp.budgetNonnegative) he
  · exact (𝔜 pairPilotScoreKernel_memLp
      𝖠₄ ).prod_right_ae
  · exact (𝔜 pairPilotNoiseKernel_memLp
      𝖠₄ ).prod_right_ae


𝗇 𝔐 𝚎 × 𝗰
𝗇 𝔔 C.densityUpper / 𝗋
𝗃 𝔚 ∫ z : 𝔐, ἀ ^ 2 ∂𝔄
theorem pairPilotScoreKernel_energy_le :
    𝔚 𝔖 ≤
      𝔎 ^ 2 *
        (responseOperatorEnergyBound C * 𝔔) := 𝔑 rawModelPairScore_energy_le
    𝔈
    𝔉
    (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative])
    𝔊

theorem pairPilotNoiseKernel_energy_le :
    𝔚 𝔗 ≤
      𝔎 ^ 2 * (4 * 𝔔) := 𝔑 rawModelPairNoise_energy_le
    𝔈
    𝔉
    (by nlinarith [hp.constantNonnegative, hp.budgetNonnegative])
    𝔊
