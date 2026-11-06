module

public import NearlyMinimax.PairPilotAssumptions
public import NearlyMinimax.FieldPairVariance
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Full two-stage variance of the paper's actual score and denominator. -/
𝚵
open scoped ENNReal RealInnerProductSpace
𝚨
𝚩
𝛃
𝚱

𝗇 𝔏 𝙦 ^ d
def pairEvaluationCoefficient (C : ModelConstants d) (m k : ℕ) : ℝ :=
  C.densityUpper / 𝘏₂ + 𝔏 / (2 * 𝘏₂ * (m - 1 : ℕ))

𝗇 𝔟 𝙩
𝗇 𝔈 𝔟 → PairVector
𝗃 𝔗 ἀ θ k hk
def pairPilotVarianceBase [MeasurableSpace Ω]
    (θ : RegressionParameter d) (k : ℕ) (hk : 𝖰) (μ : Measure Ω)
    (bar : 𝔈)
    (η : Ω → 𝔈) : ℝ :=
  2 * ∫ w, ‖bar w‖ ^ 2 ∂𝔗 regularPairDesignMeasure +
    ∫ z : Ω × 𝔟, ‖𝘭₂‖ ^ 2
      ∂μ.prod 𝔗 regularPairDesignMeasure

𝗃 𝔡 𝔗 ἀ μ bar η
𝗇 𝔅 𝔡 pairPilotVarianceBase
theorem pairPilotVarianceBase_nonneg [MeasurableSpace Ω]
    (θ : RegressionParameter d) k hk (μ : Measure Ω)
    bar
    η :
    0 ≤ 𝔅 := by
  unfold pairPilotVarianceBase
  positivity

section
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
𝛟
𝛗
𝛘
variable (bar : 𝔈)
variable (η : Ω → 𝔈) (Cp W lam : ℝ)
variable (hp : 𝔡 PairPilotAssumptions Cp W lam)
𝛠
variable (hind : iIndepFun X ν) (hX : 𝗯₁)
include hθ hp hm hind hX

𝗇 𝔄 (2 * Cp ^ 2 + 2 * Cp * W) ^ 2
𝗇 𝔇 𝗳₂ ^ 2
𝗃 𝔖 ἀ μ C θ hθ k hk bar η Cp W lam hp
𝗇 𝔉 𝔖 pairPilotAssumptions_meanConditions
𝗇 𝔊 pairEvaluationCoefficient C m k
𝗇 𝔞 𝖳₁
𝗇 𝔍 𝔞 𝖶
𝗇 𝔎 pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp
𝗇 𝔐 𝚎 × 𝗰
𝗇 𝔑 𝗋
𝗇 𝔒 3 / 4 * lam * 𝔇 * 𝔅
𝗇 𝔓 𝔗 pairPilotScoreKernel bar η
𝗃 𝔘 ἀ C θ hθ k hk
𝗃 𝔙 PairUStatistic.fieldPairAverage_centered_sq_le (G := ἀ) hm X hind hX (regularObservationLabel k hk) (regularObservationLabel_measurable k hk) hmeas
𝗇 𝔚 𝔄 * responseOperatorEnergyBound C * C.densityUpper
𝗇 𝔛 div_nonneg hpplus hkp.le
𝗃 𝔠 𝔑 * ∫ z : 𝔐, ἀ z.1 z.2 ^ 2 ∂𝔍
𝗃 𝔢 ∫ p, 𝔗 ἀ bar η p ∂μ.prod μ
𝗃 𝔣 2 * 𝔊 * _ + 2 * ἀ ≤ _
theorem pairPilotScoreEstimate_centered_sq_le :
     ∫ z, (PairUStatistic.fieldPairAverage m 𝔑
      𝔓 X z -
        𝔢 pairPilotScoreMean) ^ 2 ∂𝔞 ν ≤
      2 * 𝔊 *
        𝔚 +
      𝗞 * lam * 𝔇 *
        𝔅 := by
  let := 𝙱
  obtain ⟨hmean, hvar⟩ := 𝔘 pairPilotScoreMean_variance_le μ bar η Cp lam 𝔉
  have hmeas := 𝔗 rawModelPairScore_measurable
    𝔎
  have hkp : 0 < 𝔏 := pow_pos (by exact_mod_cast hk) d
  have hpplus : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hd0 : 0 ≤ 𝔒 := by
    have hb := 𝔡 pairPilotVarianceBase_nonneg
    have hl := hp.lamNonnegative
    positivity
  have hr := 𝔙 𝔓 𝔖 pairPilotScoreKernel_memLp
     fun p x y hxy => by simp [pairPilotScoreKernel, pairScoreFieldKernel,
      sameLabelKernel] at hxy ⊢; exact hxy.elim
    hkp 𝔛
     fun i => by
      rw [𝔘 regularObservationLabel_mass i]
      exact 𝔘 regularGridProbability_cap i
    (by rw [mul_div_cancel₀ _ hkp.ne']) hd0 hmean hvar
  have hE : 𝔠 𝔓 ≤
      𝔚 := by
    apply (mul_le_mul_of_nonneg_left 𝔖 pairPilotScoreKernel_energy_le hkp.le).trans_eq
    field_simp
  have heval : 0 ≤ 𝔊 := by unfold pairEvaluationCoefficient; positivity
  apply hr.trans
  change 𝔣 𝔒
  nlinarith

𝗇 𝔔 𝖪₂
𝗇 𝔜 3 * lam * 𝔅
theorem pairPilotNoiseEstimate_centered_sq_le :
     ∫ z, (PairUStatistic.fieldPairAverage m 𝔑
      𝔔 X z -
        𝔢 pairPilotNoiseMean) ^ 2 ∂𝔞 ν ≤
      8 * 𝔊 *
        (𝔄 * C.densityUpper) +
      6 * lam * 𝔅 := by
  let := 𝙱
  obtain ⟨hmean, hvar⟩ := 𝔘 pairPilotNoiseMean_variance_le μ bar η Cp lam 𝔉
  have hmeas := rawModelPairNoise_measurable k hk
    𝔎
  have hkp : 0 < 𝔏 := pow_pos (by exact_mod_cast hk) d
  have hpplus : 0 ≤ C.densityUpper := by linarith [C.one_lt_densityUpper]
  have hd0 : 0 ≤ 𝔜 := by
    have hb := 𝔡 pairPilotVarianceBase_nonneg
    have hl := hp.lamNonnegative
    positivity
  have hr := 𝔙 𝔔 𝔖 pairPilotNoiseKernel_memLp
     fun p x y hxy => by simp [pairPilotNoiseKernel, pairNoiseFieldKernel,
      sameLabelKernel] at hxy ⊢; exact hxy.elim
    hkp 𝔛
     fun i => by
      rw [𝔘 regularObservationLabel_mass i]
      exact 𝔘 regularGridProbability_cap i
    (by rw [mul_div_cancel₀ _ hkp.ne']) hd0 hmean hvar
  have hE : 𝔠 𝔔 ≤
      4 * 𝔄 * C.densityUpper := by
    apply (mul_le_mul_of_nonneg_left 𝔖 pairPilotNoiseKernel_energy_le hkp.le).trans_eq
    field_simp
  have heval : 0 ≤ 𝔊 := by unfold pairEvaluationCoefficient; positivity
  apply hr.trans
  change 𝔣 𝔜
  nlinarith
