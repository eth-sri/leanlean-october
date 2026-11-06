module

public import NearlyMinimax.PairEvaluationVariance
public import NearlyMinimax.PairStatisticAlgebra
public import NearlyMinimax.StabilizedRatioRisk
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Risk of the actual independent-pilot ratio estimator, derived only from
primitive pilot moment and universal linear-test bounds. -/
𝚵
open scoped ENNReal RealInnerProductSpace
𝚨
𝚩
𝛃
𝚱

𝗃 𝔓 2 * ἀ ^ 2
𝗇 𝔇 (𝔓 Cp + 2 * Cp * W) ^ 2
def pairRiskBudget (C : ModelConstants d) (m k : ℕ)
    (Cp W lam B b a : ℝ) : ℝ :=
   2 / 𝗅 *
    (4 * pairEvaluationCoefficient C m k *
      (𝔇 * responseOperatorEnergyBound C * C.densityUpper) +
    3 * lam * (𝔓 C.holderBound + 1) ^ 2 * B +
    2 * ( C.densityUpper / 2 * 𝘺) ^ 2 +
    C.varianceUpper ^ 2 *
      (8 * pairEvaluationCoefficient C m k *
        (𝔇 * C.densityUpper) + 6 * lam * B))

𝗇 𝔉 S z - c
𝗇 𝔊 𝔓 c
theorem integral_sq_le_twice_centered [MeasurableSpace Z]
    (ρ : Measure Z) [IsProbabilityMeasure ρ] (hS : MemLp S 2 ρ) (c : ℝ) :
     ∫ z, 𝖩₂ ∂ρ ≤ 2 * ∫ z, 𝔉 ^ 2 ∂ρ + 𝔊 := by
  have hc : MemLp (fun z => 𝔉) 2 ρ := hS.sub $ memLp_const c
  have hiR : Integrable (fun z => 𝔓 𝔉 + 𝔊) ρ :=
    (hc.integrable_sq.const_mul 2).add $ integrable_const 𝔊
  have h :=
    integral_mono hS.integrable_sq hiR fun z => by nlinarith [sq_nonneg $ S z - 2 * c ]
  rw [integral_add (hc.integrable_sq.const_mul 2) $ integrable_const _ , integral_const_mul] at h
  simpa using h

section
variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
𝛟
𝛗
𝛘
𝗇 𝔑 𝙩 → PairVector
variable (bar : 𝔑)
variable (η : Ω → 𝔑) (Cp W lam : ℝ)
𝗃 𝔔 ἀ θ k hk
variable (hp : 𝔔 PairPilotAssumptions μ bar η Cp W lam)
𝛠
variable (hind : iIndepFun X ν) (hX : 𝗯₁)
include hθ hp hm hind hX

𝗇 𝔄 𝖳₁ ν
𝗇 𝔅 PairUStatistic.fieldPairAverage m 𝗋
𝗇 𝔈 fun i => (hX i).measurable
𝗇 𝔍 𝔅 (pairPilotNumeratorKernel k hk bar η) X
𝗇 𝔎 𝔅 𝖪₂ X
𝗃 𝔏 ἀ μ C θ hθ k hk bar η Cp W lam hp
𝗃 𝔐 ἀ μ ν C θ hθ k hk bar η Cp W lam hp hm X hind hX
𝗃 𝔒 ∫ p, ἀ θ k hk bar η p ∂μ.prod μ
/-- Extended-real MSE of the actual floored and clipped ratio. All moments,
conditional means, denominator positivity, and covariance bounds are derived. -/
theorem common_pair_ratio_risk_le b a (ha : 𝙆)
    (hresidual : ∀ᵐ w ∂𝔔 regularPairDesignMeasure,
      |⟪bar w, 𝘙⟫| ≤ b)
    (hfloor : 2 * a ≤ 𝔒 pairPilotNoiseMean) :
     ∫⁻ z, ENNReal.ofReal
      ((stabilizedRatio C.varianceLower C.varianceUpper a
        𝔍
        𝔎 z -
          θ.variance) ^ 2) ∂𝔄 ≤
    ENNReal.ofReal (pairRiskBudget C m k Cp W lam
      (𝔔 pairPilotVarianceBase μ bar η) b a) := by
  let := 𝙱
  let S := 𝔅 (𝔔 pairPilotScoreKernel bar η) X
  let D := 𝔎
  let N := 𝔍
  have hmc := pairPilotCoefficient_measurable μ θ k hk bar η Cp W lam hp
  have hmS : Measurable S := PairUStatistic.fieldPairAverage_measurable _ _
    (𝔔 rawModelPairScore_measurable hmc) X 𝔈
  have hmD : Measurable D := PairUStatistic.fieldPairAverage_measurable _ _
    (rawModelPairNoise_measurable k hk hmc) X 𝔈
  have hS : MemLp S 2 𝔄 := PairUStatistic.fieldPairAverage_memLp _
    𝔏 pairPilotScoreKernel_memLp X hind hX
  have hD : MemLp D 2 𝔄 := PairUStatistic.fieldPairAverage_memLp _
    𝔏 pairPilotNoiseKernel_memLp X hind hX
  have he : N = fun z => S z + θ.variance * D z := by
    funext z
    dsimp [N]
    rw [pairPilotNumeratorKernel_eq_score_add_noise θ]
    exact PairUStatistic.fieldPairAverage_add_smul ..
  have hmN : Measurable N := by rw [he]; exact hmS.add $ hmD.const_mul _
  have hdif : (fun z => N z - θ.variance * D z) = S := by
    rw [he]
    funext z
    ring
  have hvlo := hθ.2.2.2.2.2.1
  have hr := stabilized_ratio_lintegral_mse_le 𝔄 hmN hmD (by rw [hdif]; exact hS) hD
    ha hvlo hθ.2.2.2.2.2.2.1 (C.varianceLower_pos.le.trans hvlo) hfloor
  simp_rw [ congrFun hdif ] at hr
  have hb2 := 𝗂 (pairPilotScoreMean_abs_bias_le C θ hθ k hk μ bar η Cp lam 𝔏 pairPilotAssumptions_meanConditions b hresidual) 2
  rw [sq_abs] at hb2
  have hSv := 𝔐 pairPilotScoreEstimate_centered_sq_le
  have hSb := integral_sq_le_twice_centered 𝔄 hS
    𝔒 pairPilotScoreMean
  apply hr.trans
  apply ENNReal.ofReal_mono
  apply mul_le_mul_of_nonneg_left _ 𝖠₃
  apply add_le_add
  · nlinarith
  · exact mul_le_mul_of_nonneg_left 𝔐 pairPilotNoiseEstimate_centered_sq_le $ sq_nonneg _
