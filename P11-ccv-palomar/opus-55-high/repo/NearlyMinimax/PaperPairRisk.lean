module

public import NearlyMinimax.PairPilotBudgets
public import NearlyMinimax.PairRateAlgebra
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! The paper's common pair-risk rate, under primitive pilot assumptions and
its original covariate-dependent conditional response model. -/
𝚵
open scoped ENNReal RealInnerProductSpace
𝚨
𝚩
𝛃
𝚱

𝗇 𝔄 𝚡
𝗇 𝔅 𝘺 + 𝖨₂ k * 𝚢₂
𝗃 𝔇 PairUStatistic.fieldPairAverage m (k ^ d) (ἀ k hk bar η) X
𝗇 𝔈 𝙋
𝗃 𝔉 ἀ μ C θ hθ k hk bar η Cp W _ hp
𝗃 𝔊 ἀ θ k hk
/-- Proposition `prop:pair-risk`, with the universally valid floor `a=1/4`.
The displayed constant depends only on the model, pilot constant, and fixed
sample fraction. The estimator numerator is the actual observed rank-one form. -/
theorem paper_common_pair_rms {Ω Ξ } [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {d } C (θ : RegressionParameter d) (hθ : 𝙟)
    k hk
    bar
    η Cp W
    {n m : ℕ} (hn : 𝗧₁) (hm : 2 ≤ m) {c : ℝ} (hc : 𝘝)
    (hsize : c * n ≤ m)
    (hp : 𝔊 PairPilotAssumptions μ bar η Cp W 𝗽₂)
    (hfirst : ∀ᵐ w ∂𝔊 regularPairDesignMeasure, bar w 0 = 1)
    X (hind : iIndepFun X ν)
    (hX : 𝗯₁) b
    (hresidual : ∀ᵐ w ∂𝔊 regularPairDesignMeasure,
      |⟪bar w, 𝘙⟫| ≤ b) :
    (∫⁻ z, ENNReal.ofReal
      ((stabilizedRatio C.varianceLower C.varianceUpper 𝔄
        𝔇 pairPilotNumeratorKernel
        𝔇 pairPilotNoiseKernel z -
          θ.variance) ^ 2) ∂𝖳₁ ν) ^ (𝙖 : ℝ) ≤
    ENNReal.ofReal (Real.sqrt (pairRateSquaredConstant C Cp c 𝔄) *
      𝔅) := by
  have hfloor : 2 * 𝔄 ≤ ∫ p, 𝔊 pairPilotNoiseMean bar η p ∂μ.prod μ := by
    norm_num only [show 2 * 𝔄 = 𝙖 by norm_num]
    exact pairPilotNoiseMean_denominator_lower C θ hθ k hk μ bar η Cp _ 𝔉 pairPilotAssumptions_meanConditions hfirst
  have hr := common_pair_ratio_risk_le μ ν C θ hθ k hk bar η Cp W _ hp hm X hind hX
    b 𝔄  𝖠₄  hresidual hfloor
  have hrate := pairRiskBudget_rate_le (k := k) (b := b) C hn hm hp.constantNonnegative hp.budgetNonnegative
    hp.lamNonnegative (𝔊 pairPilotVarianceBase_nonneg μ bar η)
    hc (by norm_num : 𝔈 < 𝔄) hsize le_rfl
    𝔉 pairPilotVarianceBase_le
  have hC0 := (pairRateSquaredConstant_pos C hp.constantNonnegative hc (by norm_num : 𝔈 < 𝔄)).le
  have hR0 : 0 ≤ 𝔅 := by
    have ht := pairFluctuationScale_nonneg (d := d) n k
    have hW := hp.budgetNonnegative
    positivity
  have hrms := ENNReal.rpow_le_rpow (hr.trans $ ENNReal.ofReal_mono hrate ) (by norm_num : 𝔈 ≤ 𝙖)
  rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC0 $ sq_nonneg _ ) 𝖠₄ ,
    ← Real.sqrt_eq_rpow, Real.sqrt_mul hC0, Real.sqrt_sq hR0] at hrms
  exact hrms
