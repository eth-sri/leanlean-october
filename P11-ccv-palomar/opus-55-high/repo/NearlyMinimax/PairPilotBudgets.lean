module

public import NearlyMinimax.CommonPairRisk
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The paper's pointwise pilot budget supplies the actual spatial energy. -/
𝚫
𝚮
𝚨
𝚩
𝛃

𝛥
𝛗
𝛘
𝗇 𝔅 𝙩 → PairVector
variable (bar : 𝔅)
variable (η : Ω → 𝔅) (Cp W lam : ℝ)
variable (hp : PairPilotAssumptions θ k hk μ bar η Cp W lam)
include hθ hp

𝗇 𝔄 𝗪₁
𝗇 𝔇 Cp ^ 2
𝗇 𝔈 mul_nonneg hp.constantNonnegative hp.budgetNonnegative
𝗇 𝔉 regularPairDesignMeasure_ae_of_supported θ k hk
theorem pairPilotVarianceBase_le :
    pairPilotVarianceBase θ k hk μ bar η ≤ C.densityUpper * (2 * 𝔇 + Cp * W) := by
  let := regularPairDesignMeasure_isFinite C θ hθ k hk
  have hb := 𝔉 hp.barBound
  have hbar : MemLp bar 2 𝔄 :=
    MemLp.of_bound hp.barMeasurable.aestronglyMeasurable Cp hb
  have hbarE : ∫ w, ‖bar w‖ ^ 2 ∂𝔄 ≤
      𝔇 * (𝔄).real univ := by
    have h := integral_mono_ae hbar.norm.integrable_sq (integrable_const 𝔇)
      $ hb.mono fun w hw => 𝗩₁ hw 2
    simpa only [integral_const, smul_eq_mul, mul_comm] using h
  have hnoiseE := PilotFields.joint_energy_le_of_uniform_sections hp.noiseMeasurable (𝔉 hp.noiseSection)
    𝔈 $ 𝔉 hp.noiseEnergy
  have hmass := (regularPairDesignMeasure_mass_bounds C θ hθ k hk).2
  have hnoiseU := mul_le_mul_of_nonneg_left hmass
    𝔈
  unfold pairPilotVarianceBase
  nlinarith
