/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedCenterTransfer
public import DOZZ.GMC.SharpMoments.WeightedScale
import DOZZ.GMC.SharpMoments.WeightedLocalSufficiency

/-! # Local moments uniform in the moving root -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The weighted moment comparison holds between any two centers in a bounded chart. -/
theorem fusion_weightedMoment_location_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    α z z₀ ρ R (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hR : 0 ≤ R) (hzR : ‖z‖ + ρ ≤ R) (hz₀R : ‖z₀‖ + ρ ≤ R)
    p (hp : 0 < p) (hp4 : p < 4 / γ ^ 2) :
    weightedGmcBallMoment P M γ α z ρ p ≤
      (ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 *
          |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p|) *
        weightedGmcBallMoment P M γ α z₀ ρ p := by
  have hN : ∀ N : ℕ, ∫⁻ ω, (∫⁻ x in Metric.ball z ρ,
      (insertionTruncWeight γ α N (x - z) : ℝ≥0∞) ∂M ω) ^ p ∂P ≤
        (ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 * |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p|) * weightedGmcBallMoment P M γ α z₀ ρ p := by
    intro N
    refine (gmc_weighted_ball_moment_transfer P X hX γ hγ hγ2 M hM z z₀ ρ R hρ hρ8
      hR hzR hz₀R (insertionTruncWeight γ α N)
      (measurable_insertionTruncWeight γ α N) (N : ℝ≥0) (insertionTruncWeight_le γ α N) p hp
      hp4).trans (mul_le_mul' le_rfl ?_)
    apply lintegral_mono
    intro ω
    refine ENNReal.rpow_le_rpow ?_ hp.le
    apply lintegral_mono
    intro x
    dsimp only
    rw [coe_insertionTruncWeight]
    exact insertionTruncWeightE_le_weight γ α N (x - z₀)
  -- monotone convergence in the truncation height
  have hmono : ∀ᵐ ω ∂P, Monotone fun N => (∫⁻ x in Metric.ball z ρ,
      (insertionTruncWeight γ α N (x - z) : ℝ≥0∞) ∂M ω) ^ p := by
    refine Eventually.of_forall fun ω m n hmn => ENNReal.rpow_le_rpow ?_ hp.le
    apply lintegral_mono
    intro x
    simp only [coe_insertionTruncWeight]
    exact insertionTruncWeightE_mono γ α (x - z) hmn
  exact le_of_tendsto' (lintegral_tendsto_of_tendsto_of_monotone (fun N => (gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _ (measurable_coe_nnreal_ennreal.comp ((measurable_insertionTruncWeight γ α N).comp (measurable_id.sub_const z))) _ Metric.isOpen_ball.measurableSet).pow_const p) hmono (Eventually.of_forall fun ω => ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp (insertionTrunc_mass_tendsto γ α (M ω) z ρ))) hN

/-- Subcritical weighted moments vanish with a positive power, uniformly in the unit chart. -/
theorem fusion_weightedMoment_small_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    α p (hp : 0 < p)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α))) :
    let ξ := γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2
    0 < ξ ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → ∀ r : ℝ,
      0 < r → r ≤ 1 / 8 →
      weightedGmcBallMoment P M γ α z r p ≤ C * ENNReal.ofReal (r ^ ξ) := by
  let ξ := γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2
  change 0 < ξ ∧ _
  have hpin := (lt_min_iff.mp hpRange).2
  let D := ENNReal.ofReal (Real.exp
      (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + 2))) / 2 * |p ^ 2 - p|)) *
    ENNReal.ofReal (((1 : ℝ) + 2) ^ 4) ^ |p|
  let B := weightedGmcBallMoment P M γ α 0 (1 / 8) p
  refine ⟨(by rw [div_mul_eq_mul_div] at hpin; dsimp [ξ]; nlinarith only [(mul_lt_mul_of_pos_left (show γ ^ 2 * p < 2 * γ * (Q γ - α) by nlinarith only [(mul_lt_mul_of_pos_left ((lt_div_iff₀ hγ).mp hpin) hγ)]) hp)]), D * ENNReal.ofReal ((8 : ℝ) ^ ξ) * B,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.rpow_ne_top_of_nonneg (abs_nonneg p) ENNReal.ofReal_ne_top).lt_top) ENNReal.ofReal_lt_top) (weightedGmcBallMoment_lt_top_of_sharp_range P X hX γ hγ hγ2 M hM α 0 (1 / 8) (by norm_num) p hp hpRange), ?_⟩
  intro z hz r hr hr8
  have hscale := gmc_weighted_ball_moment_scale P X hX γ M hM α
    (c := 8 * r) (R := 1 / 8) (by positivity) (by linarith) (by norm_num) (by norm_num) p
  have he : (2 - γ * α) * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 = ξ := by
    dsimp [ξ]
    unfold Q
    field_simp
    ring
  rw [(show 8 * r * (1 / 8) = r by ring), he, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hr.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)] at hscale
  calc
    _ ≤ D * weightedGmcBallMoment P M γ α 0 r p := (fusion_weightedMoment_location_transfer P X hX γ hγ hγ2 M hM α z 0 r 2 hr hr8 (by norm_num) (by linarith) (by simp; linarith) p hp ((lt_min_iff.mp hpRange).1))
    _ = _ := by rw [hscale]; dsimp [B]; ring

end DOZZ.Proofs
