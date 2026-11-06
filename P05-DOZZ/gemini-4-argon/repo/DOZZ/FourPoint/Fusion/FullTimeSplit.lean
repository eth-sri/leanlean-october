/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.SpatialFunctions
public import DOZZ.FourPoint.Fusion.SpatialSplit
public import DOZZ.FourPoint.Fusion.MixedSpatialSplit
public import DOZZ.FourPoint.Fusion.LocalSpatialBound
public import DOZZ.FourPoint.Fusion.TimeIntegrability
public import DOZZ.FourPoint.Fusion.LocalR1Scaling
public import DOZZ.FourPoint.Fusion.LocalR2Scaling
public import DOZZ.Statements.FourPoint.GammaHalfRootedR2
/-! # Splitting the literal full Taylor contributions -/
@[expose] public section
open MeasureTheory Set Filter
namespace DOZZ.Proofs
/-- The full `r₁` term splits into the local term `fusionLocalR1` and a bounded exterior time
integral. -/
theorem fusionRootedR1_split {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    α₁ α₂ α₃ (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) p (hp : 0 ≤ p)
    z (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    gammaHalfRootedR1 P M γ α₁ α₂ α₃ p z = fusionLocalR1 P M γ α₁ α₂ α₃ p z +
      ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) * z ^ 2 *
        (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) *
          fusionPureSpatial P M γ α₁ α₂ α₃ p (Metric.ball (0 : ℂ) (1 / 2))ᶜ ((t : ℂ) * z)) := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  let F := fusionPureSpatial P M γ α₁ α₂ α₃ p univ
  let L := fusionPureSpatial P M γ α₁ α₂ α₃ p B
  let E := fusionPureSpatial P M γ α₁ α₂ α₃ p Bᶜ
  obtain ⟨CL, _, hbL⟩ := fusion_localR1_expectation_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp
  obtain ⟨CE, _, hbE⟩ := fusion_exteriorR1_expectation_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  have hc := congrArg (fun q : ℂ => (((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) * z ^ 2) * q) (fusion_time_split F L E z (fusion_time_integrable_of_power_bound L (fusionPureSpatial_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p B Metric.isOpen_ball.measurableSet) CL (γ ^ 2 / 2 - γ * α₁) (1 / 4) (by linarith only [(fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁).2.2.2.1]) hbL z hz hz4) (fusion_time_integrable_of_power_bound E (fusionPureSpatial_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p Bᶜ Metric.isOpen_ball.measurableSet.compl) CE 0 (1 / 4) (by norm_num) (fun w hw hw4 => by simpa only [E, B, fusionPureSpatial, Real.rpow_zero, mul_one] using (hbE w hw hw4).2) z hz hz4) (by filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0; simpa only [F, L, E, fusionPureSpatial, Measure.restrict_univ] using fusion_pureSpatial_expectation_split P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (by nlinarith [mul_lt_mul_of_pos_left hlo hγ]) hα₁ hα₂ hα₃ p hp ((t : ℂ) * z) (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht0) hz) (by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]; exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hz4)))
  simpa only [gammaHalfRootedR1, fusionLocalR1, F, L, E, B, fusionPureSpatial,
    Measure.restrict_univ, ENNReal.rpow_eq_pow, Complex.ofReal_pow, mul_add] using hc

/-- The full `r₂` term splits into the local term `fusionLocalR2` and a bounded exterior time
integral. -/
theorem fusionRootedR2_split {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    α₁ α₂ α₃ (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) p (hp : 0 ≤ p)
    z (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    gammaHalfRootedR2 P M γ α₁ α₂ α₃ p z = fusionLocalR2 P M γ α₁ α₂ α₃ p z +
      ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z * star z *
        (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) *
          fusionMixedSpatial P M γ α₁ α₂ α₃ p (Metric.ball (0 : ℂ) (1 / 2))ᶜ ((t : ℂ) * z)) := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  let F := fusionMixedSpatial P M γ α₁ α₂ α₃ p univ
  let L := fusionMixedSpatial P M γ α₁ α₂ α₃ p B
  let E := fusionMixedSpatial P M γ α₁ α₂ α₃ p Bᶜ
  obtain ⟨CL, _, hbL⟩ := fusion_localR2_expectation_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp
  obtain ⟨CE, _, hbE⟩ := fusion_exteriorR2_expectation_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  simpa only [gammaHalfRootedR2, fusionLocalR2, F, L, E, B, fusionMixedSpatial,
    Measure.restrict_univ, ENNReal.rpow_eq_pow, Complex.ofReal_pow, mul_add] using (congrArg (fun q : ℂ => (((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z * star z) * q) (fusion_time_split F L E z (fusion_time_integrable_of_power_bound L (fusionMixedSpatial_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p B Metric.isOpen_ball.measurableSet) CL (γ ^ 2 / 2 - γ * α₁) (1 / 4) (by linarith only [(fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁).2.2.2.1]) hbL z hz hz4) (fusion_time_integrable_of_power_bound E (fusionMixedSpatial_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p Bᶜ Metric.isOpen_ball.measurableSet.compl) CE 0 (1 / 4) (by norm_num) (fun w hw hw4 => by simpa only [E, B, fusionMixedSpatial, Real.rpow_zero, mul_one] using (hbE w hw hw4).2) z hz hz4) (by filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0; simpa only [F, L, E, fusionMixedSpatial, Measure.restrict_univ] using fusion_mixedSpatial_expectation_split P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (by nlinarith [mul_lt_mul_of_pos_left hlo hγ]) hα₁ hα₂ hα₃ p hp ((t : ℂ) * z) (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht0) hz) (by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]; exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hz4))))

end DOZZ.Proofs
