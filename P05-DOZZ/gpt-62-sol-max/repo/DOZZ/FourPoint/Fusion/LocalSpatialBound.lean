/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.ScaledSpatialBound
public import DOZZ.FourPoint.Fusion.ScaledLocalRooting
public import DOZZ.FourPoint.Fusion.Parameters
/-! # Uniform local power bounds for the second variation -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs

theorem fusion_local_second_expectation_bound {Ω : Type*} [MeasurableSpace Ω] (mixed : Bool)
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 →
      ‖fusionSecondSpatial mixed P M γ α₁ α₂ α₃ p (Metric.ball 0 (1 / 2)) z‖ ≤
        C * ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) := by
  have hβ : γ ^ 2 / 2 < γ * α₁ := by nlinarith [mul_lt_mul_of_pos_left hlo hγ]
  have hβ2 : γ * α₁ < 2 := by nlinarith [(lt_div_iff₀ hγ).mp hα₁]
  obtain ⟨C, hC, hb⟩ := fusionScaledIntegral_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃
    (-p - 1) (by linarith) _ (fusionPlanarSecond_integrable mixed (by positivity) hβ hβ2)
  refine ⟨C, hC, fun z hz hz4 => ?_⟩
  rw [fusion_local_second_spatial_scaled mixed P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃ p hp z hz hz4,
    norm_mul, norm_div, norm_fusionSecondDenom, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  have hκ : γ * (Q γ - α₁) = (γ ^ 2 / 2 - γ * α₁) + 2 := by
    rw [fusion_exponent_eq γ α₁ hγ.ne']; ring
  rw [hκ, Real.rpow_add (norm_pos_iff.mpr hz), Real.rpow_two,
    mul_div_cancel_right₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hz)), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hb z (by linarith)) (Real.rpow_nonneg (norm_nonneg _) _)

end DOZZ.Proofs
