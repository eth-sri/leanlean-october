/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.LocalSecondScaling
public import DOZZ.Statements.FourPoint.GammaHalfRootedCoefficient

/-! # The normalized local second variation limit -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The planar constant is real in the Taylor-integrability window. -/
theorem fusion_planarGauss_real (k β : ℝ) (hk : 0 < k) (hβ : k < β)
    (hβ2 : β < 2) (hβlin : β < k + 1) :
    planarGaussConstant k β = ((planarGaussConstant k β).re : ℂ) := by
  have h := planarTaylor_constant_from_discrete_laplacian k β hk hβ hβ2 hβlin
  rw [← h]
  rfl

/-- Shared normalized limit for the pure and mixed terms. -/
theorem fusionLocalSecond_normalized_tendsto {Ω : Type*} [MeasurableSpace Ω] (mixed : Bool)
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun z : ℂ => fusionLocalSecond mixed P M γ α₁ α₂ α₃ p z /
      (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ)) (nhdsWithin 0 {0}ᶜ)
      (nhds ((fusionSecondCoeff mixed γ p : ℂ) *
        ((1 / ((γ ^ 2 / 2 - γ * α₁ + 1) * (γ ^ 2 / 2 - γ * α₁ + 2)) : ℝ) *
          ((∫ y : ℂ, fusionPlanarSecond mixed (γ ^ 2 / 2) (γ * α₁) 1 y) *
            ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ (-p - 1) ∂P).toReal : ℂ))))) := by
  obtain ⟨hk, hβ, hβ2, hβlin, _, _⟩ := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
  have h := fusionScaledTimeIntegral_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo.le hα₁ hα₂ hα₃
    (-p - 1) (by linarith) _ (fusionPlanarSecond_measurable mixed _ _)
    (fusionPlanarSecond_integrable mixed hk hβ hβ2) (γ ^ 2 / 2 - γ * α₁) (by linarith)
  have hc := (tendsto_const_nhds (x := (fusionSecondCoeff mixed γ p : ℂ))).mul h
  apply (hc.mono_left (show nhdsWithin (0 : ℂ) {0}ᶜ ≤ nhds 0 from nhdsWithin_le_nhds)).congr'
  have hz4 : ∀ᶠ z : ℂ in nhds 0, ‖z‖ < 1 / 4 :=
    (continuous_norm.tendsto (0 : ℂ)).eventually_lt_const (by simp)
  filter_upwards [hz4.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz4 hz
  have hz₀ : z ≠ 0 := hz
  rw [fusionLocalSecond_scaled mixed P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃ p hp z hz₀ hz4.le]
  have hr := Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz₀)
    (γ * (Q γ - α₁))).ne'
  have cancel (a b c : ℂ) (hb : b ≠ 0) : a * b * c / b = a * c := by
    rw [mul_assoc, mul_comm b c, ← mul_assoc, mul_div_cancel_right₀ _ hb]
  exact (cancel _ _ _ hr).symm

end DOZZ.Proofs
