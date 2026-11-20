/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ScaledLocalKernel
public import DOZZ.FourPoint.Fusion.ScaledFactor
public import DOZZ.FourPoint.Fusion.LocalRooting
public import DOZZ.FourPoint.Fusion.SpatialFunctions
public import DOZZ.FourPoint.Fusion.Parameters

/-! # Rescaling the rooted local second variation -/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

section
variable {Ω : Type*} [MeasurableSpace Ω] (mixed : Bool) (P : Measure Ω) (X : Ω → Distr)
  (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω X hX hγ hγ2 hM

private theorem fusion_local_second_reference_scaled
    (α₁ α₂ α₃ s : ℝ) (z : ℂ) (hz : z ≠ 0) :
    (∫ x in Metric.ball (0 : ℂ) (1 / 2), fusionSecondKernel mixed γ α₁ α₂ α₃ z x *
      ((∫⁻ ω, coulombMass γ (gmcRootedMeasure γ x (M ω))
        ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s ∂P).toReal : ℂ)) =
      (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ) / fusionSecondDenom mixed z *
        (∫ y : ℂ, fusionPlanarSecond mixed (γ ^ 2 / 2) (γ * α₁) 1 y *
          (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)) := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  let K := fusionPlanarSecond mixed (γ ^ 2 / 2) (γ * α₁) 1
  let F := B.indicator (fun x => fusionSecondKernel mixed γ α₁ α₂ α₃ z x *
    ((∫⁻ ω, coulombMass γ (gmcRootedMeasure γ x (M ω))
      ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s ∂P).toReal : ℂ))
  have hpoint : ∀ᵐ y : ℂ ∂volume, F (y * z) =
      (‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) : ℝ) / fusionSecondDenom mixed z *
        (K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with y hy₀ hy₁
    by_cases hy : ‖y * z‖ < 1 / 2
    · have hyB : y * z ∈ B := by simpa only [B, Metric.mem_ball, dist_zero_right] using hy
      have he : (∫⁻ ω, coulombMass γ (gmcRootedMeasure γ (y * z) (M ω))
          ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s ∂P) =
          ∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y z (M ω) ^ s ∂P := by
        apply lintegral_congr_ae
        filter_upwards [fusionMovingMass_eq_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y z] with ω hω
        rw [hω]
      dsimp only [F]
      rw [Set.indicator_of_mem hyB, fusion_localSecond_kernel_scaled mixed γ α₁ α₂ α₃ y z hz hy₀ hy₁ hy, he]
      simp only [K, fusionScaledFactor, ite_eq_left hy, Complex.ofReal_mul, mul_assoc]
    · have hyB : y * z ∉ B := by simpa only [B, Metric.mem_ball, dist_zero_right] using hy
      simp only [F, Set.indicator_of_notMem hyB, fusionScaledFactor, ite_eq_right hy, Complex.ofReal_zero, mul_zero]
  have hp : ‖z‖ ^ (2 : ℕ) * ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) = ‖z‖ ^ (γ * (Q γ - α₁)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.mpr hz), fusion_exponent_eq γ α₁ hγ.ne']
    norm_num
    congr 1
    ring
  calc
    _ = ∫ x : ℂ, F x := (integral_indicator Metric.isOpen_ball.measurableSet).symm
    _ = _ := by
      rw [fusion_integral_mul_complex F z hz, integral_congr_ae hpoint, integral_const_mul,
        ← mul_assoc, ← mul_div_assoc, ← Complex.ofReal_mul, hp]

theorem fusion_local_second_spatial_scaled
    (α₁ α₂ α₃ : ℝ) (hβ : γ ^ 2 / 2 < γ * α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    fusionSecondSpatial mixed P M γ α₁ α₂ α₃ p (Metric.ball 0 (1 / 2)) z =
      (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ) / fusionSecondDenom mixed z *
        (∫ y : ℂ, fusionPlanarSecond mixed (γ ^ 2 / 2) (γ * α₁) 1 y *
          (fusionScaledFactor P M γ α₁ α₂ α₃ (-p - 1) y z : ℂ)) := by
  unfold fusionSecondSpatial
  rw [fusion_local_second_rooting mixed P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃ _ (by linarith) z hz hz4,
    fusion_local_second_reference_scaled mixed P X hX γ hγ hγ2 M hM α₁ α₂ α₃ _ z hz]

end

end DOZZ.Proofs
