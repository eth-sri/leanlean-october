/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.InterpolatedSpatialConvergence
/-! # Signed spatial and time dominated convergence for KRV -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs
/-- A single uniform majorant gives spatial and time dominated convergence over the mass
segment. -/
theorem fusionInterpolatedTimeIntegral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    α₁ α₂ α₃ (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) s (hs : s < 0)
    K (hKm : Measurable K) (hK : Integrable K volume) :
    Tendsto (fun z : ℂ => ∫ t in Icc (0 : ℝ) 1,
      (∫ y : ℂ, K y * (fusionInterpolatedFactor P M γ α₁ α₂ α₃ s t y z : ℂ)))
      (nhds 0) (nhds ((∫ y : ℂ, K y) *
        ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P).toReal : ℂ))) := by
  obtain ⟨B, hB, hb⟩ := fusionInterpolatedFactor_uniform_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s hs.le
  let D := (∫ y : ℂ, ‖K y‖) * B
  have hdom : ∀ᶠ z : ℂ in nhds 0, ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 1),
      ‖∫ y : ℂ, K y * (fusionInterpolatedFactor P M γ α₁ α₂ α₃ s t y z : ℂ)‖ ≤ D := by
    have hz : ∀ᶠ z : ℂ in nhds 0, ‖z‖ ≤ 1 :=
      ((continuous_norm.tendsto (0 : ℂ)).eventually_lt_const (by simp)).mono fun _ h => h.le
    filter_upwards [hz] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    calc
      _ ≤ ∫ y : ℂ, ‖K y‖ * B := norm_integral_le_of_norm_le (hK.norm.mul_const B)
        (ae_of_all _ fun y => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hb t ht y z hz) (norm_nonneg _))
      _ = D := integral_mul_const _ _
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => D)
    (by apply Eventually.of_forall; intro z; exact ((hKm.comp measurable_snd).mul (show Measurable (fun q : ℝ × ℂ => (fusionInterpolatedFactor P M γ α₁ α₂ α₃ s q.1 q.2 z : ℂ)) by simpa only [Function.comp_def] using Complex.measurable_ofReal.comp ((fusionInterpolatedFactor_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s).comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))))).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) hdom (integrable_const D) (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact fusionInterpolatedIntegral_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα hα₁ hα₂ hα₃ s hs t ht K hK)
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
    ENNReal.toReal_one, one_smul] using h
end DOZZ.Proofs
