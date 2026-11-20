/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.InterpolatedSpatialConvergence
/-! # Signed spatial and time dominated convergence for KRV -/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs
/-- A uniformly bounded factor controls integration of an arbitrary integrable kernel. -/
theorem fusionIntegral_norm_le {K : ℂ → ℂ} (hK : Integrable K volume)
    {F : ℂ → ℝ} {B : ℝ} (hF : ∀ y, |F y| ≤ B) :
    ‖∫ y : ℂ, K y * (F y : ℂ)‖ ≤ (∫ y : ℂ, ‖K y‖) * B := by
  rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le (hK.norm.mul_const B) (ae_of_all _ fun y => ?_)
  simpa [norm_mul, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left (hF y) (norm_nonneg (K y))

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ)
  (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (s : ℝ) (hs : s < 0)
  (K : ℂ → ℂ) (hKm : Measurable K) (hK : Integrable K volume)
include Ω X hX hγ hγ2 hM hα hα₁ hα₂ hα₃ hs hKm hK

/-- A common spatial majorant works under time-dependent interpolation and rescaling. -/
theorem fusionSpaceTimeIntegral_tendsto
    (u : ℝ → ℝ) (hu : Measurable u) (huI : MapsTo u (Icc 0 1) (Icc 0 1))
    (v : ℝ → ℂ → ℂ) (hv : ∀ z, Measurable (fun t => v t z))
    (hvB : ∀ t ∈ Icc 0 1, ∀ z, ‖z‖ ≤ 1 → ‖v t z‖ ≤ 1)
    (hvL : ∀ t ∈ Icc 0 1, Tendsto (v t) (nhds 0) (nhds 0))
    (w : ℝ → ℝ) (hw : IntegrableOn w (Icc 0 1) volume) :
    Tendsto (fun z : ℂ => ∫ t in Icc (0 : ℝ) 1, (w t : ℂ) *
        ∫ y : ℂ, K y * (fusionInterpolatedFactor P M γ α₁ α₂ α₃ s (u t) y (v t z) : ℂ))
      (nhds 0) (nhds (((∫ t in Icc (0 : ℝ) 1, w t : ℝ) : ℂ) * ((∫ y : ℂ, K y) *
        ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P).toReal : ℂ)))) := by
  obtain ⟨B, _, hb⟩ := fusionInterpolatedFactor_uniform_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s hs.le
  let D := (∫ y : ℂ, ‖K y‖) * B
  let F (t : ℝ) (z : ℂ) : ℂ := (w t : ℂ) *
    ∫ y : ℂ, K y * (fusionInterpolatedFactor P M γ α₁ α₂ α₃ s (u t) y (v t z) : ℂ)
  let L : ℂ := (∫ y : ℂ, K y) * ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P).toReal : ℂ)
  have hm := fusionInterpolatedFactor_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s
  have hmeas (z : ℂ) : AEStronglyMeasurable (F · z) (volume.restrict (Icc 0 1)) := by
    have hp : Measurable (fun q : ℝ × ℂ => (u q.1, (q.2, v q.1 z))) := by fun_prop
    have h := (hKm.comp measurable_snd).mul (Complex.measurable_ofReal.comp (hm.comp hp))
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul
      h.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hdom : ∀ᶠ z : ℂ in nhds 0, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), ‖F t z‖ ≤ ‖w t‖ * D := by
    have hz : ∀ᶠ z : ℂ in nhds 0, ‖z‖ < 1 :=
      (continuous_norm.tendsto (0 : ℂ)).eventually_lt_const (by simp)
    filter_upwards [hz] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp [F]
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (fusionIntegral_norm_le hK
      (fun y => hb (u t) (huI ht) y _ (hvB t ht z hz.le))) (norm_nonneg _)
  have hlim : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), Tendsto (F t) (nhds 0) (nhds ((w t : ℂ) * L)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact tendsto_const_nhds.mul ((fusionInterpolatedIntegral_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃
      hα hα₁ hα₂ hα₃ s hs (u t) (huI ht) K hK).comp (hvL t ht))
  have h := tendsto_integral_filter_of_dominated_convergence (fun t => ‖w t‖ * D)
    (Eventually.of_forall hmeas) hdom (hw.norm.mul_const D) hlim
  simpa [F, L, integral_mul_const, integral_complex_ofReal] using h

/-- A single uniform majorant gives spatial and time dominated convergence over the mass
segment. -/
theorem fusionInterpolatedTimeIntegral_tendsto :
    Tendsto (fun z : ℂ => ∫ t in Icc (0 : ℝ) 1,
      (∫ y : ℂ, K y * (fusionInterpolatedFactor P M γ α₁ α₂ α₃ s t y z : ℂ)))
      (nhds 0) (nhds ((∫ y : ℂ, K y) *
        ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P).toReal : ℂ))) := by
  have h := fusionSpaceTimeIntegral_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα hα₁ hα₂ hα₃ s hs K hKm hK
    id measurable_id (fun _ h => h) (fun _ z => z) (fun _ => measurable_const)
    (fun _ _ _ h => h) (fun _ _ => tendsto_id) (fun _ => 1) (integrable_const _)
  simpa [integral_const, Measure.real, Real.volume_Icc] using h

end

end DOZZ.Proofs
