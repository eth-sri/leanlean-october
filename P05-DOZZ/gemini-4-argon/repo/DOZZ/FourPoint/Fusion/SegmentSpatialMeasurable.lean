/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.MassSegment
public import DOZZ.FourPoint.Fusion.MeasurableIntegralFamily
/-! # Measurability of signed spatial segment integrands -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- Signed spatial integrals times segment inverse powers are measurable almost surely. -/
theorem fusion_segment_spatial_aestronglyMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ t s : ℝ) z f (hf : Measurable f) :
    AEStronglyMeasurable (fun ω => (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ s).toReal *
      ∫ x, f x ∂M ω) P := by
  obtain ⟨N, hN, hfN, he⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  exact (((fusionUnrootedSegment_measurable γ α₁ α₂ α₃ t s z).comp hN).ennreal_toReal.mul (fusion_measurable_real_integral_finite_family N hN hfN _ (hf.comp measurable_snd))).aestronglyMeasurable.congr (he.mono fun ω h => by
    change (fusionUnrootedSegment γ α₁ α₂ α₃ t z (N ω) ^ s).toReal * (∫ x, f x ∂N ω) = _
    simp only [h])
/-- Spatial segment expectations are measurable in interpolation time. -/
theorem fusion_segment_time_expectation_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) z f (hf : Measurable f) :
    Measurable (fun t : ℝ => ∫ ω, (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ s).toReal *
      (∫ x, f x ∂M ω) ∂P) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hN, hfN, he⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have heq : (fun t => ∫ ω, (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ s).toReal *
      (∫ x, f x ∂M ω) ∂P) =
      fun t => ∫ ω, (fusionUnrootedSegment γ α₁ α₂ α₃ t z (N ω) ^ s).toReal * (∫ x, f x ∂N ω) ∂P := by
    funext t
    apply integral_congr_ae
    filter_upwards [he] with ω h
    rw [h]
  rw [heq]
  exact ((((((ENNReal.measurable_ofReal.comp measurable_fst).mul (((fusion_measurable_coulombMass γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).comp hN).comp measurable_snd)).add ((ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_fst)).mul (((fusion_measurable_coulombMass γ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃).comp hN).comp measurable_snd))).pow_const s).ennreal_toReal).mul ((fusion_measurable_real_integral_finite_family N hN hfN _ (hf.comp measurable_snd)).comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
end DOZZ.Proofs
