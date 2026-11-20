/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.MassSegment
public import DOZZ.FourPoint.Fusion.MeasurableIntegralFamily
public import DOZZ.GMC.MeasurableIntegrals
/-! # Measurability of signed spatial segment integrands -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include Ω X hX hγ hγ2 hM

/-- Signed spatial integrals times segment inverse powers are measurable almost surely. -/
theorem fusion_segment_spatial_aestronglyMeasurable
    (α₁ α₂ α₃ t s : ℝ) (z : ℂ) (f : ℂ → ℝ) (hf : Measurable f) :
    AEStronglyMeasurable (fun ω => (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ s).toReal *
      ∫ x, f x ∂M ω) P := by
  have hm := (fusionUnrootedSegment_joint_measurable γ α₁ α₂ α₃ z).pow_const s
  have hF := hm.ennreal_toReal.mul
    (measurable_integral_finiteMeasure_parameter (hf.comp (measurable_snd : Measurable (Prod.snd : ℝ × ℂ → ℂ))))
  exact (hF.comp_aemeasurable (aemeasurable_const.prodMk
    (equatorGFF_finiteGMC_aemeasurable P X hX γ hγ hγ2 M hM))).aestronglyMeasurable
/-- Spatial segment expectations are measurable in interpolation time. -/
theorem fusion_segment_time_expectation_measurable
    (α₁ α₂ α₃ s : ℝ) (z : ℂ) (f : ℂ → ℝ) (hf : Measurable f) :
    Measurable (fun t : ℝ => ∫ ω, (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ s).toReal *
      (∫ x, f x ∂M ω) ∂P) := by
  letI := hX.1
  have hm := (fusionUnrootedSegment_joint_measurable γ α₁ α₂ α₃ z).pow_const s
  exact measurable_integral_ae_parameter (equatorGFF_finiteGMC_aemeasurable P X hX γ hγ hγ2 M hM)
    (hm.ennreal_toReal.mul (measurable_integral_finiteMeasure_parameter
      (hf.comp (measurable_snd : Measurable (Prod.snd : ℝ × ℂ → ℂ)))))

end
end DOZZ.Proofs
