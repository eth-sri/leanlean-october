/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.InterpolatedInverseMoments
public import DOZZ.FourPoint.Fusion.MovingExpectationMeasurable
public import DOZZ.FourPoint.Fusion.RootOnlyKernelMeasurable
/-! # Joint measurability of the interpolated inverse expectation -/
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs
/-- Measurability of a rooted mass in an arbitrary finite measurable family. -/
theorem fusionMovingMass_family_measurable {U : Type*} [MeasurableSpace U]
    γ α₁ α₂ α₃ (μ : U → Measure ℂ) (hμ : Measurable μ) (hfin : ∀ u, IsFiniteMeasure (μ u))
    y z (hy : Measurable y) (hz : Measurable z) :
    Measurable (fun u => fusionMovingMass γ α₁ α₂ α₃ (y u) (z u) (μ u)) := by
  apply measurable_lintegral_finite_family μ hμ hfin
    (fun q : U × ℂ => fusionMovingKernel γ α₁ α₂ α₃ (y q.1) (z q.1) q.2)
  simpa only [Function.comp_def] using (fusionMovingKernel_joint_measurable γ α₁ α₂ α₃).comp (((hy.comp measurable_fst).prodMk (hz.comp measurable_fst)).prodMk measurable_snd)
/-- Measurability of a rooted mass in an arbitrary finite measurable family. -/
theorem fusionRootOnlyMass_family_measurable {U : Type*} [MeasurableSpace U]
    γ α₁ α₂ α₃ (μ : U → Measure ℂ) (hμ : Measurable μ) (hfin : ∀ u, IsFiniteMeasure (μ u))
    y z (hy : Measurable y) (hz : Measurable z) :
    Measurable (fun u => fusionRootOnlyMass γ α₁ α₂ α₃ (y u) (z u) (μ u)) := by
  apply measurable_lintegral_finite_family μ hμ hfin
    (fun q : U × ℂ => fusionRootOnlyKernel γ α₁ α₂ α₃ (y q.1) (z q.1) q.2)
  simpa only [Function.comp_def] using (fusionRootOnlyKernel_joint_measurable γ α₁ α₂ α₃).comp (((hy.comp measurable_fst).prodMk (hz.comp measurable_fst)).prodMk measurable_snd)
/-- The inverse expectation is jointly measurable in time, rescaled root, and insertion. -/
theorem fusionInterpolatedMass_expectation_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) :
    Measurable (fun q : ℝ × (ℂ × ℂ) => ∫⁻ ω,
      fusionInterpolatedMass γ α₁ α₂ α₃ q.1 q.2.1 q.2.2 (M ω) ^ s ∂P) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hN, hf, he⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hy : Measurable (fun q : (ℝ × (ℂ × ℂ)) × Ω => q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hz : Measurable (fun q : (ℝ × (ℂ × ℂ)) × Ω => q.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have ht : Measurable (fun q : (ℝ × (ℂ × ℂ)) × Ω => q.1.1) := measurable_fst.comp measurable_fst
  rw [(show (fun q : ℝ × (ℂ × ℂ) => ∫⁻ ω, fusionInterpolatedMass γ α₁ α₂ α₃ q.1 q.2.1 q.2.2 (M ω) ^ s ∂P) = (fun q : ℝ × (ℂ × ℂ) => ∫⁻ ω, fusionInterpolatedMass γ α₁ α₂ α₃ q.1 q.2.1 q.2.2 (N ω) ^ s ∂P) by funext q; exact lintegral_congr_ae (he.mono fun ω h => by dsimp only; rw [h]))]
  exact (((((ENNReal.measurable_ofReal.comp ht).mul (fusionMovingMass_family_measurable γ α₁ α₂ α₃ (fun q : (ℝ × (ℂ × ℂ)) × Ω => N q.2) (hN.comp measurable_snd) (fun q => hf q.2) _ _ hy hz)).add ((ENNReal.measurable_ofReal.comp (measurable_const.sub ht)).mul (fusionRootOnlyMass_family_measurable γ α₁ α₂ α₃ (fun q : (ℝ × (ℂ × ℂ)) × Ω => N q.2) (hN.comp measurable_snd) (fun q => hf q.2) _ _ hy hz))).pow_const s).lintegral_prod_right')
end DOZZ.Proofs
