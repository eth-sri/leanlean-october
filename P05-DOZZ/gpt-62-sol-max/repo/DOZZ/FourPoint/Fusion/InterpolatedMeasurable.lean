/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.InterpolatedInverseMoments
public import DOZZ.FourPoint.Fusion.MovingExpectationMeasurable
public import DOZZ.FourPoint.Fusion.RootOnlyKernelMeasurable
public import DOZZ.GMC.MeasurableIntegrals
/-! # Joint measurability of the interpolated inverse expectation -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The inverse expectation is jointly measurable in time, rescaled root, and insertion. -/
theorem fusionInterpolatedMass_expectation_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) :
    Measurable (fun q : ℝ × (ℂ × ℂ) => ∫⁻ ω,
      fusionInterpolatedMass γ α₁ α₂ α₃ q.1 q.2.1 q.2.2 (M ω) ^ s ∂P) := by
  letI := hX.1
  refine measurable_lintegral_ae_parameter (equatorGFF_finiteGMC_aemeasurable P X hX γ hγ hγ2 M hM)
    (F := fun q : (ℝ × (ℂ × ℂ)) × FiniteMeasure ℂ => fusionInterpolatedMass γ α₁ α₂ α₃ q.1.1 q.1.2.1 q.1.2.2 q.2.toMeasure ^ s) ?_
  have hm (f : (ℂ × ℂ) × ℂ → ℝ≥0∞) (hf : Measurable f) :=
    (measurable_lintegral_finiteMeasure_parameter hf).comp
      ((measurable_fst.snd : Measurable (fun q : (ℝ × (ℂ × ℂ)) × FiniteMeasure ℂ => q.1.2)).prodMk measurable_snd)
  exact (((ENNReal.measurable_ofReal.comp measurable_fst.fst).mul
    (hm _ (fusionMovingKernel_joint_measurable γ α₁ α₂ α₃))).add
    ((ENNReal.measurable_ofReal.comp (measurable_const.sub measurable_fst.fst)).mul
      (hm _ (fusionRootOnlyKernel_joint_measurable γ α₁ α₂ α₃)))).pow_const s
end DOZZ.Proofs
