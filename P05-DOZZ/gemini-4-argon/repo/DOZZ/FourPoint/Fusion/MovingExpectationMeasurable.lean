/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.InverseExpectation
public import DOZZ.GMC.Construction.RootedMeasureKernel

/-! # Joint measurability of the moving inverse expectation -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem fusionMovingKernel_joint_measurable γ α₁ α₂ α₃ :
    Measurable (fun q : (ℂ × ℂ) × ℂ => fusionMovingKernel γ α₁ α₂ α₃ q.1.1 q.1.2 q.2) := by
  have hr : Measurable (fun q : (ℂ × ℂ) × ℂ => (q.1.1 * q.1.2, q.2)) :=
    ((measurable_fst.comp measurable_fst).mul (measurable_snd.comp measurable_fst)).prodMk
      measurable_snd
  change Measurable (fun q : (ℂ × ℂ) × ℂ => ENNReal.ofReal
    (gammaHalfKernel γ α₁ α₂ α₃ q.1.2 q.2 * Real.exp (γ ^ 2 * gffKernel (q.1.1 * q.1.2) q.2)))
  have hprod : Measurable (fun q : (ℂ × ℂ) × ℂ =>
    gammaHalfKernel γ α₁ α₂ α₃ q.1.2 q.2 * Real.exp (γ ^ 2 * gffKernel (q.1.1 * q.1.2) q.2)) :=
    (show Measurable (fun q : (ℂ × ℂ) × ℂ => gammaHalfKernel γ α₁ α₂ α₃ q.1.2 q.2) by simpa only [Function.comp_def] using (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).mul (by simpa only [Function.comp_def] using ((measurable_pointRootPotential.comp hr).const_mul (γ ^ 2)).exp)
  simpa only [Function.comp_def] using ENNReal.measurable_ofReal.comp hprod

/-- Measurability holds jointly in both the rescaled root and the moving insertion point. -/
theorem fusionMovingMass_expectation_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    γ (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) :
    Measurable (fun q : ℂ × ℂ => ∫⁻ ω,
      fusionMovingMass γ α₁ α₂ α₃ q.1 q.2 (M ω) ^ s ∂P) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hN, hf, he⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hm : Measurable (fun q : (ℂ × ℂ) × Ω =>
      fusionMovingMass γ α₁ α₂ α₃ q.1.1 q.1.2 (N q.2)) := by
    apply measurable_lintegral_finite_family (fun q : (ℂ × ℂ) × Ω => N q.2)
      (hN.comp measurable_snd) (fun q => hf q.2)
      (fun q : ((ℂ × ℂ) × Ω) × ℂ =>
        fusionMovingKernel γ α₁ α₂ α₃ q.1.1.1 q.1.1.2 q.2)
    simpa only [Function.comp_def] using ((fusionMovingKernel_joint_measurable γ α₁ α₂ α₃).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd : Measurable (fun q : ((ℂ × ℂ) × Ω) × ℂ => (q.1.1, q.2))))
  rw [(show (fun q : ℂ × ℂ => ∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ q.1 q.2 (M ω) ^ s ∂P) = (fun q : ℂ × ℂ => ∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ q.1 q.2 (N ω) ^ s ∂P) by funext q; exact lintegral_congr_ae (he.mono fun ω h => by dsimp only; rw [h]))]
  exact ((hm.pow_const s).lintegral_prod_right')

end DOZZ.Proofs
