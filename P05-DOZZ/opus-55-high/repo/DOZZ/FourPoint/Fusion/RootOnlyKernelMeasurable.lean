/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RootOnlyMass
public import DOZZ.GMC.Construction.RootedMeasureKernel

/-! # Joint measurability of the moving inverse expectation -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem fusionRootOnlyKernel_joint_measurable (γ α₁ α₂ α₃ : ℝ) :
    Measurable (fun q : (ℂ × ℂ) × ℂ => fusionRootOnlyKernel γ α₁ α₂ α₃ q.1.1 q.1.2 q.2) := by
  have hp : Measurable (fun q : (ℂ × ℂ) × ℂ => ((0 : ℂ), q.2)) :=
    measurable_const.prodMk measurable_snd
  have hK : Measurable (fun q : (ℂ × ℂ) × ℂ => gammaHalfKernel γ α₁ α₂ α₃ 0 q.2) :=
    by simpa only [Function.comp_def] using (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp hp
  have hr : Measurable (fun q : (ℂ × ℂ) × ℂ => (q.1.1 * q.1.2, q.2)) :=
    by fun_prop
  have hD : Measurable (fun q : (ℂ × ℂ) × ℂ => Real.exp (γ ^ 2 * gffKernel (q.1.1 * q.1.2) q.2)) :=
    by simpa using ((measurable_pointRootPotential.comp hr).const_mul _).exp
  change Measurable (fun q : (ℂ × ℂ) × ℂ => ENNReal.ofReal
    (gammaHalfKernel γ α₁ α₂ α₃ 0 q.2 * Real.exp _))
  fun_prop

end DOZZ.Proofs
