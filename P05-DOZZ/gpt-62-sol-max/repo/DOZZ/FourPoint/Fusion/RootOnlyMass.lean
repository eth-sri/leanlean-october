/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.Kernel
public import DOZZ.FourPoint.Fusion.RootedMass
import DOZZ.GMC.Construction.RootedMeasureKernel
import DOZZ.GMC.SharpMoments.SeibergMoment
public import DOZZ.FourPoint.Fusion.MovingMass

/-! # The moving mass after rooting at `y*z` -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The real density in the scaled one-rooted fusion integrals. -/
noncomputable def fusionRootOnlyKernel (γ α₁ α₂ α₃ : ℝ) (y z x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x * Real.exp (γ ^ 2 * gffKernel (y * z) x))

/-- The moving rooted mass, including both colliding insertion points. -/
noncomputable def fusionRootOnlyMass (γ α₁ α₂ α₃ : ℝ) (y z : ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ x, fusionRootOnlyKernel γ α₁ α₂ α₃ y z x ∂μ

theorem fusionRootOnlyMass_eq_rooted_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (y z : ℂ) :
    ∀ᵐ ω ∂P, fusionRootOnlyMass γ α₁ α₂ α₃ y z (M ω) =
      coulombMass γ (gmcRootedMeasure γ (y * z) (M ω)) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ :=
  fusionRootedMass_eq_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ 0 (y * z)

end DOZZ.Proofs
