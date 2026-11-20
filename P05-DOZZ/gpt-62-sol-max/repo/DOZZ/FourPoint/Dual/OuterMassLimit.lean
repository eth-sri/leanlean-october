/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.Kernel
public import DOZZ.FourPoint.Reflected.MassFiniteness
import DOZZ.FourPoint.RootedPairMoments
import Mathlib.Tactic

/-! The literal dual mass restricted outside the moving root. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The actual dual Coulomb mass restricted outside the moving fusion disk. -/
noncomputable def dualOuterMass (γ α₁ α₂ α₃ : ℝ) (μ : Measure ℂ) (z : ℂ) (ξ : ℝ) : ℝ≥0∞ :=
  coulombMass γ (μ.restrict {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖})
    ![-2 / γ, α₁, α₂] ![z, 0, 1] α₃

/-- The moving root is absent from the retained region, so no atom assumption at `z` is needed. -/
theorem dual_outerMass_eq_kernel_integral (γ α₁ α₂ α₃ ξ : ℝ) (hγ : γ ≠ 0) (z : ℂ)
    (μ : Measure ℂ) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hz : ‖z‖ < ‖z‖ ^ (1 - ξ)) :
    dualOuterMass γ α₁ α₂ α₃ μ z ξ =
      ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖},
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ := by
  simpa only [dual_kernel_eq_bpzWeight γ α₁ α₂ α₃ hγ, dualOuterMass, fusionOuterMass, ← neg_div] using
    fusionOuterMass_eq_lintegral γ (2 / γ) α₁ α₂ α₃ ξ z μ h0 h1 hz



end DOZZ.Proofs
