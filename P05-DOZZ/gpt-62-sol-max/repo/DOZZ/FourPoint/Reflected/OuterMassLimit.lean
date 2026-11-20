/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Reflected.OuterKernel
public import DOZZ.FourPoint.Reflected.MassFiniteness
public import DOZZ.FourPoint.TaylorKernelMass
public import DOZZ.Statements.FourPoint.GammaHalfOuterMass
import Mathlib.Tactic

/-! # The literal outer mass and its subcritical limiting rho -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The moving root is absent from the retained region, so no atom assumption at `z` is needed. -/
theorem reflected_outerMass_eq_kernel_integral (γ α₁ α₂ α₃ ξ : ℝ) (z : ℂ)
    (μ : Measure ℂ) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hz : ‖z‖ < ‖z‖ ^ (1 - ξ)) :
    gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ =
      ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
  simpa only [gammaHalf_kernel_eq_bpzWeight, gammaHalfOuterMass, fusionOuterMass, ← neg_div] using
    fusionOuterMass_eq_lintegral γ (γ / 2) α₁ α₂ α₃ ξ z μ h0 h1 hz

end DOZZ.Proofs
