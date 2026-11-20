/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.MassComparison
public import DOZZ.FourPoint.Reflected.SpatialKernelApprox
/-! Compact spatial tests for the literal reflected kernel. -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs

/-- The integration-point kernel is continuous away from its two singular roots; its moving
insertion has a nonnegative exponent and does not need to be excluded. -/
theorem dual_kernel_continuousOn (γ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    ContinuousOn (dualFusionKernel γ α₁ α₂ α₃ z) ({0, 1} : Set ℂ)ᶜ :=
  continuousOn_twoRootPowerKernel (by norm_num : (0 : ℝ) ≤ 2) _ _ _ z

end DOZZ.Proofs
