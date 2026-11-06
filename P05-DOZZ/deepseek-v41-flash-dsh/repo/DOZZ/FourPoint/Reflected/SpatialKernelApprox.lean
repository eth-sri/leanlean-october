/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SpatialCutoffs
public import DOZZ.FourPoint.Reflected.OuterKernelLimit
public import DOZZ.FourPoint.TwoRootedDomination
/-! Compact spatial tests for the literal reflected kernel. -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs

/-- The integration-point kernel is continuous away from its two singular roots; its moving
insertion has a nonnegative exponent and does not need to be excluded. -/
theorem reflected_spatial_kernel_continuousOn (γ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    ContinuousOn (gammaHalfKernel γ α₁ α₂ α₃ z) ({0, 1} : Set ℂ)ᶜ := by
  intro x hx
  have h0 : 0 < ‖x‖ := norm_pos_iff.mpr (fun h => hx (by simp [h]))
  have h1 : 0 < ‖x-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hx (by simp [h])))
  have hplus : Continuous normPlus := by unfold normPlus; fun_prop
  have hpp : 0 < normPlus x := by unfold normPlus; positivity
  have hn : ContinuousAt (fun x : ℂ => ‖x-z‖^(γ^2/2)) x :=
    ((continuous_id.sub continuous_const).norm.continuousAt).rpow_const
      (Or.inr (by positivity))
  have hd0 : ContinuousAt (fun x : ℂ => ‖x‖^(γ*α₁)) x :=
    continuous_norm.continuousAt.rpow_const (Or.inl h0.ne')
  have hd1 : ContinuousAt (fun x : ℂ => ‖x-1‖^(γ*α₂)) x :=
    ((continuous_id.sub continuous_const).norm.continuousAt).rpow_const (Or.inl h1.ne')
  exact ((hn.mul (hplus.continuousAt.rpow_const (Or.inl hpp.ne'))).div
    (hd0.mul hd1) (mul_ne_zero (Real.rpow_pos_of_pos h0 _).ne'
      (Real.rpow_pos_of_pos h1 _).ne')).continuousWithinAt

end DOZZ.Proofs
