/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SpatialCutoffs
public import DOZZ.FourPoint.Reflected.OuterKernel
public import DOZZ.FourPoint.TwoRootedDomination
/-! Compact spatial tests for the literal reflected kernel. -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs

/-- A moving insertion of nonnegative order does not add a singularity. -/
theorem continuousOn_twoRootPowerKernel {e : ℝ} (he : 0 ≤ e) (a b p : ℝ) (z : ℂ) :
    ContinuousOn (fun x : ℂ => ‖x - z‖ ^ e * normPlus x ^ p / (‖x‖ ^ a * ‖x - 1‖ ^ b))
      ({0, 1} : Set ℂ)ᶜ := by
  intro x hx
  have hx0 : x ≠ 0 := fun h => hx (by simp [h])
  have hx1 : x ≠ 1 := fun h => hx (by simp [h])
  have h0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h1 : 0 < ‖x-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  have hn : ContinuousAt (fun x : ℂ => ‖x-z‖^e) x :=
    ((continuous_id.sub continuous_const).norm.continuousAt).rpow_const
      (Or.inr he)
  have hd0 : ContinuousAt (fun x : ℂ => ‖x‖^a) x :=
    continuous_norm.continuousAt.rpow_const (Or.inl h0.ne')
  have hd1 : ContinuousAt (fun x : ℂ => ‖x-1‖^b) x :=
    ((continuous_id.sub continuous_const).norm.continuousAt).rpow_const (Or.inl h1.ne')
  exact ((hn.mul (continuous_normPlus.continuousAt.rpow_const (Or.inl (normPlus_pos x).ne'))).div
    (hd0.mul hd1) (mul_ne_zero (Real.rpow_pos_of_pos h0 _).ne'
      (Real.rpow_pos_of_pos h1 _).ne')).continuousWithinAt

/-- The integration-point kernel is continuous away from its two singular roots; its moving
insertion has a nonnegative exponent and does not need to be excluded. -/
theorem reflected_spatial_kernel_continuousOn (γ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    ContinuousOn (gammaHalfKernel γ α₁ α₂ α₃ z) ({0, 1} : Set ℂ)ᶜ :=
  continuousOn_twoRootPowerKernel (by positivity : 0 ≤ γ ^ 2 / 2) _ _ _ z

end DOZZ.Proofs
