/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.KernelPerturbation
public import DOZZ.FourPoint.ReflectedOuter.ZeroMass
import Mathlib.Tactic
public import DOZZ.FourPoint.Fusion.RetainedMassLimit

/-! # Relative comparison of the actual retained masses -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The exterior mass comparison for any degenerate charge with radial power in `[0,2]`. -/
theorem fusionOuterMass_relative_comparison (γ χ α₁ α₂ α₃ ξ : ℝ)
    (hb : 0 ≤ γ * χ) (hb₂ : γ * χ ≤ 2) (z : ℂ) (μ : Measure ℂ)
    (hr : 0 < ‖z‖ ^ (1 - ξ)) (hz : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    RelativeMassBound (4 * (‖z‖ / ‖z‖ ^ (1 - ξ)))
      (retainedZeroMass γ (-χ) α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) μ) (fusionOuterMass γ (-χ) α₁ α₂ α₃ μ z ξ) := by
  rw [fusionOuterMass_eq_lintegral γ χ α₁ α₂ α₃ ξ z μ h0 h1 (by linarith),
    retainedZeroMass_eq_setLIntegral γ (-χ) α₁ α₂ α₃ _ μ h0 h1 _
      (fun ν h0' h1' => coulombMass_eq_lintegral_bpzSoftWeight ν 0 h0' h0' h1')]
  refine exterior_kernel_relative_mass (γ * χ) hb hb₂ z _ hr hz μ _ _
    (measurable_bpzSoftWeight 0 0) (measurable_bpzSoftWeight 0 z) (bpzSoftWeight_nonneg 0 0) ?_
  intro x hx
  simp only [bpzSoftWeight_zero, sub_zero]
  rw [Real.div_rpow (norm_nonneg _) hx.le]
  field_simp [(Real.rpow_pos_of_pos hx (γ * χ)).ne']

/-- The literal moving and zero masses have two additive comparisons and a common quarter
lower bound. The radius is exactly the outer cutoff. -/
theorem reflected_outerMass_relative_comparison (γ α₁ α₂ α₃ ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (z : ℂ) (μ : Measure ℂ)
    (hr : 0 < ‖z‖ ^ (1 - ξ)) (hz : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    RelativeMassBound (4 * (‖z‖ / ‖z‖ ^ (1 - ξ)))
      (reflectedRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) μ) (gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ) := by
  have h := fusionOuterMass_relative_comparison γ (γ / 2) α₁ α₂ α₃ ξ (by positivity)
    (by nlinarith only [hγ, hγ₂]) z μ hr hz h0 h1
  simpa only [neg_div, reflectedRetainedZeroMass, gammaHalfOuterMass, fusionOuterMass] using h

end DOZZ.Proofs
