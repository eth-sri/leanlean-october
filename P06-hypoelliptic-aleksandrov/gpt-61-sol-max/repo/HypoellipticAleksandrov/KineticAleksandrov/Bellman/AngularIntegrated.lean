module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensities
import Mathlib.Tactic

/-! # The integrated angular identity for the actual density and flux representatives -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- Two integrations of the actual density and flux give the source angular identity. -/
theorem angular_integrated (R β : ℝ) (F H : Measure ℝ) (f h J : ℝ → ℝ)
    (hd :
    F = volume.withDensity (fun y => ENNReal.ofReal (f y)) ∧
    H = volume.withDensity (fun y => ENNReal.ofReal (h y)) ∧
    LocallyIntegrable f  ∧ (∀ᵐ y, 0 ≤ f y) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) ∧
    (∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval J a b) ∧
    (∀ᵐ y, f y ≤ h y ∧ h y ≤ R * f y) ∧
    (∀ᵐ y, deriv h y = J y - y ^ 2 * f y / 3) ∧
    (∀ᵐ y, deriv J y = -(β - 2) / 3 * y * f y)) : type_of% (bellmanAngularDensity_integrated β f h J hd.2.2.1 hd.2.2.2.2.1
    hd.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.2) := bellmanAngularDensity_integrated β f h J hd.2.2.1 hd.2.2.2.2.1
    hd.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2.2

end HypoellipticAleksandrov.KineticAleksandrov
