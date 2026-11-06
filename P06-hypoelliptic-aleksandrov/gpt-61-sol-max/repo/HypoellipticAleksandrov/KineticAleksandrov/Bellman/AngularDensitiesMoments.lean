module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesComparison
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic

/-! # Absolute continuity and derivatives of literal angular moments -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory

/-- Multiplying a locally integrable density by a polynomial preserves local integrability. -/
theorem bellman_polynomial_locallyIntegrable (f : ℝ → ℝ)
    (hf : LocallyIntegrable f ) (n : ℕ) :
    LocallyIntegrable (fun x => x ^ n * f x)  := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (hf.integrableOn_isCompact hK).continuousOn_mul (by fun_prop) hK

/-- A constant function is absolutely continuous on every interval. -/
theorem bellman_const_locallyAC (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _  => c) a b :=
  ContDiffOn.absolutelyContinuousOnInterval
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn

section
variable (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)

include hf
/-- Literal moments of a locally integrable angular density are locally absolutely continuous. -/
theorem bellman_moment_locallyAC
    (n : ℕ) (a b : ℝ) (hab : a ≤ b) : type_of% (bellman_lebesguePrimitive_locallyAC _ (bellman_polynomial_locallyIntegrable f hf n) a b hab) :=
  bellman_lebesguePrimitive_locallyAC _ (bellman_polynomial_locallyIntegrable f hf n) a b hab

/-- The flux written with its first moment has the asserted almost everywhere derivative. -/
theorem bellman_momentFlux_deriv  (j c : ℝ) :
    ∀ᵐ x, deriv (fun y => j - c * (∫ z in 0..y, z * f z)) x = -c * x * f x := by

  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral (by
      simpa using bellman_polynomial_locallyIntegrable f hf 1)] with x hx

  convert ((hasDerivAt_const x j).sub ((hx 0).const_mul c)).deriv using 1; ring
end


/-- The density written with the second moment has the asserted almost everywhere derivative. -/
theorem bellman_momentDensity_deriv (f J : ℝ → ℝ) (hf : LocallyIntegrable f )
    (hJ : LocallyIntegrable J ) (c : ℝ) :
    ∀ᵐ x, deriv (fun y => c + (∫ z in 0..y, J z) -
      (1 / 3 : ℝ) * (∫ z in 0..y, z ^ 2 * f z)) x = J x - x ^ 2 * f x / 3 := by

  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hJ,
    _root_.LocallyIntegrable.ae_hasDerivAt_integral (bellman_polynomial_locallyIntegrable f hf 2)] with x hx hix

  convert (((hasDerivAt_const x c).add (hx 0)).sub ((hix 0).const_mul (1 / 3))).deriv using 1; ring

end HypoellipticAleksandrov.KineticAleksandrov
