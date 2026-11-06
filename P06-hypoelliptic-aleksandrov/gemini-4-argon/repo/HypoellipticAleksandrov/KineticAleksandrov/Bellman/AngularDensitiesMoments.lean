module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesComparison
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic

/-! # Absolute continuity and derivatives of literal angular moments -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- Multiplying a locally integrable density by a polynomial preserves local integrability. -/
theorem bellman_polynomial_locallyIntegrable (f : ℝ → ℝ)
    (hf : LocallyIntegrable f volume) (n : ℕ) :
    LocallyIntegrable (fun x => x ^ n * f x) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (hf.integrableOn_isCompact hK).continuousOn_mul (by fun_prop) hK

/- A constant function is absolutely continuous on every interval. -/
theorem bellman_const_locallyAC (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  ContDiffOn.absolutelyContinuousOnInterval
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c)).contDiffOn

/- Literal moments of a locally integrable angular density are locally absolutely continuous. -/
theorem bellman_momentFlux_deriv (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (j c : ℝ) :
    ∀ᵐ x ∂volume, deriv (fun y => j - c * (∫ z in 0..y, z * f z)) x = -c * x * f x := by
  have hi : LocallyIntegrable (fun x => x * f x) volume := by
    simpa only [pow_one] using bellman_polynomial_locallyIntegrable f hf 1
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hi] with x hx
  convert ((hasDerivAt_const x j).sub ((hx 0).const_mul c)).deriv using 1; ring

/- The density written with the second moment has the asserted almost everywhere derivative. -/
end HypoellipticAleksandrov.KineticAleksandrov
