module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationMoments
import Mathlib.Tactic

/-! # Backward monotonicity and lower bounds for negative angular moments -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- The negative first moment grows as the endpoint moves to the left. -/
theorem bellmanAngularDensity_negative_lower (β ) (f h J : ℝ → ℝ)
    (hβ : 3 ≤ β) (hf : LocallyIntegrable f volume) (hn : ∀ᵐ z ∂volume, 0 ≤ f z)
    (h0 : h 0 = 0) (hj0 : J 0 = 0)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (y ) (hy : y ≤ 0) :
    (-y / 3) * bellmanAngularFirstMoment f y ≤ h y := by
  have hb := bellmanAngularSecondMoment_negative_bound hf hn hy
  have hd : 0 ≤ (β - 3) / 3 := by linarith
  have hm := mul_le_mul_of_nonneg_left hb hd
  rw [he y, h0, hj0]
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov
