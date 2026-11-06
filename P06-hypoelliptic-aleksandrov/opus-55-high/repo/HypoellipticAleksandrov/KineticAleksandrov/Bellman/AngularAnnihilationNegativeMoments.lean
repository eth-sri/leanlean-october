module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularAnnihilationMoments
import Mathlib.Tactic

/-! # Backward monotonicity and lower bounds for negative angular moments -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- The negative first moment grows as the endpoint moves to the left. -/
theorem bellmanAngularFirstMoment_negative_mono {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (hn : ∀ᵐ z ∂volume, 0 ≤ f z)
    (y a : ℝ) (hya : y ≤ a) (ha : a ≤ 0) :
    bellmanAngularFirstMoment f a ≤ bellmanAngularFirstMoment f y := by
  have hi (u v : ℝ) : IntervalIntegrable (fun z => z * f z) volume u v := by
    simpa using bellmanAngularMoment_intervalIntegrable hf u v 1
  have he := intervalIntegral.integral_add_adjacent_intervals (hi y a) (hi a 0)
  have hnon : (∫ z in y..a, z * f z) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hya]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hn] with z hz hfz
    exact mul_nonpos_of_nonpos_of_nonneg (hz.2.trans ha) hfz
  rw [bellmanAngularFirstMoment, bellmanAngularFirstMoment,
    intervalIntegral.integral_symm,
    intervalIntegral.integral_symm (a := y)]
  linarith

/-- The integrated angular identity gives the source negative linear lower bound. -/
theorem bellmanAngularDensity_negative_lower (β : ℝ) (f h J : ℝ → ℝ)
    (hβ : 3 ≤ β) (hf : LocallyIntegrable f volume) (hn : ∀ᵐ z ∂volume, 0 ≤ f z)
    (h0 : h 0 = 0) (hj0 : J 0 = 0)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (y : ℝ) (hy : y ≤ 0) :
    (-y / 3) * bellmanAngularFirstMoment f y ≤ h y := by
  have hb := bellmanAngularSecondMoment_negative_bound hf hn hy
  rw [he]
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov
