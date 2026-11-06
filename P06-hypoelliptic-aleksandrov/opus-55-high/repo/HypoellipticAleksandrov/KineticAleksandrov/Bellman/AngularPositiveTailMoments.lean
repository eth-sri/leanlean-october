module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegratedCalculus
import Mathlib.Tactic

/-! # Positive angular moment inequalities without pointwise density assumptions -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

variable {f : ℝ → ℝ}

/-- The second angular moment is nonnegative on positive oriented intervals. -/
theorem bellmanAngularSecondMoment_nonneg 
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ bellmanAngularSecondMoment f y := by
  apply intervalIntegral.integral_nonneg_of_ae hy
  filter_upwards [hf] with z hz
  positivity

/-- On the positive half-line the second moment is bounded by y times the first moment. -/
theorem bellmanAngularSecondMoment_le 
    (hi : LocallyIntegrable f volume) (hf : ∀ᵐ z ∂volume, 0 ≤ f z)
    {y : ℝ} (hy : 0 ≤ y) :
    bellmanAngularSecondMoment f y ≤ y * bellmanAngularFirstMoment f y := by
  rw [bellmanAngularFirstMoment,
    ← intervalIntegral.integral_const_mul]
  have hfirst : IntervalIntegrable (fun z => z * f z) volume 0 y := by
    simpa using bellmanAngularMoment_intervalIntegrable hi 0 y 1
  apply intervalIntegral.integral_mono_ae_restrict hy
    (bellmanAngularMoment_intervalIntegrable hi 0 y 2) (hfirst.const_mul y)
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hf] with z hz
  intro hzy
  nlinarith [mul_nonneg (sub_nonneg.mpr hzy.2) (mul_nonneg hzy.1 hz)]

/-- The integrated angular identity bounds the positive first moment using nonnegative h. -/
theorem bellmanAngularFirstMoment_bound (β : ℝ) (f h J : ℝ → ℝ)
    (hβ : 3 ≤ β) (hi : LocallyIntegrable f volume)
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) (hh : ∀ y : ℝ, 0 ≤ h y)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    {y : ℝ} (hy : 0 < y) :
    bellmanAngularFirstMoment f y ≤ 3 * (h 0 / y + J 0) := by
  have hm := bellmanAngularSecondMoment_le hi hf hy.le
  have hn := hh y
  rw [he] at hn
  apply le_of_mul_le_mul_right (a := y) _ hy
  have heq : (3 * (h 0 / y + J 0)) * y = 3 * (h 0 + J 0 * y) := by
    grind
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov
