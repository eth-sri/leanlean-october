module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegratedCalculus
import Mathlib.Tactic

/-! # Positive angular moment inequalities without pointwise density assumptions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- The second angular moment is nonnegative on positive oriented intervals. -/
theorem bellmanAngularSecondMoment_nonneg {f }
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) {y } (hy : 0 ≤ y) :
    0 ≤ bellmanAngularSecondMoment f y := by
  apply intervalIntegral.integral_nonneg_of_ae hy
  filter_upwards [hf] with z hz
  exact mul_nonneg (sq_nonneg z) hz

/- On the positive half-line the second moment is bounded by y times the first moment. -/
theorem bellmanAngularSecondMoment_le {f }
    (hi : LocallyIntegrable f volume) (hf : ∀ᵐ z ∂volume, 0 ≤ f z)
    {y } (hy : 0 ≤ y) :
    bellmanAngularSecondMoment f y ≤ y * bellmanAngularFirstMoment f y := by
  rw [bellmanAngularSecondMoment, bellmanAngularFirstMoment,
    ← intervalIntegral.integral_const_mul]
  have hfirst : IntervalIntegrable (fun z => z * f z) volume 0 y := by
    simpa only [pow_one] using bellmanAngularMoment_intervalIntegrable hi 0 y 1
  apply intervalIntegral.integral_mono_ae_restrict hy
    (bellmanAngularMoment_intervalIntegrable hi 0 y 2) (hfirst.const_mul y)
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hf] with z hz
  intro hzy
  nlinarith [mul_nonneg (sub_nonneg.mpr hzy.2) (mul_nonneg hzy.1 hz)]

/- The integrated angular identity bounds the positive first moment using nonnegative h. -/
end HypoellipticAleksandrov.KineticAleksandrov
