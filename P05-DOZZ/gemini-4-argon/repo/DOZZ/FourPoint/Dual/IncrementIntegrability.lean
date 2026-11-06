/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.MaximumSandwich
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-! Integrability of signed inverse-power increments from the retained inverse moment. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- A nonnegative inner addition bounds the entire signed increment by the retained
inverse power, uniformly in the added mass. -/
theorem dual_negative_increment_abs_le (p A t : ℝ) (hp : 0 ≤ p)
    (hA : 0 < A) (ht : 0 ≤ t) :
    |(A+t)^(-p)-A^(-p)| ≤ A^(-p) := by
  exact abs_le.mpr ⟨by linarith only [(Real.rpow_nonneg (by positivity) _ : 0 ≤ (A+t)^(-p))], by linarith only [(Real.rpow_le_rpow_of_nonpos hA (by linarith only [ht]) (neg_nonpos.mpr hp) : (A+t)^(-p) ≤ A^(-p)), Real.rpow_nonneg hA.le (-p)]⟩

/-- No moment of the inner mass is needed for integrability of the signed increment
when the retained inverse moment is finite. -/
theorem dual_negative_increment_integrable
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p : ℝ) (hp : 0 ≤ p) (A b : Ω → ℝ) (S : Λ → ℝ)
    (hA : ∀ᵐ ω ∂P, 0 < A ω) (hb : ∀ᵐ ω ∂P, 0 ≤ b ω)
    (hS : ∀ᵐ v ∂R, 0 ≤ S v)
    (hAm : AEMeasurable A P) (hbm : AEMeasurable b P) (hSm : AEMeasurable S R)
    (hInv : Integrable (fun ω => (A ω)^(-p)) P) :
    Integrable (fun v : Ω × Λ =>
      (A v.1+b v.1*S v.2)^(-p)-(A v.1)^(-p)) (P.prod R) := by
  apply (hInv.comp_fst R).mono' (by convert (((hAm.comp_fst.add (hbm.comp_fst.mul hSm.comp_snd)).pow_const (-p)).sub (hAm.comp_fst.pow_const (-p))).aestronglyMeasurable using 1)
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hA,
    measurePreserving_fst.quasiMeasurePreserving.ae hb,
    measurePreserving_snd.quasiMeasurePreserving.ae hS] with v hAv hbv hSv
  simpa only [Real.norm_eq_abs] using
    dual_negative_increment_abs_le p (A v.1) (b v.1*S v.2) hp hAv (mul_nonneg hbv hSv)

end DOZZ.Proofs
