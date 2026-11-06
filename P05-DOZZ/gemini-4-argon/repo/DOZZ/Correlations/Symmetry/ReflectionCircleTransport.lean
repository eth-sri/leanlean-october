/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionCircleCovariance
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- Reflection sends each uniform circle to the reflected uniform circle. -/
theorem symmetryReflection_circle_integral (f : ℂ → ℝ) (hf : Measurable f) (x : ℂ) (r : ℝ) :
    (∫ z, f (1 - z) ∂circleMeasure x r) = ∫ z, f z ∂circleMeasure (1 - x) r := by
  have hφf : Measurable (fun z : ℂ => f (1 - z)) := hf.comp (measurable_const.sub measurable_id)
  rw [integral_circleMeasure_eq_circleAverage x r _ hφf,
    integral_circleMeasure_eq_circleAverage (1 - x) r f hf]
  calc
    Real.circleAverage (fun z => f (1 - z)) x (Real.exp (-r)) =
        Real.circleAverage (fun z => f (-Real.exp (-r) * z + (1 - x))) 0 1 := by
      rw [Real.circleAverage_eq_circleAverage_zero_one]
      congr 1
      funext z
      congr 1
      ring
    _ = Real.circleAverage f (1 - x) (-Real.exp (-r)) :=
      by simpa only [Complex.ofReal_neg] using
        (Real.circleAverage_eq_circleAverage_zero_one (f := f) (c := 1 - x)
          (R := -Real.exp (-r))).symm
    _ = Real.circleAverage f (1 - x) (Real.exp (-r)) := Real.circleAverage_neg_radius

/-- The reflection potential's circle mean is the difference of the two pinning means. -/
theorem symmetryReflection_circle_potential (x : ℂ) (r : ℝ) :
    (∫ z, symmetryReflectionPotential z ∂circleMeasure x r) =
      (∫ z, Real.log (normPlus z) ∂circleMeasure (1 - x) r) -
        (∫ z, Real.log (normPlus z) ∂circleMeasure x r) := by
  have hcont : Continuous (fun z : ℂ => Real.log (normPlus (1 - z))) :=
    continuous_log_normPlus.comp (continuous_const.sub continuous_id)
  change (∫ z, Real.log (normPlus (1 - z)) - Real.log (normPlus z)
    ∂circleMeasure x r) = _
  rw [integral_sub (show Integrable (fun z : ℂ => Real.log (normPlus (1 - z))) (circleMeasure x r) by exact integrable_circleMeasure_of_circleIntegrable x r hcont.measurable hcont.continuousOn.circleIntegrable') (integrable_log_normPlus_circleMeasure x r),
    symmetryReflection_circle_integral _ continuous_log_normPlus.measurable]

/-- The mixed reflected circle potential has exactly the two pinning corrections. -/
theorem symmetryReflection_circle_kernel x z r :
    (∫ w, gffKernel (1 - z) w ∂circleMeasure (1 - x) r) =
      (∫ w, gffKernel z w ∂circleMeasure x r) + symmetryReflectionPotential z +
        (∫ w, symmetryReflectionPotential w ∂circleMeasure x r) := by
  rw [integral_gffKernel_circleMeasure, integral_gffKernel_circleMeasure,
    symmetryReflection_circle_potential]
  rw [(show ‖(1 - x) - (1 - z)‖ = ‖x - z‖ by rw [show (1 - x) - (1 - z) = -(x - z) by ring, norm_neg])]
  unfold symmetryReflectionPotential
  ring
end DOZZ.Proofs
