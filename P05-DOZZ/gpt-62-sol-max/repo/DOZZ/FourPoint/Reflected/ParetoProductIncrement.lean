/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ParetoIncrement
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-! Integrating the signed Pareto coefficient against independent outer and reflection masses. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
namespace DOZZ.Proofs

/-- The scalar Pareto expectation is measurable for the actual random mass parameters. -/
theorem reflected_pareto_increment_aestronglyMeasurable
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p a : ℝ) (ha : 0 < a) (A b : Ω → ℝ) (S : Λ → ℝ)
    (hA : AEMeasurable A P) (hb : AEMeasurable b P) (hS : AEMeasurable S R) :
    AEStronglyMeasurable (fun v : Ω × Λ => ∫ w,
      ((A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p)) ∂paretoMeasure 1 a) (P.prod R) := by
  let _ : IsProbabilityMeasure (paretoMeasure 1 a) := isProbabilityMeasure_paretoMeasure zero_lt_one ha
  have hAp : AEMeasurable (fun v : Ω × Λ => A v.1) (P.prod R) :=
    hA.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving
  have hbp : AEMeasurable (fun v : Ω × Λ => b v.1) (P.prod R) :=
    hb.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving
  have hSp : AEMeasurable (fun v : Ω × Λ => S v.2) (P.prod R) :=
    hS.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving
  have hAA := hAp.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P.prod R) (ν := paretoMeasure 1 a)).quasiMeasurePreserving
  have hbb := hbp.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P.prod R) (ν := paretoMeasure 1 a)).quasiMeasurePreserving
  have hSS := hSp.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P.prod R) (ν := paretoMeasure 1 a)).quasiMeasurePreserving
  change AEMeasurable (fun v : (Ω × Λ) × ℝ => A v.1.1)
    ((P.prod R).prod (paretoMeasure 1 a)) at hAA
  change AEMeasurable (fun v : (Ω × Λ) × ℝ => b v.1.1)
    ((P.prod R).prod (paretoMeasure 1 a)) at hbb
  change AEMeasurable (fun v : (Ω × Λ) × ℝ => S v.1.2)
    ((P.prod R).prod (paretoMeasure 1 a)) at hSS
  have hpow : Measurable (fun x : ℝ => x^(-p)) := by fun_prop
  exact ((hpow.comp_aemeasurable (hAA.add ((hbb.mul hSS).mul measurable_snd.aemeasurable))).sub
      (hpow.comp_aemeasurable hAA)).aestronglyMeasurable.integral_prod_right'

/-- Pareto's leading and first-order weights are exactly the powers supplied by the
Cameron-Martin charge shift and the freezing estimate. -/
theorem reflected_pareto_parameter_weights (p a A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) :
    A^(-p)*(b/A)^a = b^a*A^(-p-a) ∧ A^(-p)*(b/A) = b*A^(-p-1) := by
  constructor
  · rw [Real.div_rpow hb hA.le, Real.rpow_sub hA]
    ring
  · rw [Real.rpow_sub_one hA.ne']
    ring

end DOZZ.Proofs
