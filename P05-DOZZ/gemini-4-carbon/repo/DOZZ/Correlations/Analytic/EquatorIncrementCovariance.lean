/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.CirclePotential
public import DOZZ.GFFStructure.CircleCovariance

/-! The equator correction in the vertex increment argument. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- Circle mean of the regular equator pin. -/
noncomputable def equatorCircleMean (z : ℂ) (r : ℝ) : ℝ :=
  ∫ w, Real.log (normPlus w) ∂circleMeasure z r

/-- The concentric covariance retains both equator circle means. -/
theorem circle_covariance_concentric
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (r s : ℝ) :
    covariance (fun ω => Xc ω z r) (fun ω => Xc ω z s) P =
      min r s + equatorCircleMean z r + equatorCircleMean z s := by
  rw [circleAverage_covariance P X Xc hX hc]
  simp only [sub_self, nnnorm_zero, circleLogPotential_concentric, neg_neg]
  simp only [equatorCircleMean, integral_log_normPlus_circleMeasure_eq_closed]

end DOZZ.Proofs
