/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionCircleMean
public import DOZZ.GMC.Moments.InversionCutoff
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal
namespace DOZZ.Proofs


/-- The finite reflected Wick cutoff includes the scalar normalization and both deterministic
pinning corrections. This is an equality of measures on the original probability space. -/
theorem regularizedGMC_symmetryRepinned
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc)
    γ r ω :
    regularizedGMC P (fun ω x r => Xc ω (1 - x) r - Xc ω 1 0) γ r ω =
      ((regularizedGMC P Xc γ r ω).map (fun x : ℂ => 1 - x)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-γ * Xc ω 1 0 +
          γ ^ 2 * symmetryCirclePotentialMean r x + 4 * symmetryReflectionPotential x))) := by
  have reflection_circle_square_energy X (hX : IsEquatorGFF P X) Xc (hXc : IsCircleAverage P X Xc) x r : (∫ ω, Xc ω x r ^ 2 ∂P) = circleSelfEnergy x r := by
    have hc := circleAverage_covariance_self X Xc hX hXc x r
    simp only [ProbabilityTheory.covariance, ((circleAverage_isGaussianProcess P X Xc hX hXc).2 x r), sub_zero] at hc
    simpa only [pow_two] using hc
  let : IsProbabilityMeasure P := hX.1
  have hd : Measurable (fun x => ENNReal.ofReal
      (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) *
        normPlus x ^ (-4 : ℝ))) :=
    ENNReal.measurable_ofReal.comp (((Real.measurable_exp.comp
      (((hXc.1 r).comp (measurable_const.prodMk measurable_id)).const_mul γ |>.sub
        ((show Measurable (fun x => ∫ ω', Xc ω' x r ^ 2 ∂P) by exact (((hXc.1 r).comp measurable_swap).pow_const 2).stronglyMeasurable.integral_prod_right.measurable).const_mul (γ ^ 2 / 2)))).mul (((continuous_const.max continuous_norm).measurable).pow_const _)))
  have hw : Measurable (fun x => ENNReal.ofReal (Real.exp (-γ * Xc ω 1 0 +
      γ ^ 2 * symmetryCirclePotentialMean r x + 4 * symmetryReflectionPotential x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_const.add ((symmetryCirclePotentialMean r).continuous.measurable.const_mul _)).add
        (symmetryReflectionPotential_continuous.measurable.const_mul _)))
  have hdφ : Measurable (fun x => ENNReal.ofReal
      (Real.exp (γ * Xc ω (1 - x) r - γ ^ 2 / 2 * ∫ ω', Xc ω' (1 - x) r ^ 2 ∂P) *
        normPlus (1 - x) ^ (-4 : ℝ))) := hd.comp (measurable_const.sub measurable_id)
  unfold regularizedGMC
  rw [measurePreserving_involutive_map_withDensity _ _
    (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1)
    symmetryReflection_involutive _ hd, ← withDensity_mul _ hdφ hw]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  have hψ : 0 < normPlus (1 - x) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [reflection_circle_square_energy _ (isEquatorGFF_symmetryRepinnedField P X hX Xc hXc) _ (isCircleAverage_symmetryRepinned P X hX Xc hXc),
    reflection_circle_square_energy X hX Xc hXc, reflection_circle_self,
    ← symmetryCirclePotentialMean_apply, ← ENNReal.ofReal_mul
      (mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg hψ.le _))]
  congr 1
  rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _) : 0 < normPlus x), Real.rpow_def_of_pos hψ, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold symmetryReflectionPotential
  ring
end DOZZ.Proofs
