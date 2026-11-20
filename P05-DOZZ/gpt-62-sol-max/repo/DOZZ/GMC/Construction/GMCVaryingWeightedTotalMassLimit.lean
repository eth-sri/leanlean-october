/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCVaryingWeightedTotalMass
public import DOZZ.GMC.Construction.GMCWeightedTotalMass
public import DOZZ.GMC.ConvergenceInMeasure

/-! Convergence of total cutoff masses under uniformly varying weights. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

/-- For an `IsGMCOf` limit, the total cutoff mass under a uniformly convergent family of
nonnegative bounded-continuous weights converges in measure to the limit mass under the fixed
limiting weight. -/
theorem regularizedGMC_varyingWithDensity_univ_mass_tendstoInMeasure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (u : ℝ → BoundedContinuousFunction ℂ ℝ) (hu : ∀ r z, 0 ≤ u r z)
    (v : BoundedContinuousFunction ℂ ℝ) (hv : ∀ z, 0 ≤ v z)
    (hconv : TendstoUniformly (fun r z => u r z) v atTop) :
    TendstoInMeasure P
      (fun r ω => (((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal) atTop
      (fun ω => ((M ω).withDensity
        (fun z => ENNReal.ofReal (v z)) Set.univ).toReal) := by
  let f : ℝ → Ω → ℝ := fun r ω => (((regularizedGMC P Xc γ r ω).withDensity
    (fun z => ENNReal.ofReal (u r z))) Set.univ).toReal
  let g : ℝ → Ω → ℝ := fun r ω => (((regularizedGMC P Xc γ r ω).withDensity
    (fun z => ENNReal.ofReal (v z))) Set.univ).toReal
  let y : Ω → ℝ := fun ω => ((M ω).withDensity
    (fun z => ENNReal.ofReal (v z)) Set.univ).toReal
  have hdiff : TendstoInMeasure P (fun r ω => f r ω - g r ω) atTop (fun _ => 0) := by
    simpa [f, g] using
      (regularizedGMC_varyingWithDensity_set_mass_diff_tendstoInMeasure
        P X hX Xc hXc γ u hu v hv hconv MeasurableSet.univ)
  have hfixed : TendstoInMeasure P g atTop y := by
    simpa [g, y] using
      regularizedGMC_withDensity_univ_mass_tendstoInMeasure
        P X hX Xc hXc γ M hM v hv
  simpa [f, y] using tendstoInMeasure_add_of_sub P f g y hdiff hfixed

end DOZZ.Proofs
