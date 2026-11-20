/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.AnnularMeasureLaw
public import DOZZ.GMC.Moments.InversionRadialCircleLaw
@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Distributions ENNReal NNReal
open DOZZ.Assembly
namespace DOZZ.Proofs

/-- Reverse the logarithmic-radius parameter of a continuous radial path. -/
def originReversedRadialPath (A : TwoSidedPath) : TwoSidedPath :=
  A.comp ⟨fun s : ℝ => -s, continuous_neg⟩

/-- Reversal preserves measurability up to a null event of the entire radial path. -/
theorem originReversedRadialPath_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Ω → TwoSidedPath) (hA : AEMeasurable A P) :
    AEMeasurable (fun ω => originReversedRadialPath (A ω)) P := by
  apply aemeasurable_twoSidedPath_of_eval
  intro s
  exact (ContinuousMap.measurable_eval (-s)).comp_aemeasurable hA

section
variable (γ : ℝ) (A : TwoSidedPath)

/-- The radial removal weight reverses exactly under complex inversion,
including at its stipulated zero value at the origin. -/
theorem lateralRadialWeight_inversion (x : ℂ) :
    lateralRadialWeight γ (originReversedRadialPath A) x⁻¹ = lateralRadialWeight γ A x := by
  simp only [lateralRadialWeight, norm_inv, inv_eq_zero, Real.log_inv,
    originReversedRadialPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    neg_neg, abs_neg]

/-- Inversion of the measure and reversal of its coupled radial path commute with
radial removal. This identity retains their coupling sample by sample. -/
theorem originRadialRemovedGMC_inversion_commutes (M : Measure ℂ) :
    (M.map (fun x : ℂ => x⁻¹)).withDensity (lateralRadialWeight γ (originReversedRadialPath A)) =
      (M.withDensity (lateralRadialWeight γ A)).map (fun x : ℂ => x⁻¹) := by
  have harg : Measurable (fun x : ℂ => ((γ, originReversedRadialPath A), x)) :=
    measurable_const.prodMk measurable_id
  have hw : Measurable (lateralRadialWeight γ (originReversedRadialPath A)) :=
    measurable_lateralRadialWeight.comp harg
  apply Measure.ext
  intro S hS
  rw [withDensity_apply _ hS, Measure.map_apply measurable_inv hS,
    withDensity_apply _ (hS.preimage measurable_inv), setLIntegral_map hS hw measurable_inv]
  apply setLIntegral_congr_fun (hS.preimage measurable_inv)
  intro x _
  exact lateralRadialWeight_inversion γ A x

/-- The actual polar projection `DOZZ.lateralProjectedGMC` turns simultaneous
source inversion and radial reversal into reflection of the whole cylinder
measure. -/
theorem lateralProjectedGMC_reversed_inversion (M : Measure ℂ) :
    lateralProjectedGMC γ (originReversedRadialPath A) (M.map (fun x : ℂ => x⁻¹)) =
      (lateralProjectedGMC γ A M).map (fun s : ℝ => -s) := by
  change ((M.map (fun x : ℂ => x⁻¹)).withDensity
    (lateralRadialWeight γ (originReversedRadialPath A))).map (fun x => -Real.log ‖x‖) = _
  rw [originRadialRemovedGMC_inversion_commutes, logRadiusProjection_inversion]
  rfl

end

end DOZZ.Proofs
