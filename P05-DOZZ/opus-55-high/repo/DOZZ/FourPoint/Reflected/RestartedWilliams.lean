/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.RadialWindowUniform
public import DOZZ.Brownian.Lateral.BrownianWindowExponential
public import DOZZ.Correlations.Tails.WilliamsPolarMassLaw
public import DOZZ.Statements.Brownian.EquatorGFFLateralGMCDecomposition
public import DOZZ.FourPoint.Reflected.MaximumParetoLaw

/-! Deterministic restart and Williams' law for the actual source lateral projection. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Restarting an actual continuous inward Brownian half preserves its full path law. -/
theorem reflected_restarted_radial_path_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → TwoSidedPath)
    (hA : AEMeasurable A P) (hB : IsBrownianReal (fun t ω => A ω (t : ℝ)) P)
    (T : ℝ≥0) :
    P.map (fun ω => brownianShiftPath T (radialPositiveHalf (A ω))) =
      P.map (fun ω => radialPositiveHalf (A ω)) := by
  have hD := continuous_radialPositiveHalf.measurable.comp_aemeasurable hA
  have hs : Measurable (brownianShiftPath T) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
  have he := (AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hD).symm.trans
    (brownianPath_deterministic_shift_map _
      (radialPositiveHalf_map_isBrownian P A hA hB) T)
  simpa only [Function.comp_def] using he

end DOZZ.Proofs
