/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Moments.InversionMeasureLaw
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- Inversion chart law of the equator chaos. -/
theorem equatorGFF_GMC_inversion_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (H : Measure ℂ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ ω, H ((M ω).map (fun x => x⁻¹)) ∂P = ∫⁻ ω, H (M ω) ∂P := by
  let := hX.1
  let N := fun ω => (M ω).map (fun z : ℂ => z⁻¹)
  have hm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hn : AEMeasurable N P := (Measure.measurable_map _ measurable_inv).comp_aemeasurable hm
  have hN (ω : Ω) : IsFiniteMeasure (N ω) := by let := hM.1 ω; infer_instance
  exact finite_random_measure_law_of_open_fdd P N M hn hm hN hM.1
    (fun _ _ U hU => gmc_inversion_open_mass_fintype_law P X hX γ hγ hγ2 M hM hm U hU) H hH

end DOZZ.Proofs
