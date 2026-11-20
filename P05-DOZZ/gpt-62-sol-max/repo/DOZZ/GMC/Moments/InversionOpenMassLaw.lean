/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Moments.InversionGlobalTestLaw
public import DOZZ.GMC.EquatorGFFChaosTransport
import DOZZ.GMC.MeasurableIntegrals
@[expose] public section
open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology Distributions ENNReal
namespace DOZZ.Proofs

/-- Inversion preserves finite vectors of open-set masses of the GMC. -/
theorem gmc_inversion_open_mass_fintype_law
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hmeas : AEMeasurable M P)
    (U : ι → Set ℂ) (hU : ∀ j, IsOpen (U j)) :
    P.map (fun ω j => (M ω).map (fun z : ℂ => z⁻¹) (U j)) =
      P.map (fun ω j => M ω (U j)) := by
  classical
  let := hX.1
  let N := fun ω => (M ω).map (fun z : ℂ => z⁻¹)
  have hN : AEMeasurable N P := (Measure.measurable_map _ measurable_inv).comp_aemeasurable hmeas
  have hNfin (ω : Ω) : IsFiniteMeasure (N ω) := by let := hM.1 ω; infer_instance
  apply (identDistrib_open_mass U hU N M (fun ω _ => by let := hNfin ω; exact measure_lt_top _ _)
    (fun ω _ => by let := hM.1 ω; exact measure_lt_top _ _) ?_).map_eq
  intro n
  let e := (Fintype.equivFin ι).symm
  let f := fun j => gmcOpenApprox (U (e j)) (hU (e j)) n
  exact identDistrib_pi_of_reindex e
    ⟨AEMeasurable.of_eval (fun j => finiteMeasure_bcf_integral_aemeasurable P N hN hNfin (f j)),
      AEMeasurable.of_eval (fun j => finiteMeasure_bcf_integral_aemeasurable P M hmeas hM.1 (f j)),
      gmc_inversion_test_vector_law P X hX γ hγ hγ2 M hM f⟩
end DOZZ.Proofs
