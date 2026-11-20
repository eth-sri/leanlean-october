/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Moments.InversionOpenMassLaw
public import DOZZ.GMC.EquatorGFFChaosTransportLaw
@[expose] public section
open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology Distributions ENNReal
namespace DOZZ.Proofs

/-- Finite random measure laws are determined by their finite vectors of open masses. -/
theorem finite_random_measure_law_of_open_fdd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (M N : Ω → Measure ℂ) (hM : AEMeasurable M P) (hN : AEMeasurable N P)
    (hMf : ∀ ω, IsFiniteMeasure (M ω)) (hNf : ∀ ω, IsFiniteMeasure (N ω))
    (hfdd : ∀ (ι : Type) [Fintype ι] (U : ι → Set ℂ), (∀ j, IsOpen (U j)) →
      P.map (fun ω j => M ω (U j)) = P.map (fun ω j => N ω (U j)))
    (H : Measure ℂ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ ω, H (M ω) ∂P = ∫⁻ ω, H (N ω) ∂P := by
  exact ((identDistrib_measure_of_mass_fdd finiteOpenMassCode_comap_eq hM hN hMf hNf
    fun s => hfdd s (fun j => j.1.1) (fun j => j.1.2)).comp hH).lintegral_eq

end DOZZ.Proofs
