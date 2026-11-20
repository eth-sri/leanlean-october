/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.MeasureTheory.MeasureMassCode

public import DOZZ.GMC.EquatorGFFChaosTransport
public import DOZZ.GMC.Construction.GMCMeasurableVersion
public import DOZZ.GMC.Construction.FiniteMeasureTotalize
public import DOZZ.GMC.Moments.ChaosLawFDD

/-! Measurable-law transport for the equator field and its GMC. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

section
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (X : Ω → Distr)
  (hX : IsEquatorGFF P X) (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X') (γ : ℝ)
include hX hX'

/-- The open-mass finite-dimensional law extends from `Fin` to arbitrary finite index types. -/
theorem equatorGFF_GMC_open_mass_test_fintype_law (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (tests : ι → TestFn) (U : κ → Set ℂ) (hU : ∀ j, IsOpen (U j)) :
    IdentDistrib (fun ω => (fun i => X ω (tests i), fun j => M ω (U j)))
      (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) P P' := by
  classical
  let eι := (Fintype.equivFin ι).symm
  let eκ := (Fintype.equivFin κ).symm
  exact identDistrib_pair_pi_of_reindex eι eκ
    (equatorGFF_GMC_open_mass_test_vector_law P X hX P' X' hX' γ M hM M' hM'
      (tests ∘ eι) (U ∘ eκ) (fun j => hU (eκ j)))

/-- The joint law of the distribution-valued field and its finite GMC is determined by the
finite-dimensional laws of test evaluations and open-set masses. -/
theorem equatorGFF_GMC_law_transport (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    ∫⁻ ω, H (fun f => X ω f) (M ω) ∂P =
      ∫⁻ ω', H (fun f => X' ω' f) (M' ω') ∂P' := by
  let := hX.1
  have hm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hn := equatorGFF_GMC_aemeasurable P' X' hX' γ hγ hγ2 M' hM'
  have hf : AEMeasurable (fun ω => ((fun f : TestFn => X ω f), (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ))) P :=
    (Measurable.of_eval fun f => (hX.2 f).1).aemeasurable.prodMk (hm.subtype_mk (hfs := hM.1))
  have hg : AEMeasurable (fun ω => ((fun f : TestFn => X' ω f), (⟨M' ω, hM'.1 ω⟩ : FiniteMeasure ℂ))) P' :=
    (Measurable.of_eval fun f => (hX'.2 f).1).aemeasurable.prodMk (hn.subtype_mk (hfs := hM'.1))
  have h := identDistrib_prod_of_coded_fdd hf hg (C := id) MeasurableSpace.comap_id
    finiteOpenMassCode_comap_eq fun s t =>
      (equatorGFF_GMC_open_mass_test_fintype_law P X hX P' X' hX' γ M hM M' hM'
        (fun i : s => i.1) (fun j : t => j.1.1) (fun j => j.1.2)).map_eq
  exact (h.comp (hH.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)))).lintegral_eq

end

end DOZZ.Proofs
