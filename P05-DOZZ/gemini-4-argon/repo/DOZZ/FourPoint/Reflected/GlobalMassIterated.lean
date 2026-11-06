/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.GlobalCompactComparison
/-! Full punctured-plane moments conditioned on the actual radial-path law. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Full weighted mass expectations on the independent source copies are the iterated
expectations over the actual radial-path law and the same global lateral carrier. -/
theorem reflected_global_mass_iterated
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → TwoSidedPath) (hA : AEMeasurable A P)
    γ (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (q : ℝ) :
    (∫⁻ ω : Ω × Ω, (∫⁻ x in ({0} : Set ℂ)ᶜ,
      f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2)^q ∂P.prod P) =
    ∫⁻ a, ∫⁻ ω, (∫⁻ x in ({0} : Set ℂ)ᶜ,
      f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω)^q ∂P ∂P.map A := by
  have hF : Measurable (fun p => (∫⁻ x in ({0} : Set ℂ)ᶜ, f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2)^q : TwoSidedPath × Ω → ℝ≥0∞) :=
    (reflected_chart_parameter_mass_measurable ({0} : Set ℂ)ᶜ
      (isClosed_singleton (x := (0 : ℂ))).isOpen_compl N hN hfin
      (fun p => f p.2*ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 p.2))
      ((hf.comp measurable_snd).mul
        (reflected_global_reinsertionWeight_measurable γ).ennreal_ofReal)).pow_const q
  exact (lintegral_prod _ (hF.comp_aemeasurable ((hA.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk measurable_snd.aemeasurable : AEMeasurable (fun ω : Ω × Ω => (A ω.1, ω.2)) (P.prod P)))).trans (lintegral_map' (hF.lintegral_prod_right' (ν := P)).aemeasurable hA).symm

end DOZZ.Proofs
