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
    (γ : ℝ) (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) (q : ℝ) :
    (∫⁻ ω : Ω × Ω, (∫⁻ x in ({0} : Set ℂ)ᶜ,
      f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2)^q ∂P.prod P) =
    ∫⁻ a, ∫⁻ ω, (∫⁻ x in ({0} : Set ℂ)ᶜ,
      f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω)^q ∂P ∂P.map A := by
  let F : TwoSidedPath × Ω → ℝ≥0∞ := fun p =>
    (∫⁻ x in ({0})ᶜ,
      f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2)^q
  have hF :=
    (reflected_chart_parameter_mass_measurable _ᶜ
      (isClosed_singleton).isOpen_compl N hN hfin
      (fun p => f p.2*ENNReal.ofReal _)
      ((hf.comp measurable_snd).mul
        (reflected_global_reinsertionWeight_measurable γ).ennreal_ofReal)).pow_const q
  have hp : AEMeasurable (fun ω => (A ω.1, ω.2)) (P.prod P) :=
    by fun_prop
  have he := lintegral_prod _ (hF.comp_aemeasurable hp)
  have hm := lintegral_map' (hF.lintegral_prod_right' (ν := P)).aemeasurable hA
  grind

end DOZZ.Proofs
