/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.GlobalCompactComparison
public import DOZZ.MeasureTheory.FiniteOnChart
public import DOZZ.FourPoint.Reflected.ReinsertedRegionCode
/-! Full punctured-plane moments conditioned on the actual radial-path law. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Restricting a test to any measurable part of the punctured plane commutes with
independent radial reinsertion and disintegration over the radial path. -/
theorem radial_reinsertion_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → TwoSidedPath) (hA : AEMeasurable A P) (γ : ℝ) (M N : Ω → Measure ℂ)
    (hN : Measurable N) (hfin : ∀ ω, FiniteOnChart ({0} : Set ℂ)ᶜ (N ω))
    (hlaw : RadialReinsertionLaw P A γ M N) {S : Set ℂ} (hS : MeasurableSet S)
    (hS0 : S ⊆ ({0} : Set ℂ)ᶜ) (f : ℂ → ℝ≥0∞) (hf : Measurable f) (q : ℝ) :
    let I := ∫⁻ ω, (∫⁻ x in S, f x ∂M ω)^q ∂P
    let F := fun p : TwoSidedPath × Ω => (∫⁻ x in S,
      f x * ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2)^q
    I = (∫⁻ p, F p ∂(P.map A).prod P) ∧ I = (∫⁻ a, ∫⁻ ω, F (a, ω) ∂P ∂P.map A) := by
  let U : Set ℂ := {0}ᶜ
  let W (a : TwoSidedPath) (x : ℂ) := ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)
  let F := fun p : TwoSidedPath × Ω => (∫⁻ x in S, f x * W p.1 x ∂N p.2)^q
  have hfS := hf.indicator hS
  have he (μ : Measure ℂ) (g : ℂ → ℝ≥0∞) :
      (∫⁻ x in U, S.indicator g x ∂μ) = ∫⁻ x in S, g x ∂μ := by
    rw [setLIntegral_indicator hS, inter_eq_left.mpr hS0]
  have hw (a : TwoSidedPath) (μ : Measure ℂ) :
      (∫⁻ x in U, S.indicator f x * W a x ∂μ) = ∫⁻ x in S, f x * W a x ∂μ := by
    simp_rw [← Set.indicator_mul_left, he]
  have hF : Measurable F := (reflected_reinserted_region_measurable hN hfin γ hS hS0 hf).pow_const q
  have hL := hlaw (S.indicator f) hfS (fun p => p.2^q) (measurable_snd.pow_const q)
  dsimp only [U, W] at he hw
  simp only [he, hw] at hL
  have hp := (hA.comp_fst (ν := P)).prodMk (measurable_snd.aemeasurable (μ := P.prod P))
  have hi := lintegral_prod _ (hF.comp_aemeasurable hp)
  have hm := lintegral_map' (hF.lintegral_prod_right' (ν := P)).aemeasurable hA
  have hI := hL.trans (hi.trans hm.symm)
  exact ⟨hI.trans (lintegral_prod F hF.aemeasurable).symm, hI⟩

end DOZZ.Proofs
