/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.GlobalMassIterated
/-! Transport of arbitrary two-region mass observables to a radial/lateral product law. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The complete law of a mass observable under independent radial and lateral copies. -/
abbrev Contract.radialPlaneLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Ω → TwoSidedPath) (γ : ℝ) (M N : Ω → Measure ℂ) : Prop :=
  ∀ (f : ℂ → ℝ≥0∞), Measurable f →
    ∀ G : TwoSidedPath × ℝ≥0∞ → ℝ≥0∞, Measurable G →
      (∫⁻ ω, G (A ω, ∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂M ω) ∂P) =
      ∫⁻ ω, G (A ω.1, ∫⁻ x in ({0} : Set ℂ)ᶜ,
        f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2) ∂P.prod P

/-- Splitting a nonnegative weight across disjoint regions commutes with the complete law. -/
theorem two_region_source_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Ω → TwoSidedPath) (hAr : AEMeasurable A P)
    (γ : ℝ) (M N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (hwhole : Contract.radialPlaneLaw P A γ M N)
    (k : ℂ → ℝ≥0∞) (hk : Measurable k)
    (U₀ U₁ : Set ℂ) (hU₀ : MeasurableSet U₀) (hU₁ : MeasurableSet U₁)
    (hU₀0 : U₀ ⊆ ({0} : Set ℂ)ᶜ) (hU₁0 : U₁ ⊆ ({0} : Set ℂ)ᶜ)
    (hdis : Disjoint U₀ U₁) (q : ℝ) :
    (∫⁻ ω, ((∫⁻ x in U₀, k x ∂M ω) + (∫⁻ x in U₁, k x ∂M ω))^q ∂P) =
      ∫⁻ p : TwoSidedPath × Ω,
        ((∫⁻ x in U₀, k x*ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2) +
         (∫⁻ x in U₁, k x*ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2))^q
        ∂(P.map A).prod P := by
  let U := U₀ ∪ U₁
  have hU  := hU₀.union hU₁
  have hU0  := union_subset hU₀0 hU₁0
  have hsource (μ : Measure ℂ) (f : ℂ → ℝ≥0∞) :
      (∫⁻ x in ({0} : Set ℂ)ᶜ, U.indicator f x ∂μ) =
        (∫⁻ x in U₀, f x ∂μ)+(∫⁻ x in U₁, f x ∂μ) := by
    rw [setLIntegral_indicator hU, inter_eq_left.mpr hU0]
    exact lintegral_union hU₁ hdis
  let W : TwoSidedPath × ℂ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 p.2)
  have hW  := (reflected_global_reinsertionWeight_measurable γ).ennreal_ofReal
  have hcopied (a : TwoSidedPath) (μ : Measure ℂ) :
      (∫⁻ x in ({0} : Set ℂ)ᶜ, U.indicator k x*W (a, x) ∂μ) =
        (∫⁻ x in U₀, k x*W (a, x) ∂μ)+(∫⁻ x in U₁, k x*W (a, x) ∂μ) := by
    simpa only [Set.indicator_mul_left] using hsource μ (fun x => k x*W (a, x))
  have hlaw := hwhole (U.indicator k) (hk.indicator hU)
    (fun p => p.2^q) (measurable_snd.pow_const q)
  have hit := reflected_global_mass_iterated P A hAr γ N hN hfin
    (U.indicator k) (hk.indicator hU) q
  dsimp only [W] at hcopied
  simp only [hsource, hcopied] at hlaw hit
  have hFm := reflected_chart_parameter_mass_measurable ({0} : Set ℂ)ᶜ
    (isClosed_singleton (x := (0 : ℂ))).isOpen_compl N hN hfin
    (fun p => U.indicator k p.2*W p)
    (((hk.indicator hU).comp measurable_snd).mul hW)
  have hp : Measurable (fun p : TwoSidedPath × Ω =>
      ((∫⁻ x in U₀, k x*W (p.1, x) ∂N p.2)+(∫⁻ x in U₁, k x*W (p.1, x) ∂N p.2))^q) := by
    simpa only [W, hcopied] using hFm.pow_const q
  exact hlaw.trans (hit.trans (lintegral_prod _ hp.aemeasurable).symm)

end DOZZ.Proofs
