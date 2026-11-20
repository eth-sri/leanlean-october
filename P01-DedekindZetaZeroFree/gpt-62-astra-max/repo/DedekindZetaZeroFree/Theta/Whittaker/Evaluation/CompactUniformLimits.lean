module

public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.CompletedContinuity

@[expose] public section

noncomputable section
open scoped Classical Topology
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype
variable {α : Type*} [TopologicalSpace α]
    (E : complexCore →ₗ[ℂ] (α → ℂ)) (he : ∀v,Continuous (E v)) (hb : CompactBound E)

include he in
theorem harmonic_uniform_on_compact (K : Set α) (hK : IsCompact K)
    (v : PrincipalSeries negativeParameter) (a : ℕ → complexCore)
    (ha : Tendsto (fun n=>smoothInclusion (a n)) atTop (𝓝 v)) :
    TendstoUniformlyOn (fun n=>E (a n)) (fun g=>extendedEvaluation E hb g v) atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp (harmonic_compact_limit E he hb K hK v a ha)) Set.univ isCompact_univ
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with n hn
  intro g hg
  have H := hn ⟨g,hg⟩ (Set.mem_univ _)
  rw [extendedCompact_eval] at H
  exact H

include he in
theorem extended_derivative_curve
    (E₁ : complexCore →ₗ[ℂ] (α → ℂ)) (he₁ : ∀v,Continuous (E₁ v)) (hb₁ : CompactBound E₁)
    (γ : ℝ → α) (hγ : Continuous γ)
    (hd : ∀u : complexCore, ∀t : ℝ, HasDerivAt (fun r=>E u (γ r)) (E₁ u (γ t)) t)
    (v : PrincipalSeries negativeParameter) (t : ℝ) :
    HasDerivAt (fun r=>extendedEvaluation E hb (γ r) v) (extendedEvaluation E₁ hb₁ (γ t) v) t := by
  obtain ⟨a,ha⟩ := exists_harmonic_sequence v
  have hu := harmonic_uniform_on_compact E₁ he₁ hb₁ _ ((isCompact_closedBall t 1).image hγ) v a ha
  have hui : TendstoUniformlyOn (fun n r=>E₁ (a n) (γ r))
      (fun r=>extendedEvaluation E₁ hb₁ (γ r) v) atTop (Metric.ball t 1) := by
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε hε
    filter_upwards [hu ε hε] with n hn
    intro r hr
    exact hn (γ r) ⟨r,Metric.ball_subset_closedBall hr,rfl⟩
  apply hasDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball hui
  · exact Eventually.of_forall (fun n r _=>hd (a n) r)
  · intro r hr
    simpa only [Function.comp_def,extendedEvaluation_core] using (((extendedEvaluation E hb (γ r)).continuous.tendsto v).comp ha)
  · exact Metric.mem_ball_self (by norm_num)
end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
