module

public import DedekindZetaZeroFree.Theta.Whittaker.Evaluation.ContinuousExtension

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
variable (E : complexCore →ₗ[ℂ] (α → ℂ)) (he : ∀v,Continuous (E v)) (hb : CompactBound E)

theorem harmonic_compact_limit (K : Set α) (hK : IsCompact K)
    (v : PrincipalSeries negativeParameter) (a : ℕ → complexCore)
    (ha : Tendsto (fun n=>smoothInclusion (a n)) atTop (𝓝 v)) :
    Tendsto (fun n=>compactObservation E he K (a n)) atTop (𝓝 (extendedCompact E he hb K hK v)) := by
  have ht := ((extendedCompact E he hb K hK).continuous.tendsto v).comp ha
  simpa only [Function.comp_def,extendedCompact_core] using ht

end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
